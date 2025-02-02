------------------------------ MODULE GodotSync -----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets, hlc, raft, parallelcommits

CONSTANTS
    GodotNodes,        \* Initial node tree structure in LCRS form
    Shards,            \* {s1, s2} for multi-shard transactions  
    MaxLatency,        \* Maximum network delay (ticks)
    NodeID,            \* 1..1000
    SceneOperations    \* Set of valid scene operations

VARIABLES
    (* Multi-Raft Consensus *)
    shardLogs,        \* [ShardID ↦ Seq(LogEntry)]
    shardTerms,       \* [ShardID ↦ Nat]
    shardCommitIndex, \* [ShardID ↦ Nat]
    shardLeaders,     \* [ShardID ↦ NodeID]
    
    (* Hybrid Logical Clocks *)
    pt, l, c, pc,
    
    (* Godot Scene State *)
    sceneState,         \* [node ↦ [left_child, right_sibling, properties]]
    pendingTxns,       \* [txnId ↦ [status, shards, hlc, ops]]
    appliedIndex,      \* Last applied log index per node
    
    (* Coordination *)
    preparedHLCs,     \* [ShardID ↦ Seq(HLC)] for parallel commit
    commitThresholds, \* [txnId ↦ [shard ↦ Nat]]
    shardMap,         \* [node ↦ SUBSET Shards]
    crashed           \* Set of crashed nodes

(*--------------------------- Type Definitions ----------------------------*)
HLC == <<pt[self], l[self], c[self]>>  \* Combined HLC tuple

SceneOp ==
    [ type: {"add_child", "add_sibling", "remove_node", "move_shard",
            "set_property", "move_subtree", "remove_property", 
            "batch_update", "create_root", "remove_subtree", "batch_structure",
            "move_child"},
      target: NodeID,    \* For add_child/add_sibling: target node
      new_node: NodeID, \* For add_child/add_sibling: new node ID
      node: NodeID,     \* Node to act on
      parent: NodeID,   \* For move_child: parent node
      child_node: NodeID, \* For move_child: node to move
      to_index: Int,    \* For move_child: target position
      properties: JSON, \* Initial properties for new nodes
      key: STRING,      \* For property operations
      value: STRING,     \* For set_property
      new_parent: NodeID,  \* For move_subtree
      new_sibling: NodeID, \* For move_subtree
      updates: Seq([node: NodeID, key: STRING, value: STRING]),
      structure_ops: Seq(SceneOp),
      new_shard: Shards ]  \* For move_shard

TxnState ==
    [ txnId: Nat,
      status: {"PREPARED", "COMMITTING", "COMMITTED", "ABORTED"},
      shards: SUBSET Shards,
      coordShard: Shards,  \* Coordinator shard for parallel commit
      hlc: HLC,
      ops: Seq(SceneOp) ]

JSON == [key ↦ STRING]  \* Simplified JSON representation

(*-------------------------- Raft-HLC Integration --------------------------*)
ShardLogEntry == [term: Nat, cmd: SceneOp ∨ TxnState, hlc: HLC, shard: Shards]

LeaderAppend(shard, op) ==
    LET entry == [term ↦ shardTerms[shard], cmd ↦ op, hlc ↦ HLC, shard ↦ shard]
    IN  ∧ shardLogs' = [shardLogs EXCEPT ![shard] = Append(shardLogs[shard], entry)]
        ∧ SendToShard(shard, entry)
        ∧ AdvanceHLC()
        ∧ UNCHANGED <<shardTerms, shardCommitIndex>>

(*-------------------------- Scene Tree Operations -----------------------*)
ApplySceneOp(op) ==
    LET RemoveFromOriginalParent(n, p) ==
        CASE
            sceneState[p].left_child = n →
                sceneState' = [sceneState EXCEPT ![p].left_child = sceneState[n].right_sibling]
            [] sceneState[p].right_sibling = n →
                sceneState' = [sceneState EXCEPT ![p].right_sibling = sceneState[n].right_sibling]
        ESAC
    LET Descendants(n) == 
        LET Children == { sceneState[n].left_child } ∪ { m ∈ DOMAIN sceneState : ∃ k ∈ DOMAIN sceneState : m = sceneState[k].right_sibling }
        IN  IF Children = {} THEN {n} ELSE {n} ∪ UNION { Descendants(c) : c ∈ Children } 
    LET OrderedChildren(p) ==
        LET Rec(n) == IF n = NULL THEN << >> 
                      ELSE Append(Rec(sceneState[n].right_sibling), n)
        IN Reverse(Rec(sceneState[p].left_child))
    LET RebuildSiblingLinks(p, children) ==
        IF children = << >> 
        THEN [sceneState EXCEPT ![p].left_child = NULL]
        ELSE LET first == Head(children)
                  rest == Tail(children)
             IN  LET UpdateSiblings(s, i) ==
                      IF i > Len(rest) THEN s
                      ELSE [s EXCEPT ![children[i]].right_sibling = 
                            IF i = Len(rest) THEN NULL ELSE children[i+1]]
             IN  [sceneState EXCEPT 
                  ![p].left_child = first,
                  Iterate(i ∈ 1..Len(rest): UpdateSiblings(@, i))]
    IN
    CASE op.type = "add_child" →
        LET target == op.target IN
        LET new == op.new_node IN
        sceneState' = [sceneState EXCEPT
                      ![target].left_child = new,
                      ![new] = [ left_child ↦ NULL,
                                right_sibling ↦ sceneState[target].left_child,
                                properties ↦ op.properties ]]
    [] op.type = "add_sibling" →
        LET target == op.target IN
        LET new == op.new_node IN
        sceneState' = [sceneState EXCEPT
                      ![target].right_sibling = new,
                      ![new] = [ left_child ↦ NULL,
                                right_sibling ↦ sceneState[target].right_sibling,
                                properties ↦ op.properties ]]
    [] op.type = "remove_node" →
        LET M == op.node IN
        ∧ sceneState[M].left_child = NULL  \* Precondition: no children
        ∧ LET XWithLeft == {X ∈ DOMAIN sceneState : sceneState[X].left_child = M} IN
          LET YWithRight == {Y ∈ DOMAIN sceneState : sceneState[Y].right_sibling = M} IN
          sceneState' = [ X ∈ DOMAIN sceneState ∖ {M} ↦
              IF X ∈ XWithLeft THEN
                  [sceneState[X] EXCEPT !.left_child = sceneState[M].right_sibling]
              ELSE IF X ∈ YWithRight THEN
                  [sceneState[X] EXCEPT !.right_sibling = sceneState[M].right_sibling]
              ELSE
                  sceneState[X] ]
    [] op.type = "remove_subtree" →
        LET node == op.node IN
        LET descendants == Descendants(node) IN
        ∧ ∀ n ∈ descendants:
            sceneState' = [sceneState EXCEPT ![n] = UNDEFINED]
        ∧ ∀ parent ∈ DOMAIN sceneState:
            IF sceneState[parent].left_child ∈ descendants THEN
                sceneState' = [sceneState EXCEPT ![parent].left_child = NULL]
            ELSE IF sceneState[parent].right_sibling ∈ descendants THEN
                sceneState' = [sceneState EXCEPT ![parent].right_sibling = NULL]
    [] op.type = "set_property" →
        sceneState' = [sceneState EXCEPT
                      ![op.node].properties[op.key] = op.value ]
    [] op.type = "move_subtree" →
        LET originalParent == CHOOSE p ∈ DOMAIN sceneState : 
                                sceneState[p].left_child = op.node ∨ 
                                sceneState[p].right_sibling = op.node
        IN
        ∧ RemoveFromOriginalParent(op.node, originalParent)
        ∧ IF op.new_sibling ≠ NULL 
            THEN sceneState' = [sceneState EXCEPT
                               ![op.new_parent].right_sibling = op.node,
                               ![op.node].right_sibling = sceneState[op.new_sibling].right_sibling]
            ELSE sceneState' = [sceneState EXCEPT
                               ![op.new_parent].left_child = op.node,
                               ![op.node].right_sibling = sceneState[op.new_parent].left_child]
    [] op.type = "remove_property" →
        sceneState' = [sceneState EXCEPT
                      ![op.node].properties = [k ∈ DOMAIN sceneState[op.node].properties ∖ {op.key} ↦
                                               sceneState[op.node].properties[k]]]
    [] op.type = "batch_update" →
        LET ApplySingleUpdate(s, update) ==
            [s EXCEPT ![update.node].properties[update.key] = update.value]
        IN
        sceneState' = FoldLeft(ApplySingleUpdate, sceneState, op.updates)
    [] op.type = "batch_structure" →
        LET ApplyOp(state, op) ==
            IF op.type ∈ DOMAIN SceneOperations THEN ApplySceneOp(op) ELSE state
        IN
        sceneState' = FoldLeft(ApplyOp, sceneState, op.structure_ops)
    [] op.type = "create_root" →  \* Root creation
        LET new == op.new_node IN
        sceneState' = [sceneState EXCEPT ![new] = [left_child ↦ NULL, right_sibling ↦ NULL, properties ↦ op.properties]]
    [] op.type = "move_child" →
        LET p == op.parent
            c == op.child_node
            current == OrderedChildren(p)
            adj_idx == IF op.to_index < 0 THEN Len(current) + op.to_index ELSE op.to_index
        IN
        IF c ∉ current ∨ adj_idx < 0 ∨ adj_idx >= Len(current)
        THEN UNCHANGED sceneState
        ELSE
            LET filtered == [x ∈ current : x ≠ c]
                new_order == SubSeq(filtered, 1, adj_idx) ◦ <<c>> ◦ SubSeq(filtered, adj_idx+1, Len(filtered))
            IN
            sceneState' = RebuildSiblingLinks(p, new_order)
    [] op.type = "move_shard" →
        ∧ IF Cardinality(Server) = 1 
            THEN shardMap' = [shardMap EXCEPT ![op.node] = @ ∪ {op.new_shard}]
            ELSE ∧ shardMap' = [shardMap EXCEPT ![op.node] = {op.new_shard}]
                ∧ LeaderAppend(op.new_shard, [type: "shard_leave", node: op.node, 
                                            old_shard: shardMap[op.node]])
        ∧ LET stateEntry == [type: "state_transfer", node: op.node, 
                             state: sceneState[op.node], hlc: HLC]
          IN LeaderAppend(op.new_shard, stateEntry)
        ∧ IF Cardinality(Server) > 1 
            THEN ∀ s ∈ shardMap[op.node] :
                    LeaderAppend(s, [type: "shard_remove", node: op.node])
            ELSE UNCHANGED shardLogs
        ∧ UNCHANGED <<sceneState>>  \* Structural changes handled via state transfer

(*-------------------------- Crash Recovery --------------------------*)
RecoverNode(n) ==
    ∧ n ∈ crashed
    ∧ appliedIndex' = [appliedIndex EXCEPT ![n] = 0]
    ∧ WHILE appliedIndex[n] < shardCommitIndex[n] DO
        LET entry = shardLogs[shard][appliedIndex[n] + 1]
        IN  CASE entry.cmd.type = "state_transfer" →
                sceneState' = [sceneState EXCEPT ![entry.cmd.node] = entry.cmd.state]
            [] OTHER →
                IF entry.shard ∈ shardMap[n] THEN ApplySceneOp(entry.cmd) ELSE UNCHANGED
        ∧ appliedIndex' = [appliedIndex EXCEPT ![n] = appliedIndex[n] + 1]
    ∧ crashed' = crashed ∖ {n}

(*-------------------------- Parallel Commit Protocol -----------------------*)
StartParallelCommit(txn) ==
    LET coordShard == CHOOSE s ∈ txn.shards : TRUE
    LET txnEntry == [txn EXCEPT !.status = "COMMITTING", !.coordShard = coordShard]
    IN
    ∧ pendingTxns' = [pendingTxns EXCEPT ![txn.txnId] = txnEntry]
    ∧ ∀ s ∈ txn.shards : 
        IF s = coordShard
        THEN LeaderAppend(s, txnEntry)
        ELSE LeaderAppend(s, [type: "COMMIT", txnId: txn.txnId, hlc: txn.hlc])

CheckParallelCommit(txnId) ==
    LET txn == pendingTxns[txnId]
    LET committedInShard(s) ==
        ∃ idx ∈ 1..Len(shardLogs[s]) : 
            ∧ shardLogs[s][idx].cmd.txnId = txnId
            ∧ idx ≤ shardCommitIndex[s]
    IN
    IF ∀ s ∈ txn.shards : committedInShard(s)
    THEN ∧ pendingTxns' = [pendingTxns EXCEPT ![txnId].status = "COMMITTED"]
         ∧ ApplyTxnOps(txn.ops)
    ELSE IF pc[self] - txn.hlc > MaxLatency
    THEN AbortTxn(txnId)

(*---------------------- Transaction Handling -----------------------*)
CheckConflicts(txn) ==
    LET committedOps == UNION { {entry.cmd} : s ∈ Shards, entry ∈ shardLogs[s][1..shardCommitIndex[s]] }
    IN
    ∀ op ∈ txn.ops:
        ∀ entry ∈ committedOps:
            CASE entry.type = "COMMIT" :
                ∃ op2 ∈ pendingTxns[entry.txnId].ops : 
                    Conflict(op, op2) ∧ entry.hlc < txn.hlc
            [] OTHER :
                Conflict(op, entry) ∧ entry.hlc < txn.hlc
            ⇒ AbortTxn(txn.txnId)
    ∧ ∀ s ∈ txn.shards :
        preparedHLCs[s] = Append(preparedHLCs[s], txn.hlc)

Conflict(op1, op2) ==
    ∨ (op1.node = op2.node ∧ (IsWrite(op1) ∧ IsWrite(op2)) 
       ∧ (op1.key = op2.key ∨ op1.type ∉ {"set_property", "remove_property"}))
    ∨ (op1.type = "create_root" ∧ op2.type = "create_root" ∧ op1.new_node = op2.new_node)
    ∨ (IsTreeMod(op1) ∧ (op2.node ∈ Descendants(op1.node) ∨ op1.node ∈ Descendants(op2.node)))
    ∨ (IsTreeMod(op2) ∧ (op1.node ∈ Descendants(op2.node) ∨ op2.node ∈ Descendants(op1.node)))
    ∨ (op1.type = "move_child" ∧ op2.type = "move_child" 
       ∧ op1.parent = op2.parent ∧ op1.child_node = op2.child_node)
    ∨ (op1.type = "move_child" ∧ op2.type ∈ {"add_child", "add_sibling"} 
       ∧ op1.parent = op2.target)

IsWrite(op) == op.type ∈ {"set_property", "remove_property"}
IsTreeMod(op) == op.type ∈ {"move_subtree", "remove_node", "remove_subtree", "create_root", "move_child"}

(*-------------------------- Safety Invariants ----------------------------*)
Linearizability ==
    ∀ s1, s2 ∈ Shards:
        ∀ i ∈ 1..Len(shardLogs[s1]):
            ∀ j ∈ 1..Len(shardLogs[s2]):
                shardLogs[s1][i].hlc < shardLogs[s2][j].hlc ⇒ 
                    ¬∃ op1 ∈ shardLogs[s1][i].cmd, op2 ∈ shardLogs[s2][j].cmd : 
                        Conflict(op1, op2)

NoOrphanNodes ==
    LET Roots == { n ∈ DOMAIN sceneState : 
                     ∀ m ∈ DOMAIN sceneState : 
                         n ≠ sceneState[m].left_child ∧ n ≠ sceneState[m].right_sibling } IN
    LET R(m, n) == n = sceneState[m].left_child ∨ n = sceneState[m].right_sibling IN
    LET Reachable == { n ∈ DOMAIN sceneState : 
                         ∃ path ∈ Seq(DOMAIN sceneState) : 
                             ∧ Head(path) ∈ Roots 
                             ∧ ∀ i ∈ 1..Len(path)-1 : R(path[i], path[i+1]) } IN
    DOMAIN sceneState ⊆ Reachable

TransactionAtomicity ==
    ∀ txn ∈ pendingTxns:
        txn.status = "COMMITTED" ⇒ 
            ∀ op ∈ txn.ops:
                CASE op.type ∈ {"add_child", "add_sibling", "create_root"} →
                    op.new_node ∈ DOMAIN sceneState
                [] op.type = "remove_node" ∨ op.type = "remove_subtree" →
                    op.node ∉ DOMAIN sceneState
                [] OTHER → TRUE
        txn.status = "ABORTED" ⇒ 
            ∀ op ∈ txn.ops:
                CASE op.type ∈ {"add_child", "add_sibling", "create_root"} →
                    op.new_node ∉ DOMAIN sceneState
                [] OTHER → TRUE

NoDanglingIntents ==
    ∀ txn ∈ DOMAIN pendingTxns:
        pendingTxns[txn].status = "COMMITTED" ⇒ 
            ∀ s ∈ pendingTxns[txn].shards:
                ∃! entry ∈ shardLogs[s] : entry.cmd.txnId = txn

CrossShardAtomicity ==
    ∀ t1, t2 ∈ pendingTxns :
        t1 ≠ t2 ∧ t1.status ≠ "ABORTED" ∧ t2.status ≠ "ABORTED"
        ∧ ∃ s ∈ t1.shards ∩ t2.shards
        ⇒ ¬∃ op1 ∈ t1.ops, op2 ∈ t2.ops : Conflict(op1, op2)
    ∀ t1, t2 ∈ pendingTxns:
        t1 ≠ t2 ∧ ∃ node: shardMap[node] ∈ t1.shards ∩ t2.shards
        ⇒ ¬∃ op1 ∈ t1.ops, op2 ∈ t2.ops: Conflict(op1, op2)

NoPartialBatches ==
    ∀ entry ∈ UNION {shardLogs[s] : s ∈ Shards} :
        entry.cmd.type = "batch_update" ⇒
            ∀ update ∈ entry.cmd.updates :
                ∃! e ∈ UNION {shardLogs[s] : s ∈ Shards} : e.hlc = entry.hlc ∧ e.cmd.node = update.node

PropertyTombstoneConsistency ==  
    ∀ n ∈ DOMAIN sceneState :
        ∀ k ∈ DOMAIN sceneState[n].properties :
            ∃! e ∈ UNION {shardLogs[s] : s ∈ Shards} : 
                e.cmd.node = n ∧ 
                e.cmd.key = k ∧ 
                (e.cmd.type = "set_property" ∨ e.cmd.type = "remove_property")

SiblingOrderConsistency ==
    ∀ p ∈ DOMAIN sceneState:
        LET children == OrderedChildren(p) IN
        ∀ i ∈ 1..Len(children)-1:
            sceneState[children[i]].right_sibling = children[i+1]            
ParallelCommitConsistency ==
    ∀ txn ∈ pendingTxns : txn.status = "COMMITTED" ⇒ ∀ s ∈ txn.shards : ∃! e ∈ shardLogs[s] : e.cmd.txnId = txn.txnId

(*-------------------------- Configuration ---------------------------------*)
ASSUME 
    ∧ Cardinality(Server) = 3
    ∧ Cardinality(Shards) = 2
    ∧ MaxLatency = 16
    ∧ GodotNodes ≠ {}
    ∧ NodeID ⊆ 1..1000
    ∧ IsValidLCRSTree(GodotNodes)
    ∧ IF Cardinality(Server) = 1
        THEN ∀ n ∈ NodeID : shardMap[n] = Shards
        ELSE ∧ ∀ n ∈ NodeID : Cardinality(shardMap[n]) = 1
             ∧ ∀ s ∈ Shards : 
                 Cardinality({n ∈ NodeID : s ∈ shardMap[n]}) ≥ 3
             ∧ ∀ n ∈ NodeID : ∃! s ∈ Shards : s ∈ shardMap[n]
    ∧ preparedHLCs = [s ∈ Shards ↦ << >>]
    ∧ crashed = {} 

=============================================================================

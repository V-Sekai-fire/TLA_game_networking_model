------------------------------ MODULE GodotSync -----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets, hlc, raft, parallelcommits

CONSTANTS
    GodotNodes,        \* Initial node tree structure in LCRS form
    Shards,            \* {s1, s2} for multi-shard transactions  
    MaxLatency,        \* Maximum network delay (ticks)
    NodeID,            \* 1..1000
    SceneOperations,   \* Set of valid scene operations
    NULL               \* Representing null node reference

VARIABLES
    (* Multi-Raft Consensus *)
    shardLogs,        \* [ShardID |-> Seq(LogEntry)]
    shardTerms,       \* [ShardID |-> Nat]
    shardCommitIndex, \* [ShardID |-> Nat]
    shardLeaders,     \* [ShardID |-> NodeID]
    
    (* Hybrid Logical Clocks *)
    pt, l, c, pc,
    
    (* Godot Scene State *)
    sceneState,         \* [node |-> [left_child, right_sibling, properties]]
    pendingTxns,       \* [txnId |-> [status, shards, hlc, ops]]
    appliedIndex,      \* Last applied log index per node
    
    (* Shard Mapping *)
    shardMap,         \* [node |-> SUBSET Shards]
    crashed           \* Set of crashed nodes

(*--------------------------- Type Definitions ----------------------------*)
HLC == <<pt[self], l[self], c[self]>>  \* Combined HLC tuple

SceneOp ==
    [ type: {"add_child", "add_sibling", "remove_node", "move_shard",
            "set_property", "move_subtree", "remove_property", 
            "batch_update", "batch_structure", "move_child"},
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
      status: {"COMMITTING", "COMMITTED", "ABORTED"},
      shards: SUBSET Shards,
      coordShard: Shards,  \* Coordinator shard for parallel commit
      hlc: HLC,
      ops: Seq(SceneOp) ]

JSON == [key |-> STRING]  \* Simplified JSON representation

(*-------------------------- Raft-HLC Integration --------------------------*)
ShardLogEntry == [term: Nat, cmd: SceneOp \/ TxnState, hlc: HLC, shard: Shards]

LeaderAppend(shard, op) ==
    LET entry == [term |-> shardTerms[shard], cmd |-> op, hlc |-> HLC, shard |-> shard]
    IN  /\ shardLogs' = [shardLogs EXCEPT ![shard] = Append(shardLogs[shard], entry)]
        /\ SendToShard(shard, entry)
        /\ AdvanceHLC()
        /\ UNCHANGED <<shardTerms, shardCommitIndex>>

(*-------------------------- Scene Tree Operations -----------------------*)
ApplySceneOp(op) ==
    LET RemoveFromOriginalParent(n, p) ==
        CASE
            sceneState[p].left_child = n ->
                sceneState' = [sceneState EXCEPT ![p].left_child = sceneState[n].right_sibling]
          [] sceneState[p].right_sibling = n ->
                sceneState' = [sceneState EXCEPT ![p].right_sibling = sceneState[n].right_sibling]
        END
    LET Descendants(n) == 
        LET Children == { sceneState[n].left_child } \cup { m \in DOMAIN sceneState : \E k \in DOMAIN sceneState : m = sceneState[k].right_sibling }
        IN  IF Children = {} THEN {n} ELSE {n} \cup UNION { Descendants(c) : c \in Children } 
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
                  Iterate(i \in 1..Len(rest): UpdateSiblings(@, i))]
    IN
    CASE op.type = "add_child" ->
        LET target == op.target IN
        LET new == op.new_node IN
        IF target = NULL THEN
            \* Handle root creation
            sceneState' = [sceneState EXCEPT
                          ![new] = [ left_child |-> NULL,
                                    right_sibling |-> NULL,
                                    properties |-> op.properties ]]
        ELSE
            \* Existing add_child logic for non-NULL parent
            sceneState' = [sceneState EXCEPT
                          ![target].left_child = new,
                          ![new] = [ left_child |-> NULL,
                                    right_sibling |-> sceneState[target].left_child,
                                    properties |-> op.properties ]]
  [] op.type = "add_sibling" ->
        LET target == op.target IN
        LET new == op.new_node IN
        sceneState' = [sceneState EXCEPT
                      ![target].right_sibling = new,
                      ![new] = [ left_child |-> NULL,
                                right_sibling |-> sceneState[target].right_sibling,
                                properties |-> op.properties ]]
  [] op.type = "remove_node" ->
      LET node == op.node IN
      LET descendants == Descendants(node) IN
      /\ sceneState' = [n \in DOMAIN sceneState \ descendants |-> sceneState[n]]
      /\ \A parent \in DOMAIN sceneState :
          IF sceneState[parent].left_child \in descendants THEN
              sceneState'[parent].left_child = NULL
          ELSE IF sceneState[parent].right_sibling \in descendants THEN
              sceneState'[parent].right_sibling = NULL
  [] op.type = "set_property" ->
        sceneState' = [sceneState EXCEPT
                      ![op.node].properties[op.key] = op.value ]
  [] op.type = "move_subtree" ->
        LET originalParent == CHOOSE p \in DOMAIN sceneState : 
                                sceneState[p].left_child = op.node \/ 
                                sceneState[p].right_sibling = op.node
        IN
        /\ RemoveFromOriginalParent(op.node, originalParent)
        /\ IF op.new_sibling /= NULL 
            THEN sceneState' = [sceneState EXCEPT
                               ![op.new_parent].right_sibling = op.node,
                               ![op.node].right_sibling = sceneState[op.new_sibling].right_sibling]
            ELSE sceneState' = [sceneState EXCEPT
                               ![op.new_parent].left_child = op.node,
                               ![op.node].right_sibling = sceneState[op.new_parent].left_child]
  [] op.type = "remove_property" ->
        sceneState' = [sceneState EXCEPT
                      ![op.node].properties = [k \in DOMAIN sceneState[op.node].properties \ {op.key} |->
                                               sceneState[op.node].properties[k]]]
  [] op.type = "batch_update" ->
        LET ApplySingleUpdate(s, update) ==
            [s EXCEPT ![update.node].properties[update.key] = update.value]
        IN
        sceneState' = FoldLeft(ApplySingleUpdate, sceneState, op.updates)
  [] op.type = "batch_structure" ->
        LET ApplyOp(state, op) ==
            IF op.type \in DOMAIN SceneOperations THEN ApplySceneOp(op) ELSE state
        IN
        sceneState' = FoldLeft(ApplyOp, sceneState, op.structure_ops)
  [] op.type = "move_child" ->
        LET p == op.parent
            c == op.child_node
            current == OrderedChildren(p)
            adj_idx == IF op.to_index < 0 THEN Len(current) + op.to_index ELSE op.to_index
        IN
        IF c \notin current \/ adj_idx < 0 \/ adj_idx >= Len(current)
        THEN UNCHANGED sceneState
        ELSE
            LET filtered == [x \in current : x /= c]
                new_order == SubSeq(filtered, 1, adj_idx) \o <<c>> \o SubSeq(filtered, adj_idx+1, Len(filtered))
            IN
            sceneState' = RebuildSiblingLinks(p, new_order)
  [] op.type = "move_shard" ->
        LET old_shards = shardMap[op.node]
            descendants = Descendants(op.node)  \* Get full subtree
            original_parent = CHOOSE p \in DOMAIN sceneState : 
                                 sceneState[p].left_child = op.node \/ 
                                 sceneState[p].right_sibling = op.node
        IN /\ \A n \in descendants :
                /\ LeaderAppend(op.new_shard, [type: "state_transfer", node: n, 
                                           state: sceneState[n], hlc: HLC])
                /\ shardMap' = [shardMap EXCEPT ![n] = {op.new_shard}]
                /\ \A s \in old_shards : 
                    LeaderAppend(s, [type: "shard_remove", node: n])
        \* Detach from original parent (cross-shard operation)
        /\ IF original_parent /= NULL THEN
            LET detach_op = [type: "detach_child", node: original_parent, child: op.node]
            IN \A s \in shardMap[original_parent] :
                LeaderAppend(s, detach_op)
        \* Attach to new parent in target shard (atomic with move)
        /\ IF op.new_parent /= NULL THEN
            LET attach_op = [type: "attach_child", node: op.new_parent, 
                            child: op.node, position: op.position]
            IN LeaderAppend(op.new_shard, attach_op)
        \* Preserve structure if no new parent (use add_child with NULL target)
        /\ IF op.new_parent = NULL THEN
            LeaderAppend(op.new_shard, [type: "add_child", target: NULL, new_node: op.node, properties: sceneState[op.node].properties])
        \* Cleanup old shard references
        /\ \A s \in old_shards :
            LeaderAppend(s, [type: "shard_remove", node: op.node])
        /\ UNCHANGED <<sceneState>>  \* State transfers handle structure

(*-------------------------- Crash Recovery --------------------------*)
RecoverNode(n) ==
    /\ n \in crashed
    /\ appliedIndex' = [appliedIndex EXCEPT ![n] = 0]
    /\ \A idx \in 0..(shardCommitIndex[n] - appliedIndex[n] - 1):
        LET entry = shardLogs[shard][appliedIndex[n] + idx + 1]
        IN  CASE entry.cmd.type = "state_transfer" ->
                sceneState' = [sceneState EXCEPT ![entry.cmd.node] = entry.cmd.state]
            [] OTHER ->
                IF entry.shard \in shardMap[n] THEN ApplySceneOp(entry.cmd) ELSE UNCHANGED
        /\ appliedIndex' = [appliedIndex EXCEPT ![n] = appliedIndex[n] + 1]
    /\ crashed' = crashed \ {n}

(*-------------------------- Parallel Commit Protocol -----------------------*)
StartParallelCommit(txn) ==
    LET coordShard == CHOOSE s \in txn.shards : TRUE
    LET txnEntry == [txn EXCEPT !.status = "COMMITTING", !.coordShard = coordShard]
    IN
    /\ pendingTxns' = [pendingTxns EXCEPT ![txn.txnId] = txnEntry]
    /\ \A s \in txn.shards :
        LeaderAppend(s, IF s = coordShard THEN txnEntry ELSE [type: "COMMIT", txnId: txn.txnId, hlc: txn.hlc])

CheckParallelCommit(txnId) == 
    LET txn == pendingTxns[txnId]
    LET committedInShard(s) ==
        \E idx \in 1..Len(shardLogs[s]) : 
            /\ shardLogs[s][idx].cmd.txnId = txnId
            /\ idx <= shardCommitIndex[s]
    IN
    IF \A s \in txn.shards : committedInShard(s)
    THEN /\ pendingTxns' = [pendingTxns EXCEPT ![txnId].status = "COMMITTED"]
         /\ ApplyTxnOps(txn.ops)
    ELSE IF HLC_Diff(pc[self], txn.hlc) > MaxLatency
    THEN AbortTxn(txnId)

(*---------------------- Transaction Handling -----------------------*)
CheckConflicts(txn) ==
    LET committedOps == UNION { {entry.cmd} : s \in Shards, entry \in shardLogs[s][1..shardCommitIndex[s]] }
    IN
    /\ \A op \in txn.ops:
        \A entry \in committedOps:
            CASE entry.type = "COMMIT" ->
                \E op2 \in pendingTxns[entry.txnId].ops : 
                    Conflict(op, op2) /\ entry.hlc < txn.hlc
            [] OTHER ->
                Conflict(op, entry) /\ entry.hlc < txn.hlc
            => AbortTxn(txn.txnId)

Conflict(op1, op2) ==
    \/ (op1.node = op2.node /\ (IsWrite(op1) /\ IsWrite(op2)) 
       /\ (op1.key = op2.key \/ op1.type \notin {"set_property", "remove_property"}))
    \/ (IsTreeMod(op1) /\ (op2.node \in Descendants(op1.node) \/ op1.node \in Descendants(op2.node)))
    \/ (IsTreeMod(op2) /\ (op1.node \in Descendants(op2.node) \/ op2.node \in Descendants(op1.node)))
    \/ (op1.type = "move_child" /\ op2.type = "move_child" 
       /\ op1.parent = op2.parent /\ op1.child_node = op2.child_node)
    \/ (op1.type = "move_child" /\ op2.type \in {"add_child", "add_sibling"} 
       /\ op1.parent = op2.target)

IsWrite(op) == op.type \in {"set_property", "remove_property"}
IsTreeMod(op) == op.type \in {"move_subtree", "remove_node", "remove_subtree", "move_child"}

(*-------------------------- Safety Invariants ----------------------------*)
Linearizability ==
    \A s1, s2 \in Shards:
        \A i \in 1..Len(shardLogs[s1]):
            \A j \in 1..Len(shardLogs[s2]):
                shardLogs[s1][i].hlc < shardLogs[s2][j].hlc => 
                    ~\E op1 \in {shardLogs[s1][i].cmd}, op2 \in {shardLogs[s2][j].cmd} : 
                        Conflict(op1, op2)

NoOrphanNodes ==
    LET Roots == { n \in DOMAIN sceneState : 
                     \A m \in DOMAIN sceneState : 
                         n /= sceneState[m].left_child /\ n /= sceneState[m].right_sibling } IN
    LET R(m, n) == n = sceneState[m].left_child \/ n = sceneState[m].right_sibling IN
    LET Reachable == { n \in DOMAIN sceneState : 
                         \E path \in Seq(DOMAIN sceneState) : 
                             /\ Head(path) \in Roots 
                             /\ \A i \in 1..(Len(path)-1) : R(path[i], path[i+1]) } IN
    DOMAIN sceneState \subseteq Reachable

TransactionAtomicity ==
    \A txn \in pendingTxns:
        txn.status = "COMMITTED" => 
            \A op \in txn.ops:
                CASE op.type \in {"add_child", "add_sibling"} ->
                    op.new_node \in DOMAIN sceneState
                [] op.type = "remove_node" ->
                    op.node \notin DOMAIN sceneState
                [] OTHER -> TRUE
        txn.status = "ABORTED" => 
            \A op \in txn.ops:
                CASE op.type \in {"add_child", "add_sibling"} ->
                    op.new_node \notin DOMAIN sceneState
                [] OTHER -> TRUE

NoDanglingIntents ==
    \A txn \in DOMAIN pendingTxns:
        pendingTxns[txn].status = "COMMITTED" => 
            \A s \in pendingTxns[txn].shards:
                \E! entry \in shardLogs[s] : entry.cmd.txnId = txn

CrossShardAtomicity ==
    \A t1, t2 \in pendingTxns :
        t1 /= t2 /\ t1.status /= "ABORTED" /\ t2.status /= "ABORTED"
        /\ \E s \in t1.shards \cap t2.shards
        => ~\E op1 \in t1.ops, op2 \in t2.ops : Conflict(op1, op2)
    /\ \A t1, t2 \in pendingTxns:
        t1 /= t2 /\ \E node: shardMap[node] \in t1.shards \cap t2.shards
        => ~\E op1 \in t1.ops, op2 \in t2.ops: Conflict(op1, op2)

NoPartialBatches ==
    \A entry \in UNION {shardLogs[s] : s \in Shards} :
        entry.cmd.type = "batch_update" =>
            \A update \in entry.cmd.updates :
                \E! e \in UNION {shardLogs[s] : s \in Shards} : e.hlc = entry.hlc /\ e.cmd.node = update.node

PropertyTombstoneConsistency ==  
    \A n \in DOMAIN sceneState :
        \A k \in DOMAIN sceneState[n].properties :
            \E! e \in UNION {shardLogs[s] : s \in Shards} : 
                e.cmd.node = n /\ 
                e.cmd.key = k /\ 
                (e.cmd.type = "set_property" \/ e.cmd.type = "remove_property")

SiblingOrderConsistency ==
    \A p \in DOMAIN sceneState:
        LET children == OrderedChildren(p) IN
        \A i \in 1..(Len(children)-1):
            sceneState[children[i]].right_sibling = children[i+1]            
ParallelCommitConsistency ==
    \A txn \in pendingTxns : txn.status = "COMMITTED" => 
        \A s \in txn.shards : 
            \E! e \in shardLogs[s] : e.cmd.txnId = txn.txnId

(*-------------------------- Configuration ---------------------------------*)
ASSUME 
    /\ Cardinality(NodeID) >= 3
    /\ Cardinality(Shards) = 2
    /\ MaxLatency = 16
    /\ GodotNodes /= {}
    /\ NodeID \subseteq 1..1000
    /\ IsValidLCRSTree(GodotNodes)
    /\ IF Cardinality(NodeID) = 1
        THEN \A n \in NodeID : shardMap[n] = Shards
        ELSE /\ \A n \in NodeID : Cardinality(shardMap[n]) = 1
             /\ \A s \in Shards : 
                 Cardinality({n \in NodeID : s \in shardMap[n]}) >= 3
             /\ \A n \in NodeID : \E! s \in Shards : s \in shardMap[n]
    /\ crashed = {} 

=============================================================================

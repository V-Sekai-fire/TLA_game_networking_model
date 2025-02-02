------------------------------ MODULE GodotSync -----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets, hlc, raft, parallelcommits

CONSTANTS
    GodotNodes,        \* Initial node tree structure in LCRS form
    Shards,            \* {s1, s2} for multi-shard transactions  
    MaxLatency,        \* Maximum network delay (ticks)
    NodeID,            \* 1..1000
    SceneOperations    \* Set of valid scene operations

VARIABLES
    (* Raft Consensus *)
    messages, elections, allLogs, currentTerm, state, votedFor, log, commitIndex,
    votesResponded, votesGranted, voterLog, nextIndex, matchIndex,
    
    (* Hybrid Logical Clocks *)
    pt, msg, l, c, pc,
    
    (* Godot Scene State *)
    sceneState,         \* [node ↦ [left_child, right_sibling, properties]]
    pendingTxns,       \* [txnId ↦ [status, shards, hlc, ops]]
    appliedIndex,      \* Last applied log index per node
    
    (* Coordination *)
    intents,           \* [txnId ↦ [shard ↦ {"PENDING", "ACK"}]] 
    shardMap,         \* [node ↦ shard]
    crashed           \* Set of crashed nodes

(*--------------------------- Type Definitions ----------------------------*)
HLC == <<pt[self], l[self], c[self]>>  \* Combined HLC tuple

SceneOp ==
    [ type: {"add_child", "add_sibling", "remove_node", 
            "set_property", "get_property", "reparent_subtree", 
            "remove_property", "batch_update"},
      target: NodeID,    \* For add_child/add_sibling: target node
      new_node: NodeID, \* For add_child/add_sibling: new node ID
      node: NodeID,     \* Node to act on
      properties: JSON, \* Initial properties for new nodes
      key: STRING,      \* For property operations
      value: STRING,     \* For set_property
      new_parent: NodeID,  \* For reparent_subtree
      new_sibling: NodeID, \* For reparent_subtree
      updates: Seq([node: NodeID, key: STRING, value: STRING]) ]  \* For batch_update

TxnState ==
    [ txnId: Nat,
      status: {"PREPARED", "COMMITTED", "ABORTED"},
      shards: SUBSET Shards,
      hlc: HLC,
      ops: Seq(SceneOp) ]

JSON == [key ↦ STRING]  \* Simplified JSON representation

(*-------------------------- Raft-HLC Integration --------------------------*)
LogEntry == [term: Nat, cmd: SceneOp ∨ TxnState, hlc: HLC]

LeaderAppend(op) ==
    LET entry == [term ↦ currentTerm[self], cmd ↦ op, hlc ↦ HLC]
    IN  ∧ log' = [log EXCEPT ![self] = Append(log[self], entry)]
        ∧ SendToAll(entry)
        ∧ AdvanceHLC()

(*-------------------------- Scene Tree Operations -----------------------*)
ApplySceneOp(op) ==
    LET RemoveFromOriginalParent(n, p) ==
        CASE
            sceneState[p].left_child = n →
                sceneState' = [sceneState EXCEPT ![p].left_child = sceneState[n].right_sibling]
            [] sceneState[p].right_sibling = n →
                sceneState' = [sceneState EXCEPT ![p].right_sibling = sceneState[n].right_sibling]
        ESAC
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
    [] op.type = "set_property" →
        sceneState' = [sceneState EXCEPT
                      ![op.node].properties[op.key] = op.value ]
    [] op.type = "get_property" →
        \* Read operation preserves state
        UNCHANGED sceneState
    [] op.type = "reparent_subtree" →
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

ApplyCommittedOps() ==
    WHILE appliedIndex[self] < commitIndex[self] DO
        LET entry = log[self][appliedIndex[self] + 1]
        IN  CASE entry.cmd.type ∈ DOMAIN ApplySceneOp →
                    ApplySceneOp(entry.cmd)
              [] entry.cmd.type = "COMMIT" →
                    IF ∀ shard ∈ pendingTxns[entry.cmd.txnId].shards: 
                         intents[entry.cmd.txnId][shard] = "ACK"
                      THEN ApplyTxnOps(pendingTxns[entry.cmd.txnId].ops)
                      ELSE AbortTxn(entry.cmd.txnId)
        appliedIndex' = [appliedIndex EXCEPT ![self] = appliedIndex[self] + 1]

(*---------------------- Transaction Handling -----------------------*)
PrepareTxn(txn) ==
    ∧ txn ∈ pendingTxns
    ∧ ∀ shard ∈ txn.shards:
        SendIntent(shard, txn)
    ∧ intents' = [intents EXCEPT ![txn.txnId][shard] = "PENDING" FOR shard ∈ txn.shards]

AckIntent(txnId, shard) ==
    ∧ intents[txnId][shard] = "PENDING"
    ∧ intents' = [intents EXCEPT ![txnId][shard] = "ACK"]

CheckConflicts(txn) ==
    ∀ op ∈ txn.ops:
        ∀ other ∈ pendingTxns:
            other ≠ txn 
            ∧ ∃ op2 ∈ other.ops: 
                Conflict(op, op2) 
                ∧ other.hlc < txn.hlc 
            ⇒ AbortTxn(other.txnId)

Conflict(op1, op2) ==
    ∨ (op1.node = op2.node ∧ (
           (op1.type ∉ {"set_property", "remove_property", "get_property"} ∨ 
            op2.type ∉ {"set_property", "remove_property", "get_property"}) 
           ∨ (op1.key = op2.key ∧ 
              (op1.type ∈ {"set_property", "remove_property"} ∨ 
               op2.type ∈ {"set_property", "remove_property"}))
       ))
    ∨ (op1.type ∈ {"reparent_subtree", "remove_node"} ∧ 
       op2.node ∈ Descendants(op1.node))
    ∨ (op2.type ∈ {"reparent_subtree", "remove_node"} ∧ 
       op1.node ∈ Descendants(op2.node))

(*-------------------------- Safety Invariants ----------------------------*)
CausalConsistency ==
    ∀ n1, n2 ∈ Server:
        ∀ i ∈ 1..Len(log[n1]):
            ∀ j ∈ 1..Len(log[n2]):
                log[n1][i].hlc < log[n2][j].hlc ⇒ 
                    ¬∃ op1 ∈ log[n1][i].cmd, op2 ∈ log[n2][j].cmd : 
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
        txn.status = "COMMITTED" ⇒ ∀ op ∈ txn.ops : 
            op.type ≠ "get_property" ⇒ op ∈ DOMAIN sceneState
        txn.status = "ABORTED" ⇒ ∀ op ∈ txn.ops : op ∉ DOMAIN sceneState

NoDanglingIntents ==
    ∀ txn ∈ pendingTxns:
        txn.status = "COMMITTED" ⇒ ∀ shard ∈ txn.shards: intents[txn.txnId][shard] = "ACK"

CrossShardAtomicity ==
    ∀ t1, t2 ∈ pendingTxns:
        t1 ≠ t2 ∧ ∃ node: shardMap[node] ∈ t1.shards ∩ t2.shards
        ⇒ ¬∃ op1 ∈ t1.ops, op2 ∈ t2.ops: Conflict(op1, op2)

NoPartialBatches ==
    ∀ entry ∈ UNION {log[n] : n ∈ Server} :
        entry.cmd.type = "batch_update" ⇒
            ∀ update ∈ entry.cmd.updates :
                ∃! e ∈ log : e.hlc = entry.hlc ∧ e.cmd.node = update.node

PropertyTombstoneConsistency ==  
    ∀ n ∈ DOMAIN sceneState :
        ∀ k ∈ DOMAIN sceneState[n].properties :
            ∃! e ∈ log : 
                e.cmd.node = n ∧ 
                e.cmd.key = k ∧ 
                (e.cmd.type = "set_property" ∨ e.cmd.type = "remove_property")

(*-------------------------- Configuration ---------------------------------*)
ASSUME 
    ∧ Cardinality(Server) = 3
    ∧ Cardinality(Shards) = 2
    ∧ MaxLatency = 16
    ∧ GodotNodes ≠ {}
    ∧ NodeID ⊆ 1..1000
    ∧ IsValidLCRSTree(GodotNodes)
    ∧ shardMap ∈ [NodeID → Shards]
    ∧ intents = [txnId ∈ {} ↦ [shard ∈ Shards ↦ "PENDING"]]
    ∧ crashed = {} 

=============================================================================

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
    appliedIndex       \* Last applied log index per node

(*--------------------------- Type Definitions ----------------------------*)
HLC == <<pt[self], l[self], c[self]>>  \* Combined HLC tuple

SceneOp ==
    [ type: {"add_child", "add_sibling", "remove_node", "update_property"},
      target: NodeID,    \* For add_child/add_sibling: target node
      new_node: NodeID, \* For add_child/add_sibling: new node ID
      node: NodeID,     \* For remove_node/update_property: node to act on
      properties: JSON ]

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
      [] op.type = "update_property" →
          sceneState' = [sceneState EXCEPT
                        ![op.node].properties = op.properties ]

ApplyCommittedOps() ==
    WHILE appliedIndex[self] < commitIndex[self] DO
        LET entry = log[self][appliedIndex[self] + 1]
        IN  CASE entry.cmd.type ∈ {"add_child", "add_sibling", "remove_node", "update_property"} →
                    ApplySceneOp(entry.cmd)
              [] entry.cmd.type = "COMMIT" →
                    ApplyTxnOps(pendingTxns[entry.cmd.txnId].ops)
        appliedIndex' = [appliedIndex EXCEPT ![self] = appliedIndex[self] + 1]

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
        txn.status = "COMMITTED" ⇒ ∀ op ∈ txn.ops : op ∈ DOMAIN sceneState
        txn.status = "ABORTED" ⇒ ∀ op ∈ txn.ops : op ∉ DOMAIN sceneState

(*-------------------------- Configuration ---------------------------------*)
ASSUME 
    ∧ Cardinality(Server) = 3
    ∧ Cardinality(Shards) = 2
    ∧ MaxLatency = 16
    ∧ GodotNodes ≠ {}
    ∧ NodeID ⊆ 1..1000
    ∧ IsValidLCRSTree(GodotNodes)  \* Ensure initial tree follows LCRS structure

=============================================================================

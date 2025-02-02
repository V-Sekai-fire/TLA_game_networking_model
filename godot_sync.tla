----------------------------- MODULE GodotSync -----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets, hlc, raft, parallelcommits

CONSTANTS
    GodotNodes,        \* Initial node tree structure
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
    sceneState,         \* [node ↦ [parent, properties]]
    pendingTxns,       \* [txnId ↦ [status, shards, hlc, ops]]
    appliedIndex       \* Last applied log index per node

(*--------------------------- Type Definitions ----------------------------*)
HLC == <<pt[self], l[self], c[self]>>  \* Combined HLC tuple

SceneOp ==
    [ type: {"add_node", "remove_node", "update_property"},
      node: NodeID,
      parent: NodeID ∪ {NULL},
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

SendToAll(entry) ==
    ∀ follower ∈ Server \ {self}:
        Send([mtype ↦ "AppendEntries",
              term ↦ currentTerm[self],
              entries ↦ <<entry>>,
              commitIndex ↦ commitIndex[self],
              hlc ↦ entry.hlc])

HandleAppendEntries(i, entries) ==
    IF FollowerAcceptEntries(entries) THEN
        ∧ UpdateHLC(entries[Len(entries)].hlc)
        ∧ AppendEntriesToLog(entries)
        ∧ ApplyCommittedOps()
    ELSE
        RejectEntries()

(*-------------------------- Parallel Commits ----------------------------*)
PrepareTxn(txnId, ops) ==
    LET shards = ChooseShards(ops)
    IN  ∧ txnId ∉ DOMAIN pendingTxns
        ∧ pendingTxns' = pendingTxns ∪ 
            [txnId ↦ [status ↦ "PREPARED",
                      shards ↦ shards,
                      hlc ↦ HLC,
                      ops ↦ ops]]
        ∧ BroadcastIntent(shards, txnId, ops)
        ∧ LeaderAppend([type ↦ "PREPARE", txnId ↦ txnId])

CommitTxn(txnId) ==
    LET txn = pendingTxns[txnId]
    IN  ∧ txn.status = "PREPARED"
        ∧ ∀ s ∈ txn.shards: ReceivedAck(s, txnId)
        ∧ pendingTxns' = [pendingTxns EXCEPT ![txnId].status = "COMMITTED"]
        ∧ LeaderAppend([type ↦ "COMMIT", txnId ↦ txnId])
        ∧ ApplyTxnOps(txn.ops)

AbortTxn(txnId) ==
    ∧ pendingTxns' = [pendingTxns EXCEPT ![txnId].status = "ABORTED"]
    ∧ LeaderAppend([type ↦ "ABORT", txnId ↦ txnId])

(*-------------------------- Scene Tree Operations -----------------------*)
ApplySceneOp(op) ==
    CASE op.type = "add_node" →
            sceneState' = sceneState ∪ 
                [op.node ↦ [parent ↦ op.parent, properties ↦ op.properties]]
      [] op.type = "remove_node" →
            sceneState' = [n ∈ DOMAIN sceneState ↦ 
                IF n = op.node THEN UNDEFINED ELSE sceneState[n]]
      [] op.type = "update_property" →
            sceneState' = [n ∈ DOMAIN sceneState ↦ 
                IF n = op.node 
                THEN [sceneState[n] EXCEPT !.properties = op.properties] 
                ELSE sceneState[n]]

ApplyCommittedOps() ==
    WHILE appliedIndex[self] < commitIndex[self] DO
        LET entry = log[self][appliedIndex[self] + 1]
        IN  CASE entry.cmd.type ∈ {"add_node", "remove_node", "update_property"} →
                    ApplySceneOp(entry.cmd)
              [] entry.cmd.type = "COMMIT" →
                    ApplyTxnOps(pendingTxns[entry.cmd.txnId].ops)
        appliedIndex' = [appliedIndex EXCEPT ![self] = appliedIndex[self] + 1]

(*-------------------------- HLC Operations -------------------------------*)
AdvanceHLC() ==
    pt' = [pt EXCEPT ![self] = pt[self] + 1]
    l' = [l EXCEPT ![self] = Max(l[self], pt[self] + 1)]

UpdateHLC(receivedHLC) ==
    l' = [l EXCEPT ![self] = Max(l[self], receivedHLC[2])]
    c' = [c EXCEPT ![self] = Max(c[self], receivedHLC[3]) + 1]

(*-------------------------- Combined Transitions -------------------------*)
Next == 
    ∨ ∃ self ∈ Server: 
        ∨ LeaderAppend(NextSceneOp())
        ∨ PrepareTxn(NewTxnId(), GetPendingOps())
        ∨ CommitTxn(ChooseCommittableTxn())
        ∨ AbortTxn(ChooseAbortableTxn())
        ∨ HandleAppendEntries(self, messages[self])
        ∨ HandleTimeout()
        ∨ ProcessHLC()
    
    ∨ ∃ m ∈ DOMAIN messages: 
        ∨ DeliverMessage(m)
        ∨ DropMessage(m)
    
    ∨ ∃ self ∈ Server:
        ∨ CrashNode(self)
        ∨ RecoverNode(self)

(*-------------------------- Safety Invariants ----------------------------*)
CausalConsistency ==
    ∀ n1, n2 ∈ Server:
        ∀ i ∈ 1..Len(log[n1]):
            ∀ j ∈ 1..Len(log[n2]):
                log[n1][i].hlc < log[n2][j].hlc ⇒ 
                    ¬∃ op1 ∈ log[n1][i].cmd, op2 ∈ log[n2][j].cmd : 
                        Conflict(op1, op2)

NoOrphanNodes ==
    ∀ node ∈ DOMAIN sceneState:
        sceneState[node].parent ≠ NULL ⇒ sceneState[node].parent ∈ DOMAIN sceneState

TransactionAtomicity ==
    ∀ txn ∈ pendingTxns:
        txn.status = "COMMITTED" ⇒ ∀ op ∈ txn.ops : op ∈ sceneState
        txn.status = "ABORTED" ⇒ ∀ op ∈ txn.ops : op ∉ sceneState

(*-------------------------- Liveness Properties -------------------------*)
EventualConsistency ==
    ∀ op ∈ SceneOperations :
        ◇(∃ txn ∈ pendingTxns : 
            txn.status = "COMMITTED" ∧ op ∈ txn.ops)

Progress ==
    ∀ txn ∈ pendingTxns :
        ◇(txn.status ∈ {"COMMITTED", "ABORTED"})

(*-------------------------- Configuration ---------------------------------*)
ASSUME 
    ∧ Cardinality(Server) = 3
    ∧ Cardinality(Shards) = 2
    ∧ MaxLatency = 16
    ∧ GodotNodes ≠ {}
    ∧ NodeID ⊆ 1..1000

=============================================================================

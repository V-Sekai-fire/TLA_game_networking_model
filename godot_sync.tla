----------------------------- MODULE GodotSync -----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets, hlc

(*
    Combined specification integrating:
    - Raft-based Godot node synchronization
    - CockroachDB-style parallel commits
    - External HLC implementation
*)

CONSTANTS
    Nodes,              \* {n1, n2, n3}
    NodeTree,           \* Initial Godot scene tree
    Shards,             \* {s1, s2} if using multi-shard
    MaxLatency,         \* Maximum network delay (e.g., 16)
    STOP, EPS           \* From HLC module

VARIABLES
    (* Raft State *)
    currentTerm,        \* Latest term server has seen
    votedFor,          \* CandidateId that received vote in current term
    log,                \* Log entries (containing Godot operations)
    commitIndex,        \* Highest log entry known to be committed
    
    (* HLC State (from external module) *)
    pt,                 \* Physical time
    msg,                \* Message clocks
    l, c,               \* HLC components
    pc,                 \* Process counters
    
    (* Parallel Commits *)
    pendingTxns,        \* {txnId: [shards: SUBSET Shards, status: IntentStatus]}
    sceneState          \* Applied Godot node tree state

(*---------------------------- Type Definitions ----------------------------*)
NodeID == 1..1000  \* Godot node identifiers
JSON == [key ↦ STRING]  \* Simplified JSON representation

SceneOp ==
    [ type: {"add_node", "remove_node", "update_property"},
      node: NodeID,
      parent: NodeID \union {NULL},
      properties: JSON ]

IntentStatus == {"PREPARED", "COMMITTED", "ABORTED"}
TxnState == [ txnId: Nat, shards: SUBSET Shards, status: IntentStatus ]

HLC == <<pt[self], l[self], c[self]>>  \* Combined HLC tuple

(*---------------------------- Raft Integration ----------------------------*)
LogEntry == [term: Nat, cmd: SceneOp, hlc: HLC]

RaftLeaderUpdate ==
    LET entry == [term ↦ currentTerm, cmd ↦ NextSceneOp(), hlc ↦ HLC]
    IN  ∧ LeaderAppendLog(entry)
        ∧ SendToAll(entry)  \* Triggers HLC Send process
        ∧ UNCHANGED <<pt, msg, l, c>>

HandleAppendEntries(entries) ==
    IF FollowerAcceptEntries(entries) THEN
        ∧ UpdateFromHLC(entries[Len(entries)].hlc)
        ∧ RecvFromLeader()  \* Triggers HLC Recv process
    ELSE
        RejectAppendEntries()

(*---------------------------- HLC Integration ----------------------------*)
UpdateFromHLC(receivedHLC) ==
    ∧ msg' = [msg EXCEPT ![self] = receivedHLC]
    ∧ Recv(self)  \* Use HLC's receive logic

SendToAll(entry) ==
    ∧ WITH k ∈ Procs \ {self}
        msg' = [msg EXCEPT ![k] = <<pt[self], l[self], c[self]>>]
    ∧ Send(self)  \* Use HLC's send logic

(*---------------------------- Parallel Commits ----------------------------*)
PrepareTransaction(txnId, shards, cmd) ==
    ∧ txnId ∉ DOMAIN pendingTxns
    ∧ pendingTxns' = pendingTxns ∪ [txnId ↦ [shards ↦ shards, status ↦ "PREPARED"]]
    ∧ ∀ s ∈ shards: SendIntent(s, txnId, cmd)
    ∧ Send(self)  \* HLC update on send

CommitTransaction(txnId) ==
    LET txn ≜ pendingTxns[txnId]
    IN  ∧ txn.status = "PREPARED"
        ∧ ∀ s ∈ txn.shards: ReceivedAck(s, txnId)
        ∧ pendingTxns' = [pendingTxns EXCEPT ![txnId].status = "COMMITTED"]
        ∧ ApplySceneOp(txn.cmd)
        ∧ Recv(self)  \* HLC update on receive

(*---------------------------- Godot Scene Tree ----------------------------*)
ApplySceneOp(cmd) ==
    CASE cmd.type = "add_node" →
            sceneState' = AddNode(sceneState, cmd.node, cmd.parent, cmd.properties)
      [] cmd.type = "remove_node" →
            sceneState' = RemoveNode(sceneState, cmd.node)
      [] cmd.type = "update_property" →
            sceneState' = UpdateProperty(sceneState, cmd.node, cmd.properties)

(*---------------------------- State Transitions ---------------------------*)
Next ==
    ∨ RaftLeaderUpdate
    ∨ PrepareTransaction
    ∨ CommitTransaction
    ∨ HandleAppendEntries
    ∨ LeaderCrash
    ∨ NetworkPartition
    ∨ (\E self ∈ Procs: j(self))  \* HLC processes

(*---------------------------- Combined Invariants --------------------------*)
CombinedInvariants ==
    ∧ RaftInvariant
    ∧ TypeOK              \* From HLC
    ∧ Sync                 \* From HLC
    ∧ Boundedl             \* From HLC
    ∧ Boundedc             \* From HLC
    ∧ NoOrphanNodes
    ∧ CausalOrdering

(*---------------------------- Configuration ---------------------------------*)
ASSUME Cardinality(Nodes) = 3
ASSUME MaxLatency ≤ 16
ASSUME N = Cardinality(Nodes)  \* HLC process count

=============================================================================

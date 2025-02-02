----------------------------- MODULE GodotSync -----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets, hlc, raft

(*
    Complete specification for Godot node tree synchronization using:
    - Raft consensus (from raft.tla)
    - Hybrid Logical Clocks (from hlc.tla)
    - Parallel commits for low-latency scene updates
*)

CONSTANTS
    GodotNodes,        \* Initial node tree structure
    Shards,            \* {s1, s2} if using multi-shard
    MaxLatency,        \* Maximum network delay (e.g., 16)
    STOP, EPS          \* From HLC module

VARIABLES
    (* Inherited from raft.tla *)
    messages, elections, allLogs, currentTerm, state, votedFor, log, commitIndex,
    votesResponded, votesGranted, voterLog, nextIndex, matchIndex,

    (* Inherited from hlc.tla *)
    pt, msg, l, c, pc,

    (* Godot-specific *)
    sceneState,         \* Applied node tree
    pendingTxns        \* Parallel commit transactions

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
    LET entry == [term ↦ currentTerm[self], cmd ↦ NextSceneOp(), hlc ↦ HLC]
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

AddNode(tree, node, parent, props) ==
    tree ∪ [node ↦ [parent ↦ parent, properties ↦ props]]

RemoveNode(tree, node) ==
    [n ∈ DOMAIN tree ↦ IF n = node THEN UNDEFINED ELSE tree[n]]

UpdateProperty(tree, node, props) ==
    [n ∈ DOMAIN tree ↦ IF n = node 
                        THEN [tree[n] EXCEPT !.properties = props]
                        ELSE tree[n]]

(*---------------------------- Combined Transitions -------------------------*)
Next ==
    ∨ RaftLeaderUpdate
    ∨ PrepareTransaction
    ∨ CommitTransaction
    ∨ HandleAppendEntries
    ∨ LeaderCrash
    ∨ NetworkPartition
    ∨ (\E self ∈ Procs: j(self))  \* HLC processes
    ∨ \E m ∈ DOMAIN messages : Receive(m)  \* Raft message handling
    ∨ \E i ∈ Server : BecomeLeader(i)  \* Raft leadership
    ∨ \E i ∈ Server : AdvanceCommitIndex(i)  \* Raft commit

(*---------------------------- Combined Invariants --------------------------*)
CombinedInvariants ==
    ∧ RaftInvariant
    ∧ TypeOK              \* From HLC
    ∧ Sync                 \* From HLC
    ∧ Boundedl             \* From HLC
    ∧ Boundedc             \* From HLC
    ∧ NoOrphanNodes
    ∧ CausalOrdering

NoOrphanNodes ==
    ∀ node ∈ DOMAIN sceneState:
        sceneState[node].parent ≠ NULL ⇒ sceneState[node].parent ∈ DOMAIN sceneState

CausalOrdering ==
    ∀ e1, e2 ∈ log:
        e1.hlc < e2.hlc ⇒ ¬(e2.cmd \dependsOn e1.cmd)

(*---------------------------- Configuration --------------------------------*)
ASSUME Cardinality(Server) = 3
ASSUME Cardinality(Shards) = 1  \* Start with single-shard
ASSUME MaxLatency ≤ 16
ASSUME N = Cardinality(Server)  \* HLC process count

=============================================================================

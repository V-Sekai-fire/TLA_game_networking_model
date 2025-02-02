----------------------------- MODULE GodotSync -----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets

(*
    A complete specification for a leader-based Godot node tree synchronization
    system using Raft consensus, parallel commits, and hybrid logical clocks.
*)

CONSTANTS
    Nodes,              \* {n1, n2, n3}
    NodeTree,           \* Initial Godot scene tree
    Shards,             \* {s1, s2} if using multi-shard
    MaxLatency          \* Maximum network delay (e.g., 16)

VARIABLES
    (* Raft State *)
    currentTerm,        \* Latest term server has seen
    votedFor,          \* CandidateId that received vote in current term
    log,                \* Log entries (containing Godot operations)
    commitIndex,        \* Highest log entry known to be committed
    
    (* HLC Clocks *)
    hlc,                \* Hybrid logical clocks [node ↦ (physical, logical)]
    
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

HLC == [physical: Nat, logical: Nat]

(*---------------------------- Raft Integration ----------------------------*)
LogEntry == [term: Nat, cmd: SceneOp, hlc: HLC]

RaftLeaderUpdate ==
    LET entry == [term ↦ currentTerm, cmd ↦ NextSceneOp(), hlc ↦ hlc[self]]
    IN  ∧ LeaderAppendLog(entry)
        ∧ UpdateHLC()
        ∧ BroadcastAppendEntries(entry)

HandleAppendEntries(entries) ==
    IF FollowerAcceptEntries(entries) THEN
        UpdateHLC(entries[Len(entries)].hlc)
    ELSE
        RejectAppendEntries()

(*---------------------------- Hybrid Logical Clock -------------------------*)
UpdateHLC(observedHLC) ==
    LET observedPhysical ≜ observedHLC.physical
        currentPhysical ≜ hlc[self].physical
        newPhysical ≜ MAX(currentPhysical, observedPhysical)
        newLogical ≜ IF newPhysical = currentPhysical 
                     THEN hlc[self].logical + 1 
                     ELSE 0
    IN  hlc' = [hlc EXCEPT ![self] = [physical ↦ newPhysical, logical ↦ newLogical]]

(*---------------------------- Parallel Commits ----------------------------*)
PrepareTransaction(txnId, shards, cmd) ==
    ∧ txnId ∉ DOMAIN pendingTxns
    ∧ pendingTxns' = pendingTxns ∪ [txnId ↦ [shards ↦ shards, status ↦ "PREPARED"]]
    ∧ ∀ s ∈ shards: SendIntent(s, txnId, cmd)
    ∧ UpdateHLC()

CommitTransaction(txnId) ==
    LET txn ≜ pendingTxns[txnId]
    IN  ∧ txn.status = "PREPARED"
        ∧ ∀ s ∈ txn.shards: ReceivedAck(s, txnId)
        ∧ pendingTxns' = [pendingTxns EXCEPT ![txnId].status = "COMMITTED"]
        ∧ ApplySceneOp(txn.cmd)

AbortTransaction(txnId) ==
    ∧ pendingTxns[txnId].status = "PREPARED"
    ∧ ∃ s ∈ pendingTxns[txnId].shards: ¬ReceivedAck(s, txnId)
    ∧ pendingTxns' = [pendingTxns EXCEPT ![txnId].status = "ABORTED"]

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

(*---------------------------- State Transitions ---------------------------*)
Next ==
    ∨ RaftLeaderUpdate
    ∨ PrepareTransaction
    ∨ CommitTransaction
    ∨ AbortTransaction
    ∨ HandleAppendEntries
    ∨ LeaderCrash
    ∨ NetworkPartition

(*---------------------------- Invariants & Properties ----------------------*)
TypeInvariant ==
    ∧ RaftInvariant
    ∧ ∀ n ∈ Nodes: hlc[n].logical ≥ 0
    ∧ ∀ txn ∈ DOMAIN pendingTxns: pendingTxns[txn].status ∈ IntentStatus

CausalOrdering ==
    ∀ e1, e2 ∈ log:
        e1.hlc < e2.hlc ⇒ ¬(e2.cmd \dependsOn e1.cmd)

Linearizability ==
    ∀ op ∈ ClientOps:
        ∃ i ∈ 1..Len(log):
            log[i].cmd = op ∧ IsInstantaneous(log, i)

NoOrphanNodes ==
    ∀ node ∈ DOMAIN sceneState:
        sceneState[node].parent ≠ NULL ⇒ sceneState[node].parent ∈ DOMAIN sceneState

(*---------------------------- Configuration ---------------------------------*)
ASSUME Cardinality(Nodes) = 3
ASSUME MaxLatency ≤ 16

=============================================================================

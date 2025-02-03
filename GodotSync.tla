------------------------------ MODULE GodotSync ------------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets, hlc, raft, ParallelCommits

CONSTANTS
    GodotNodes,        \* Initial node tree structure in LCRS form
    MaxLatency,        \* Maximum network delay (ticks)
    NodeID,            \* 1..1000
    SceneOperations,   \* Set of valid scene operations
    NULL               \* Representing null node reference

VARIABLES
    (* Single Raft Consensus *)
    log,             \* Seq(LogEntry)
    currentTerm,     \* Current term number
    commitIndex,    \* Index of highest committed entry
    currentLeader,  \* Current leader node
    
    (* Godot Scene State *)
    sceneState,      \* [node |-> [left_child, right_sibling, properties]]
    pendingTxns,    \* [txnId |-> [status, hlc, ops]]
    appliedIndex,   \* [NodeID |-> Nat]
    crashed         \* Set of crashed nodes

(*--------------------------- Type Definitions ----------------------------*)
HLC(n) == <<l[n], c[n]>>  \* HLC tuple for node n

JSON == [key |-> STRING]  \* Simplified JSON representation

SceneOp ==
    [ type |-> {"add_child", "add_sibling", "remove_node",
               "set_property", "move_subtree", 
               "batch_update", "batch_structure", "move_child"},
      target |-> NodeID,    \* For add_child/add_sibling: target node
      new_node |-> NodeID, \* For add_child/add_sibling: new node ID
      node |-> NodeID,     \* Node to act on
      parent |-> NodeID,   \* For move_child: parent node
      child_node |-> NodeID, \* For move_child: node to move
      to_index |-> Int,    \* For move_child: target position
      properties |-> JSON, \* Initial properties for new nodes
      key |-> STRING,      \* For property operations
      value |-> STRING,     \* For set_property
      new_parent |-> NodeID,  \* For move_subtree
      new_sibling |-> NodeID, \* For move_subtree
      updates |-> Seq([node |-> NodeID, key |-> STRING, value |-> STRING]),
      structure_ops |-> Seq(SceneOp) ]

TxnState ==
    [ txnId |-> Nat,
      status |-> {"COMMITTING", "COMMITTED", "ABORTED"},
      hlc |-> HLC,
      ops |-> Seq(SceneOp) ]

(*-------------------------- Raft-HLC Integration --------------------------*)
LogEntry == [term |-> Nat, cmd |-> SceneOp \/ TxnState, hlc |-> HLC]

LeaderAppend(op) ==
    LET new_pt == pt[currentLeader] + 1
        new_l == IF l[currentLeader] >= new_pt THEN l[currentLeader] ELSE new_pt
        new_c == IF l[currentLeader] >= new_pt THEN c[currentLeader] + 1 ELSE 0
        entry == [term |-> currentTerm, cmd |-> op, hlc |-> HLC(currentLeader)]
    IN  /\ pt' = [pt EXCEPT ![currentLeader] = new_pt]
        /\ l' = [l EXCEPT ![currentLeader] = new_l]
        /\ c' = [c EXCEPT ![currentLeader] = new_c]
        /\ log' = Append(log, entry)
        /\ SendToAll(entry)
        /\ UNCHANGED <<currentTerm, commitIndex>>

(*-------------------------- Scene Tree Operations -----------------------*)
RECURSIVE OrderedChildrenAux(_, _)
OrderedChildrenAux(n, acc) ==
    IF n = NULL
    THEN acc
    ELSE OrderedChildrenAux(sceneState[n].right_sibling, acc \o <<n>>)

OrderedChildren(p) ==
    LET first_child == sceneState[p].left_child
    IN  IF first_child = NULL
        THEN << >>
        ELSE OrderedChildrenAux(first_child, <<first_child>>)

Fold(f(_,_), acc, seq) ==
  LET F[i \in 0..Len(seq)] ==
    IF i = 0 THEN acc
    ELSE f(F[i-1], seq[i])
  IN F[Len(seq)]

RECURSIVE FilterSeq(_, _)
FilterSeq(seq, elem) ==
    IF seq = << >> THEN << >>
    ELSE IF Head(seq) = elem 
         THEN FilterSeq(Tail(seq), elem)
         ELSE <<Head(seq)>> \o FilterSeq(Tail(seq), elem)

RECURSIVE Siblings(_)
Siblings(n) == 
    LET sib == sceneState[n].right_sibling
    IN  IF sib = NULL THEN {} ELSE {sib} \cup Siblings(sib)

Children(n) == 
    LET first == sceneState[n].left_child
    IN  IF first = NULL THEN {} 
        ELSE {first} \cup Siblings(first)

RECURSIVE Descendants(_)
Descendants(n) == 
    {n} \cup UNION { Descendants(children) : children \in Children(n) }

RECURSIVE ApplySceneOp(_)
ApplySceneOp(op) ==
    LET RemoveFromOriginalParent(n, p) ==
        IF sceneState[p].left_child = n 
        THEN [sceneState EXCEPT ![p].left_child = sceneState[n].right_sibling]
        ELSE IF sceneState[p].right_sibling = n 
             THEN [sceneState EXCEPT ![p].right_sibling = sceneState[n].right_sibling]
             ELSE sceneState
    IN
    LET RebuildSiblingLinks(p, children) ==
        IF children = << >> 
        THEN [sceneState EXCEPT ![p].left_child = NULL]
        ELSE LET first == Head(children)
                  rest == Tail(children)
                  UpdateSiblings(s, i) ==
                      [s EXCEPT ![children[i]].right_sibling = 
                        IF i = Len(rest) THEN NULL ELSE children[i+1]]
                  indices == 1..Len(rest)
                  initialSceneState == [sceneState EXCEPT ![p].left_child = first]
                  updatedState == Fold(UpdateSiblings, initialSceneState, indices)
             IN updatedState
    IN
    CASE op.type = "add_child" ->
        LET target == op.target IN
        LET new == op.new_node IN
        IF target = NULL THEN
            [sceneState EXCEPT
             ![new] = [ left_child |-> NULL,
                      right_sibling |-> NULL,
                      properties |-> op.properties ]]
        ELSE
            [sceneState EXCEPT
             ![target].left_child = new,
             ![new] = [ left_child |-> NULL,
                      right_sibling |-> sceneState[target].left_child,
                      properties |-> op.properties ]]
  [] op.type = "add_sibling" ->
        LET target == op.target IN
        LET new == op.new_node IN
        [sceneState EXCEPT
         ![target].right_sibling = new,
         ![new] = [ left_child |-> NULL,
                  right_sibling |-> sceneState[target].right_sibling,
                  properties |-> op.properties ]]
  [] op.type = "remove_node" ->
      LET node == op.node IN
      LET descendants == Descendants(node) IN
      [n \in DOMAIN sceneState |-> 
        IF n \in descendants THEN UNDEFINED 
        ELSE IF sceneState[n].left_child \in descendants THEN [sceneState[n] EXCEPT !.left_child = NULL]
        ELSE IF sceneState[n].right_sibling \in descendants THEN [sceneState[n] EXCEPT !.right_sibling = NULL]
        ELSE sceneState[n]]
  [] op.type = "set_property" ->
        [sceneState EXCEPT
         ![op.node].properties = [op.node].properties @@ (op.key :> op.value) ]
  [] op.type = "move_subtree" ->
        LET originalParent == 
            IF \E p \in DOMAIN sceneState : 
                sceneState[p].left_child = op.node \/ sceneState[p].right_sibling = op.node
            THEN CHOOSE p \in DOMAIN sceneState : 
                    sceneState[p].left_child = op.node \/ 
                    sceneState[p].right_sibling = op.node
            ELSE NULL
        IN
        IF originalParent = NULL THEN sceneState
        ELSE
            LET stateAfterRemoval == RemoveFromOriginalParent(op.node, originalParent)
            IN IF op.new_sibling /= NULL 
                THEN [stateAfterRemoval EXCEPT
                     ![op.new_parent].right_sibling = op.node,
                     ![op.node].right_sibling = stateAfterRemoval[op.new_sibling].right_sibling]
                ELSE [stateAfterRemoval EXCEPT
                     ![op.new_parent].left_child = op.node,
                     ![op.node].right_sibling = stateAfterRemoval[op.new_parent].left_child]
  [] op.type = "batch_update" ->
        LET ApplySingleUpdate(s, update) ==
            [s EXCEPT ![update.node].properties = @ @@ (update.key :> update.value)]
        IN
        Fold(ApplySingleUpdate, sceneState, op.updates)
  [] op.type = "batch_structure" ->
        LET ApplyOp(state, op) ==
            IF op.type \in DOMAIN SceneOperations THEN ApplySceneOp(op) ELSE state
        IN
        Fold(ApplyOp, sceneState, op.structure_ops)
  [] op.type = "move_child" ->
        LET p == op.parent
            c == op.child_node
            current == OrderedChildren(p)
            adj_idx == IF op.to_index < 0 THEN Len(current) + op.to_index ELSE op.to_index
        IN
        IF c \notin current \/ adj_idx < 0 \/ adj_idx >= Len(current)
        THEN sceneState
        ELSE
            LET filtered == FilterSeq(current, c)
                new_order == SubSeq(filtered, 1, adj_idx) \o <<c>> \o SubSeq(filtered, adj_idx+1, Len(filtered))
            IN
            RebuildSiblingLinks(p, new_order)

(*-------------------------- Crash Recovery --------------------------*)
RecoverNode(n) ==
    /\ n \in crashed
    /\ LET maxIdx == commitIndex - appliedIndex[n] - 1
           entries == { log[appliedIndex[n] + idx + 1] : idx \in 0..maxIdx }
           stateTransfers == { entry \in entries : entry.cmd.type = "state_transfer" }
           sceneUpdates == [node \in DOMAIN sceneState |->
                              IF \E entry \in stateTransfers : entry.cmd.node = node
                              THEN (CHOOSE entry \in stateTransfers : entry.cmd.node = node).cmd.state
                              ELSE sceneState[node]]
       IN
           /\ sceneState' = sceneUpdates
           /\ appliedIndex' = [appliedIndex EXCEPT ![n] = appliedIndex[n] + maxIdx + 1]
    /\ crashed' = crashed \ {n}

(*-------------------------- Parallel Commit Protocol -----------------------*)
HLC_Diff(n, h2) == h2.l - HLC(n).l

StartParallelCommit(txn) ==
    /\ pendingTxns' = [pendingTxns EXCEPT ![txn.txnId] = [txn EXCEPT !.status = "COMMITTING"]]
    /\ LeaderAppend(txn)

CheckParallelCommit(txnId) == 
    LET txn == pendingTxns[txnId]
        committed == \E idx \in 1..Len(log) : 
                        /\ log[idx].cmd.txnId = txnId
                        /\ idx <= commitIndex
    IN
    IF committed
    THEN /\ pendingTxns' = [pendingTxns EXCEPT ![txnId].status = "COMMITTED"]
         /\ ApplyTxnOps(txn.ops)
    ELSE IF HLC_Diff(currentNode, txn.hlc) > MaxLatency
         THEN AbortTxn(txnId)
         ELSE UNCHANGED <<pendingTxns, log>>

(*-------------------------- Safety Invariants ----------------------------*)
IsWrite(op) == op.type = "set_property"
IsTreeMod(op) == op.type \in {"move_subtree", "remove_node", "move_child"}

Conflict(op1, op2) ==
    \/ (op1.node = op2.node /\ (IsWrite(op1) /\ IsWrite(op2)) 
       /\ (op1.key = op2.key \/ op1.type \notin {"set_property"}))
    \/ (IsTreeMod(op1) /\ (op2.node \in Descendants(op1.node) \/ op1.node \in Descendants(op2.node)))
    \/ (IsTreeMod(op2) /\ (op1.node \in Descendants(op2.node) \/ op2.node \in Descendants(op1.node)))
    \/ (op1.type = "move_child" /\ op2.type = "move_child" 
       /\ op1.parent = op2.parent /\ op1.child_node = op2.child_node)
    \/ (op1.type = "move_child" /\ op2.type \in {"add_child", "add_sibling"} 
       /\ op1.parent = op2.target)

CheckConflicts(txn) ==
    LET committedOps == { entry.cmd : entry \in log[1..commitIndex] }
    IN
    /\ \A op \in txn.ops:
        \A entry \in committedOps:
            CASE entry.type = "COMMIT" ->
                \E op2 \in pendingTxns[entry.txnId].ops : 
                    Conflict(op, op2) /\ entry.hlc < txn.hlc
            [] OTHER ->
                Conflict(op, entry) /\ entry.hlc < txn.hlc
            => AbortTxn(txn.txnId)

Linearizability ==
    \A i, j \in 1..Len(log) :
        i < j /\ log[i].hlc < log[j].hlc => 
            ~\E op1 \in {log[i].cmd}, op2 \in {log[j].cmd} : 
                Conflict(op1, op2)

NoOrphanNodes ==
    LET Roots == { n \in DOMAIN sceneState : 
                     \A m \in DOMAIN sceneState : 
                         n /= sceneState[m].left_child /\ n /= sceneState[m].right_sibling } 
    IN
    LET Reachable == { n \in DOMAIN sceneState : 
                         \E path \in Seq(DOMAIN sceneState) : 
                             Head(path) \in Roots /\ \A i \in 1..(Len(path)-1) : 
                                 path[i+1] = sceneState[path[i]].left_child \/ path[i+1] = sceneState[path[i]].right_sibling } 
    IN
    DOMAIN sceneState \subseteq Reachable

TransactionAtomicity ==
    \A txn \in DOMAIN pendingTxns:
        /\ pendingTxns[txn].status = "COMMITTED" => 
            \A op \in pendingTxns[txn].ops:
                CASE op.type \in {"add_child", "add_sibling"} -> 
                    op.new_node \in DOMAIN sceneState
                  [] op.type = "remove_node" ->
                    op.node \notin DOMAIN sceneState
                  [] OTHER -> TRUE
        /\ pendingTxns[txn].status = "ABORTED" => 
            \A op \in pendingTxns[txn].ops:
                CASE op.type \in {"add_child", "add_sibling"} -> 
                    op.new_node \notin DOMAIN sceneState
                  [] OTHER -> TRUE

NoDanglingIntents ==
    \A txn \in DOMAIN pendingTxns:
        pendingTxns[txn].status = "COMMITTED" => 
            \E entry \in log : 
                entry.cmd.txnId = txn /\
                \A otherEntry \in log : 
                    (otherEntry.cmd.txnId = txn) => (otherEntry = entry)

NoPartialBatches ==
    \A entry \in log :
        entry.cmd.type = "batch_update" => 
            \A update \in entry.cmd.updates :
                \E e \in log :
                    e.hlc = entry.hlc /\ e.cmd.node = update.node /\
                    \A e2 \in log :
                        (e2.hlc = entry.hlc /\ e2.cmd.node = update.node) => e2 = e

PropertyTombstoneConsistency ==  
    \A n \in DOMAIN sceneState :
        \A k \in DOMAIN sceneState[n].properties :
            \E e \in log : 
                /\ e.cmd.node = n 
                /\ e.cmd.key = k 
                /\ e.cmd.type = "set_property"
                /\ \A otherE \in log : 
                    (otherE.cmd.node = n /\ otherE.cmd.key = k /\ otherE.cmd.type = "set_property") 
                    => (otherE = e)

SiblingOrderConsistency ==
    \A p \in DOMAIN sceneState:
        LET children == OrderedChildren(p) IN
        \A i \in 1..(Len(children)-1):
            sceneState[children[i]].right_sibling = children[i+1]            

IsValidLCRSTree(tree) ==
    LET Nodes == DOMAIN tree
        Root == { n \in Nodes : \A m \in Nodes : n /= tree[m].left_child /\ n /= tree[m].right_sibling }
        ParentCount(n) == Cardinality({ m \in Nodes : n = tree[m].left_child \/ n = tree[m].right_sibling })
        AllNodesHaveOneParent == \A n \in Nodes : (n \in Root /\ ParentCount(n) = 0) \/ (ParentCount(n) = 1)
        RECURSIVE ReachableFrom(_)
        ReachableFrom(n) == 
            {n} \cup (IF tree[n].left_child /= NULL THEN ReachableFrom(tree[n].left_child) ELSE {}) 
                    \cup (IF tree[n].right_sibling /= NULL THEN ReachableFrom(tree[n].right_sibling) ELSE {})
        Reachable == IF Root = {} THEN {} ELSE ReachableFrom(CHOOSE r \in Root : TRUE)
    IN
        /\ Cardinality(Root) = 1
        /\ AllNodesHaveOneParent
        /\ Nodes \subseteq Reachable
        /\ Cardinality(Nodes) = Cardinality(Reachable)

ASSUME 
    /\ Cardinality(NodeID) >= 3
    /\ MaxLatency = 16
    /\ GodotNodes /= {}
    /\ NodeID \subseteq 1..1000
    /\ IsValidLCRSTree(GodotNodes)
    /\ crashed = {}

=============================================================================

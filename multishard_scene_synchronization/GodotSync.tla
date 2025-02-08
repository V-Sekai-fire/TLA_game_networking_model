-------------------------------- MODULE GodotSync ------------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets, hlc, ParallelCommits

CONSTANTS
    GodotNodes,        \* Initial node tree structure in LCRS form
    Shards,            \* {s1, s2} for multi-shard transactions  
    MaxLatency,        \* Maximum network delay (ticks)
    NodeID,            \* 1..1000
    SceneOperations,   \* Set of valid scene operations
    NULL               \* Representing null node reference

VARIABLES
    (* Godot Scene State *)
    sceneState,         \* [node |-> [left_child, right_sibling, properties]]
    pendingTxns,       \* [txnId |-> [status, shards, hlc, ops]]
    
    (* Shard Mapping *)
    shardMap,         \* [node |-> SUBSET Shards]
    crashed           \* Set of crashed nodes

(*--------------------------- Type Definitions ----------------------------*)
HLC(n) == <<l[n], c[n]>>  \* HLC tuple for node n

JSON == [key |-> STRING]  \* Simplified JSON representation

SceneOp ==
    [ type |-> {"add_child", "add_sibling", "remove_node", "move_shard",
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
      structure_ops |-> Seq(SceneOp),
      new_shard |-> Shards ]  \* For move_shard

TxnState ==
    [ txnId |-> Nat,
      status |-> {"COMMITTING", "COMMITTED", "ABORTED"},
      shards |-> SUBSET Shards,
      coordShard |-> Shards,  \* Coordinator shard for parallel commit
      hlc |-> HLC,
      ops |-> Seq(SceneOp) ]

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
            \* Handle root creation
            [sceneState EXCEPT
             ![new] = [ left_child |-> NULL,
                      right_sibling |-> NULL,
                      properties |-> op.properties ]]
        ELSE
            \* Existing add_child logic for non-NULL parent
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
 
   [] op.type = "move_shard" ->
    /\ shardMap' = [n \in NodeID |-> 
                    IF n \in Descendants(op.node) THEN {op.new_shard} ELSE shardMap[n]]
    /\ UNCHANGED <<sceneState>>

(*-------------------------- Safety Invariants ----------------------------*)
IsWrite(op) == op.type = "set_property"
IsTreeMod(op) == op.type \in {"move_subtree", "remove_node", "remove_subtree", "move_child"}

Conflict(op1, op2) ==
    \/ (op1.node = op2.node /\ (IsWrite(op1) /\ IsWrite(op2)) 
       /\ (op1.key = op2.key \/ op1.type \notin {"set_property"}))
    \/ (IsTreeMod(op1) /\ (op2.node \in Descendants(op1.node) \/ op1.node \in Descendants(op2.node)))
    \/ (IsTreeMod(op2) /\ (op1.node \in Descendants(op2.node) \/ op2.node \in Descendants(op1.node)))
    \/ (op1.type = "move_child" /\ op2.type = "move_child" 
       /\ op1.parent = op2.parent /\ op1.child_node = op2.child_node)
    \/ (op1.type = "move_child" /\ op2.type \in {"add_child", "add_sibling"} 
       /\ op1.parent = op2.target)

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
        RECURSIVE ReachableFrom(_)  \* Declare recursion first
        ReachableFrom(n) ==         \* Then define the function
            {n} 
            \cup (IF tree[n].left_child /= NULL THEN ReachableFrom(tree[n].left_child) ELSE {}) 
            \cup (IF tree[n].right_sibling /= NULL THEN ReachableFrom(tree[n].right_sibling) ELSE {})
        Reachable == IF Root = {} THEN {} ELSE ReachableFrom(CHOOSE r \in Root : TRUE)
    IN
        /\ Cardinality(Root) = 1
        /\ AllNodesHaveOneParent
        /\ Nodes \subseteq Reachable
        /\ Cardinality(Nodes) = Cardinality(Reachable)

ASSUME 
    /\ Cardinality(NodeID) >= 3
    /\ Cardinality(Shards) = 2
    /\ MaxLatency = 16
    /\ GodotNodes /= {}
    /\ NodeID \subseteq 1..1000
    /\ IsValidLCRSTree(GodotNodes)
    /\ (IF Cardinality(NodeID) = 1
          THEN \A n \in NodeID : shardMap[n] = Shards
          ELSE /\ \A n \in NodeID : Cardinality(shardMap[n]) = 1
               /\ \A s \in Shards : 
                   Cardinality({n \in NodeID : s \in shardMap[n]}) >= 3
               /\ \A n \in NodeID : 
                   \E s \in Shards : 
                     /\ s \in shardMap[n]
                     /\ \A otherS \in Shards : 
                         (otherS \in shardMap[n]) => (otherS = s)
        )
    /\ crashed = {}

=============================================================================

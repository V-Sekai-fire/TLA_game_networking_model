------------------------------ MODULE GodotSync ------------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets, hlc

CONSTANTS
    GodotNodes,        \* Initial node tree structure in LCRS form
    MaxLatency,        \* Maximum network delay (ticks)
    NodeID,            \* 1..1000
    SceneOperations,   \* Set of valid scene operations
    NULL               \* Representing null node reference

VARIABLES
    globalLog,         \* Seq(LogEntry) - Single ordered log
    appliedIndex,      \* [NodeID |-> Nat] - Last applied index per node
    sceneState,        \* [node |-> [left_child, right_sibling, properties]]
    pendingTxns,       \* [txnId |-> [status, hlc, ops]]
    crashed,           \* Set of crashed nodes
    messages,          \* [NodeID -> Seq(LogEntry)] - Network messages
    hlcWatermark       \* [NodeID |-> HLC] - Max HLC seen per node

(*--------------------------- Type Definitions ----------------------------*)
HLC(n) == <<l[n], c[n]>>  \* HLC tuple for node n

JSON == [key |-> STRING]  \* Simplified JSON representation

SceneOp ==
    [ type |-> {"add_child", "add_sibling", "remove_node", "set_property",
               "move_subtree", "batch_update", "batch_structure", "move_child"},
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

LogEntry == [cmd |-> SceneOp \/ TxnState, hlc |-> HLC]

TxnState ==
    [ txnId |-> Nat,
      status |-> {"PREPARING", "COMMITTING", "COMMITTED", "ABORTED"},
      hlc |-> HLC,
      ops |-> Seq(SceneOp) ]

(*-------------------------- Operation Propagation ------------------------*)
Broadcast(entry) ==
    messages' = [n \in NodeID |->
                 IF n /= currentNode 
                 THEN Append(messages[n], entry)
                 ELSE messages[n]]

ReceiveMessages(n) ==
    LET newEntries == messages[n]
    IN  IF newEntries /= << >> THEN
            /\ globalLog' = globalLog \o newEntries
            /\ hlcWatermark' = [hlcWatermark EXCEPT ![n] = 
                                MaxHLC(hlcWatermark[n], Max({e.hlc : e \in newEntries}))]
            /\ messages' = [messages EXCEPT ![n] = << >>]
        ELSE
            UNCHANGED <<globalLog, hlcWatermark, messages>>

MaxHLC(h1, h2) == 
    IF h1.l > h2.l THEN h1 ELSE
    IF h1.l < h2.l THEN h2 ELSE
    IF h1.c >= h2.c THEN h1 ELSE h2

(*-------------------------- Scene Operations ----------------------------*)
ApplySceneOp(op) ==
    CASE op.type = "add_child" ->
        LET target == op.target
            new == op.new_node
        IN [sceneState EXCEPT 
            ![target].left_child = new,
            ![new] = [ left_child |-> NULL,
                     right_sibling |-> sceneState[target].left_child,
                     properties |-> op.properties ]]
    [] op.type = "add_sibling" ->
        LET target == op.target
            new == op.new_node
        IN [sceneState EXCEPT 
            ![target].right_sibling = new,
            ![new] = [ left_child |-> NULL,
                     right_sibling |-> sceneState[target].right_sibling,
                     properties |-> op.properties ]]
    [] op.type = "remove_node" ->
        LET node == op.node
            parent == CHOOSE p \in DOMAIN sceneState : 
                        sceneState[p].left_child = node \/ sceneState[p].right_sibling = node
        IN IF sceneState[parent].left_child = node THEN
                [sceneState EXCEPT 
                    ![parent].left_child = sceneState[node].right_sibling,
                    ![node] = UNDEFINED]
           ELSE
                [sceneState EXCEPT 
                    ![parent].right_sibling = sceneState[node].right_sibling,
                    ![node] = UNDEFINED]
    [] op.type = "set_property" ->
        [sceneState EXCEPT 
            ![op.node].properties = @ @@ (op.key :> op.value)]
    [] op.type = "move_subtree" ->
        LET old_parent == CHOOSE p \in DOMAIN sceneState : 
                            sceneState[p].left_child = op.node \/ sceneState[p].right_sibling = op.node
            new_parent == op.new_parent
        IN [sceneState EXCEPT
            ![old_parent].left_child = IF sceneState[old_parent].left_child = op.node 
                                      THEN sceneState[op.node].right_sibling 
                                      ELSE sceneState[old_parent].left_child,
            ![op.node].right_sibling = sceneState[new_parent].left_child,
            ![new_parent].left_child = op.node]
    [] op.type = "batch_update" ->
        Fold([s, update |-> 
            [s EXCEPT ![update.node].properties = @ @@ (update.key :> update.value)]], 
            sceneState, op.updates)
    [] op.type = "batch_structure" ->
        Fold([s, op |-> ApplySceneOp(op)], sceneState, op.structure_ops)
    [] op.type = "move_child" ->
        LET parent == op.parent
            children == OrderedChildren(parent)
            new_order == [i \in 1..Len(children) |->
                            IF i < op.to_index THEN children[i]
                            ELSE IF i = op.to_index THEN op.child_node
                            ELSE children[i-1]]
        IN RebuildSiblingLinks(parent, new_order)

RebuildSiblingLinks(parent, children) ==
    IF children = << >> THEN
        [sceneState EXCEPT ![parent].left_child = NULL]
    ELSE
        LET first == Head(children)
            rest == Tail(children)
            updated == [sceneState EXCEPT ![parent].left_child = first]
        IN Fold([s, i |->
                [s EXCEPT ![children[i]].right_sibling = 
                    IF i = Len(rest) THEN NULL ELSE children[i+1]]],
                updated, 1..Len(rest))

(*-------------------------- Transaction Handling -------------------------*)
StartTransaction(txn) ==
    LET txnEntry == [txn EXCEPT !.status = "PREPARING", !.hlc = HLC(currentNode)]
    IN  /\ pendingTxns' = [pendingTxns EXCEPT ![txn.txnId] = txnEntry]
        /\ \A op \in txn.ops: SubmitOp(currentNode, op)

CommitTransaction(txnId) ==
    LET txn == pendingTxns[txnId]
        committed = {entry \in globalLog : entry.hlc <= txn.hlc}
    IN  IF \A op \in txn.ops : 
            \E entry \in committed : entry.cmd = op
        THEN /\ pendingTxns' = [pendingTxns EXCEPT ![txnId].status = "COMMITTED"]
             /\ ApplyTxnOps(txn.ops)
        ELSE AbortTxn(txnId)

AbortTxn(txnId) ==
    LET txn == pendingTxns[txnId]
        InverseOps == [op \in txn.ops |->
            CASE op.type = "add_child" -> [type |-> "remove_node", node |-> op.new_node]
            [] op.type = "add_sibling" -> [type |-> "remove_node", node |-> op.new_node]
            [] op.type = "remove_node" -> 
                [type |-> "add_child", 
                 target |-> op.originalParent,
                 new_node |-> op.node,
                 properties |-> op.originalProperties]
            [] op.type = "set_property" -> 
                [type |-> "set_property",
                 node |-> op.node,
                 key |-> op.key,
                 value |-> op.previousValue]
            [] OTHER -> [type |-> "noop"]]
    IN
    /\ pendingTxns' = [pendingTxns EXCEPT ![txnId].status = "ABORTED"]
    /\ \A op \in txn.ops : 
        IF InverseOps[op].type /= "noop"
        THEN SubmitOp(currentNode, InverseOps[op])
        ELSE UNCHANGED globalLog
    /\ sceneState' = [n \in DOMAIN sceneState |->
                        IF \E op \in txn.ops : 
                            op.type \in {"add_child", "add_sibling"} /\ op.new_node = n
                        THEN UNDEFINED
                        ELSE sceneState[n]]

(*-------------------------- Safety Invariants --------------------------*)
Linearizability ==
    \A i, k \in 1..Len(globalLog):
        /\ (globalLog[i].hlc < globalLog[k].hlc) => (i < k)
        /\ ~\E op1 \in {globalLog[i].cmd}, op2 \in {globalLog[k].cmd} : 
                Conflict(op1, op2)

NoOrphanNodes ==
    LET Roots == {n \in DOMAIN sceneState : 
                  \A m \in DOMAIN sceneState : 
                      n /= sceneState[m].left_child /\ n /= sceneState[m].right_sibling}
    IN
    /\ Cardinality(Roots) = 1
    /\ LET Root == CHOOSE r \in Roots : TRUE
           RECURSIVE ReachableFrom(n) ==
               {n} \cup 
               IF sceneState[n].left_child /= NULL 
                   THEN ReachableFrom(sceneState[n].left_child) 
                   ELSE {} \cup
               IF sceneState[n].right_sibling /= NULL 
                   THEN ReachableFrom(sceneState[n].right_sibling) 
                   ELSE {}
       IN DOMAIN sceneState \subseteq ReachableFrom(Root)

CausalConsistency ==
    \A n1, n2 \in NodeID:
        hlcWatermark[n1] < hlcWatermark[n2] => 
            appliedIndex[n1] <= appliedIndex[n2]

(*-------------------------- Initial State -------------------------------*)
ASSUME 
    /\ Cardinality(NodeID) >= 3
    /\ MaxLatency = 16
    /\ GodotNodes /= {}
    /\ NodeID \subseteq 1..1000
    /\ IsValidLCRSTree
    /\ crashed = {}
    /\ appliedIndex = [n \in NodeID |-> 0]
    /\ globalLog = << >>
    /\ messages = [n \in NodeID |-> << >>]
    /\ hlcWatermark = [n \in NodeID |-> <<0, 0>>]

=============================================================================

------------------------------ MODULE GodotSync ------------------------------
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
    appliedIndex,      \* [NodeID |-> [ShardID |-> Nat]]
    
    (* Shard Mapping *)
    shardMap,         \* [node |-> SUBSET Shards]
    crashed           \* Set of crashed nodes

(*--------------------------- Type Definitions ----------------------------*)
HLC == <<pt[self], l[self], c[self]>>  \* Combined HLC tuple

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

JSON == [key |-> STRING]  \* Simplified JSON representation

(*-------------------------- Raft-HLC Integration --------------------------*)
ShardLogEntry == [term |-> Nat, cmd |-> SceneOp \/ TxnState, hlc |-> HLC, shard |-> Shards]

LeaderAppend(shard, op) ==
    LET leader == shardLeaders[shard]
        new_pt == pt[leader] + 1
        new_l == IF l[leader] >= new_pt THEN l[leader] ELSE new_pt
        new_c == IF l[leader] >= new_pt THEN c[leader] + 1 ELSE 0
        entry == [term |-> shardTerms[shard], cmd |-> op, hlc |-> <<new_pt, new_l, new_c>>, shard |-> shard]
    IN  /\ pt' = [pt EXCEPT ![leader] = new_pt]
        /\ l' = [l EXCEPT ![leader] = new_l]
        /\ c' = [c EXCEPT ![leader] = new_c]
        /\ shardLogs' = [shardLogs EXCEPT ![shard] = Append(shardLogs[shard], entry)]
        /\ SendToShard(shard, entry)
        /\ UNCHANGED <<shardTerms, shardCommitIndex>>

(*-------------------------- Scene Tree Operations -----------------------*)
FilterSeq(seq, elem) ==
    IF seq = << >> THEN << >>
    ELSE IF Head(seq) = elem THEN FilterSeq(Tail(seq), elem)
    ELSE <<Head(seq)>> \o FilterSeq(Tail(seq), elem)

\* Recursive operator to build transfer entries
RecursiveTransfer(remaining, acc) ==
    IF remaining = << >> 
    THEN acc
    ELSE LET n == Head(remaining)
             newEntry == [ type |-> "state_transfer",
                            node |-> n,
                            state |-> sceneState[n],
                            hlc |-> <<pt[n], l[n], c[n]>> ]
         IN RecursiveTransfer(Tail(remaining), acc \o <<newEntry>>)

\* Recursive operator to build remove entries
RecursiveRemove(remaining, acc) ==
    IF remaining = << >> 
    THEN acc
    ELSE LET n == Head(remaining)
             newEntry == [ type |-> "shard_remove",
                            node |-> n ]
         IN RecursiveRemove(Tail(remaining), acc \o <<newEntry>>)

ApplySceneOp(op) ==
    LET RemoveFromOriginalParent(n, p) ==
        IF sceneState[p].left_child = n 
        THEN [sceneState EXCEPT ![p].left_child = sceneState[n].right_sibling]
        ELSE IF sceneState[p].right_sibling = n 
             THEN [sceneState EXCEPT ![p].right_sibling = sceneState[n].right_sibling]
             ELSE sceneState
    IN
    LET Children(n) == 
        LET first == sceneState[n].left_child
        IN  IF first = NULL THEN {} 
            ELSE {first} \cup Siblings(first)
    Siblings(n) == 
        LET sib == sceneState[n].right_sibling
        IN  IF sib = NULL THEN {} ELSE {sib} \cup Siblings(sib)
    Descendants(n) == 
        {n} \cup UNION { Descendants(c) : c \in Children(n) }
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
        LET 
            OrderedDescendants(node) == ...  \* Your existing definition
            descendantsSeq == OrderedDescendants(op.node)
            
            \* Build sequences recursively
            transferEntries == RecursiveTransfer(descendantsSeq, << >>)
            removeEntries == RecursiveRemove(descendantsSeq, << >>)
        IN
        LET newEntries == [s \in Shards |-> 
            IF s = op.new_shard 
                THEN transferEntries
            ELSE IF s \in old_shards 
                THEN removeEntries
            ELSE << >> ]
        IN
        /\ \A s \in Shards : 
            IF newEntries[s] /= << >> THEN
                /\ LeaderAppend(s, newEntries[s])
                /\ shardMap' = [n \in NodeID |-> 
                    IF n \in descendantsSeq THEN {op.new_shard} ELSE shardMap[n]]
                /\ IF original_parent /= NULL THEN
                    LET detach_op == [type |-> "detach_child", node |-> original_parent, child |-> op.node]
                    IN \A s \in shardMap[original_parent] :
                        LeaderAppend(s, detach_op)
                  ELSE
                    UNCHANGED <<shardMap, sceneState>> 
            ELSE
                UNCHANGED <<shardMap, sceneState>> 
        /\ IF op.new_parent /= NULL THEN
            LeaderAppend(op.new_shard, [type |-> "attach_child", 
                                      node |-> op.new_parent, 
                                      child |-> op.node, 
                                      position |-> op.position])
          ELSE
            UNCHANGED <<shardMap, sceneState>>
        /\ IF op.new_parent = NULL THEN
            LeaderAppend(op.new_shard, [type |-> "add_child", 
                                      target |-> NULL, 
                                      new_node |-> op.node, 
                                      properties |-> sceneState[op.node].properties])
          ELSE
            UNCHANGED <<shardMap, sceneState>>
        /\ UNCHANGED <<sceneState>>
 

(*-------------------------- Crash Recovery --------------------------*)
RecoverNode(n) ==
    /\ n \in crashed
    /\ appliedIndex' = [appliedIndex EXCEPT ![n] = [s \in Shards |-> 0]]
    /\ \A s \in shardMap[n] :
        \A idx \in 0..(shardCommitIndex[s] - appliedIndex[n][s] - 1):
            LET entry = shardLogs[s][appliedIndex[n][s] + idx + 1]
            IN  CASE entry.cmd.type = "state_transfer" ->
                    sceneState' = [sceneState EXCEPT ![entry.cmd.node] = entry.cmd.state]
                [] OTHER ->
                    IF entry.shard = s THEN ApplySceneOp(entry.cmd) ELSE UNCHANGED
            /\ appliedIndex' = [appliedIndex EXCEPT ![n][s] = appliedIndex[n][s] + 1]
    /\ crashed' = crashed \ {n}

(*-------------------------- Parallel Commit Protocol -----------------------*)
StartParallelCommit(txn) ==
    LET coordShard == CHOOSE s \in txn.shards : TRUE
    LET txnEntry == [txn EXCEPT !.status = "COMMITTING", !.coordShard = coordShard]
    IN
    /\ pendingTxns' = [pendingTxns EXCEPT ![txn.txnId] = txnEntry]
    /\ \A s \in txn.shards :
        LeaderAppend(s, IF s = coordShard THEN txnEntry ELSE [type |-> "COMMIT", txnId |-> txn.txnId, hlc |-> txn.hlc])

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
       /\ (op1.key = op2.key \/ op1.type \notin {"set_property"}))
    \/ (IsTreeMod(op1) /\ (op2.node \in Descendants(op1.node) \/ op1.node \in Descendants(op2.node)))
    \/ (IsTreeMod(op2) /\ (op1.node \in Descendants(op2.node) \/ op2.node \in Descendants(op1.node)))
    \/ (op1.type = "move_child" /\ op2.type = "move_child" 
       /\ op1.parent = op2.parent /\ op1.child_node = op2.child_node)
    \/ (op1.type = "move_child" /\ op2.type \in {"add_child", "add_sibling"} 
       /\ op1.parent = op2.target)

IsWrite(op) == op.type = "set_property"
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
                e.cmd.type = "set_property"

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

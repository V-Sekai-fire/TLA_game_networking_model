(*--algorithm GodotSync
variables
    messages = {}, 
    currentTerm = [n \in NodeID |-> 1],
    state = [n \in NodeID |-> "follower"],
    votedFor = [n \in NodeID |-> NULL],
    log = [n \in NodeID |-> <<>>],
    commitIndex = [n \in NodeID |-> 0],
    nextIndex = [n \in NodeID |-> 1],
    matchIndex = [n \in NodeID |-> 0],
    pt = [n \in NodeID |-> 0], l = [n \in NodeID |-> 0], c = [n \in NodeID |-> 0],
    sceneState = GodotNodes,
    pendingTxns = [txnId \in {} |-> [status |-> "ABORTED", shards |-> {}, hlc |-> <<0,0,0>>, ops |-> <<>>]],
    appliedIndex = [n \in NodeID |-> 0];

define
    HLC(n) == <<pt[n], l[n], c[n]>>;
    AdvanceHLC(n) ==
        pt[n] := pt[n] + 1;
        l[n] := Max(l[n], pt[n]);
        c[n] := 0;
    SendToAll(src, entry) ==
        messages := messages \union {[to |-> d, from |-> src, term |-> currentTerm[src], data |-> entry] : d \in NodeID};
    Conflict(op1, op2) ==
        \/ op1.node = op2.node
        \/ op1.target = op2.target
        \/ op1.new_node = op2.new_node;
end define;

fair process node \in NodeID
variables
    lastHLC = HLC(self),
    currentTxn = NULL;
begin
    NODE:
    while TRUE do
        \*--- Message Handling ---
        HandleRPC:
        if \E msg \in messages: msg.to = self then
            with rpc = CHOOSE msg \in messages: msg.to = self do
                messages := messages \ {rpc};
                
                \* Update HLC
                pt[self] := Max(pt[self], rpc.data.hlc[1]);
                l[self] := Max(l[self], rpc.data.hlc[2]);
                c[self] := If l[self] = lastHLC[2] THEN lastHLC[3] + 1 ELSE 0;
                lastHLC := HLC(self);
                
                \* Handle different RPC types
                if rpc.data.type = "AppendEntries" then
                    if rpc.term >= currentTerm[self] then
                        currentTerm[self] := rpc.term;
                        state[self] := "follower";
                        votedFor[self] := NULL;
                        
                        \* Log replication logic
                        if rpc.data.prevLogIndex = 0 \/ log[self][rpc.data.prevLogIndex].term = rpc.data.prevLogTerm then
                            log[self] := SubSeq(log[self], 1, rpc.data.prevLogIndex) \o rpc.data.entries;
                            commitIndex[self] := Min(rpc.data.leaderCommit, Len(log[self]));
                        end if;
                    end if;
                    
                elsif rpc.data.type = "RequestVote" then
                    if rpc.term > currentTerm[self] /\ (votedFor[self] = NULL \/ votedFor[self] = rpc.from) then
                        votedFor[self] := rpc.from;
                        messages := messages \union {[
                            to |-> rpc.from, 
                            from |-> self,
                            term |-> currentTerm[self],
                            data |-> [type |-> "VoteResponse", granted |-> TRUE, hlc |-> HLC(self)]
                        ]};
                    end if;
                end if;
            end with;
        end if;
        
        \*--- Leader Election ---
        StartElection:
        if state[self] = "follower" /\ \A msg \in messages: msg.to /= self then
            state[self] := "candidate";
            currentTerm[self] := currentTerm[self] + 1;
            votedFor[self] := self;
            SendToAll(self, [type |-> "RequestVote", 
                            lastLogIndex |-> Len(log[self]), 
                            lastLogTerm |-> IF Len(log[self]) > 0 THEN log[self][Len(log[self])].term ELSE 0,
                            hlc |-> HLC(self)]);
            AdvanceHLC(self);
        end if;
        
        \*--- Log Commitment ---
        CommitEntries:
        if state[self] = "leader" then
            with newCommit = Max({i \in 1..Len(log[self]) : 
                                Cardinality({n \in NodeID : matchIndex[n] >= i}) > Cardinality(NodeID)/2}) do
                if newCommit > commitIndex[self] /\ log[self][newCommit].term = currentTerm[self] then
                    commitIndex[self] := newCommit;
                end if;
            end with;
        end if;
        
        \*--- State Application ---
        ApplyCommits:
        if appliedIndex[self] < commitIndex[self] then
            appliedIndex[self] := appliedIndex[self] + 1;
            with entry = log[self][appliedIndex[self]] do
                if entry.cmd.type \in DOMAIN SceneOperations then
                    ApplySceneOp(entry.cmd);
                elsif entry.cmd.status = "COMMITTED" then
                    with txn = entry.cmd do
                        if \A s \in txn.shards : s.status = "PREPARED" then
                            pendingTxns[txn.txnId] := txn;
                            for op \in txn.ops do
                                ApplySceneOp(op);
                            end for;
                        end if;
                    end with;
                end if;
            end with;
        end if;
        
        \*--- Client Request Handling ---
        HandleClient:
        if state[self] = "leader" /\ currentTxn = NULL then
            with newOp = CHOOSE op \in SceneOperations : TRUE do
                if newOp.type \in {"add_child", "add_sibling"} then
                    currentTxn := [txnId |-> Len(pendingTxns)+1,
                                  status |-> "PREPARED",
                                  shards |-> {s \in Shards : newOp.node \in s},
                                  hlc |-> HLC(self),
                                  ops |-> <<newOp>>];
                    LeaderAppend(currentTxn);
                else
                    LeaderAppend(newOp);
                end if;
                currentTxn := NULL;
            end with;
        end if;
        
        \*--- HLC Advancement ---
        AdvanceClock:
        if pc[self] < MaxLatency then
            pc[self] := pc[self] + 1;
            pt[self] := pt[self] + 1;
            l[self] := Max(l[self], pt[self]);
            c[self] := 0;
        end if;
    end while;
end process;
end algorithm;*)

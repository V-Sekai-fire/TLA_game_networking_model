--------------------------------- MODULE MultiRaft ---------------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Server, Shard, Value, Follower, Candidate, Leader, Nil, 
          RequestVoteRequest, RequestVoteResponse, AppendEntriesRequest, AppendEntriesResponse

VARIABLES 
    \* Per-shard variables
    shardCurrentTerm,  \* [Shard -> [Server -> Term]]
    shardState,        \* [Shard -> [Server -> {Follower, Candidate, Leader}]]
    shardVotedFor,     \* [Shard -> [Server -> Server | Nil]]
    shardLogs,         \* [Shard -> [Server -> Seq(Entry)]]
    shardCommitIndex,  \* [Shard -> [Server -> Index]]
    shardNextIndex,    \* [Shard -> [Server -> [Server -> Index]]]
    shardMatchIndex,   \* [Shard -> [Server -> [Server -> Index]]]
    shardVotesResponded, \* [Shard -> [Server -> SUBSET Server]]
    shardVotesGranted, \* [Shard -> [Server -> SUBSET Server]]
    
    \* Global variables
    messages,          \* Bag of messages across all shards
    elections,         \* History of elections per shard
    allLogs,          \* All logs across shards
    shardMap          \* [Server -> SUBSET Shard] (Shards each server is part of)

Quorum(shard) == 
    LET Nodes == {s \in Server : shard \in shardMap[s]} 
    IN {q \in SUBSET Nodes : Cardinality(q) * 2 > Cardinality(Nodes)}

WithMessage(m, msgs) == 
    IF m \in DOMAIN msgs THEN [msgs EXCEPT ![m] = @ + 1] ELSE msgs @@ (m :> 1)

WithoutMessage(m, msgs) == 
    IF m \in DOMAIN msgs THEN 
        IF msgs[m] <= 1 THEN [x \in DOMAIN msgs \ {m} |-> msgs[x]] 
        ELSE [msgs EXCEPT ![m] = @ - 1]
    ELSE msgs

Send(m) == messages' = WithMessage(m, messages)
Discard(m) == messages' = WithoutMessage(m, messages)
Reply(response, request) == messages' = WithoutMessage(request, WithMessage(response, messages))

LastTerm(shard, s) == 
    IF Len(shardLogs[shard][s]) = 0 THEN 0 ELSE shardLogs[shard][s][Len(shardLogs[shard][s])].term

Init == 
    /\ messages = [m \in {} |-> 0]
    /\ elections = {}
    /\ allLogs = {}
    /\ shardCurrentTerm = [sh \in Shard |-> [s \in Server |-> 1]]
    /\ shardState = [sh \in Shard |-> [s \in Server |-> Follower]]
    /\ shardVotedFor = [sh \in Shard |-> [s \in Server |-> Nil]]
    /\ shardLogs = [sh \in Shard |-> [s \in Server |-> <<>>]]
    /\ shardCommitIndex = [sh \in Shard |-> [s \in Server |-> 0]]
    /\ shardNextIndex = [sh \in Shard |-> [s \in Server |-> [d \in Server |-> 1]]]
    /\ shardMatchIndex = [sh \in Shard |-> [s \in Server |-> [d \in Server |-> 0]]]
    /\ shardVotesResponded = [sh \in Shard |-> [s \in Server |-> {}]]
    /\ shardVotesGranted = [sh \in Shard |-> [s \in Server |-> {}]]
    /\ shardMap = [s \in Server |-> {}]

Restart(s, shard) ==
    /\ shardState' = [shardState EXCEPT ![shard][s] = Follower]
    /\ shardVotesResponded' = [shardVotesResponded EXCEPT ![shard][s] = {}]
    /\ shardVotesGranted' = [shardVotesGranted EXCEPT ![shard][s] = {}]
    /\ shardNextIndex' = [shardNextIndex EXCEPT ![shard][s] = [d \in Server |-> 1]]
    /\ shardMatchIndex' = [shardMatchIndex EXCEPT ![shard][s] = [d \in Server |-> 0]]
    /\ shardCommitIndex' = [shardCommitIndex EXCEPT ![shard][s] = 0]
    /\ UNCHANGED <<messages, shardCurrentTerm, shardVotedFor, shardLogs>>

Timeout(s, shard) == 
    /\ shard \in shardMap[s]
    /\ shardState[shard][s] \in {Follower, Candidate}
    /\ shardState' = [shardState EXCEPT ![shard][s] = Candidate]
    /\ shardCurrentTerm' = [shardCurrentTerm EXCEPT ![shard][s] = @ + 1]
    /\ shardVotedFor' = [shardVotedFor EXCEPT ![shard][s] = Nil]
    /\ shardVotesResponded' = [shardVotesResponded EXCEPT ![shard][s] = {}]
    /\ shardVotesGranted' = [shardVotesGranted EXCEPT ![shard][s] = {}]
    /\ UNCHANGED <<messages, shardLogs, shardCommitIndex>>

RequestVote(s, shard, dest) ==
    /\ shard \in shardMap[s]
    /\ shardState[shard][s] = Candidate
    /\ dest \in shardMap[dest]
    /\ dest \notin shardVotesResponded[shard][s]
    /\ Send([mtype |-> RequestVoteRequest, shard |-> shard, mterm |-> shardCurrentTerm[shard][s], 
             mlastLogTerm |-> LastTerm(shard, s), mlastLogIndex |-> Len(shardLogs[shard][s]), 
             msource |-> s, mdest |-> dest])
    /\ UNCHANGED <<shardCurrentTerm, shardState, shardVotedFor, shardLogs>>

BecomeLeader(s, shard) ==
    /\ shardState[shard][s] = Candidate
    /\ shardVotesGranted[shard][s] \in Quorum(shard)
    /\ shardState' = [shardState EXCEPT ![shard][s] = Leader]
    /\ shardNextIndex' = [shardNextIndex EXCEPT ![shard][s] = [d \in Server |-> Len(shardLogs[shard][s]) + 1]]
    /\ shardMatchIndex' = [shardMatchIndex EXCEPT ![shard][s] = [d \in Server |-> 0]]
    /\ elections' = elections \cup {[shard |-> shard, leader |-> s, term |-> shardCurrentTerm[shard][s]]}
    /\ UNCHANGED <<messages, shardCurrentTerm, shardVotedFor, shardLogs>>

AppendEntries(s, shard, dest) ==
    /\ s /= dest
    /\ shardState[shard][s] = Leader
    /\ LET localPrevLogIndex == shardNextIndex[shard][s][dest] - 1
           prevLogTerm == IF localPrevLogIndex > 0 THEN shardLogs[shard][s][localPrevLogIndex].term ELSE 0
           entries == IF localPrevLogIndex + 1 <= Len(shardLogs[shard][s]) THEN <<shardLogs[shard][s][localPrevLogIndex + 1]>> ELSE <<>>
       IN Send([mtype |-> AppendEntriesRequest, shard |-> shard, mterm |-> shardCurrentTerm[shard][s],
                mprevLogIndex |-> localPrevLogIndex, mprevLogTerm |-> prevLogTerm, mentries |-> entries,
                mcommitIndex |-> Min({shardCommitIndex[shard][s], localPrevLogIndex + Len(entries)}),
                msource |-> s, mdest |-> dest])
    /\ UNCHANGED <<shardCurrentTerm, shardState, shardVotedFor, shardLogs>>

HandleRequestVoteRequest(s, shard, m) ==
    LET logOk = \/ m.mlastLogTerm > LastTerm(shard, s)
                \/ /\ m.mlastLogTerm = LastTerm(shard, s)
                   /\ m.mlastLogIndex >= Len(shardLogs[shard][s])
        grant = /\ m.mterm = shardCurrentTerm[shard][s]
                /\ logOk
                /\ shardVotedFor[shard][s] \in {Nil, m.msource}
    IN /\ m.mterm <= shardCurrentTerm[shard][s]
       /\ \/ grant /\ shardVotedFor' = [shardVotedFor EXCEPT ![shard][s] = m.msource]
          \/ ~grant /\ UNCHANGED shardVotedFor
       /\ Reply([mtype |-> RequestVoteResponse, shard |-> shard, mterm |-> shardCurrentTerm[shard][s],
                 mvoteGranted |-> grant, msource |-> s, mdest |-> m.msource], m)
       /\ UNCHANGED <<shardState, shardCurrentTerm, shardLogs>>

HandleRequestVoteResponse(s, shard, m) ==
    /\ m.mterm = shardCurrentTerm[shard][s]
    /\ shardVotesResponded' = [shardVotesResponded EXCEPT ![shard][s] = @ \cup {m.msource}]
    /\ \/ m.mvoteGranted /\ shardVotesGranted' = [shardVotesGranted EXCEPT ![shard][s] = @ \cup {m.msource}
       \/ ~m.mvoteGranted /\ UNCHANGED shardVotesGranted
    /\ Discard(m)
    /\ UNCHANGED <<shardCurrentTerm, shardState, shardVotedFor, shardLogs>>

HandleAppendEntriesRequest(s, shard, m) ==
    LET logOk = \/ m.mprevLogIndex = 0
                \/ /\ m.mprevLogIndex <= Len(shardLogs[shard][s])
                   /\ m.mprevLogTerm = shardLogs[shard][s][m.mprevLogIndex].term
    IN /\ m.mterm <= shardCurrentTerm[shard][s]
       /\ \/ /\ (m.mterm < shardCurrentTerm[shard][s] \/ ~logOk)
             /\ Reply([mtype |-> AppendEntriesResponse, shard |-> shard, mterm |-> shardCurrentTerm[shard][s],
                       msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> s, mdest |-> m.msource], m)
             /\ UNCHANGED <<shardState, shardLogs>>
          \/ /\ m.mterm = shardCurrentTerm[shard][s]
             /\ shardState' = [shardState EXCEPT ![shard][s] = Follower]
             /\ UNCHANGED <<shardCurrentTerm, shardVotedFor, shardLogs>>
          \/ /\ logOk
             /\ shardCommitIndex' = [shardCommitIndex EXCEPT ![shard][s] = m.mcommitIndex]
             /\ Reply([mtype |-> AppendEntriesResponse, shard |-> shard, mterm |-> shardCurrentTerm[shard][s],
                       msuccess |-> TRUE, mmatchIndex |-> m.mprevLogIndex + Len(m.mentries),
                       msource |-> s, mdest |-> m.msource], m)
             /\ UNCHANGED <<shardLogs>>
    /\ UNCHANGED <<shardCurrentTerm, shardVotedFor>>

AdvanceCommitIndex(s, shard) ==
    /\ shardState[shard][s] = Leader
    /\ LET agreeIndexes = {index \in 1..Len(shardLogs[shard][s]) : 
                           {s} \cup {k \in Server | shardMatchIndex[shard][s][k] >= index} \in Quorum(shard)}
           newCommit = IF agreeIndexes /= {} /\ shardLogs[shard][s][Max(agreeIndexes)].term = shardCurrentTerm[shard][s]
                       THEN Max(agreeIndexes) ELSE shardCommitIndex[shard][s]
       IN shardCommitIndex' = [shardCommitIndex EXCEPT ![shard][s] = newCommit]
    /\ UNCHANGED <<messages, shardCurrentTerm, shardState, shardVotedFor, shardLogs>>

Receive(m) ==
    LET s = m.mdest
        shard = m.shard
    IN \/ /\ m.mterm > shardCurrentTerm[shard][s]
          /\ shardCurrentTerm' = [shardCurrentTerm EXCEPT ![shard][s] = m.mterm]
          /\ shardState' = [shardState EXCEPT ![shard][s] = Follower]
          /\ shardVotedFor' = [shardVotedFor EXCEPT ![shard][s] = Nil]
          /\ UNCHANGED <<messages, shardLogs>>
       \/ /\ m.mtype = RequestVoteRequest
          /\ HandleRequestVoteRequest(s, shard, m)
       \/ /\ m.mtype = RequestVoteResponse
          /\ HandleRequestVoteResponse(s, shard, m)
       \/ /\ m.mtype = AppendEntriesRequest
          /\ HandleAppendEntriesRequest(s, shard, m)
       \/ /\ m.mtype = AppendEntriesResponse
          /\ HandleAppendEntriesResponse(s, shard, m)

Next == 
    \/ \E s \in Server, shard \in Shard : Restart(s, shard)
    \/ \E s \in Server, shard \in Shard : Timeout(s, shard)
    \/ \E s, dest \in Server, shard \in Shard : RequestVote(s, shard, dest)
    \/ \E s \in Server, shard \in Shard : BecomeLeader(s, shard)
    \/ \E s, dest \in Server, shard \in Shard : AppendEntries(s, shard, dest)
    \/ \E m \in DOMAIN messages : Receive(m)
    \/ \E s \in Server, shard \in Shard : AdvanceCommitIndex(s, shard)
    /\ allLogs' = allLogs \cup {shardLogs[shard][s] : s \in Server, shard \in Shard}

Spec == Init /\ [][Next]_<<messages, shardCurrentTerm, shardState, shardVotedFor, shardLogs, shardCommitIndex, shardNextIndex, shardMatchIndex, shardVotesResponded, shardVotesGranted, elections, allLogs, shardMap>>

=============================================================================
--------------------------------- MODULE MultiRaft ---------------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Server, Shard, Value, Follower, Candidate, Leader, Nil, 
          RequestVoteRequest, RequestVoteResponse, AppendEntriesRequest, AppendEntriesResponse
          
(*
 * This is the formal specification for a Multi-Shard Raft consensus algorithm.
 * Each shard operates as an independent Raft cluster with its own leader election and log replication.
 * 
 * Adapted from the original Raft specification by Diego Ongaro. https://github.com/ongardie/raft.tla
 *)

VARIABLES 
    \* Per-shard variables
    shardCurrentTerm,  \* For each shard, the current term of each server (function: Shard → [Server → Term])
    shardState,        \* For each shard, the state of each server (Follower, Candidate, Leader)
    shardVotedFor,     \* For each shard, the candidate a server voted for in its current term, or Nil
    shardLogs,         \* For each shard, the log entries on each server (sequence of entries)
    shardCommitIndex,  \* For each shard, the index of the highest committed log entry on each server
    shardNextIndex,    \* For each shard, a leader's next index for each follower (function: Shard → Server → [Server → Index])
    shardMatchIndex,   \* For each shard, a leader's match index for each follower (highest known replicated index)
    shardVotesResponded, \* For each shard, set of servers that responded to a candidate's vote requests
    shardVotesGranted, \* For each shard, set of servers that granted a candidate their vote
    
    \* Global variables
    messages,          \* Bag of in-flight messages across all shards (messages include shard identifier)
    elections,         \* History of successful elections per shard, tracking leaders and their terms
    allLogs,          \* Union of all logs across all shards and servers (used for proof purposes)
    shardMap          \* Assignment of servers to shards (each server participates in a subset of shards)

(* 
 * A quorum for a shard is a majority of servers in that shard's configuration.
 * This ensures that any two quorums for the same shard have overlapping servers.
 *)
Quorum(shard) == 
    LET Nodes == {s \in Server : shard \in shardMap[s]} 
    IN {q \in SUBSET Nodes : Cardinality(q) * 2 > Cardinality(Nodes)}

(*
 * Helper functions to manipulate the message bag.
 * WithMessage adds a message, WithoutMessage removes one.
 * These operate globally across all shards.
 *)
WithMessage(m, msgs) == 
    IF m \in DOMAIN msgs THEN [msgs EXCEPT ![m] = @ + 1] ELSE msgs @@ (m :> 1)

WithoutMessage(m, msgs) == 
    IF m \in DOMAIN msgs THEN 
        IF msgs[m] <= 1 THEN [x \in DOMAIN msgs \ {m} |-> msgs[x]] 
        ELSE [msgs EXCEPT ![m] = @ - 1]
    ELSE msgs

Send(m) == messages' = WithMessage(m, messages)
(* Remove a message from the bag after processing *)
Discard(m) == messages' = WithoutMessage(m, messages)
(* Send a response and remove the corresponding request *)
Reply(response, request) == messages' = WithoutMessage(request, WithMessage(response, messages))

(*
 * The term of the last entry in a server's log for a specific shard.
 * Returns 0 if the log is empty.
 *)
LastTerm(shard, s) == 
    IF Len(shardLogs[shard][s]) = 0 THEN 0 ELSE shardLogs[shard][s][Len(shardLogs[shard][s])].term

(* Initial state: all shards start with servers as followers, empty logs, and no votes *)
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

(* Server s restarts in a shard, resetting transient state but preserving log and term *)
Restart(s, shard) ==
    /\ shardState' = [shardState EXCEPT ![shard][s] = Follower]
    /\ shardVotesResponded' = [shardVotesResponded EXCEPT ![shard][s] = {}]
    /\ shardVotesGranted' = [shardVotesGranted EXCEPT ![shard][s] = {}]
    /\ shardNextIndex' = [shardNextIndex EXCEPT ![shard][s] = [d \in Server |-> 1]]
    /\ shardMatchIndex' = [shardMatchIndex EXCEPT ![shard][s] = [d \in Server |-> 0]]
    /\ shardCommitIndex' = [shardCommitIndex EXCEPT ![shard][s] = 0]
    /\ UNCHANGED <<messages, shardCurrentTerm, shardVotedFor, shardLogs>>

(* Server s times out in a shard, starting a new election by becoming candidate *)
Timeout(s, shard) == 
    /\ shard \in shardMap[s]
    /\ shardState[shard][s] \in {Follower, Candidate}
    /\ shardState' = [shardState EXCEPT ![shard][s] = Candidate]
    /\ shardCurrentTerm' = [shardCurrentTerm EXCEPT ![shard][s] = @ + 1]
    /\ shardVotedFor' = [shardVotedFor EXCEPT ![shard][s] = Nil]
    /\ shardVotesResponded' = [shardVotesResponded EXCEPT ![shard][s] = {}]
    /\ shardVotesGranted' = [shardVotesGranted EXCEPT ![shard][s] = {}]
    /\ UNCHANGED <<messages, shardLogs, shardCommitIndex>>

(* Candidate s in shard sends a vote request to destination server dest *)
RequestVote(s, shard, dest) ==
    /\ shard \in shardMap[s]
    /\ shardState[shard][s] = Candidate
    /\ dest \in shardMap[dest]
    /\ dest \notin shardVotesResponded[shard][s]
    /\ Send([mtype |-> RequestVoteRequest, shard |-> shard, mterm |-> shardCurrentTerm[shard][s], 
             mlastLogTerm |-> LastTerm(shard, s), mlastLogIndex |-> Len(shardLogs[shard][s]), 
             msource |-> s, mdest |-> dest])
    /\ UNCHANGED <<shardCurrentTerm, shardState, shardVotedFor, shardLogs>>

(* Candidate s in shard becomes leader upon receiving a quorum of votes *)
BecomeLeader(s, shard) ==
    /\ shardState[shard][s] = Candidate
    /\ shardVotesGranted[shard][s] \in Quorum(shard)
    /\ shardState' = [shardState EXCEPT ![shard][s] = Leader]
    /\ shardNextIndex' = [shardNextIndex EXCEPT ![shard][s] = [d \in Server |-> Len(shardLogs[shard][s]) + 1]]
    /\ shardMatchIndex' = [shardMatchIndex EXCEPT ![shard][s] = [d \in Server |-> 0]]
    /\ elections' = elections \cup {[shard |-> shard, leader |-> s, term |-> shardCurrentTerm[shard][s], 
                                      voterLogs |-> [voter \in shardVotesGranted[shard][s] |-> shardLogs[shard][voter]]]}
    /\ UNCHANGED <<messages, shardCurrentTerm, shardVotedFor, shardLogs>>

(* Leader s in shard sends log entries to destination server dest *)
AppendEntries(s, shard, dest) ==
    /\ s /= dest
    /\ shardState[shard][s] = Leader
    /\ LET localPrevLogIndex == shardNextIndex[shard][s][dest] - 1
           prevLogTerm == IF localPrevLogIndex > 0 THEN shardLogs[shard][s][localPrevLogIndex].term ELSE 0
           entries == IF localPrevLogIndex + 1 <= Len(shardLogs[shard][s]) THEN <<shardLogs[shard][s][localPrevLogIndex + 1]>> ELSE <<>>
           commitIndex == IF shardCommitIndex[shard][s] <= localPrevLogIndex + Len(entries)
                             THEN shardCommitIndex[shard][s]
                             ELSE localPrevLogIndex + Len(entries)
       IN Send([mtype |-> AppendEntriesRequest, shard |-> shard, mterm |-> shardCurrentTerm[shard][s],
                mprevLogIndex |-> localPrevLogIndex, mprevLogTerm |-> prevLogTerm, mentries |-> entries,
                mcommitIndex |-> commitIndex,
                msource |-> s, mdest |-> dest])
    /\ UNCHANGED <<shardCurrentTerm, shardState, shardVotedFor, shardLogs>>

(* Server s in shard processes a vote request from m.msource *)
HandleRequestVoteRequest(s, shard, m) ==
    LET logOk == \/ m.mlastLogTerm > LastTerm(shard, s)
                \/ /\ m.mlastLogTerm = LastTerm(shard, s)
                   /\ m.mlastLogIndex >= Len(shardLogs[shard][s])
        grant == /\ m.mterm = shardCurrentTerm[shard][s]
                /\ logOk
                /\ shardVotedFor[shard][s] \in {Nil, m.msource}
    IN /\ m.mterm <= shardCurrentTerm[shard][s]
       /\ \/ grant /\ shardVotedFor' = [shardVotedFor EXCEPT ![shard][s] = m.msource]
          \/ ~grant /\ UNCHANGED shardVotedFor
       /\ Reply([mtype |-> RequestVoteResponse, shard |-> shard, mterm |-> shardCurrentTerm[shard][s],
                 mvoteGranted |-> grant, msource |-> s, mdest |-> m.msource], m)
       /\ UNCHANGED <<shardState, shardCurrentTerm, shardLogs>>

(* Server s in shard processes a vote response from m.msource *)
HandleRequestVoteResponse(s, shard, m) ==
    /\ IF m.mterm < shardCurrentTerm[shard][s] THEN
           Discard(m) /\ UNCHANGED <<shardVotesResponded, shardVotesGranted>>
       ELSE
           /\ m.mterm = shardCurrentTerm[shard][s]
           /\ shardVotesResponded' = [shardVotesResponded EXCEPT ![shard][s] = @ \cup {m.msource}]
           /\ \/ m.mvoteGranted /\ shardVotesGranted' = [shardVotesGranted EXCEPT ![shard][s] = @ \cup {m.msource}]
              \/ ~m.mvoteGranted /\ UNCHANGED shardVotesGranted
           /\ Discard(m)
    /\ UNCHANGED <<shardCurrentTerm, shardState, shardVotedFor, shardLogs>>

(* Server s in shard processes an append entries request from m.msource *)
HandleAppendEntriesRequest(s, shard, m) ==
    LET logOk == \/ m.mprevLogIndex = 0
                \/ /\ m.mprevLogIndex <= Len(shardLogs[shard][s])
                   /\ m.mprevLogTerm = shardLogs[shard][s][m.mprevLogIndex].term
        entries == m.mentries
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
             /\ \* Append new entries and truncate conflicting ones
                LET index == m.mprevLogIndex + 1
                    logLength == Len(shardLogs[shard][s])
                IN IF logLength >= index /\ logLength > 0 /\ index <= logLength /\ 
                      shardLogs[shard][s][index].term /= entries[1].term THEN
                       shardLogs' = [shardLogs EXCEPT ![shard][s] = 
                                       SubSeq(shardLogs[shard][s], 1, m.mprevLogIndex) \o entries]
                   ELSE 
                       shardLogs' = [shardLogs EXCEPT ![shard][s] = 
                                       IF Len(entries) > 0 THEN @ \o entries ELSE @]
             /\ Reply([mtype |-> AppendEntriesResponse, shard |-> shard, mterm |-> shardCurrentTerm[shard][s],
                       msuccess |-> TRUE, mmatchIndex |-> m.mprevLogIndex + Len(entries),
                       msource |-> s, mdest |-> m.msource], m)
    /\ UNCHANGED <<shardCurrentTerm, shardVotedFor>>

(* Leader s in shard advances the commit index based on quorum agreement *)
AdvanceCommitIndex(s, shard) ==
    /\ shardState[shard][s] = Leader
    /\ LET agreeIndexes == {index \in 1..Len(shardLogs[shard][s]) : 
                           {s} \cup {k \in Server : shardMatchIndex[shard][s][k] >= index} \in Quorum(shard)}
           newCommit == IF agreeIndexes /= {} 
                           /\ shardLogs[shard][s][CHOOSE x \in agreeIndexes : \A y \in agreeIndexes : y <= x].term 
                              = shardCurrentTerm[shard][s]
                       THEN CHOOSE x \in agreeIndexes : \A y \in agreeIndexes : y <= x
                       ELSE shardCommitIndex[shard][s]
       IN shardCommitIndex' = [shardCommitIndex EXCEPT ![shard][s] = newCommit]
    /\ UNCHANGED <<messages, shardCurrentTerm, shardState, shardVotedFor, shardLogs>>

(* Add AssignServerToShard action to modify shardMap *)
AssignServerToShard(s, shard) ==
    /\ shardMap' = [shardMap EXCEPT ![s] = @ \cup {shard}]
    /\ UNCHANGED <<messages, shardCurrentTerm, shardState, shardVotedFor, shardLogs, shardCommitIndex, 
                    shardNextIndex, shardMatchIndex, shardVotesResponded, shardVotesGranted, elections, allLogs>>

(* ClientRequest action for leaders to append entries *)
ClientRequest(s, shard, v) ==
    /\ shardState[shard][s] = Leader
    /\ shard \in shardMap[s]
    /\ LET entry == [term |-> shardCurrentTerm[shard][s], value |-> v]
           newLog == Append(shardLogs[shard][s], entry)
       IN shardLogs' = [shardLogs EXCEPT ![shard][s] = newLog]
    /\ UNCHANGED <<messages, shardCurrentTerm, shardState, shardVotedFor>>

(* Leader s processes an append entries response from a follower *)
HandleAppendEntriesResponse(s, shard, m) ==
    /\ m.mtype = AppendEntriesResponse
    /\ shardState[shard][s] = Leader
    /\ m.mterm = shardCurrentTerm[shard][s]
    /\ LET follower == m.msource
       IN IF m.msuccess THEN
              /\ shardMatchIndex' = [shardMatchIndex EXCEPT ![shard][s][follower] = m.mmatchIndex]
              /\ shardNextIndex' = [shardNextIndex EXCEPT ![shard][s][follower] = m.mmatchIndex + 1]
          ELSE
              /\ shardNextIndex' = [shardNextIndex EXCEPT ![shard][s][follower] = 
                                      IF shardNextIndex[shard][s][follower] > 1 THEN shardNextIndex[shard][s][follower] - 1 ELSE 1]
              /\ UNCHANGED shardMatchIndex
    /\ Discard(m)
    /\ UNCHANGED <<shardCurrentTerm, shardState, shardVotedFor, shardLogs, shardCommitIndex>>

(* Server s processes an incoming message m for a specific shard *)
Receive(m) ==
    LET s == m.mdest
        shard == m.shard
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

(* The next-state relation covering all possible transitions *)
Next == 
    \/ \E s \in Server, shard \in Shard : Restart(s, shard)
    \/ \E s \in Server, shard \in Shard : Timeout(s, shard)
    \/ \E s, dest \in Server, shard \in Shard : RequestVote(s, shard, dest)
    \/ \E s \in Server, shard \in Shard : BecomeLeader(s, shard)
    \/ \E s, dest \in Server, shard \in Shard : AppendEntries(s, shard, dest)
    \/ \E m \in DOMAIN messages : Receive(m)
    \/ \E s \in Server, shard \in Shard : AdvanceCommitIndex(s, shard)
    \/ \E s \in Server, shard \in Shard, v \in Value : ClientRequest(s, shard, v)
    \/ \E s \in Server, shard \in Shard : AssignServerToShard(s, shard)
    /\ allLogs' = allLogs \cup {shardLogs[shard][s] : s \in Server, shard \in Shard}

(* The complete system specification *)
Spec == Init /\ [][Next]_<<messages, shardCurrentTerm, shardState, shardVotedFor, shardLogs, shardCommitIndex, shardNextIndex, shardMatchIndex, shardVotesResponded, shardVotesGranted, elections, allLogs, shardMap>>

=============================================================================

---- MODULE NetworkModel ----
EXTENDS Naturals, Sequences, TLC

CONSTANT NUM_SERVERS, MAX_PLAYERS, MAX_OBJECTS

(* Define the types for synchronization variables *)
TYPE SandboxSynced = {"SyncedVar", "LocalVar"}

(* Define the state of a network event without payload *)
TYPE NetworkEvent == [ 
    eventType: {"AddPlayer", "DeletePlayer", "CreateObject", "DeleteObject", "AddVote", "MoveChair", "SitOnChair"},
    syncedVars: Seq([variable: String, value: ANY, state: SandboxSynced])
]

(* Define the state of an object, including its aggregation group and synchronized variables *)
TYPE ObjectState == [
    id: Nat,
    aggregate_group: Nat \/ NULL,
    synced_vars: Seq([variable: String, state: SandboxSynced])
]

(* Define the state of a player, including their ID, state, and owned objects *)
TYPE PlayerState == [ 
    id: Nat,
    state: [
        aggregate_group: Nat \/ NULL,
        synced_vars: << 
            [variable |-> "position", state |-> "SyncedVar"],
            [variable |-> "rotation", state |-> "SyncedVar"],
            [variable |-> "velocity", state |-> "SyncedVar"]
        >>
    ],
    objects: Seq(ObjectState)
]

(* Define the state of a server *)
TYPE ServerState == [ 
    id: Nat,
    players: Seq(PlayerState),
    objects: Seq(ObjectState)
]

(* Global state variables *)
VARIABLES 
    servers,         \* Sequence of ServerState *
    event_queue,     \* Sequence of NetworkEvent *
    last_timestamp   \* Sequence of records with player ID and timestamp *

(* Initialization of the system state *)
Init == 
    /\ servers = [i \in 1..NUM_SERVERS |-> [id |-> i, players |-> <<>>, objects |-> <<>>]]
    /\ event_queue = <<>>
    /\ last_timestamp = <<>>

(* Operation to add a new player to a specific server *)
AddPlayer(serverID, pState) ==
    /\ serverID \in 1..NUM_SERVERS
    /\ Len(servers[serverID].players) < MAX_PLAYERS
    /\ servers' = [servers EXCEPT ![serverID].players = @ \o << pState >>]
    /\ event_queue' = Append(event_queue, [eventType |-> "AddPlayer", syncedVars |-> <<>>])
    /\ UNCHANGED <<servers EXCEPT ![serverID].players, last_timestamp>>

(* Operation to remove an existing player from a specific server *)
DeletePlayer(serverID, pid) ==
    /\ serverID \in 1..NUM_SERVERS
    /\ servers'[serverID].players = [ p \in servers[serverID].players : p.id /= pid ]
    /\ event_queue' = Append(event_queue, [eventType |-> "DeletePlayer", syncedVars |-> <<>>])
    /\ UNCHANGED <<servers EXCEPT ![serverID].players, last_timestamp>>

(* Operation to create a new object for a player on a specific server *)
CreateObject(serverID, pid, oid, oState) ==
    /\ serverID \in 1..NUM_SERVERS
    /\ LET player == [p \in servers[serverID].players : p.id = pid]
    /\ Len(player.objects) < MAX_OBJECTS
    /\ servers'[serverID].players = [p \in servers[serverID].players | p.id /= pid 
        \/ [p EXCEPT !.objects = @ \o << [id |-> oid, state |-> oState ] >>]]
    /\ event_queue' = Append(event_queue, [eventType |-> "CreateObject", syncedVars |-> <<>>])
    /\ UNCHANGED <<servers EXCEPT ![serverID].players, last_timestamp>>

(* Operation to delete an existing object from a specific server *)
DeleteObject(serverID, oid) ==
    /\ serverID \in 1..NUM_SERVERS
    /\ servers'[serverID].objects = [ o \in servers[serverID].objects : o.id /= oid ]
    /\ event_queue' = Append(event_queue, [eventType |-> "DeleteObject", syncedVars |-> <<>>])
    /\ UNCHANGED <<servers EXCEPT ![serverID].objects, last_timestamp>>

(* Operation to process a network event without payload *)
ProcessNetworkEvent(event) ==
    CASE event.eventType OF
        "AddPlayer" -> 
            /\ SOME sv \in event.syncedVars: sv.variable = "serverID" /\ sv.variable = "id"
            /\ AddPlayer(sv.value, [ id |-> sv.value,
                                     state |-> [ position |-> [x |-> 0, y |-> 0, z |-> 0],
                                                rotation |-> [x |-> 0, y |-> 0, z |-> 0],
                                                velocity |-> [x |-> 0, y |-> 0, z |-> 0],
                                                aggregate_group |-> NULL,
                                                synced_vars |-> << [variable |-> "position", state |-> "SyncedVar"],
                                                              [variable |-> "rotation", state |-> "SyncedVar"],
                                                              [variable |-> "velocity", state |-> "SyncedVar"] >>
                                     ],
                                     objects |-> <<>> ])
        "DeletePlayer" -> 
            /\ SOME sv \in event.syncedVars: sv.variable = "serverID" /\ sv.variable = "id"
            /\ DeletePlayer(sv.value, sv.value)
        "CreateObject" -> 
            /\ SOME sv1 \in event.syncedVars: sv1.variable = "serverID"
            /\ SOME sv2 \in event.syncedVars: sv2.variable = "playerId"
            /\ SOME sv3 \in event.syncedVars: sv3.variable = "objectId"
            /\ SOME sv4 \in event.syncedVars: sv4.variable = "initialState"
            /\ CreateObject(sv1.value, sv2.value, sv3.value, sv4.value)
        "DeleteObject" -> 
            /\ SOME sv1 \in event.syncedVars: sv1.variable = "serverID"
            /\ SOME sv2 \in event.syncedVars: sv2.variable = "objectId"
            /\ DeleteObject(sv1.value, sv2.value)
        OTHER -> 
            /\ HandleSyncedVars(event.syncedVars)
    END

HandleSyncedVars(syncedVars) ==
    /\ \A sv \in syncedVars: 
        CASE sv.variable OF
            "vote" -> 
                /\ EXISTS o \in servers[sv.value].objects: o.id = sv.value
                /\ servers' = [servers EXCEPT ![sv.value].objects = Append(@, <<sv>>)]
            OTHER -> UNCHANGED
        END

(* Tick operation representing the passage of time with no state changes *)
Tick ==
    /\ UNCHANGED <<servers, event_queue, last_timestamp>>

(* PlusCal Algorithm for state transitions *)
BEGIN
  while TRUE do
    either
      \* Add a new player with default state to a random server *
      AddPlayer(RandomServerID, [ id |-> NewID,
                                   state |-> [ position |-> [x |-> 0, y |-> 0, z |-> 0],
                                              rotation |-> [x |-> 0, y |-> 0, z |-> 0],
                                              velocity |-> [x |-> 0, y |-> 0, z |-> 0],
                                              aggregate_group |-> NULL,
                                              synced_vars |-> << [variable |-> "position", state |-> "SyncedVar"],
                                                            [variable |-> "rotation", state |-> "SyncedVar"],
                                                            [variable |-> "velocity", state |-> "SyncedVar"] >>
                                   ],
                                   objects |-> <<>> ])
    or
      \* Remove an existing player from a random server if any exist *
      IF EXISTS s \in servers: Len(s.players) > 0 THEN
        /\ LET server == CHOOSE s \in servers: Len(s.players) > 0
           /\ pid == FIRST(server.players).id IN DeletePlayer(server.id, pid)
      ELSE
        SKIP
    or
      \* Add a vote to an existing object on a random server if any exist *
      IF EXISTS s \in servers: Len(s.objects) > 0 THEN
        /\ LET server == CHOOSE s \in servers: Len(s.objects) > 0
           /\ oid == FIRST(server.objects).id IN AddVote(server.id, oid)
      ELSE
        SKIP
    or
      \* Create a new object with default state on a random server *
      CreateObject(RandomServerID, NewPID, NewOID, [ position |-> [x |-> 1, y |-> 1, z |-> 1],
                                                    rotation |-> [x |-> 0, y |-> 0, z |-> 0],
                                                    velocity |-> [x |-> 0, y |-> 0, z |-> 0],
                                                    aggregate_group |-> 0,
                                                    synced_vars |-> <<>> ])
    or
      \* Delete an existing object from a random server if any exist *
      IF EXISTS s \in servers: Len(s.objects) > 0 THEN
        /\ LET server == CHOOSE s \in servers: Len(s.objects) > 0
           /\ oid == FIRST(server.objects).id IN DeleteObject(server.id, oid)
      ELSE
        SKIP
    or
      \* Process the next network event if any *
      IF Len(event_queue) > 0 THEN
        /\ LET event == Head(event_queue) IN
            /\ event_queue' = Tail(event_queue)
            /\ ProcessNetworkEvent(event)
      ELSE
        \* Perform a tick to advance time *
        Tick
    end while
END

(* Specification combining initialization and all possible operations *)
Spec ==
    Init /\ [][AddPlayer \/ DeletePlayer \/ CreateObject \/ DeleteObject \/ Tick \/ ChairSpec \/ ProcessNetworkEvent]_<<servers, event_queue, last_timestamp>>

(* Invariant ensuring the number of players does not exceed the maximum allowed on any server *)
PlayersCountInvariant == 
    \A s \in servers : Len(s.players) <= MAX_PLAYERS

(* Invariant ensuring the number of objects does not exceed the maximum allowed on any server *)
ObjectsCountInvariant == 
    \A s \in servers : Len(s.objects) <= MAX_OBJECTS

(* Theorem stating that the specifications maintain the invariants *)
THEOREM Spec => []PlayersCountInvariant /\ []ObjectsCountInvariant

====

---- MODULE NetworkModel ----
EXTENDS Naturals, Sequences, TLC

CONSTANT MAX_PLAYERS, MAX_OBJECTS

(* Define the types for synchronization variables *)
TYPE SandboxSynced = {"SyncedVar", "LocalVar"}

(* Define the state of a network event without payload *)
TYPE NetworkEvent == [ 
    eventType: {"AddPlayer", "DeletePlayer", "CreateObject", "DeleteObject", "AddVote", "MoveChair", "SitOnChair"},
    syncedVars: Seq([variable: String, value: ANY, state: SandboxSynced])
]

(* Define the state of an object, including its aggregation group and synchronized variables *)
TYPE ObjectState == [
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
    objects: Seq([id: Nat, state: ObjectState])
]

(* Global state variables *)
VARIABLES 
    players,         \* Sequence of PlayerState *
    objects,         \* Sequence of ObjectState *
    event_queue,     \* Sequence of NetworkEvent *
    last_timestamp   \* Sequence of records with player ID and timestamp *

(* Initialization of the system state *)
Init == 
    /\ players = <<>>
    /\ objects = <<>>
    /\ event_queue = <<>>
    /\ last_timestamp = <<>>

(* Operation to add a new player *)
AddPlayer(pState) ==
    /\ Len(players) < MAX_PLAYERS
    /\ players' = players \o << pState >>
    /\ event_queue' = Append(event_queue, [eventType |-> "AddPlayer", syncedVars |-> <<>>])
    /\ UNCHANGED <<objects, last_timestamp>>

(* Operation to remove an existing player *)
DeletePlayer(pid) ==
    /\ players' = [ p \in players : p.id /= pid ]
    /\ event_queue' = Append(event_queue, [eventType |-> "DeletePlayer", syncedVars |-> <<>>])
    /\ UNCHANGED <<objects, last_timestamp>>

(* Operation to create a new object for a player *)
CreateObject(pid, oid, oState) ==
    /\ LET player == [p \in players : p.id = pid]
    /\ Len(player.objects) < MAX_OBJECTS
    /\ player.objects' = player.objects \o << [id |-> oid, state |-> oState ] >>
    /\ event_queue' = Append(event_queue, [eventType |-> "CreateObject", syncedVars |-> <<>>])
    /\ UNCHANGED <<players, objects, last_timestamp>>

(* Operation to delete an existing object *)
DeleteObject(oid) ==
    /\ objects' = [ o \in objects : o.id /= oid ]
    /\ event_queue' = Append(event_queue, [eventType |-> "DeleteObject", syncedVars |-> <<>>])
    /\ UNCHANGED <<players, last_timestamp>>

(* Operation to add a vote to an object *)
AddVote(oid) ==
    /\ EXISTS o \in objects: o.id = oid
    /\ objects' = [ 
        o \in objects : 
            IF o.id = oid THEN 
                [ o EXCEPT !.state.synced_vars = Append(Seq([variable |-> "vote", state |-> "SyncedVar"]), {x \in o.state.synced_vars | x.variable /= "vote"}) ]
            ELSE 
                o
    ]
    /\ event_queue' = Append(event_queue, [eventType |-> "AddVote", syncedVars |-> <<>>])
    /\ UNCHANGED <<players, last_timestamp>>

(* Operation to process a network event without payload *)
ProcessNetworkEvent(event) ==
    CASE event.eventType OF
        "AddPlayer" -> 
            /\ SOME sv \in event.syncedVars: sv.variable = "id"
            /\ AddPlayer([ id |-> sv.value,
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
            /\ SOME sv \in event.syncedVars: sv.variable = "id"
            /\ DeletePlayer(sv.value)
        "CreateObject" -> 
            /\ SOME sv1 \in event.syncedVars: sv1.variable = "playerId"
            /\ SOME sv2 \in event.syncedVars: sv2.variable = "objectId"
            /\ SOME sv3 \in event.syncedVars: sv3.variable = "initialState"
            /\ CreateObject(sv1.value, sv2.value, sv3.value)
        "DeleteObject" -> 
            /\ SOME sv \in event.syncedVars: sv.variable = "objectId"
            /\ DeleteObject(sv.value)
        "AddVote" -> 
            /\ SOME sv \in event.syncedVars: sv.variable = "objectId"
            /\ AddVote(sv.value)
        OTHER -> UNCHANGED
    END

(* Tick operation representing the passage of time with no state changes *)
Tick ==
    /\ UNCHANGED <<players, objects, event_queue, last_timestamp>>

(* PlusCal Algorithm for state transitions *)
BEGIN
  while TRUE do
    either
      \* Add a new player with default state *
      AddPlayer([ id |-> NewID,
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
      \* Remove an existing player if any exist *
      IF Len(players) > 0 THEN
        /\ LET pid == FIRST(players).id IN DeletePlayer(pid)
      ELSE
        SKIP
    or
      \* Add a vote to an existing object if any exist *
      IF Len(objects) > 0 THEN
        /\ LET oid == FIRST(objects).id IN AddVote(oid)
      ELSE
        SKIP
    or
      \* Create a new object with default state *
      CreateObject(NewOID,  [ position |-> [x |-> 1, y |-> 1, z |-> 1],
                            rotation |-> [x |-> 0, y |-> 0, z |-> 0],
                            velocity |-> [x |-> 0, y |-> 0, z |-> 0],
                            aggregate_group |-> 0,
                            synced_vars |-> <<>> ])
    or
      \* Delete an existing object if any exist *
      IF Len(objects) > 0 THEN
        /\ LET oid == FIRST(objects).id IN DeleteObject(oid)
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
Spec == Init /\ [][AddPlayer \/ DeletePlayer \/ AddVote \/ CreateObject \/ DeleteObject \/ Tick \/ ChairSpec \/ ProcessNetworkEvent]_<<players, objects, event_queue, last_timestamp>>

(* Invariant ensuring the number of players does not exceed the maximum allowed *)
PlayersCountInvariant == Len(players) <= MAX_PLAYERS

(* Invariant ensuring the number of objects does not exceed the maximum allowed *)
ObjectsCountInvariant == Len(objects) <= MAX_OBJECTS

(* Theorem stating that the specifications maintain the invariants *)
THEOREM Spec => []PlayersCountInvariant /\ []ObjectsCountInvariant

====

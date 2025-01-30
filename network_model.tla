---- MODULE NetworkModel ----
EXTENDS Naturals, Sequences, TLC

CONSTANT MAX_PLAYERS, MAX_OBJECTS

(* Define the types for synchronization variables *)
TYPE SandboxSynced = {"SyncedVar", "LocalVar"}

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

(* Define the global state variables *)
VARIABLES 
    players,         \* Sequence of PlayerState *
    event_queue,     \* Sequence of NetworkEventState *
    last_timestamp   \* Sequence of records with player ID and timestamp *

(* Initialization of the system state *)
Init == 
    /\ players = <<>>
    /\ objects = <<>>
    /\ event_queue = <<>>
    /\ last_timestamp = <<>>

(* Operation to add a new player *)
AddPlayer(pid, pState) ==
    /\ Len(players) < MAX_PLAYERS
    /\ players' = players \o << pState >>
    /\ players'.synced_vars = Append(players.synced_vars, << "AddPlayer", ToString(pid) >>)
    /\ UNCHANGED <<objects, event_queue, last_timestamp>>

(* Operation to remove an existing player *)
DeletePlayer(pid) ==
    /\ players' = [ p \in players : p.id /= pid ]
    /\ players'.synced_vars = Append(players.synced_vars, << "DeletePlayer", ToString(pid) >>)
    /\ UNCHANGED <<objects, event_queue, last_timestamp>>

(* Operation to create a new object for a player *)
CREATE CreateObject(pid, oid, oState) ==
    /\ LET player = [p \in players : p.id = pid]
    /\ Len(player.objects) < MAX_OBJECTS
    /\ player.objects' = player.objects \o << [id |-> oid, state |-> oState ] >>
    /\ player.objects'.synced_vars = Append(player.objects.synced_vars, << "CreateObject", ToString(oid) >>)
    /\ UNCHANGED <<players, event_queue, last_timestamp>>

(* Operation to delete an existing object *)
DeleteObject(oid) ==
    /\ objects' = [ o \in objects : o.id /= oid ]
    /\ objects'.synced_vars = Append(objects.synced_vars, << "DeleteObject", ToString(oid) >>)
    /\ UNCHANGED <<players, event_queue, last_timestamp>>

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
    /\ UNCHANGED <<players, event_queue, last_timestamp>>

(* Tick operation representing the passage of time with no state changes *)
Tick ==
    /\ UNCHANGED <<players, objects, event_queue, last_timestamp>>

(* PlusCal Algorithm for state transitions *)
BEGIN
  while TRUE do
    either
      \* Add a new player with default state *
      AddPlayer(NewID, [ id |-> NewID,
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
      CreateObject(NewOID, [ position |-> [x |-> 1, y |-> 1, z |-> 1],
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
      \* Perform a tick to advance time *
      Tick
  end while
END

(* Specification combining initialization and all possible operations *)
Spec == Init /\ [][AddPlayer \/ DeletePlayer \/ AddVote \/ CreateObject \/ DeleteObject \/ Tick \/ ChairSpec]_<<players, objects, event_queue, last_timestamp>>

(* Invariant ensuring the number of players does not exceed the maximum allowed *)
PlayersCountInvariant == Len(players) <= MAX_PLAYERS

(* Invariant ensuring the number of objects does not exceed the maximum allowed *)
ObjectsCountInvariant == Len(objects) <= MAX_OBJECTS

(* Theorem stating that the specifications maintain the invariants *)
THEOREM Spec => []PlayersCountInvariant /\ []ObjectsCountInvariant

====

(* Define the state of a chair, based on ObjectState *)
TYPE ChairState == ObjectState

(* Operation to add a new chair *)
AddChair(cid, cState) ==
    /\ Len(objects) < MAX_OBJECTS
    /\ objects' = objects \o << [id |-> cid, state |-> cState] >>
    /\ UNCHANGED <<players, event_queue, last_timestamp>>

(* Operation for a player to sit on a chair *)
SitOnChair(pid, cid) ==
    /\ EXISTS p \in players: p.id = pid
    /\ EXISTS c \in objects: c.id = cid /\ c.aggregate_group = NULL
    /\ players' = [ p \in players:
                      IF p.id = pid THEN 
                          [ p EXCEPT !.state.aggregate_group = cid ]
                      ELSE
                          p
                  ]
    /\ objects' = [ c \in objects:
                      IF c.id = cid THEN
                          [ c EXCEPT !.state.aggregate_group = pid ]
                      ELSE
                          c
                  ]
    /\ UNCHANGED <<event_queue, last_timestamp>>

(* Operation to move a chair to a new position *)
MoveChair(cid, newPosition) ==
    /\ EXISTS c \in objects: c.id = cid
    /\ objects' = [ c \in objects:
                      IF c.id = cid THEN
                          [ c EXCEPT !.state.position = newPosition ]
                      ELSE
                          c
                  ]
    /\ UNCHANGED <<players, event_queue, last_timestamp>>

(* Specification for chair-related operations *)
ChairSpec ==
    /\ AddChair \/ SitOnChair \/ MoveChair

(* Updated specification including chair operations *)
Spec == Init /\ [][AddPlayer \/ DeletePlayer \/ AddVote \/ CreateObject \/ DeleteObject \/ Tick \/ ChairSpec]_<<players, objects, event_queue, last_timestamp>>

(* 
    Test suite for NetworkModel.tla
    This module defines tests to exhaustively cover the eight failure modes
    of the request/reply steps in the network model.
*)

(* Constants for testing *)
CONSTANT 
        MAX_PLAYERS <- 5,
        MAX_OBJECTS <- 10

(* Import the NetworkModel module *)
EXTENDS NetworkModel

(* Initialization for tests *)
InitTest == Init

(* Test 1: POST REQUEST fails *)
Test_POST_REQUEST_Fail ==
        /\ AddPlayer(1, [ 
                        id |-> 1,
                        state |-> [ 
                                aggregate_group |-> NULL,
                                synced_vars |-> << 
                                        [variable |-> "position", state |-> "SyncedVar"],
                                        [variable |-> "rotation", state |-> "SyncedVar"],
                                        [variable |-> "velocity", state |-> "SyncedVar"]
                                >>
                        ],
                        objects |-> <<>>
                ])
        /\ FALSE  (* Simulate failure by forcing a state contradiction *)

(* Test 2: DELIVER REQUEST fails *)
Test_DELIVER_REQUEST_Fail ==
        /\ AddPlayer(2, [ 
                        id |-> 2,
                        state |-> [ 
                                aggregate_group |-> NULL,
                                synced_vars |-> << 
                                        [variable |-> "position", state |-> "SyncedVar"],
                                        [variable |-> "rotation", state |-> "SyncedVar"],
                                        [variable |-> "velocity", state |-> "SyncedVar"]
                                >>
                        ],
                        objects |-> <<>>
                ])
        /\ DeletePlayer(2)

(* Test 3: VALIDATE REQUEST fails *)
Test_VALIDATE_REQUEST_Fail ==
        /\ AddPlayer("invalid_id", [ 
                        id |-> "invalid_id",  (* Invalid ID to cause validation failure *)
                        state |-> [ 
                                aggregate_group |-> NULL,
                                synced_vars |-> << 
                                        [variable |-> "position", state |-> "SyncedVar"],
                                        [variable |-> "rotation", state |-> "SyncedVar"],
                                        [variable |-> "velocity", state |-> "SyncedVar"]
                                >>
                        ],
                        objects |-> <<>>
                ])

(* Test 4: UPDATE SERVER STATE fails *)
Test_UPDATE_SERVER_STATE_Fail ==
        /\ AddPlayer(3, [ 
                        id |-> 3,
                        state |-> [ 
                                aggregate_group |-> NULL,
                                synced_vars |-> << 
                                        [variable |-> "position", state |-> "SyncedVar"],
                                        [variable |-> "rotation", state |-> "SyncedVar"],
                                        [variable |-> "velocity", state |-> "SyncedVar"]
                                >>
                        ],
                        objects |-> <<>>
                ])
        /\ players'.state = [INVALID_STATE]  (* Force an invalid state *)

(* Test 5: POST REPLY fails *)
Test_POST_REPLY_Fail ==
        /\ AddVote(1)  (* Assuming player 1 exists *)
        /\ FALSE  (* Simulate failure by forcing a state contradiction *)

(* Test 6: DELIVER REPLY fails *)
Test_DELIVER_REPLY_Fail ==
        /\ AddVote(1)
        /\ DeleteVote(1)  (* Simulate reply failure by removing the vote *)

(* Test 7: VALIDATE REPLY fails *)
Test_VALIDATE_REPLY_Fail ==
        /\ AddVote(1)
        /\ objects[1].synced_vars = << [variable |-> "invalid_reply", state |-> "SyncedVar"] >>

(* Test 8: UPDATE CLIENT STATE fails *)
Test_UPDATE_CLIENT_STATE_Fail ==
        /\ CreateObject(1, 101, [ 
                        position |-> [x |-> 2, y |-> 2, z |-> 2],
                        rotation |-> [x |-> 0, y |-> 0, z |-> 0],
                        velocity |-> [x |-> 0, y |-> 0, z |-> 0],
                        aggregate_group |-> NULL,
                        synced_vars |-> <<>>
                ])
        /\ players[1].state.position = [x |-> "invalid", y |-> "invalid", z |-> "invalid"]

(* Specification including all tests *)
SpecTest ==
        InitTest /\ 
        [](
                Test_POST_REQUEST_Fail \/
                Test_DELIVER_REQUEST_Fail \/
                Test_VALIDATE_REQUEST_Fail \/
                Test_UPDATE_SERVER_STATE_Fail \/
                Test_POST_REPLY_Fail \/
                Test_DELIVER_REPLY_Fail \/
                Test_VALIDATE_REPLY_Fail \/
                Test_UPDATE_CLIENT_STATE_Fail
        )

(* Invariants to ensure system resilience *)
Invariant_AllFailuresHandled ==
        /\ []PlayersCountInvariant
        /\ []ObjectsCountInvariant

(* Theorem to verify that all failure tests maintain invariants *)
THEOREM SpecTest => Invariant_AllFailuresHandled

====

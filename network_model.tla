---- MODULE NetworkModel ----
EXTENDS Naturals, Sequences, TLC

CONSTANT MAX_PLAYERS, MAX_OBJECTS

(* Define SandboxSynced *)
TYPE SandboxSynced = {"SyncedVar", "LocalVar"}

(* Define ObjectState *)
TYPE ObjectState == [
    aggregate_group: Nat \/ NULL,
    synced_vars: Seq([variable: String, state: SandboxSynced])
]

(* Define PlayerState *)
TYPE PlayerState == [ 
    id: Nat,
    state: ObjectState,
    objects: Seq([id: Nat, state: ObjectState])
]
(* Define GlobalState *)
VARIABLES 
    players,         \* Seq of PlayerState *
    event_queue,     \* Seq of NetworkEventState *
    last_timestamp   \* Seq of [id: Nat, timestamp: Int] *

(* Initialization *)
Init == 
    /\ players = <<>>
    /\ objects = <<>>
    /\ event_queue = <<>>
    /\ last_timestamp = <<>>

(* AddPlayer Operation *)
AddPlayer(pid, pState) ==
    /\ Len(players) < MAX_PLAYERS
    /\ players' = players \o << pState >>
    /\ players'.synced_vars = Append(players.synced_vars, << "AddPlayer", ToString(pid) >>)
    /\ UNCHANGED <<objects, event_queue, last_timestamp>>
(* DeletePlayer Operation *)
DeletePlayer(pid) ==
    /\ players' = [ p \in players : p.id /= pid ]
    /\ players'.synced_vars = Append(players.synced_vars, << "DeletePlayer", ToString(pid) >>)
    /\ UNCHANGED <<objects, event_queue, last_timestamp>>
(* CreateObject Operation *)
CREATE CreateObject(pid, oid, oState) ==
    /\ LET player = [p \in players : p.id = pid]
    /\ Len(player.objects) < MAX_OBJECTS
    /\ player.objects' = player.objects \o << [id |-> oid, state |-> oState ] >>
    /\ player.objects'.synced_vars = Append(player.objects.synced_vars, << "CreateObject", ToString(oid) >>)
    /\ UNCHANGED <<players, event_queue, last_timestamp>>
(* DeleteObject Operation *)
DeleteObject(oid) ==
    /\ objects' = [ o \in objects : o.id /= oid ]
    /\ objects'.synced_vars = Append(objects.synced_vars, << "DeleteObject", ToString(oid) >>)
    /\ UNCHANGED <<players, event_queue, last_timestamp>>
(* AddVote Operation *)
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

(* Tick Operation *)
Tick ==
    /\ UNCHANGED <<players, objects, event_queue, last_timestamp>>

(* Updated PlusCal Algorithm *)
BEGIN
  while TRUE do
    either
      \* Add a new player
      AddPlayer(NewID, [ id |-> NewID,
                        state |-> [ position |-> [x |-> 0, y |-> 0, z |-> 0],
                                   velocity |-> [x |-> 0, y |-> 0, z |-> 0],
                                   aggregate_group |-> NULL,
                                   synced_vars |-> <<>> ] ])
    or
      \* Delete an existing player
      IF Len(players) > 0 THEN
        /\ LET pid == FIRST(players).id IN DeletePlayer(pid)
      ELSE
        SKIP
    or
      \* Add a vote to an object
      IF Len(objects) > 0 THEN
        /\ LET oid == FIRST(objects).id IN AddVote(oid)
      ELSE
        SKIP
    or
      \* Create a new object
      CreateObject(NewOID, [ position |-> [x |-> 1, y |-> 1, z |-> 1],
                            velocity |-> [x |-> 1, y |-> 1, z |-> 1],
                            aggregate_group |-> 0,
                            synced_vars |-> <<>> ])
    or
      \* Delete an existing object
      IF Len(objects) > 0 THEN
        /\ LET oid == FIRST(objects).id IN DeleteObject(oid)
      ELSE
        SKIP
    or
      \* Perform a tick
      Tick
  end while
END

(* Specifications *)
Spec == Init /\ [][AddPlayer \/ DeletePlayer \/ AddVote \/ CreateObject \/ DeleteObject \/ Tick]_<<players, objects, event_queue, last_timestamp>>

(* Invariant: Players count does not exceed MAX_PLAYERS *)
PlayersCountInvariant == Len(players) <= MAX_PLAYERS

(* Invariant: Objects count does not exceed MAX_OBJECTS *)
ObjectsCountInvariant == Len(objects) <= MAX_OBJECTS

(* Properties to Check *)
THEOREM Spec => []PlayersCountInvariant /\ []ObjectsCountInvariant

====
(* Define ChairState *)
TYPE ChairState == ObjectState

(* AddChair Operation *)
AddChair(cid, cState) ==
    /\ Len(objects) < MAX_OBJECTS
    /\ objects' = objects \o << [id |-> cid, state |-> cState] >>
    /\ UNCHANGED <<players, event_queue, last_timestamp>>

(* SitOnChair Operation *)
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
                          [ c EXCEPT !.aggregate_group = pid ]
                      ELSE
                          c
                  ]
    /\ UNCHANGED <<event_queue, last_timestamp>>

(* MoveChair Operation *)
MoveChair(cid, newPosition) ==
    /\ EXISTS c \in objects: c.id = cid
    /\ objects' = [ c \in objects:
                      IF c.id = cid THEN
                          [ c EXCEPT !.state.position = newPosition ]
                      ELSE
                          c
                  ]
    /\ UNCHANGED <<players, event_queue, last_timestamp>>

(* Chair Specifications *)
ChairSpec ==
    /\ AddChair \/ SitOnChair \/ MoveChair

(* Update Spec *)
Spec == Init /\ [][AddPlayer \/ DeletePlayer \/ AddVote \/ CreateObject \/ DeleteObject \/ Tick \/ ChairSpec]_<<players, objects, event_queue, last_timestamp>>
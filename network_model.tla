---- MODULE NetworkModel ----
EXTENDS Naturals, Sequences, TLC

CONSTANT MAX_PLAYERS

(* Define SandboxSynced *)
TYPE SandboxSynced = {"SyncedVar", "LocalVar"}

(* Define PlayerState *)
TYPE PlayerState == [ 
    position: [x: Real, y: Real, z: Real],
    velocity: [x: Real, y: Real, z: Real],
    aggregate_group: Nat \/ NULL,
    synced_vars: Seq([variable: String, state: SandboxSynced])
]

(* Define GlobalState *)
VARIABLES 
    players,         \* Seq of [id: Nat, state: PlayerState] *
    event_queue,     \* Seq of NetworkEventState *
    last_timestamp   \* Seq of [id: Nat, timestamp: Int] *

(* Initialization *)
Init == 
    /\ players = <<>>
    /\ event_queue = <<>>
    /\ last_timestamp = <<>>

(* AddPlayer Operation *)
AddPlayer(pid, pState) ==
    /\ Len(players) < MAX_PLAYERS
    /\ players' = players \o << [id |-> pid, state |-> pState] >>
    /\ UNCHANGED <<event_queue, last_timestamp>>

(* DeletePlayer Operation *)
DeletePlayer(pid) ==
    /\ players' = [ p \in players : p.id /= pid ]
    /\ UNCHANGED <<event_queue, last_timestamp>>

(* AddVote Operation *)
AddVote(pid) ==
    /\ EXISTS p \in players: p.id = pid
    /\ players' = [ 
        p \in players : 
            IF p.id = pid THEN 
                [ p EXCEPT !.state.synced_vars = Append(Seq(<< "vote", "SyncedVar" >>), {x \in p.state.synced_vars | x.variable /= "vote"}) ]
            ELSE 
                p
    ]
    /\ UNCHANGED <<event_queue, last_timestamp>>

(* Tick Operation *)
Tick ==
    /\ UNCHANGED <<players, event_queue, last_timestamp>>

(* PlusCal Algorithm *)
(* The algorithm defines the possible actions in the system *)
BEGIN
  while TRUE do
    either
      \* Add a new player
      AddPlayer(NewID, [ position |-> [x |-> 0, y |-> 0, z |-> 0],
                        velocity |-> [x |-> 0, y |-> 0, z |-> 0],
                        aggregate_group |-> NULL,
                        synced_vars |-> <<>> ])
    or
      \* Delete an existing player
      IF Len(players) > 0 THEN
        /\ LET pid == FIRST(players).id IN DeletePlayer(pid)
      ELSE
        SKIP
    or
      \* Add a vote to a player
      IF Len(players) > 0 THEN
        /\ LET pid == FIRST(players).id IN AddVote(pid)
      ELSE
        SKIP
    or
      \* Perform a tick
      Tick
  end while
END
----

(* Specifications *)
Spec == Init /\ [][AddPlayer \/ DeletePlayer \/ AddVote \/ Tick]_<<players, event_queue, last_timestamp>>

(* Invariant: Players count does not exceed MAX_PLAYERS *)
PlayersCountInvariant == Len(players) <= MAX_PLAYERS

=============================================================================

(* Properties to Check *)
THEOREM Spec => []PlayersCountInvariant

=============================================================================
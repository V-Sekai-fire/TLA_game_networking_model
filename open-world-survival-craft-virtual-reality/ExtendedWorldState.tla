---- MODULE ExtendedWorldState ----
(*
SPDX-License-Identifier: MIT
Copyright (c) 2025-present K. S. Ernest (iFire) Lee
*)

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
    NumPlayers,         (* Number of players in the simulation *)
    MaxEntities,        (* Maximum possible entities in the world *)
    EntityTypes,        (* e.g., {"player_avatar", "tree", "rock", "item_wood", "structure_wall"} *)
    InitialEntityStates (* A function mapping initial entity IDs (from 1..MaxEntities) to their states,
                           e.g., [1 |-> [type |-> "player_avatar", hp |-> 100, ...], 2 |-> [type |-> "tree", hp |-> 50, ...]]
                           Only entities in DOMAIN InitialEntityStates exist initially. *)

VARIABLES
    players,            (* The set of players *)
    playerInputs,       (* [player |-> Sequence of inputs submitted by the player for the *next* server frame] *)
    serverFrames,       (* Log of processed frames: << [frameNo |-> N, inputsProcessed |-> {...}, worldDeltaApplied |-> TRUE] >> *)
    frameNumber,        (* Current server frame number that has been processed and committed *)
    serverState,        (* FSM state of the server *)

    (* World State Variables *)
    worldEntities,      (* Set of IDs of all currently active entities in the game world *)
    entityState,        (* [entity_id |-> record of its state, e.g., [type |-> "tree", hp |-> 100, position |-> <<x,y>>, inventory |-> <<>>]] *)

    (* For counting transactions *)
    transactionCounter

(* --- Definitions --- *)
Player == 1..NumPlayers
EntityID == 1..MaxEntities
FrameNo == Nat (* Using FrameNo to avoid confusion with the record field "frame" *)

(* Example Input Structure (can be made more complex based on game actions) *)
InputType == {"move", "harvest", "build", "interact", "idle"}
PlayerInputRecord == [type: InputType, targetEntityID: UNION {EntityID, {"none"}}, details: ANY]

(* Example Entity State Structure (can be made more complex) *)
EntityStateRecord == [type: EntityTypes, hp: Int, position: Int \X Int, inventory: Seq(ANY)] (* inventory could be Seq of item IDs or records *)

Vars == <<players, playerInputs, serverFrames, frameNumber, serverState, worldEntities, entityState, transactionCounter>>

(* Helper: A default entity state for newly created entities - simplified *)
DefaultEntityState(eType, ePos) ==
    [type |-> eType, hp |-> 100, position |-> ePos, inventory |-> <<>>]

(* --- Initial State --- *)
Init ==
    /\ players = Player
    /\ playerInputs = [p \in Player |-> <<>>] (* Each player starts with an empty sequence of pending inputs *)
    /\ serverFrames = <<>>
    /\ frameNumber = 0
    /\ serverState = "waiting_for_inputs"
    /\ worldEntities = DOMAIN InitialEntityStates
    /\ entityState = InitialEntityStates
    /\ transactionCounter = 0

(* --- Type Invariants --- *)
TypeInvariant ==
    /\ players = Player
    /\ frameNumber \in Nat
    /\ serverState \in {"waiting_for_inputs", "processing_inputs", "broadcasting_frame_info"}
    /\ worldEntities \subseteq EntityID
    /\ \A eid \in worldEntities : DOMAIN entityState[eid] = {"type", "hp", "position", "inventory"} \* Adjust as per EntityStateRecord
    /\ \A eid \in worldEntities : entityState[eid].type \in EntityTypes
    /\ \A eid \in worldEntities : entityState[eid].hp \in Int
    /\ \A eid \in worldEntities : entityState[eid].position \in (Int \X Int)
    /\ \A eid \in worldEntities : IsSequence(entityState[eid].inventory)
    /\ transactionCounter \in Nat
    /\ \A p \in Player:
        /\ IsSequence(playerInputs[p])
        /\ \A rec \in playerInputs[p] :
               DOMAIN rec = {"type", "targetEntityID", "details"}
               /\ rec.type \in InputType
               /\ rec.targetEntityID \in EntityID \cup {"none"}

(* --- Actions --- *)

(* A player sends an input for the server to process in the upcoming frame. *)
(* Each such received input is considered a transaction for durable logging. *)
SendInput(p, inputRec) ==
    /\ serverState = "waiting_for_inputs"
    /\ inputRec.type \in InputType /\ inputRec.targetEntityID \in EntityID \cup {"none"} (* Basic input validation *)
    /\ playerInputs' = [playerInputs EXCEPT ![p] = Append(@, inputRec)]
    /\ transactionCounter' = transactionCounter + 1 (* T1: Input Reception Transaction *)
    /\ UNCHANGED <<players, serverFrames, frameNumber, serverState, worldEntities, entityState>>

(* Server decides to start processing inputs for the next frame. *)
(* This condition signifies that the server is ready to process a batch.
   For this model, we assume it happens when all players have sent at least one input.
   In reality, it could be time-based or based on other heuristics. *)
StartProcessingInputs ==
    /\ serverState = "waiting_for_inputs"
    /\ \A p \in Player : Len(playerInputs[p]) > 0 (* Each player has at least one pending input *)
    /\ serverState' = "processing_inputs"
    /\ UNCHANGED <<players, playerInputs, serverFrames, frameNumber, worldEntities, entityState, transactionCounter>>

(* Server processes all collected inputs, updates world state, logs the frame, and advances frame number. *)
(* This entire operation is considered one large atomic transaction (T2). *)
ProcessInputsAndUpdateWorld ==
    /\ serverState = "processing_inputs"

    (* --- Abstracted World State Update Logic --- *)
    (* This LET block defines how the world state changes.
       'ApplyInputsToWorld' is an abstract function representing the game's core logic.
       It takes the current world state and all player inputs for this frame,
       and non-deterministically CHOOSEs a new valid world state.
       This abstraction allows us to acknowledge complex changes without specifying every rule.
    *)
    /\ LET
           CurrentInputsToProcess == [p \in Player |-> playerInputs[p]]

           ApplyInputsToWorld(currentWRDEntities, currentENTState, inputsForAllPlayers) ==
               CHOOSE newWorldEntities, newEntityState :
                   (***
                       BEGIN COMPLEX GAME LOGIC ABSTRACTION
                       In a real game, this section would iterate through inputsForAllPlayers:
                       - For each input:
                           - Validate the input against currentWRDEntities and currentENTState.
                           - If valid, calculate changes (e.g., modify an entity's HP, change position, add/remove from inventory).
                           - Potentially create new entities (e.g., building, spawning item) and add to newWorldEntities.
                           - Potentially remove entities (e.g., depleted resource, picked-up item) from newWorldEntities.
                       - Handle interactions and conflicts between player actions.
                       - Ensure newWorldEntities and newEntityState satisfy all game invariants.
                       For this TLA+ model, we simply assert that a valid new state is chosen.
                       This could involve:
                        - Modifying existing entities in currentENTState.
                        - Adding new entities to newWorldEntities and defining their state in newEntityState.
                        - Removing entities from newWorldEntities.
                   ***)
                   /\ \/ /\ newWorldEntities = currentWRDEntities \* Option 1: No change (e.g., all inputs were "idle")
                        /\ newEntityState = currentENTState
                     \/ /\ newWorldEntities \subseteq EntityID    \* Option 2: Some changes occurred
                        /\ \A eid \in newWorldEntities : DOMAIN newEntityState[eid] = DOMAIN Labrat(EntityStateRecord)
                           (* Add more constraints here to ensure the new state is valid if needed for specific properties *)

           NewWorldStateTuple == ApplyInputsToWorld(worldEntities, entityState, CurrentInputsToProcess)
           NewWorldEntitiesAfterProcessing == NewWorldStateTuple[1]
           NewEntityStateAfterProcessing   == NewWorldStateTuple[2]
       IN
           /\ worldEntities' = NewWorldEntitiesAfterProcessing
           /\ entityState' = NewEntityStateAfterProcessing
    (* --- End of Abstracted World State Update Logic --- *)

    /\ serverFrames' = Append(serverFrames, [
                              frameNo           |-> frameNumber + 1,
                              inputsProcessed   |-> CurrentInputsToProcess, (* Log the inputs that were processed *)
                              worldDeltaApplied |-> TRUE                   (* Abstractly indicates world state was updated *)
                         ])
    /\ frameNumber' = frameNumber + 1
    /\ playerInputs' = [p \in Player |-> <<>>] (* Clear the processed inputs for each player *)
    /\ serverState' = "broadcasting_frame_info"
    /\ transactionCounter' = transactionCounter + 1 (* T2: Frame Processing, World State Commit, Logging Transaction *)
    /\ UNCHANGED <<players>>

(* Server finishes the frame cycle, perhaps by broadcasting necessary info (not detailed here) and prepares for new inputs. *)
FinishFrameCycle ==
    /\ serverState = "broadcasting_frame_info"
    /\ serverState' = "waiting_for_inputs"
    /\ UNCHANGED <<players, playerInputs, serverFrames, frameNumber, worldEntities, entityState, transactionCounter>>

(* --- Next State Relation --- *)
Next ==
    \/ (\E p \in Player, inputRec \in {PlayerInputRecord} : SendInput(p, inputRec)) \* A player sends an input
    \/ StartProcessingInputs
    \/ ProcessInputsAndUpdateWorld
    \/ FinishFrameCycle

(* --- Specification --- *)
Spec ==
    Init /\ [][Next]_Vars

(* --- Helper for TLA+ Toolbox (Optional) --- *)
(* Example of a simple entity state for initialization *)
DefaultPlayerAvatarState(pos) == [type |-> "player_avatar", hp |-> 100, position |-> pos, inventory |-> <<>>]
DefaultTreeState(pos) == [type |-> "tree", hp |-> 50, position |-> pos, inventory |-> <<>>]

(*
Example for CONSTANTS in .cfg file:
CONSTANT NumPlayers = 2
CONSTANT MaxEntities = 10
CONSTANT EntityTypes = {"player_avatar", "tree", "rock"}
CONSTANT InitialEntityStates = (
    1 :> [type |-> "player_avatar", hp |-> 100, position |-> <<0,0>>, inventory |-> <<>>] @@
    2 :> [type |-> "player_avatar", hp |-> 100, position |-> <<1,1>>, inventory |-> <<>>] @@
    3 :> [type |-> "tree", hp |-> 50, position |-> <<5,5>>, inventory |-> <<>>]
)
*)

====

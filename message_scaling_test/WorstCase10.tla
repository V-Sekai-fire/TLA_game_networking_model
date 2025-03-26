---- MODULE WorstCase10 ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS
    NumPlayers

VARIABLES 
    players, 
    playerInputs,
    serverFrames,
    frameNumber,
    serverState

Player == 1..NumPlayers
Frame  == Nat

Vars == <<players, playerInputs, serverFrames, frameNumber, serverState>>

Init ==
    /\ players = Player
    /\ playerInputs = [p \in Player |-> {}]
    /\ serverFrames = <<>>
    /\ frameNumber = 0
    /\ serverState = "waiting"

TypeInvariant ==
    /\ players = Player
    /\ frameNumber \in Nat
    /\ serverState \in {"waiting", "processing", "broadcasting"}

SendInput(p) ==
    /\ serverState = "waiting"
    /\ ~([frame |-> frameNumber + 1, input |-> "input"] \in playerInputs[p])
    /\ playerInputs' = [playerInputs EXCEPT ![p] = @ \cup {[frame |-> frameNumber + 1, input |-> "input"]}]
    /\ UNCHANGED <<players, serverFrames, frameNumber, serverState>>

StartProcessing ==
    /\ serverState = "waiting"
    /\ \A p \in Player : [frame |-> frameNumber + 1, input |-> "input"] \in playerInputs[p]
    /\ serverState' = "processing"
    /\ UNCHANGED <<players, playerInputs, serverFrames, frameNumber>>

CreateFrame ==
    /\ serverState = "processing"
    /\ serverFrames' = Append(serverFrames, <<[
         frame |-> frameNumber + 1,
         inputs |-> { [p |-> p, input |-> "input"] : p \in Player }
       ]>>)
    /\ frameNumber' = frameNumber + 1
    /\ playerInputs' = [p \in Player |-> {}]  \* Reset inputs for next frame
    /\ serverState' = "broadcasting"
    /\ UNCHANGED players

BroadcastFrame ==
    /\ serverState = "broadcasting"
    /\ serverState' = "waiting"
    /\ UNCHANGED <<players, playerInputs, serverFrames, frameNumber>>

Next ==
    \/ \E p \in Player : SendInput(p)
    \/ StartProcessing
    \/ CreateFrame
    \/ BroadcastFrame

Spec ==
    Init 
    /\ [][Next]_Vars
    /\ \A p \in Player: SF_Vars(SendInput(p))
    /\ SF_Vars(StartProcessing)
    /\ SF_Vars(CreateFrame)
    /\ SF_Vars(BroadcastFrame)

==== 

---- MODULE QueueLoad ----

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    MaxEntitiesPerCell,       (*  Max entities a cell can hold before considering overload *)
    MinEntitiesForMerge,      (*  Minimum entities threshold for merge consideration *)
    MaxQueueLengthPerCell,    (*  Max request queue length before considering overload *)
    MinQueueLengthForMerge,   (*  Minimum queue length threshold for merge consideration *)
    
    TaskImpact_Common,        (*  Load impact of a common task. *)
    TaskImpact_Rare,          (*  Load impact of a rare, high-impact task. *)
    TaskImpact_Movement,      (*  Player/avatar movement updates *)
    TaskImpact_Interaction,   (*  Object interaction events *)
    TaskImpact_WorldLoad,     (*  Loading world assets/geometry *)
    TaskImpact_NetworkSync,   (*  Network state synchronization *)
    TaskImpact_Physics,       (*  Physics simulation updates *)
    CellProcessingCapacity,   (*  Max total task impact processed by a cell in one ProcessCellWork step. *)
    BaselineEntities,         (*  Initial entity count for the root cell. *)
    
    (* WebRTC Channel Configuration - 4 channels for 4 delivery modes *)
    MaxChannelQueueLength     (*  Max queue length per channel before dropping packets *)

ASSUME A_QueueConstantsPositive ==
    /\ TaskImpact_Common \in Nat \ {0}
    /\ TaskImpact_Rare \in Nat \ {0}
    /\ TaskImpact_Movement \in Nat \ {0}
    /\ TaskImpact_Interaction \in Nat \ {0}
    /\ TaskImpact_WorldLoad \in Nat \ {0}
    /\ TaskImpact_NetworkSync \in Nat \ {0}
    /\ TaskImpact_Physics \in Nat \ {0}
    /\ CellProcessingCapacity \in Nat \ {0}
ASSUME A_EntityConstantsPositive ==
    /\ MaxEntitiesPerCell \in Nat \ {0}
    /\ MinEntitiesForMerge \in Nat
    /\ BaselineEntities \in Nat
ASSUME A_QueueLengthConstantsPositive ==
    /\ MaxQueueLengthPerCell \in Nat \ {0}
    /\ MinQueueLengthForMerge \in Nat
ASSUME A_WebRTCChannelConstraints ==
    /\ MaxChannelQueueLength \in Nat \ {0}
ASSUME A_ImpactHierarchy ==
    TaskImpact_Rare >= TaskImpact_Common
ASSUME A_MaxEntitiesSensible ==
    MaxEntitiesPerCell >= BaselineEntities
ASSUME A_MaxQueueSensible ==
    MaxQueueLengthPerCell > 0

VARIABLES 
    cell_data,                          (*  Record for the single cell: [numEntities: Nat, requestQueue: Seq(Nat)] *)
    overload_state,                     (*  Track if cell is overloaded: BOOLEAN *)
    merge_eligible,                     (*  Track if cell is eligible for merge: BOOLEAN *)
    channel_reliable_sequenced,         (*  Channel 1: Reliable + Sequenced - Critical interactions *)
    channel_reliable_unsequenced,       (*  Channel 2: Reliable + Unsequenced - Important data *)
    channel_unreliable_sequenced,       (*  Channel 3: Unreliable + Sequenced - Real-time updates *)
    channel_unreliable_unsequenced      (*  Channel 4: Unreliable + Unsequenced - Fire-and-forget *)

vars == <<cell_data, overload_state, merge_eligible, 
          channel_reliable_sequenced, channel_reliable_unsequenced,
          channel_unreliable_sequenced, channel_unreliable_unsequenced>>

(*  ----------------------------- TYPE DEFINITIONS AND HELPERS ----------------------------- *)
CellType == [numEntities : Nat,
             requestQueue : Seq(Nat) ] (*  Nat here is TaskImpact *)

(* WebRTC Channel Type - queue contains packet sizes, dropped counts failed transmissions *)
ChannelType == [queue : Seq(Nat), 
                dropped : Nat]

(* WebRTC Delivery Mode Enumeration *)
DeliveryMode == "ReliableSequenced" \cup "ReliableUnsequenced" \cup "UnreliableSequenced" \cup "UnreliableUnsequenced"

(* Task Type to Delivery Mode Mapping *)
GetTaskDeliveryMode(task_type) ==
    CASE task_type \in {"interaction", "rare"} -> "ReliableSequenced"        (* Critical: Must arrive in order *)
      [] task_type \in {"worldload", "networksync"} -> "ReliableUnsequenced" (* Important: Must arrive, order flexible *)
      [] task_type \in {"movement", "physics"} -> "UnreliableSequenced"      (* Real-time: Latest matters, order important *)
      [] task_type \in {"common", "heartbeat"} -> "UnreliableUnsequenced"    (* Fire-and-forget: No guarantees *)
      [] OTHER -> "UnreliableUnsequenced"

(* Channel Assignment by Delivery Mode *)
GetChannelForMode(delivery_mode) ==
    CASE delivery_mode = "ReliableSequenced" -> 1
      [] delivery_mode = "ReliableUnsequenced" -> 2  
      [] delivery_mode = "UnreliableSequenced" -> 3
      [] delivery_mode = "UnreliableUnsequenced" -> 4
      [] OTHER -> 4

TypeOK ==
    /\ cell_data \in CellType
    /\ cell_data.numEntities >= 0
    /\ \A i \in 1..Len(cell_data.requestQueue) : cell_data.requestQueue[i] \in Nat \ {0}
    /\ overload_state \in BOOLEAN
    /\ merge_eligible \in BOOLEAN
    /\ channel_reliable_sequenced \in ChannelType
    /\ channel_reliable_unsequenced \in ChannelType
    /\ channel_unreliable_sequenced \in ChannelType
    /\ channel_unreliable_unsequenced \in ChannelType

(* Helper functions for load management *)
IsOverloaded(cell) ==
    cell.numEntities > MaxEntitiesPerCell \/ Len(cell.requestQueue) > MaxQueueLengthPerCell

IsMergeEligible(cell) ==
    cell.numEntities < MinEntitiesForMerge /\ Len(cell.requestQueue) < MinQueueLengthForMerge

(* WebRTC Channel Helpers for 4 separate channels *)
CanEnqueueToReliableSequenced == 
    Len(channel_reliable_sequenced.queue) < MaxChannelQueueLength

CanEnqueueToReliableUnsequenced == 
    Len(channel_reliable_unsequenced.queue) < MaxChannelQueueLength

CanEnqueueToUnreliableSequenced == 
    Len(channel_unreliable_sequenced.queue) < MaxChannelQueueLength

CanEnqueueToUnreliableUnsequenced == 
    Len(channel_unreliable_unsequenced.queue) < MaxChannelQueueLength

(* Task Type to Channel Mapping - each task type assigned to appropriate delivery mode *)
GetChannelForTaskType(task_type) ==
    CASE task_type = "interaction" -> "ReliableSequenced"      (* Critical UI interactions *)
      [] task_type = "rare" -> "ReliableSequenced"             (* Critical rare events *)
      [] task_type = "worldload" -> "ReliableUnsequenced"      (* Asset loading, order flexible *)
      [] task_type = "networksync" -> "ReliableUnsequenced"    (* State sync, order flexible *)
      [] task_type = "movement" -> "UnreliableSequenced"       (* Avatar position, latest matters *)
      [] task_type = "physics" -> "UnreliableSequenced"        (* Physics state, latest matters *)
      [] task_type = "common" -> "UnreliableUnsequenced"       (* Background tasks *)
      [] OTHER -> "UnreliableUnsequenced"

(* Invariant to test queue capacity limits - model checking will fail when queue gets too long *)
QueueCapacityInvariant ==
    Len(cell_data.requestQueue) <= 2  (* 7ms photon-to-photon VR constraint: max 1-2ms server processing *)

(* Invariant to test entity growth limits *)
EntityCapacityInvariant ==
    cell_data.numEntities <= 100  (* Adjust this limit to test different thresholds *)

(* Overload management invariant - ensures system responds to overload conditions *)
OverloadManagementInvariant ==
    overload_state = IsOverloaded(cell_data)

(* Merge eligibility invariant - tracks when cell could be merged (in multi-cell context) *)
MergeEligibilityInvariant ==
    merge_eligible = IsMergeEligible(cell_data)

(*  ------------------------------------ INITIALIZATION ------------------------------------ *)
Init ==
    /\ cell_data = [ numEntities  |-> BaselineEntities,
                    requestQueue |-> << >> ]
    /\ overload_state = IsOverloaded(cell_data)
    /\ merge_eligible = IsMergeEligible(cell_data)
    /\ channel_reliable_sequenced = [ queue |-> << >>, dropped |-> 0 ]
    /\ channel_reliable_unsequenced = [ queue |-> << >>, dropped |-> 0 ]
    /\ channel_unreliable_sequenced = [ queue |-> << >>, dropped |-> 0 ]
    /\ channel_unreliable_unsequenced = [ queue |-> << >>, dropped |-> 0 ]

(*  --------------------------------------- ACTIONS ---------------------------------------- *)

(*  --- Actions to simulate task generation and enqueueing --- *)
EnqueueTask(task_impact) ==
    /\ task_impact \in Nat \ {0}
    /\ cell_data' = [cell_data EXCEPT !.requestQueue = Append(cell_data.requestQueue, task_impact)]
    /\ overload_state' = IsOverloaded(cell_data')
    /\ merge_eligible' = IsMergeEligible(cell_data')
    /\ UNCHANGED <<channel_reliable_sequenced, channel_reliable_unsequenced, 
                   channel_unreliable_sequenced, channel_unreliable_unsequenced>>

AddEntitiesToCell(entity_increment) ==
    /\ entity_increment \in Nat \ {0}
    /\ cell_data' = [cell_data EXCEPT !.numEntities = cell_data.numEntities + entity_increment]
    /\ overload_state' = IsOverloaded(cell_data')
    /\ merge_eligible' = IsMergeEligible(cell_data')
    /\ UNCHANGED <<channel_reliable_sequenced, channel_reliable_unsequenced, 
                   channel_unreliable_sequenced, channel_unreliable_unsequenced>>

GenerateCommonTaskActivity ==
    EnqueueTask(TaskImpact_Common)

GenerateRareTaskActivity ==
    EnqueueTask(TaskImpact_Rare)

GenerateMovementActivity ==
    EnqueueTask(TaskImpact_Movement)

GenerateInteractionActivity ==
    EnqueueTask(TaskImpact_Interaction)

GenerateWorldLoadActivity ==
    EnqueueTask(TaskImpact_WorldLoad)

GenerateNetworkSyncActivity ==
    EnqueueTask(TaskImpact_NetworkSync)

GeneratePhysicsActivity ==
    EnqueueTask(TaskImpact_Physics)

GenerateEntityArrival == (*  Action to increase numEntities linearly *)
    AddEntitiesToCell(5)  (*  Add 5 entities per arrival event for linear growth *)

(*  --- Action to simulate cell processing its queue --- *)
ProcessCellWork ==
    /\ Len(cell_data.requestQueue) > 0
    /\ LET first_task == Head(cell_data.requestQueue)
       IN /\ first_task <= CellProcessingCapacity
          /\ cell_data' = [cell_data EXCEPT !.requestQueue = Tail(cell_data.requestQueue)]
          /\ overload_state' = IsOverloaded(cell_data')
          /\ merge_eligible' = IsMergeEligible(cell_data')
          /\ UNCHANGED <<channel_reliable_sequenced, channel_reliable_unsequenced, 
                         channel_unreliable_sequenced, channel_unreliable_unsequenced>>

(*  --- WebRTC Channel Actions for each of the 4 permutations --- *)

(* Channel 1: Reliable + Sequenced - Critical interactions, rare events *)
SendToReliableSequenced(packet_size) ==
    /\ packet_size \in Nat \ {0}
    /\ IF CanEnqueueToReliableSequenced THEN
        \* Queue has space - enqueue packet
        /\ channel_reliable_sequenced' = [channel_reliable_sequenced EXCEPT 
                                         !.queue = Append(channel_reliable_sequenced.queue, packet_size)]
        /\ UNCHANGED <<cell_data, overload_state, merge_eligible, 
                      channel_reliable_unsequenced, channel_unreliable_sequenced, channel_unreliable_unsequenced>>
       ELSE
        \* Reliable channel blocks when full - action disabled
        FALSE

(* Channel 2: Reliable + Unsequenced - World loading, network sync *)
SendToReliableUnsequenced(packet_size) ==
    /\ packet_size \in Nat \ {0}
    /\ IF CanEnqueueToReliableUnsequenced THEN
        \* Queue has space - enqueue packet
        /\ channel_reliable_unsequenced' = [channel_reliable_unsequenced EXCEPT 
                                           !.queue = Append(channel_reliable_unsequenced.queue, packet_size)]
        /\ UNCHANGED <<cell_data, overload_state, merge_eligible, 
                      channel_reliable_sequenced, channel_unreliable_sequenced, channel_unreliable_unsequenced>>
       ELSE
        \* Reliable channel blocks when full - action disabled
        FALSE

(* Channel 3: Unreliable + Sequenced - Movement, physics *)
SendToUnreliableSequenced(packet_size) ==
    /\ packet_size \in Nat \ {0}
    /\ IF CanEnqueueToUnreliableSequenced THEN
        \* Queue has space - enqueue packet
        /\ channel_unreliable_sequenced' = [channel_unreliable_sequenced EXCEPT 
                                           !.queue = Append(channel_unreliable_sequenced.queue, packet_size)]
        /\ UNCHANGED <<cell_data, overload_state, merge_eligible, 
                      channel_reliable_sequenced, channel_reliable_unsequenced, channel_unreliable_unsequenced>>
       ELSE
        \* Unreliable channel drops when full - non-blocking
        /\ channel_unreliable_sequenced' = [channel_unreliable_sequenced EXCEPT 
                                           !.dropped = channel_unreliable_sequenced.dropped + 1]
        /\ UNCHANGED <<cell_data, overload_state, merge_eligible, 
                      channel_reliable_sequenced, channel_reliable_unsequenced, channel_unreliable_unsequenced>>

(* Channel 4: Unreliable + Unsequenced - Common tasks, heartbeats *)
SendToUnreliableUnsequenced(packet_size) ==
    /\ packet_size \in Nat \ {0}
    /\ IF CanEnqueueToUnreliableUnsequenced THEN
        \* Queue has space - enqueue packet
        /\ channel_unreliable_unsequenced' = [channel_unreliable_unsequenced EXCEPT 
                                             !.queue = Append(channel_unreliable_unsequenced.queue, packet_size)]
        /\ UNCHANGED <<cell_data, overload_state, merge_eligible, 
                      channel_reliable_sequenced, channel_reliable_unsequenced, channel_unreliable_sequenced>>
       ELSE
        \* Unreliable channel drops when full - non-blocking
        /\ channel_unreliable_unsequenced' = [channel_unreliable_unsequenced EXCEPT 
                                             !.dropped = channel_unreliable_unsequenced.dropped + 1]
        /\ UNCHANGED <<cell_data, overload_state, merge_eligible, 
                      channel_reliable_sequenced, channel_reliable_unsequenced, channel_unreliable_sequenced>>

(* Process each channel's queue - transmit buffered packets *)
ProcessReliableSequencedQueue ==
    /\ Len(channel_reliable_sequenced.queue) > 0
    /\ channel_reliable_sequenced' = [channel_reliable_sequenced EXCEPT 
                                     !.queue = Tail(channel_reliable_sequenced.queue)]
    /\ UNCHANGED <<cell_data, overload_state, merge_eligible, 
                  channel_reliable_unsequenced, channel_unreliable_sequenced, channel_unreliable_unsequenced>>

ProcessReliableUnsequencedQueue ==
    /\ Len(channel_reliable_unsequenced.queue) > 0
    /\ channel_reliable_unsequenced' = [channel_reliable_unsequenced EXCEPT 
                                       !.queue = Tail(channel_reliable_unsequenced.queue)]
    /\ UNCHANGED <<cell_data, overload_state, merge_eligible, 
                  channel_reliable_sequenced, channel_unreliable_sequenced, channel_unreliable_unsequenced>>

ProcessUnreliableSequencedQueue ==
    /\ Len(channel_unreliable_sequenced.queue) > 0
    /\ channel_unreliable_sequenced' = [channel_unreliable_sequenced EXCEPT 
                                       !.queue = Tail(channel_unreliable_sequenced.queue)]
    /\ UNCHANGED <<cell_data, overload_state, merge_eligible, 
                  channel_reliable_sequenced, channel_reliable_unsequenced, channel_unreliable_unsequenced>>

ProcessUnreliableUnsequencedQueue ==
    /\ Len(channel_unreliable_unsequenced.queue) > 0
    /\ channel_unreliable_unsequenced' = [channel_unreliable_unsequenced EXCEPT 
                                         !.queue = Tail(channel_unreliable_unsequenced.queue)]
    /\ UNCHANGED <<cell_data, overload_state, merge_eligible, 
                  channel_reliable_sequenced, channel_reliable_unsequenced, channel_unreliable_sequenced>>

(* VR-specific message generation with appropriate channel assignment *)
SendMovementUpdate ==
    (* Movement uses Channel 3: Unreliable + Sequenced - latest position matters, drops OK *)
    SendToUnreliableSequenced(TaskImpact_Movement)

SendInteractionEvent ==
    (* Interactions use Channel 1: Reliable + Sequenced - must arrive in order *)
    SendToReliableSequenced(TaskImpact_Interaction)

SendWorldStateUpdate ==
    (* World state uses Channel 2: Reliable + Unsequenced - must arrive, order less critical *)
    SendToReliableUnsequenced(TaskImpact_WorldLoad)

SendNetworkSyncUpdate ==
    (* Network sync uses Channel 2: Reliable + Unsequenced - must arrive, order flexible *)
    SendToReliableUnsequenced(TaskImpact_NetworkSync)

SendPhysicsUpdate ==
    (* Physics uses Channel 3: Unreliable + Sequenced - latest state matters *)
    SendToUnreliableSequenced(TaskImpact_Physics)

SendCommonUpdate ==
    (* Common tasks use Channel 4: Unreliable + Unsequenced - fire-and-forget *)
    SendToUnreliableUnsequenced(TaskImpact_Common)

SendRareEvent ==
    (* Rare events use Channel 1: Reliable + Sequenced - critical, must arrive in order *)
    SendToReliableSequenced(TaskImpact_Rare)

(* Zipfian-weighted task generation - more frequent tasks have higher probability *)
GenerateZipfianTaskActivity ==
    \/ GenerateMovementActivity          (* Rank 1: Most frequent (40% of tasks) *)
    \/ GenerateMovementActivity          (* Rank 1: Most frequent (40% of tasks) *)
    \/ GenerateMovementActivity          (* Rank 1: Most frequent (40% of tasks) *)
    \/ GenerateMovementActivity          (* Rank 1: Most frequent (40% of tasks) *)
    \/ GenerateCommonTaskActivity        (* Rank 2: Common (20% of tasks) *)
    \/ GenerateCommonTaskActivity        (* Rank 2: Common (20% of tasks) *)
    \/ GenerateNetworkSyncActivity       (* Rank 3: Moderate (15% of tasks) *)
    \/ GeneratePhysicsActivity           (* Rank 4: Less common (10% of tasks) *)
    \/ GenerateInteractionActivity       (* Rank 5: Uncommon (8% of tasks) *)
    \/ GenerateRareTaskActivity          (* Rank 6: Rare (5% of tasks) *)
    \/ GenerateWorldLoadActivity         (* Rank 7: Very rare but expensive (2% of tasks) *)

Next ==
    \/ GenerateZipfianTaskActivity
    \/ GenerateEntityArrival
    \/ ProcessCellWork
    \/ SendMovementUpdate
    \/ SendInteractionEvent
    \/ SendWorldStateUpdate
    \/ SendNetworkSyncUpdate
    \/ SendPhysicsUpdate
    \/ SendCommonUpdate
    \/ SendRareEvent
    \/ ProcessReliableSequencedQueue
    \/ ProcessReliableUnsequencedQueue
    \/ ProcessUnreliableSequencedQueue
    \/ ProcessUnreliableUnsequencedQueue

(* -------------------------------- SPECIFICATION AND THEOREM -------------------------------- *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

THEOREM Spec => [](TypeOK)

=============================================================================

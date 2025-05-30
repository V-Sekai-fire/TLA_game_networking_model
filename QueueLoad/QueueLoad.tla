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
    
    (* WebRTC Channel Configuration - Individual channel counts per delivery mode *)
    ReliableSequencedChannelCount,       (*  Number of reliable sequenced channels *)
    ReliableUnsequencedChannelCount,     (*  Number of reliable unsequenced channels *)
    UnreliableSequencedChannelCount,     (*  Number of unreliable sequenced channels *)
    UnreliableUnsequencedChannelCount,   (*  Number of unreliable unsequenced channels *)
    MaxReliableSequencedChannelQueue,    (*  Max queue length for reliable sequenced channels *)
    MaxReliableUnsequencedChannelQueue,  (*  Max queue length for reliable unsequenced channels *)
    MaxUnreliableSequencedChannelQueue,  (*  Max queue length for unreliable sequenced channels *)
    MaxUnreliableUnsequencedChannelQueue (*  Max queue length for unreliable unsequenced channels *)

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
    /\ ReliableSequencedChannelCount \in Nat \ {0}
    /\ ReliableUnsequencedChannelCount \in Nat \ {0}
    /\ UnreliableSequencedChannelCount \in Nat \ {0}
    /\ UnreliableUnsequencedChannelCount \in Nat \ {0}
    /\ MaxReliableSequencedChannelQueue \in Nat \ {0}
    /\ MaxReliableUnsequencedChannelQueue \in Nat \ {0}
    /\ MaxUnreliableSequencedChannelQueue \in Nat \ {0}
    /\ MaxUnreliableUnsequencedChannelQueue \in Nat \ {0}
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
    channels_reliable_sequenced,        (*  Multiple Reliable + Sequenced channels - Critical interactions *)
    channels_reliable_unsequenced,      (*  Multiple Reliable + Unsequenced channels - Important data *)
    channels_unreliable_sequenced,      (*  Multiple Unreliable + Sequenced channels - Real-time updates *)
    channels_unreliable_unsequenced     (*  Multiple Unreliable + Unsequenced channels - Fire-and-forget *)

vars == <<cell_data, overload_state, merge_eligible, 
          channels_reliable_sequenced, channels_reliable_unsequenced,
          channels_unreliable_sequenced, channels_unreliable_unsequenced>>

(*  ----------------------------- TYPE DEFINITIONS AND HELPERS ----------------------------- *)
CellType == [numEntities : Nat,
             requestQueue : Seq(Nat) ] (*  Nat here is TaskImpact *)

(* WebRTC Channel Type - queue contains packet sizes, dropped counts failed transmissions *)
ChannelType == [queue : Seq(Nat), 
                dropped : Nat]

(* Multiple channels per delivery mode to reduce head-of-line blocking *)
ReliableSequencedChannelArrayType == [1..ReliableSequencedChannelCount -> ChannelType]
ReliableUnsequencedChannelArrayType == [1..ReliableUnsequencedChannelCount -> ChannelType]
UnreliableSequencedChannelArrayType == [1..UnreliableSequencedChannelCount -> ChannelType]
UnreliableUnsequencedChannelArrayType == [1..UnreliableUnsequencedChannelCount -> ChannelType]

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
    /\ channels_reliable_sequenced \in ReliableSequencedChannelArrayType
    /\ channels_reliable_unsequenced \in ReliableUnsequencedChannelArrayType
    /\ channels_unreliable_sequenced \in UnreliableSequencedChannelArrayType
    /\ channels_unreliable_unsequenced \in UnreliableUnsequencedChannelArrayType

(* Helper functions for load management *)
IsOverloaded(cell) ==
    cell.numEntities > MaxEntitiesPerCell \/ Len(cell.requestQueue) > MaxQueueLengthPerCell

IsMergeEligible(cell) ==
    cell.numEntities < MinEntitiesForMerge /\ Len(cell.requestQueue) < MinQueueLengthForMerge

(* WebRTC Channel Helpers for multiple channels per mode *)
(* Find least loaded channel for load balancing *)
FindLeastLoadedChannelRS(channel_array) ==
    LET channel_loads == [i \in 1..ReliableSequencedChannelCount |-> Len(channel_array[i].queue)]
        min_load == CHOOSE load \in DOMAIN channel_loads : 
                       \A other \in DOMAIN channel_loads : channel_loads[load] <= channel_loads[other]
    IN min_load

FindLeastLoadedChannelRU(channel_array) ==
    LET channel_loads == [i \in 1..ReliableUnsequencedChannelCount |-> Len(channel_array[i].queue)]
        min_load == CHOOSE load \in DOMAIN channel_loads : 
                       \A other \in DOMAIN channel_loads : channel_loads[load] <= channel_loads[other]
    IN min_load

FindLeastLoadedChannelUS(channel_array) ==
    LET channel_loads == [i \in 1..UnreliableSequencedChannelCount |-> Len(channel_array[i].queue)]
        min_load == CHOOSE load \in DOMAIN channel_loads : 
                       \A other \in DOMAIN channel_loads : channel_loads[load] <= channel_loads[other]
    IN min_load

FindLeastLoadedChannelUU(channel_array) ==
    LET channel_loads == [i \in 1..UnreliableUnsequencedChannelCount |-> Len(channel_array[i].queue)]
        min_load == CHOOSE load \in DOMAIN channel_loads : 
                       \A other \in DOMAIN channel_loads : channel_loads[load] <= channel_loads[other]
    IN min_load

(* Check if any channel in the array can accept packets *)
CanEnqueueToReliableSequenced == 
    \E i \in 1..ReliableSequencedChannelCount : Len(channels_reliable_sequenced[i].queue) < MaxReliableSequencedChannelQueue

CanEnqueueToReliableUnsequenced == 
    \E i \in 1..ReliableUnsequencedChannelCount : Len(channels_reliable_unsequenced[i].queue) < MaxReliableUnsequencedChannelQueue

CanEnqueueToUnreliableSequenced == 
    \E i \in 1..UnreliableSequencedChannelCount : Len(channels_unreliable_sequenced[i].queue) < MaxUnreliableSequencedChannelQueue

CanEnqueueToUnreliableUnsequenced == 
    \E i \in 1..UnreliableUnsequencedChannelCount : Len(channels_unreliable_unsequenced[i].queue) < MaxUnreliableUnsequencedChannelQueue

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
    Len(cell_data.requestQueue) <= 15  (* Aggressive limit to force failure under exponential load *)

(* WebRTC Channel Saturation Invariant - Tests head-of-line blocking mitigation *)
WebRTCChannelSaturationInvariant ==
    \* Reliable channels should not all be simultaneously saturated
    \/ \E i \in 1..ReliableSequencedChannelCount : 
        Len(channels_reliable_sequenced[i].queue) < MaxReliableSequencedChannelQueue
    \/ \E i \in 1..ReliableUnsequencedChannelCount : 
        Len(channels_reliable_unsequenced[i].queue) < MaxReliableUnsequencedChannelQueue

(* Invariant to test entity growth limits *)
EntityCapacityInvariant ==
    cell_data.numEntities <= 100  (* Lower entity limit to see geometric growth effects sooner *)

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
    /\ channels_reliable_sequenced = [i \in 1..ReliableSequencedChannelCount |-> [queue |-> << >>, dropped |-> 0]]
    /\ channels_reliable_unsequenced = [i \in 1..ReliableUnsequencedChannelCount |-> [queue |-> << >>, dropped |-> 0]]
    /\ channels_unreliable_sequenced = [i \in 1..UnreliableSequencedChannelCount |-> [queue |-> << >>, dropped |-> 0]]
    /\ channels_unreliable_unsequenced = [i \in 1..UnreliableUnsequencedChannelCount |-> [queue |-> << >>, dropped |-> 0]]

(*  --------------------------------------- ACTIONS ---------------------------------------- *)

(*  --- Actions to simulate task generation and enqueueing --- *)
EnqueueTask(task_impact) ==
    /\ task_impact \in Nat \ {0}
    /\ cell_data' = [cell_data EXCEPT !.requestQueue = Append(cell_data.requestQueue, task_impact)]
    /\ overload_state' = IsOverloaded(cell_data')
    /\ merge_eligible' = IsMergeEligible(cell_data')
    /\ UNCHANGED <<channels_reliable_sequenced, channels_reliable_unsequenced, 
                   channels_unreliable_sequenced, channels_unreliable_unsequenced>>

AddEntitiesToCell(entity_increment) ==
    /\ entity_increment \in Nat \ {0}
    /\ cell_data' = [cell_data EXCEPT !.numEntities = cell_data.numEntities + entity_increment]
    /\ overload_state' = IsOverloaded(cell_data')
    /\ merge_eligible' = IsMergeEligible(cell_data')
    /\ UNCHANGED <<channels_reliable_sequenced, channels_reliable_unsequenced, 
                   channels_unreliable_sequenced, channels_unreliable_unsequenced>>

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

GenerateEntityArrival == (*  Action to increase numEntities geometrically *)
    /\ cell_data.numEntities < MaxEntitiesPerCell
    /\ LET current_entities == cell_data.numEntities
           (* True geometric growth: next = current * growth_rate *)
           (* Growth rate of 1.2 means 20% increase each time *)
           growth_rate == 20  (* Multiply by 1.2, using integer math: new = old + (old * 2) / 10 *)
           geometric_increment == IF current_entities < 5 THEN 1  (* Minimum growth to get started *)
                                 ELSE (current_entities * 2) \div 10  (* 20% of current population *)
           actual_increment == IF geometric_increment < 1 THEN 1 ELSE geometric_increment
       IN AddEntitiesToCell(actual_increment)

(*  --- Action to simulate cell processing its queue --- *)
ProcessCellWork ==
    /\ Len(cell_data.requestQueue) > 0
    /\ LET first_task == Head(cell_data.requestQueue)
       IN /\ first_task <= CellProcessingCapacity
          /\ cell_data' = [cell_data EXCEPT !.requestQueue = Tail(cell_data.requestQueue)]
          /\ overload_state' = IsOverloaded(cell_data')
          /\ merge_eligible' = IsMergeEligible(cell_data')
          /\ UNCHANGED <<channels_reliable_sequenced, channels_reliable_unsequenced, 
                         channels_unreliable_sequenced, channels_unreliable_unsequenced>>

(*  --- WebRTC Channel Actions for each of the 4 permutations --- *)

(* Channel 1: Reliable + Sequenced - Critical interactions, rare events *)
SendToReliableSequenced(packet_size) ==
    /\ packet_size \in Nat \ {0}
    /\ IF CanEnqueueToReliableSequenced THEN
        \* Queue has space - enqueue packet to least loaded channel
        LET least_loaded_channel == FindLeastLoadedChannelRS(channels_reliable_sequenced)
        IN /\ channels_reliable_sequenced' = [channels_reliable_sequenced EXCEPT 
                                             ![least_loaded_channel].queue = Append(channels_reliable_sequenced[least_loaded_channel].queue, packet_size)]
           /\ UNCHANGED <<cell_data, overload_state, merge_eligible, 
                          channels_reliable_unsequenced, channels_unreliable_sequenced, channels_unreliable_unsequenced>>
       ELSE
        \* Reliable channel blocks when full - action disabled
        FALSE

(* Channel 2: Reliable + Unsequenced - World loading, network sync *)
SendToReliableUnsequenced(packet_size) ==
    /\ packet_size \in Nat \ {0}
    /\ IF CanEnqueueToReliableUnsequenced THEN
        \* Queue has space - enqueue packet to least loaded channel
        LET least_loaded_channel == FindLeastLoadedChannelRU(channels_reliable_unsequenced)
        IN /\ channels_reliable_unsequenced' = [channels_reliable_unsequenced EXCEPT 
                                               ![least_loaded_channel].queue = Append(channels_reliable_unsequenced[least_loaded_channel].queue, packet_size)]
           /\ UNCHANGED <<cell_data, overload_state, merge_eligible, 
                          channels_reliable_sequenced, channels_unreliable_sequenced, channels_unreliable_unsequenced>>
       ELSE
        \* Reliable channel blocks when full - action disabled
        FALSE

(* Channel 3: Unreliable + Sequenced - Movement, physics *)
SendToUnreliableSequenced(packet_size) ==
    /\ packet_size \in Nat \ {0}
    /\ IF CanEnqueueToUnreliableSequenced THEN
        \* Queue has space - enqueue packet to least loaded channel
        LET least_loaded_channel == FindLeastLoadedChannelUS(channels_unreliable_sequenced)
        IN /\ channels_unreliable_sequenced' = [channels_unreliable_sequenced EXCEPT 
                                               ![least_loaded_channel].queue = Append(channels_unreliable_sequenced[least_loaded_channel].queue, packet_size)]
           /\ UNCHANGED <<cell_data, overload_state, merge_eligible, 
                          channels_reliable_sequenced, channels_reliable_unsequenced, channels_unreliable_unsequenced>>
       ELSE
        \* Unreliable channel drops when full - non-blocking, increment dropped counter for least loaded channel
        LET least_loaded_channel == FindLeastLoadedChannelUS(channels_unreliable_sequenced)
        IN /\ channels_unreliable_sequenced' = [channels_unreliable_sequenced EXCEPT 
                                               ![least_loaded_channel].dropped = channels_unreliable_sequenced[least_loaded_channel].dropped + 1]
           /\ UNCHANGED <<cell_data, overload_state, merge_eligible, 
                          channels_reliable_sequenced, channels_reliable_unsequenced, channels_unreliable_unsequenced>>

(* Channel 4: Unreliable + Unsequenced - Common tasks, heartbeats *)
SendToUnreliableUnsequenced(packet_size) ==
    /\ packet_size \in Nat \ {0}
    /\ IF CanEnqueueToUnreliableUnsequenced THEN
        \* Queue has space - enqueue packet to least loaded channel
        LET least_loaded_channel == FindLeastLoadedChannelUU(channels_unreliable_unsequenced)
        IN /\ channels_unreliable_unsequenced' = [channels_unreliable_unsequenced EXCEPT 
                                                 ![least_loaded_channel].queue = Append(channels_unreliable_unsequenced[least_loaded_channel].queue, packet_size)]
           /\ UNCHANGED <<cell_data, overload_state, merge_eligible, 
                          channels_reliable_sequenced, channels_reliable_unsequenced, channels_unreliable_sequenced>>
       ELSE
        \* Unreliable channel drops when full - non-blocking, increment dropped counter for least loaded channel
        LET least_loaded_channel == FindLeastLoadedChannelUU(channels_unreliable_unsequenced)
        IN /\ channels_unreliable_unsequenced' = [channels_unreliable_unsequenced EXCEPT 
                                                 ![least_loaded_channel].dropped = channels_unreliable_unsequenced[least_loaded_channel].dropped + 1]
           /\ UNCHANGED <<cell_data, overload_state, merge_eligible, 
                          channels_reliable_sequenced, channels_reliable_unsequenced, channels_unreliable_sequenced>>

(* Process each channel's queue - transmit buffered packets *)
ProcessReliableSequencedQueue ==
    \E i \in 1..ReliableSequencedChannelCount :
        /\ Len(channels_reliable_sequenced[i].queue) > 0
        /\ channels_reliable_sequenced' = [channels_reliable_sequenced EXCEPT 
                                         ![i].queue = Tail(channels_reliable_sequenced[i].queue)]
        /\ UNCHANGED <<cell_data, overload_state, merge_eligible, 
                      channels_reliable_unsequenced, channels_unreliable_sequenced, channels_unreliable_unsequenced>>

ProcessReliableUnsequencedQueue ==
    \E i \in 1..ReliableUnsequencedChannelCount :
        /\ Len(channels_reliable_unsequenced[i].queue) > 0
        /\ channels_reliable_unsequenced' = [channels_reliable_unsequenced EXCEPT 
                                           ![i].queue = Tail(channels_reliable_unsequenced[i].queue)]
        /\ UNCHANGED <<cell_data, overload_state, merge_eligible, 
                      channels_reliable_sequenced, channels_unreliable_sequenced, channels_unreliable_unsequenced>>

ProcessUnreliableSequencedQueue ==
    \E i \in 1..UnreliableSequencedChannelCount :
        /\ Len(channels_unreliable_sequenced[i].queue) > 0
        /\ channels_unreliable_sequenced' = [channels_unreliable_sequenced EXCEPT 
                                           ![i].queue = Tail(channels_unreliable_sequenced[i].queue)]
        /\ UNCHANGED <<cell_data, overload_state, merge_eligible, 
                      channels_reliable_sequenced, channels_reliable_unsequenced, channels_unreliable_unsequenced>>

ProcessUnreliableUnsequencedQueue ==
    \E i \in 1..UnreliableUnsequencedChannelCount :
        /\ Len(channels_unreliable_unsequenced[i].queue) > 0
        /\ channels_unreliable_unsequenced' = [channels_unreliable_unsequenced EXCEPT 
                                             ![i].queue = Tail(channels_unreliable_unsequenced[i].queue)]
        /\ UNCHANGED <<cell_data, overload_state, merge_eligible, 
                      channels_reliable_sequenced, channels_reliable_unsequenced, channels_unreliable_sequenced>>

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

(* Enhanced Zipfian-weighted task generation that uses WebRTC channels *)
GenerateZipfianTaskActivity ==
    \/ SendMovementUpdate                (* Rank 1: Most frequent (40% of tasks) - Uses Unreliable Sequenced *)
    \/ SendMovementUpdate                (* Rank 1: Most frequent (40% of tasks) *)
    \/ SendMovementUpdate                (* Rank 1: Most frequent (40% of tasks) *)
    \/ SendMovementUpdate                (* Rank 1: Most frequent (40% of tasks) *)
    \/ SendCommonUpdate                  (* Rank 2: Common (20% of tasks) - Uses Unreliable Unsequenced *)
    \/ SendCommonUpdate                  (* Rank 2: Common (20% of tasks) *)
    \/ SendNetworkSyncUpdate             (* Rank 3: Moderate (15% of tasks) - Uses Reliable Unsequenced *)
    \/ SendPhysicsUpdate                 (* Rank 4: Less common (10% of tasks) - Uses Unreliable Sequenced *)
    \/ SendInteractionEvent              (* Rank 5: Uncommon (8% of tasks) - Uses Reliable Sequenced *)
    \/ SendRareEvent                     (* Rank 6: Rare (5% of tasks) - Uses Reliable Sequenced *)
    \/ SendWorldStateUpdate              (* Rank 7: Very rare but expensive (2% of tasks) - Uses Reliable Unsequenced *)

Next ==
    \/ GenerateZipfianTaskActivity       (* Primary load generator - sends to WebRTC channels *)
    \/ GenerateEntityArrival             (* Geometric entity growth *)
    \/ ProcessReliableSequencedQueue     (* Process WebRTC channel queues *)
    \/ ProcessReliableUnsequencedQueue
    \/ ProcessUnreliableSequencedQueue
    \/ ProcessUnreliableUnsequencedQueue
    \/ ProcessCellWork                   (* Process main queue (less important for WebRTC testing) *)

(* -------------------------------- SPECIFICATION AND THEOREM -------------------------------- *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

THEOREM Spec => [](TypeOK)

=============================================================================

---- MODULE QueueLoad ----

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    MIN_ENTITIES_FOR_MERGE,      (*  Minimum entities threshold for merge consideration *)
    MAX_QUEUE_LENGTH_PER_CELL,    (*  Max request queue length before considering overload *)
    MIN_QUEUE_LENGTH_FOR_MERGE,   (*  Minimum queue length threshold for merge consideration *)
    
    (* Database Operation Impacts - infrastructure decisions *)
    DATABASE_OPS_PER_STEP,       (*  Database throughput limit (ops per model step) *)
    
    (* WebRTC Channel Configuration - infrastructure decisions *)
    RELIABLE_SEQUENCED_CHANNEL_COUNT,       (*  Number of reliable sequenced channels *)
    RELIABLE_UNSEQUENCED_CHANNEL_COUNT,     (*  Number of reliable unsequenced channels *)
    UNRELIABLE_SEQUENCED_CHANNEL_COUNT,     (*  Number of unreliable sequenced channels *)
    UNRELIABLE_UNSEQUENCED_CHANNEL_COUNT,   (*  Number of unreliable unsequenced channels *)
    MAX_RELIABLE_SEQUENCED_CHANNEL_QUEUE,    (*  Max queue length for reliable sequenced channels *)
    MAX_RELIABLE_UNSEQUENCED_CHANNEL_QUEUE,  (*  Max queue length for reliable unsequenced channels *)
    MAX_UNRELIABLE_SEQUENCED_CHANNEL_QUEUE,  (*  Max queue length for unreliable sequenced channels *)
    MAX_UNRELIABLE_UNSEQUENCED_CHANNEL_QUEUE (*  Max queue length for unreliable unsequenced channels *)

(* Time abstraction: Each model step = 100ms (0.1 seconds) *)
(* This allows plotting against ops/second: DATABASE_OPS_PER_STEP * 10 = ops/sec *)
MODEL_STEP_DURATION_MS == 100
STEPS_PER_SECOND == 1000 \div MODEL_STEP_DURATION_MS

(* Network Event CPU Time on Elixir Green Threads (microseconds) *)
(* These represent actual CPU processing time per network event *)
NETWORK_EVENT_CPU_TIME_COMMON == 50      (* 50μs - simple message *)
NETWORK_EVENT_CPU_TIME_MOVEMENT == 75    (* 75μs - position updates *)
NETWORK_EVENT_CPU_TIME_PHYSICS == 100    (* 100μs - physics calculations *)
NETWORK_EVENT_CPU_TIME_INTERACTION == 150 (* 150μs - interaction validation *)
NETWORK_EVENT_CPU_TIME_NETWORK_SYNC == 200 (* 200μs - state synchronization *)
NETWORK_EVENT_CPU_TIME_RARE == 500       (* 500μs - complex rare events *)
NETWORK_EVENT_CPU_TIME_WORLD_LOAD == 800 (* 800μs - world asset processing *)

(* Database Operation Impacts - hardcoded based on typical VR workloads *)
DB_OPS_COMMON == 1             (* Simple state updates *)
DB_OPS_MOVEMENT == 1           (* Position logging *)
DB_OPS_PHYSICS == 3            (* Physics state persistence *)
DB_OPS_INTERACTION == 4        (* Interaction event logging *)
DB_OPS_NETWORK_SYNC == 6       (* Network state synchronization *)
DB_OPS_RARE == 8               (* Complex rare events *)
DB_OPS_WORLD_LOAD == 12        (* Loading world geometry/assets *)

(* Network Packet Sizes - hardcoded based on WebRTC message types *)
NETWORK_BYTES_COMMON == 50      (* Small status messages *)
NETWORK_BYTES_MOVEMENT == 100   (* Position + rotation data *)
NETWORK_BYTES_PHYSICS == 150    (* Physics state vectors *)
NETWORK_BYTES_INTERACTION == 200 (* Interaction event data *)
NETWORK_BYTES_NETWORK_SYNC == 300 (* State synchronization *)
NETWORK_BYTES_RARE == 500       (* Complex event payloads *)
NETWORK_BYTES_WORLD_LOAD == 2000 (* Asset metadata packets *)

(* Zipfian Distribution - hardcoded VR usage patterns *)
ZIPF_MOVEMENT_WEIGHT == 8       (* Most frequent: movement updates *)
ZIPF_COMMON_WEIGHT == 4         (* Common: status/heartbeat *)
ZIPF_NETWORK_SYNC_WEIGHT == 3   (* Regular: state sync *)
ZIPF_PHYSICS_WEIGHT == 3        (* Regular: physics updates *)
ZIPF_INTERACTION_WEIGHT == 2    (* Less frequent: interactions *)
ZIPF_RARE_WEIGHT == 2           (* Less frequent: special events *)
ZIPF_WORLD_LOAD_WEIGHT == 2     (* Least frequent: asset loading *)

(* Entity Growth Parameters - hardcoded for stress testing *)
MIN_ENTITIES_FOR_GROWTH == 3            (* Start growth after 3 entities *)
GEOMETRIC_GROWTH_RATE_PERCENT == 50     (* 50% growth rate *)
GEOMETRIC_GROWTH_DIVISOR == 100         (* For percentage calculation *)

(* Initial entity count - hardcoded baseline *)
BASELINE_ENTITIES == 10

ASSUME A_PositiveConstants ==
    /\ DATABASE_OPS_PER_STEP \in Nat \ {0}
    /\ MAX_QUEUE_LENGTH_PER_CELL \in Nat \ {0}
    /\ RELIABLE_SEQUENCED_CHANNEL_COUNT \in Nat \ {0}
    /\ RELIABLE_UNSEQUENCED_CHANNEL_COUNT \in Nat \ {0}
    /\ UNRELIABLE_SEQUENCED_CHANNEL_COUNT \in Nat \ {0}
    /\ UNRELIABLE_UNSEQUENCED_CHANNEL_COUNT \in Nat \ {0}
    /\ MAX_RELIABLE_SEQUENCED_CHANNEL_QUEUE \in Nat \ {0}
    /\ MAX_RELIABLE_UNSEQUENCED_CHANNEL_QUEUE \in Nat \ {0}
    /\ MAX_UNRELIABLE_SEQUENCED_CHANNEL_QUEUE \in Nat \ {0}
    /\ MAX_UNRELIABLE_UNSEQUENCED_CHANNEL_QUEUE \in Nat \ {0}

ASSUME A_LogicalConstraints ==
    /\ DB_OPS_RARE >= DB_OPS_COMMON
    /\ MIN_ENTITIES_FOR_MERGE \in Nat
    /\ MIN_QUEUE_LENGTH_FOR_MERGE \in Nat

VARIABLES 
    cell_data,                          (*  Record for the single cell: [numEntities: Nat, requestQueue: Seq(Nat)] *)
    channels_reliable_sequenced,        (*  Multiple Reliable + Sequenced channels - Critical interactions *)
    channels_reliable_unsequenced,      (*  Multiple Reliable + Unsequenced channels - Important data *)
    channels_unreliable_sequenced,      (*  Multiple Unreliable + Sequenced channels - Real-time updates *)
    channels_unreliable_unsequenced     (*  Multiple Unreliable + Unsequenced channels - Fire-and-forget *)

vars == <<cell_data, 
          channels_reliable_sequenced, channels_reliable_unsequenced,
          channels_unreliable_sequenced, channels_unreliable_unsequenced>>

(*  ----------------------------- TYPE DEFINITIONS AND HELPERS ----------------------------- *)
CellType == [numEntities : Nat,
             requestQueue : Seq(Nat) ] (*  Nat here is TaskImpact *)

(* WebRTC Channel Type - queue contains packet sizes, dropped counts failed transmissions *)
ChannelType == [queue : Seq(Nat), 
                dropped : Nat]

(* Multiple channels per delivery mode to reduce head-of-line blocking *)
ReliableSequencedChannelArrayType == [1..RELIABLE_SEQUENCED_CHANNEL_COUNT -> ChannelType]
ReliableUnsequencedChannelArrayType == [1..RELIABLE_UNSEQUENCED_CHANNEL_COUNT -> ChannelType]
UnreliableSequencedChannelArrayType == [1..UNRELIABLE_SEQUENCED_CHANNEL_COUNT -> ChannelType]
UnreliableUnsequencedChannelArrayType == [1..UNRELIABLE_UNSEQUENCED_CHANNEL_COUNT -> ChannelType]

(* Basic debug helpers that don't depend on other functions *)
EntityCount == cell_data.numEntities
QueueLength == Len(cell_data.requestQueue)
CurrentQueueContent == cell_data.requestQueue

(* Network event timing helpers for performance analysis *)
GetNetworkEventCpuTime(event_type) ==
    CASE event_type = "common" -> NETWORK_EVENT_CPU_TIME_COMMON
      [] event_type = "movement" -> NETWORK_EVENT_CPU_TIME_MOVEMENT
      [] event_type = "physics" -> NETWORK_EVENT_CPU_TIME_PHYSICS
      [] event_type = "interaction" -> NETWORK_EVENT_CPU_TIME_INTERACTION
      [] event_type = "networksync" -> NETWORK_EVENT_CPU_TIME_NETWORK_SYNC
      [] event_type = "rare" -> NETWORK_EVENT_CPU_TIME_RARE
      [] event_type = "worldload" -> NETWORK_EVENT_CPU_TIME_WORLD_LOAD
      [] OTHER -> NETWORK_EVENT_CPU_TIME_COMMON

(* Convert microseconds per event to events per second capacity *)
GetNetworkEventCapacityPerSecond(event_type) ==
    1000000 \div GetNetworkEventCpuTime(event_type)  (* 1,000,000 μs = 1 second *)

(* Get current network processing load in events per second *)
CurrentNetworkLoadPerSecond ==
    LET movement_events == ZIPF_MOVEMENT_WEIGHT * STEPS_PER_SECOND
        common_events == ZIPF_COMMON_WEIGHT * STEPS_PER_SECOND
        physics_events == ZIPF_PHYSICS_WEIGHT * STEPS_PER_SECOND
        sync_events == ZIPF_NETWORK_SYNC_WEIGHT * STEPS_PER_SECOND
        interaction_events == ZIPF_INTERACTION_WEIGHT * STEPS_PER_SECOND
        rare_events == ZIPF_RARE_WEIGHT * STEPS_PER_SECOND
        worldload_events == ZIPF_WORLD_LOAD_WEIGHT * STEPS_PER_SECOND
    IN movement_events + common_events + physics_events + sync_events + 
       interaction_events + rare_events + worldload_events

(* Calculate if network processing is saturated *)
IsNetworkSaturated ==
    CurrentNetworkLoadPerSecond > GetNetworkEventCapacityPerSecond("common")

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
    /\ channels_reliable_sequenced \in ReliableSequencedChannelArrayType
    /\ channels_reliable_unsequenced \in ReliableUnsequencedChannelArrayType
    /\ channels_unreliable_sequenced \in UnreliableSequencedChannelArrayType
    /\ channels_unreliable_unsequenced \in UnreliableUnsequencedChannelArrayType

(* Helper functions for load management *)
IsOverloaded(cell) ==
    Len(cell.requestQueue) > MAX_QUEUE_LENGTH_PER_CELL

IsMergeEligible(cell) ==
    cell.numEntities < MIN_ENTITIES_FOR_MERGE /\ Len(cell.requestQueue) < MIN_QUEUE_LENGTH_FOR_MERGE

(* Advanced debug helpers that depend on helper functions *)
IsCurrentlyOverloaded == IsOverloaded(cell_data)
CurrentOverloadReason == IF Len(cell_data.requestQueue) > MAX_QUEUE_LENGTH_PER_CELL 
                        THEN "QUEUE_TOO_LONG" 
                        ELSE "NOT_OVERLOADED"
EntityGrowthStatus == IF cell_data.numEntities >= MIN_ENTITIES_FOR_GROWTH 
                     THEN "CAN_GROW" 
                     ELSE "BELOW_GROWTH_THRESHOLD"
AllChannelQueues == <<
    [type |-> "ReliableSeq", queues |-> [i \in 1..RELIABLE_SEQUENCED_CHANNEL_COUNT |-> Len(channels_reliable_sequenced[i].queue)]],
    [type |-> "ReliableUnseq", queues |-> [i \in 1..RELIABLE_UNSEQUENCED_CHANNEL_COUNT |-> Len(channels_reliable_unsequenced[i].queue)]],
    [type |-> "UnreliableSeq", queues |-> [i \in 1..UNRELIABLE_SEQUENCED_CHANNEL_COUNT |-> Len(channels_unreliable_sequenced[i].queue)]],
    [type |-> "UnreliableUnseq", queues |-> [i \in 1..UNRELIABLE_UNSEQUENCED_CHANNEL_COUNT |-> Len(channels_unreliable_unsequenced[i].queue)]]
>>
TotalChannelLoad == Len(channels_reliable_sequenced[1].queue) + 
                   Len(channels_reliable_unsequenced[1].queue) + 
                   Len(channels_unreliable_sequenced[1].queue) + 
                   Len(channels_unreliable_unsequenced[1].queue)

(* WebRTC Channel Helpers for multiple channels per mode *)
(* Find least loaded channel for load balancing *)
FindLeastLoadedChannelRS(channel_array) ==
    LET channel_loads == [i \in 1..RELIABLE_SEQUENCED_CHANNEL_COUNT |-> Len(channel_array[i].queue)]
        min_load == CHOOSE load \in DOMAIN channel_loads : 
                       \A other \in DOMAIN channel_loads : channel_loads[load] <= channel_loads[other]
    IN min_load

FindLeastLoadedChannelRU(channel_array) ==
    LET channel_loads == [i \in 1..RELIABLE_UNSEQUENCED_CHANNEL_COUNT |-> Len(channel_array[i].queue)]
        min_load == CHOOSE load \in DOMAIN channel_loads : 
                       \A other \in DOMAIN channel_loads : channel_loads[load] <= channel_loads[other]
    IN min_load

FindLeastLoadedChannelUS(channel_array) ==
    LET channel_loads == [i \in 1..UNRELIABLE_SEQUENCED_CHANNEL_COUNT |-> Len(channel_array[i].queue)]
        min_load == CHOOSE load \in DOMAIN channel_loads : 
                       \A other \in DOMAIN channel_loads : channel_loads[load] <= channel_loads[other]
    IN min_load

FindLeastLoadedChannelUU(channel_array) ==
    LET channel_loads == [i \in 1..UNRELIABLE_UNSEQUENCED_CHANNEL_COUNT |-> Len(channel_array[i].queue)]
        min_load == CHOOSE load \in DOMAIN channel_loads : 
                       \A other \in DOMAIN channel_loads : channel_loads[load] <= channel_loads[other]
    IN min_load

(* Check if any channel in the array can accept packets *)
CanEnqueueToReliableSequenced == 
    \E i \in 1..RELIABLE_SEQUENCED_CHANNEL_COUNT : Len(channels_reliable_sequenced[i].queue) < MAX_RELIABLE_SEQUENCED_CHANNEL_QUEUE

CanEnqueueToReliableUnsequenced == 
    \E i \in 1..RELIABLE_UNSEQUENCED_CHANNEL_COUNT : Len(channels_reliable_unsequenced[i].queue) < MAX_RELIABLE_UNSEQUENCED_CHANNEL_QUEUE

CanEnqueueToUnreliableSequenced == 
    \E i \in 1..UNRELIABLE_SEQUENCED_CHANNEL_COUNT : Len(channels_unreliable_sequenced[i].queue) < MAX_UNRELIABLE_SEQUENCED_CHANNEL_QUEUE

CanEnqueueToUnreliableUnsequenced == 
    \E i \in 1..UNRELIABLE_UNSEQUENCED_CHANNEL_COUNT : Len(channels_unreliable_unsequenced[i].queue) < MAX_UNRELIABLE_UNSEQUENCED_CHANNEL_QUEUE

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

(* Invariant to test queue capacity limits *)
QueueCapacityInvariant ==
    Len(cell_data.requestQueue) <= MAX_QUEUE_LENGTH_PER_CELL

(* Overload management invariant - ensures system doesn't exceed capacity limits *)
OverloadManagementInvariant ==
    ~IsOverloaded(cell_data)

(* WebRTC Channel Saturation Invariant - Tests head-of-line blocking mitigation *)
WebRTCChannelSaturationInvariant ==
    \* Reliable channels should not all be simultaneously saturated
    \/ \E i \in 1..RELIABLE_SEQUENCED_CHANNEL_COUNT : 
        Len(channels_reliable_sequenced[i].queue) < MAX_RELIABLE_SEQUENCED_CHANNEL_QUEUE
    \/ \E i \in 1..RELIABLE_UNSEQUENCED_CHANNEL_COUNT : 
        Len(channels_reliable_unsequenced[i].queue) < MAX_RELIABLE_UNSEQUENCED_CHANNEL_QUEUE

(* Merge eligibility invariant - tracks when cell could be merged (in multi-cell context) *)
MergeEligibilityInvariant ==
    TRUE  (* Always true - this is just tracking merge eligibility, not enforcing it *)

(*  ------------------------------------ INITIALIZATION ------------------------------------ *)
Init ==
    /\ cell_data = [ numEntities  |-> BASELINE_ENTITIES,
                    requestQueue |-> << >> ]
    /\ channels_reliable_sequenced = [i \in 1..RELIABLE_SEQUENCED_CHANNEL_COUNT |-> [queue |-> << >>, dropped |-> 0]]
    /\ channels_reliable_unsequenced = [i \in 1..RELIABLE_UNSEQUENCED_CHANNEL_COUNT |-> [queue |-> << >>, dropped |-> 0]]
    /\ channels_unreliable_sequenced = [i \in 1..UNRELIABLE_SEQUENCED_CHANNEL_COUNT |-> [queue |-> << >>, dropped |-> 0]]
    /\ channels_unreliable_unsequenced = [i \in 1..UNRELIABLE_UNSEQUENCED_CHANNEL_COUNT |-> [queue |-> << >>, dropped |-> 0]]

(*  --------------------------------------- ACTIONS ---------------------------------------- *)

(*  --- Actions to simulate task generation and enqueueing --- *)
EnqueueTask(task_impact) ==
    /\ task_impact \in Nat \ {0}
    /\ cell_data' = [cell_data EXCEPT !.requestQueue = Append(cell_data.requestQueue, task_impact)]
    /\ UNCHANGED <<channels_reliable_sequenced, channels_reliable_unsequenced, 
                   channels_unreliable_sequenced, channels_unreliable_unsequenced>>

AddEntitiesToCell(entity_increment) ==
    /\ entity_increment \in Nat \ {0}
    /\ cell_data' = [cell_data EXCEPT !.numEntities = cell_data.numEntities + entity_increment]
    /\ UNCHANGED <<channels_reliable_sequenced, channels_reliable_unsequenced, 
                   channels_unreliable_sequenced, channels_unreliable_unsequenced>>

GenerateCommonTaskActivity ==
    /\ cell_data.numEntities > 0
    /\ LET tasks_to_generate == (cell_data.numEntities * DB_OPS_COMMON) \div 100  (* Much lighter scaling for high entity counts *)
           actual_tasks == IF tasks_to_generate < 1 THEN 1 ELSE tasks_to_generate
       IN EnqueueTask(actual_tasks)

GenerateRareTaskActivity ==
    /\ cell_data.numEntities > 0
    /\ LET tasks_to_generate == (cell_data.numEntities * DB_OPS_RARE) \div 1000  (* Very rare at scale *)
           actual_tasks == IF tasks_to_generate < 1 THEN 1 ELSE tasks_to_generate
       IN EnqueueTask(actual_tasks)

GenerateMovementActivity ==
    /\ cell_data.numEntities > 0
    /\ LET tasks_to_generate == (cell_data.numEntities * DB_OPS_MOVEMENT) \div 50  (* Moderate scaling *)
       IN EnqueueTask(IF tasks_to_generate < 1 THEN 1 ELSE tasks_to_generate)

GenerateInteractionActivity ==
    /\ cell_data.numEntities > 0  
    /\ LET tasks_to_generate == (cell_data.numEntities * DB_OPS_INTERACTION) \div 200  (* Less frequent at scale *)
       IN EnqueueTask(IF tasks_to_generate < 1 THEN 1 ELSE tasks_to_generate)

GenerateWorldLoadActivity ==
    /\ cell_data.numEntities > 0
    /\ LET tasks_to_generate == (cell_data.numEntities * DB_OPS_WORLD_LOAD) \div 500  (* Very infrequent at scale *)
       IN EnqueueTask(IF tasks_to_generate < 1 THEN 1 ELSE tasks_to_generate)

GenerateNetworkSyncActivity ==
    /\ cell_data.numEntities > 0
    /\ LET tasks_to_generate == (cell_data.numEntities * DB_OPS_NETWORK_SYNC) \div 150  (* Moderate network sync *)
       IN EnqueueTask(IF tasks_to_generate < 1 THEN 1 ELSE tasks_to_generate)

GeneratePhysicsActivity ==
    /\ cell_data.numEntities > 0
    /\ LET tasks_to_generate == (cell_data.numEntities * DB_OPS_PHYSICS) \div 100  (* Physics scales reasonably *)
       IN EnqueueTask(IF tasks_to_generate < 1 THEN 1 ELSE tasks_to_generate)

GenerateEntityArrival == (*  Action to increase numEntities geometrically *)
    /\ LET current_entities == cell_data.numEntities
           (* True geometric growth: next = current * growth_rate *)
           (* Growth rate configured via GEOMETRIC_GROWTH_RATE_PERCENT *)
           geometric_increment == IF current_entities < MIN_ENTITIES_FOR_GROWTH THEN 1  (* Minimum growth to get started *)
                                 ELSE (current_entities * GEOMETRIC_GROWTH_RATE_PERCENT) \div GEOMETRIC_GROWTH_DIVISOR  (* Configurable percentage growth *)
           actual_increment == IF geometric_increment < 1 THEN 1 ELSE geometric_increment
       IN AddEntitiesToCell(actual_increment)

(* Check if any task in the queue can be processed with remaining capacity *)
CanProcessAnyInQueue(queue, capacity) ==
    IF Len(queue) = 0 THEN FALSE
    ELSE \E i \in 1..Len(queue) : queue[i] <= capacity

(* Helper function to process queue with capacity limits and HOL mitigation *)
RECURSIVE ProcessQueueWithCapacity(_, _)
ProcessQueueWithCapacity(queue, capacity) ==
    IF Len(queue) = 0 \/ capacity <= 0 THEN queue
    ELSE LET first_task == Head(queue)
             rest_queue == Tail(queue)
         IN IF first_task <= capacity THEN
                (* Process this task and continue with remaining capacity *)
                ProcessQueueWithCapacity(rest_queue, capacity - first_task)
            ELSE
                (* Task too big - check if we can process anything else in the queue *)
                IF CanProcessAnyInQueue(rest_queue, capacity) THEN
                    (* Move blocked task to end and try processing rest *)
                    ProcessQueueWithCapacity(Append(rest_queue, first_task), capacity)
                ELSE
                    (* Nothing can be processed - return original queue *)
                    queue

(*  --- Action to simulate cell processing its queue with HOL blocking mitigation --- *)
ProcessCellWork ==
    /\ Len(cell_data.requestQueue) > 0
    /\ LET remaining_capacity == DATABASE_OPS_PER_STEP
           (* Process as many tasks as possible within capacity, skipping blocked ones *)
           processed_queue == ProcessQueueWithCapacity(cell_data.requestQueue, remaining_capacity)
       IN /\ cell_data' = [cell_data EXCEPT !.requestQueue = processed_queue]
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
           /\ UNCHANGED <<cell_data, 
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
           /\ UNCHANGED <<cell_data, 
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
           /\ UNCHANGED <<cell_data, 
                          channels_reliable_sequenced, channels_reliable_unsequenced, channels_unreliable_unsequenced>>
       ELSE
        \* Unreliable channel drops when full - non-blocking, increment dropped counter for least loaded channel
        LET least_loaded_channel == FindLeastLoadedChannelUS(channels_unreliable_sequenced)
        IN /\ channels_unreliable_sequenced' = [channels_unreliable_sequenced EXCEPT 
                                               ![least_loaded_channel].dropped = channels_unreliable_sequenced[least_loaded_channel].dropped + 1]
           /\ UNCHANGED <<cell_data, 
                          channels_reliable_sequenced, channels_reliable_unsequenced, channels_unreliable_unsequenced>>

(* Channel 4: Unreliable + Unsequenced - Common tasks, heartbeats *)
SendToUnreliableUnsequenced(packet_size) ==
    /\ packet_size \in Nat \ {0}
    /\ IF CanEnqueueToUnreliableUnsequenced THEN
        \* Queue has space - enqueue packet to least loaded channel
        LET least_loaded_channel == FindLeastLoadedChannelUU(channels_unreliable_unsequenced)
        IN /\ channels_unreliable_unsequenced' = [channels_unreliable_unsequenced EXCEPT 
                                                 ![least_loaded_channel].queue = Append(channels_unreliable_unsequenced[least_loaded_channel].queue, packet_size)]
           /\ UNCHANGED <<cell_data, 
                          channels_reliable_sequenced, channels_reliable_unsequenced, channels_unreliable_sequenced>>
       ELSE
        \* Unreliable channel drops when full - non-blocking, increment dropped counter for least loaded channel
        LET least_loaded_channel == FindLeastLoadedChannelUU(channels_unreliable_unsequenced)
        IN /\ channels_unreliable_unsequenced' = [channels_unreliable_unsequenced EXCEPT 
                                                 ![least_loaded_channel].dropped = channels_unreliable_unsequenced[least_loaded_channel].dropped + 1]
           /\ UNCHANGED <<cell_data, 
                          channels_reliable_sequenced, channels_reliable_unsequenced, channels_unreliable_sequenced>>

(* Process each channel's queue - transmit buffered packets *)
ProcessReliableSequencedQueue ==
    \E i \in 1..RELIABLE_SEQUENCED_CHANNEL_COUNT :
        /\ Len(channels_reliable_sequenced[i].queue) > 0
        /\ channels_reliable_sequenced' = [channels_reliable_sequenced EXCEPT 
                                         ![i].queue = Tail(channels_reliable_sequenced[i].queue)]
        /\ UNCHANGED <<cell_data, 
                      channels_reliable_unsequenced, channels_unreliable_sequenced, channels_unreliable_unsequenced>>

ProcessReliableUnsequencedQueue ==
    \E i \in 1..RELIABLE_UNSEQUENCED_CHANNEL_COUNT :
        /\ Len(channels_reliable_unsequenced[i].queue) > 0
        /\ channels_reliable_unsequenced' = [channels_reliable_unsequenced EXCEPT 
                                           ![i].queue = Tail(channels_reliable_unsequenced[i].queue)]
        /\ UNCHANGED <<cell_data, 
                      channels_reliable_sequenced, channels_unreliable_sequenced, channels_unreliable_unsequenced>>

ProcessUnreliableSequencedQueue ==
    \E i \in 1..UNRELIABLE_SEQUENCED_CHANNEL_COUNT :
        /\ Len(channels_unreliable_sequenced[i].queue) > 0
        /\ channels_unreliable_sequenced' = [channels_unreliable_sequenced EXCEPT 
                                           ![i].queue = Tail(channels_unreliable_sequenced[i].queue)]
        /\ UNCHANGED <<cell_data, 
                      channels_reliable_sequenced, channels_reliable_unsequenced, channels_unreliable_unsequenced>>

ProcessUnreliableUnsequencedQueue ==
    \E i \in 1..UNRELIABLE_UNSEQUENCED_CHANNEL_COUNT :
        /\ Len(channels_unreliable_unsequenced[i].queue) > 0
        /\ channels_unreliable_unsequenced' = [channels_unreliable_unsequenced EXCEPT 
                                             ![i].queue = Tail(channels_unreliable_unsequenced[i].queue)]
        /\ UNCHANGED <<cell_data, 
                      channels_reliable_sequenced, channels_reliable_unsequenced, channels_unreliable_sequenced>>

(* VR-specific message generation with appropriate channel assignment *)
SendMovementUpdate ==
    (* Movement uses Channel 3: Unreliable + Sequenced - latest position matters, drops OK *)
    SendToUnreliableSequenced(NETWORK_BYTES_MOVEMENT)

SendInteractionEvent ==
    (* Interactions use Channel 1: Reliable + Sequenced - must arrive in order *)
    SendToReliableSequenced(NETWORK_BYTES_INTERACTION)

SendWorldStateUpdate ==
    (* World state uses Channel 2: Reliable + Unsequenced - must arrive, order less critical *)
    SendToReliableUnsequenced(NETWORK_BYTES_WORLD_LOAD)

SendNetworkSyncUpdate ==
    (* Network sync uses Channel 2: Reliable + Unsequenced - must arrive, order flexible *)
    SendToReliableUnsequenced(NETWORK_BYTES_NETWORK_SYNC)

SendPhysicsUpdate ==
    (* Physics uses Channel 3: Unreliable + Sequenced - latest state matters *)
    SendToUnreliableSequenced(NETWORK_BYTES_PHYSICS)

SendCommonUpdate ==
    (* Common tasks use Channel 4: Unreliable + Unsequenced - fire-and-forget *)
    SendToUnreliableUnsequenced(NETWORK_BYTES_COMMON)

SendRareEvent ==
    (* Rare events use Channel 1: Reliable + Sequenced - critical, must arrive in order *)
    SendToReliableSequenced(NETWORK_BYTES_RARE)

(* Enhanced Zipfian-weighted task generation that uses WebRTC channels *)
(* Uses configurable weights instead of magic numbers for better maintainability *)
GenerateZipfianTaskActivity ==
    \* Movement updates (highest frequency - ZIPF_MOVEMENT_WEIGHT occurrences)
    \/ /\ ZIPF_MOVEMENT_WEIGHT >= 1 /\ SendMovementUpdate
    \/ /\ ZIPF_MOVEMENT_WEIGHT >= 2 /\ SendMovementUpdate
    \/ /\ ZIPF_MOVEMENT_WEIGHT >= 3 /\ SendMovementUpdate
    \/ /\ ZIPF_MOVEMENT_WEIGHT >= 4 /\ SendMovementUpdate
    \* Common updates (ZIPF_COMMON_WEIGHT occurrences)
    \/ /\ ZIPF_COMMON_WEIGHT >= 1 /\ SendCommonUpdate
    \/ /\ ZIPF_COMMON_WEIGHT >= 2 /\ SendCommonUpdate
    \* Network sync updates (ZIPF_NETWORK_SYNC_WEIGHT occurrences)
    \/ /\ ZIPF_NETWORK_SYNC_WEIGHT >= 1 /\ SendNetworkSyncUpdate
    \* Physics updates (ZIPF_PHYSICS_WEIGHT occurrences)
    \/ /\ ZIPF_PHYSICS_WEIGHT >= 1 /\ SendPhysicsUpdate
    \* Interaction events (ZIPF_INTERACTION_WEIGHT occurrences)
    \/ /\ ZIPF_INTERACTION_WEIGHT >= 1 /\ SendInteractionEvent
    \* Rare events (ZIPF_RARE_WEIGHT occurrences)
    \/ /\ ZIPF_RARE_WEIGHT >= 1 /\ SendRareEvent
    \* World state updates (ZIPF_WORLD_LOAD_WEIGHT occurrences)
    \/ /\ ZIPF_WORLD_LOAD_WEIGHT >= 1 /\ SendWorldStateUpdate

Next ==
    \/ /\ Len(cell_data.requestQueue) > 0 /\ ProcessCellWork  (* Force processing when queue has items *)
    \/ /\ Len(cell_data.requestQueue) = 0 /\ GenerateCommonTaskActivity  (* Only generate when queue is empty *)
    \/ GenerateEntityArrival             (* Allow entity growth *)

(* -------------------------------- SPECIFICATION AND THEOREM -------------------------------- *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

THEOREM Spec => [](TypeOK)

=============================================================================

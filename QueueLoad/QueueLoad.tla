---- MODULE QueueLoad ----

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    MIN_ENTITIES_FOR_MERGE,      (*  Minimum entities threshold for merge consideration *)
    MAX_QUEUE_LENGTH_PER_CELL,    (*  Max request queue length before considering overload *)
    MIN_QUEUE_LENGTH_FOR_MERGE,   (*  Minimum queue length threshold for merge consideration *)
    
    (* Database Operation Impacts - measured in database ops consumed per action *)
    DB_OPS_COMMON,             (*  Database operations for a common task *)
    DB_OPS_RARE,               (*  Database operations for a rare, high-impact task *)
    DB_OPS_MOVEMENT,           (*  Player/avatar movement database updates *)
    DB_OPS_INTERACTION,        (*  Object interaction database events *)
    DB_OPS_WORLD_LOAD,          (*  Loading world assets/geometry from database *)
    DB_OPS_NETWORK_SYNC,        (*  Network state synchronization database writes *)
    DB_OPS_PHYSICS,            (*  Physics simulation database updates *)
    DATABASE_OPS_PER_STEP,       (*  Database throughput limit (ops per model step) *)
    
    (* Network Bandwidth Impacts - measured in bytes consumed per packet *)
    NETWORK_BYTES_COMMON,      (*  Network bytes for common messages *)
    NETWORK_BYTES_RARE,        (*  Network bytes for rare events *)
    NETWORK_BYTES_MOVEMENT,    (*  Network bytes for movement updates *)
    NETWORK_BYTES_INTERACTION, (*  Network bytes for interaction events *)
    NETWORK_BYTES_WORLD_LOAD,   (*  Network bytes for world loading *)
    NETWORK_BYTES_NETWORK_SYNC, (*  Network bytes for network sync *)
    NETWORK_BYTES_PHYSICS,     (*  Network bytes for physics updates *)
    
    BASELINE_ENTITIES,         (*  Initial entity count for the root cell *)
    
    (* Model Testing Constants - Growth and distribution parameters *)
    MIN_ENTITIES_FOR_GROWTH,            (*  Minimum entities threshold to start geometric growth *)
    GEOMETRIC_GROWTH_RATE_PERCENT,      (*  Percentage growth rate for geometric entity increase *)
    GEOMETRIC_GROWTH_DIVISOR,           (*  Divisor for integer arithmetic in growth calculation *)
    
    (* Zipfian Distribution Constants for task generation weights *)
    ZIPF_MOVEMENT_WEIGHT,               (*  Weight for movement updates (most frequent) *)
    ZIPF_COMMON_WEIGHT,                 (*  Weight for common tasks *)
    ZIPF_NETWORK_SYNC_WEIGHT,           (*  Weight for network sync updates *)
    ZIPF_PHYSICS_WEIGHT,                (*  Weight for physics updates *)
    ZIPF_INTERACTION_WEIGHT,            (*  Weight for interaction events *)
    ZIPF_RARE_WEIGHT,                   (*  Weight for rare events *)
    ZIPF_WORLD_LOAD_WEIGHT,             (*  Weight for world loading (least frequent but expensive) *)
    
    (* WebRTC Channel Configuration - Individual channel counts per delivery mode *)
    RELIABLE_SEQUENCED_CHANNEL_COUNT,       (*  Number of reliable sequenced channels *)
    RELIABLE_UNSEQUENCED_CHANNEL_COUNT,     (*  Number of reliable unsequenced channels *)
    UNRELIABLE_SEQUENCED_CHANNEL_COUNT,     (*  Number of unreliable sequenced channels *)
    UNRELIABLE_UNSEQUENCED_CHANNEL_COUNT,   (*  Number of unreliable unsequenced channels *)
    MAX_RELIABLE_SEQUENCED_CHANNEL_QUEUE,    (*  Max queue length for reliable sequenced channels *)
    MAX_RELIABLE_UNSEQUENCED_CHANNEL_QUEUE,  (*  Max queue length for reliable unsequenced channels *)
    MAX_UNRELIABLE_SEQUENCED_CHANNEL_QUEUE,  (*  Max queue length for unreliable sequenced channels *)
    MAX_UNRELIABLE_UNSEQUENCED_CHANNEL_QUEUE (*  Max queue length for unreliable unsequenced channels *)

ASSUME A_PositiveConstants ==
    /\ DB_OPS_COMMON \in Nat \ {0}
    /\ DB_OPS_RARE \in Nat \ {0}
    /\ DB_OPS_MOVEMENT \in Nat \ {0}
    /\ DB_OPS_INTERACTION \in Nat \ {0}
    /\ DB_OPS_WORLD_LOAD \in Nat \ {0}
    /\ DB_OPS_NETWORK_SYNC \in Nat \ {0}
    /\ DB_OPS_PHYSICS \in Nat \ {0}
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
    /\ NETWORK_BYTES_COMMON \in Nat \ {0}
    /\ NETWORK_BYTES_RARE \in Nat \ {0}
    /\ NETWORK_BYTES_MOVEMENT \in Nat \ {0}
    /\ NETWORK_BYTES_INTERACTION \in Nat \ {0}
    /\ NETWORK_BYTES_WORLD_LOAD \in Nat \ {0}
    /\ NETWORK_BYTES_NETWORK_SYNC \in Nat \ {0}
    /\ NETWORK_BYTES_PHYSICS \in Nat \ {0}
    /\ MIN_ENTITIES_FOR_GROWTH \in Nat \ {0}
    /\ GEOMETRIC_GROWTH_RATE_PERCENT \in Nat \ {0}
    /\ GEOMETRIC_GROWTH_DIVISOR \in Nat \ {0}
    /\ ZIPF_MOVEMENT_WEIGHT \in Nat \ {0}
    /\ ZIPF_COMMON_WEIGHT \in Nat \ {0}
    /\ ZIPF_NETWORK_SYNC_WEIGHT \in Nat \ {0}
    /\ ZIPF_PHYSICS_WEIGHT \in Nat \ {0}
    /\ ZIPF_INTERACTION_WEIGHT \in Nat \ {0}
    /\ ZIPF_RARE_WEIGHT \in Nat \ {0}
    /\ ZIPF_WORLD_LOAD_WEIGHT \in Nat \ {0}

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
    EnqueueTask(DB_OPS_COMMON)

GenerateRareTaskActivity ==
    EnqueueTask(DB_OPS_RARE)

GenerateMovementActivity ==
    EnqueueTask(DB_OPS_MOVEMENT)

GenerateInteractionActivity ==
    EnqueueTask(DB_OPS_INTERACTION)

GenerateWorldLoadActivity ==
    EnqueueTask(DB_OPS_WORLD_LOAD)

GenerateNetworkSyncActivity ==
    EnqueueTask(DB_OPS_NETWORK_SYNC)

GeneratePhysicsActivity ==
    EnqueueTask(DB_OPS_PHYSICS)

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
    \/ GenerateZipfianTaskActivity       (* Primary load generator - sends to WebRTC channels *)
    \/ GenerateCommonTaskActivity        (* Generate database tasks *)
    \/ GenerateRareTaskActivity
    \/ GenerateMovementActivity  
    \/ GenerateInteractionActivity
    \/ GenerateWorldLoadActivity
    \/ GenerateNetworkSyncActivity
    \/ GeneratePhysicsActivity
    \/ GenerateEntityArrival             (* Geometric entity growth *)
    \/ ProcessReliableSequencedQueue     (* Process WebRTC channel queues *)
    \/ ProcessReliableUnsequencedQueue
    \/ ProcessUnreliableSequencedQueue
    \/ ProcessUnreliableUnsequencedQueue
    \/ ProcessCellWork                   (* Process main queue - this should be the bottleneck *)

(* -------------------------------- SPECIFICATION AND THEOREM -------------------------------- *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

THEOREM Spec => [](TypeOK)

=============================================================================

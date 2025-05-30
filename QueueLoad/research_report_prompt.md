1. In AV1, the macroblock multitype tree is a flexible mechanism for dividing video frames into blocks for encoding and decoding. It allows for different block sizes and types to be used within a single frame, adapting to the complexity of the video content. This tree structure allows for various prediction methods (intra and inter) to be applied to different parts of the frame, optimizing compression efficiency. I mean the tree that switches the different types of blocks to parition a video frame and not between video frames. "Multitype tree" in 3d for partitioned cells that have layers that are used like sim city to simulate water, and power and shadow layers that are like materialized views.

2. left-child right-sibling binary tree can be used on any tree for benefits.

```
---- MODULE QueueLoad ----


EXTENDS Integers, Sequences, FiniteSets, TLC


CONSTANTS

    MIN_ENTITIES_FOR_MERGE,

    MAX_QUEUE_LENGTH_PER_CELL,

    MIN_QUEUE_LENGTH_FOR_MERGE,

    DATABASE_OPS_PER_STEP,

    RELIABLE_SEQUENCED_CHANNEL_COUNT,

    RELIABLE_UNSEQUENCED_CHANNEL_COUNT,

    UNRELIABLE_SEQUENCED_CHANNEL_COUNT,

    UNRELIABLE_UNSEQUENCED_CHANNEL_COUNT,

    MAX_RELIABLE_SEQUENCED_CHANNEL_QUEUE,

    MAX_RELIABLE_UNSEQUENCED_CHANNEL_QUEUE,

    MAX_UNRELIABLE_SEQUENCED_CHANNEL_QUEUE,

    MAX_UNRELIABLE_UNSEQUENCED_CHANNEL_QUEUE


DB_OPS_COMMON == 1

MIN_ENTITIES_FOR_GROWTH == 3

GEOMETRIC_GROWTH_RATE_PERCENT == 2

GEOMETRIC_GROWTH_DIVISOR == 100

BASELINE_ENTITIES == 5


VARIABLES

    cell_data,

    channels_reliable_sequenced,

    channels_reliable_unsequenced,

    channels_unreliable_sequenced,

    channels_unreliable_unsequenced


vars == <<cell_data, channels_reliable_sequenced, channels_reliable_unsequenced,

          channels_unreliable_sequenced, channels_unreliable_unsequenced>>


CellType == [numEntities : Nat, requestQueue : Seq(Nat)]

ChannelType == [queue : Seq(Nat), dropped : Nat]


TypeOK ==

    /\ cell_data \in CellType

    /\ cell_data.numEntities >= 0


QueueCapacityInvariant ==

    Len(cell_data.requestQueue) <= MAX_QUEUE_LENGTH_PER_CELL


OverloadManagementInvariant ==

    Len(cell_data.requestQueue) <= MAX_QUEUE_LENGTH_PER_CELL


Init ==

    /\ cell_data = [numEntities |-> BASELINE_ENTITIES, requestQueue |-> << >>]

    /\ channels_reliable_sequenced = [i \in 1..RELIABLE_SEQUENCED_CHANNEL_COUNT |-> [queue |-> << >>, dropped |-> 0]]

    /\ channels_reliable_unsequenced = [i \in 1..RELIABLE_UNSEQUENCED_CHANNEL_COUNT |-> [queue |-> << >>, dropped |-> 0]]

    /\ channels_unreliable_sequenced = [i \in 1..UNRELIABLE_SEQUENCED_CHANNEL_COUNT |-> [queue |-> << >>, dropped |-> 0]]

    /\ channels_unreliable_unsequenced = [i \in 1..UNRELIABLE_UNSEQUENCED_CHANNEL_COUNT |-> [queue |-> << >>, dropped |-> 0]]


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

    /\ Len(cell_data.requestQueue) < MAX_QUEUE_LENGTH_PER_CELL

    /\ LET tasks_per_entity == CASE DATABASE_OPS_PER_STEP <= 1 -> 5    (* 5 tasks per entity - very aggressive *)

                                [] DATABASE_OPS_PER_STEP <= 10 -> 3   (* 3 tasks per entity - aggressive *)

                                [] DATABASE_OPS_PER_STEP <= 50 -> 2   (* 2 tasks per entity - moderate *)

                                [] DATABASE_OPS_PER_STEP <= 200 -> 1  (* 1 task per entity - light *)

                                [] OTHER -> 1                          (* 1 task per entity minimum *)

           tasks_to_generate == cell_data.numEntities * tasks_per_entity

       IN EnqueueTask(tasks_to_generate)


GenerateEntityArrival ==

    /\ cell_data.numEntities < 25

    /\ LET current_entities == cell_data.numEntities

           geometric_increment == IF current_entities < MIN_ENTITIES_FOR_GROWTH THEN 1

                                 ELSE (current_entities * GEOMETRIC_GROWTH_RATE_PERCENT) \div GEOMETRIC_GROWTH_DIVISOR

           actual_increment == IF geometric_increment < 1 THEN 1 ELSE geometric_increment

       IN AddEntitiesToCell(actual_increment)


ProcessCellWork ==

    /\ Len(cell_data.requestQueue) > 0

    /\ LET first_task == Head(cell_data.requestQueue)

       IN /\ first_task <= DATABASE_OPS_PER_STEP

          /\ cell_data' = [cell_data EXCEPT !.requestQueue = Tail(cell_data.requestQueue)]

          /\ UNCHANGED <<channels_reliable_sequenced, channels_reliable_unsequenced,

                         channels_unreliable_sequenced, channels_unreliable_unsequenced>>


Next ==

    \/ ProcessCellWork

    \/ GenerateCommonTaskActivity

    \/ GenerateEntityArrival


Spec == Init /\ [][Next]_vars


THEOREM Spec => [](TypeOK)


=============================================================================

```

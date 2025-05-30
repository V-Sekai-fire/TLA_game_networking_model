---- MODULE QueueLoad ----

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    TaskImpact_Common,        (*  Load impact of a common task. *)
    TaskImpact_Rare,          (*  Load impact of a rare, high-impact task. *)
    CellProcessingCapacity,   (*  Max total task impact processed by a cell in one ProcessCellWork step. *)
    BaselineEntities          (*  Initial entity count for the root cell. *)

ASSUME A_QueueConstantsPositive ==
    /\ TaskImpact_Common \in Nat \ {0}
    /\ TaskImpact_Rare \in Nat \ {0}
    /\ CellProcessingCapacity \in Nat \ {0}
ASSUME A_ImpactHierarchy        ==
    TaskImpact_Rare >= TaskImpact_Common
ASSUME A_BaselineEntitiesPositive ==
    BaselineEntities \in Nat

VARIABLES cell_data (*  Record for the single cell: [numEntities: Nat, requestQueue: Seq(Nat)] *)

vars == <<cell_data>>

(*  ----------------------------- TYPE DEFINITIONS AND HELPERS ----------------------------- *)
CellType == [numEntities : Nat,
             requestQueue : Seq(Nat) ] (*  Nat here is TaskImpact *)

TypeOK ==
    /\ cell_data \in CellType
    /\ cell_data.numEntities >= 0
    /\ \A i \in 1..Len(cell_data.requestQueue) : cell_data.requestQueue[i] \in Nat \ {0}

(*  ------------------------------------ INITIALIZATION ------------------------------------ *)
Init ==
    /\ cell_data = [ numEntities  |-> BaselineEntities,
                    requestQueue |-> << >> ]

(*  --------------------------------------- ACTIONS ---------------------------------------- *)

(*  --- Actions to simulate task generation and enqueueing --- *)
EnqueueTask(task_impact) ==
    /\ task_impact \in Nat \ {0}
    /\ cell_data' = [cell_data EXCEPT !.requestQueue = Append(cell_data.requestQueue, task_impact)]

AddEntitiesToCell(entity_increment) ==
    /\ entity_increment \in Nat \ {0}
    /\ cell_data' = [cell_data EXCEPT !.numEntities = cell_data.numEntities + entity_increment]

GenerateCommonTaskActivity ==
    EnqueueTask(TaskImpact_Common)

GenerateRareTaskActivity ==
    EnqueueTask(TaskImpact_Rare)

GenerateEntityArrival == (*  Action to increase numEntities *)
    AddEntitiesToCell(1) (*  Adds 1 entity, can be parameterized *)

(*  --- Action to simulate cell processing its queue --- *)
ProcessCellWork ==
    /\ Len(cell_data.requestQueue) > 0
    /\ LET (*  Find how many tasks can be processed within capacity *)
           ProcessedTasks(remaining_capacity, processed_count, queue_index) ==
               IF queue_index > Len(cell_data.requestQueue) THEN processed_count
               ELSE IF cell_data.requestQueue[queue_index] <= remaining_capacity 
                    THEN ProcessedTasks(remaining_capacity - cell_data.requestQueue[queue_index], 
                                      processed_count + 1, 
                                      queue_index + 1)
                    ELSE processed_count
           num_processed_tasks == ProcessedTasks(CellProcessingCapacity, 0, 1)
       IN /\ num_processed_tasks > 0
          /\ cell_data' = [cell_data EXCEPT !.requestQueue = SubSeq(cell_data.requestQueue, num_processed_tasks + 1, Len(cell_data.requestQueue))]

Next ==
    \/ GenerateCommonTaskActivity
    \/ GenerateRareTaskActivity
    \/ GenerateEntityArrival
    \/ ProcessCellWork

(* ------------------------------------ INVARIANTS ------------------------------------ *)
(*  Only TypeOK remains as partitioning and related overload management are removed. *)

(* -------------------------------- SPECIFICATION AND THEOREM -------------------------------- *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

THEOREM Spec => [](TypeOK)

=============================================================================

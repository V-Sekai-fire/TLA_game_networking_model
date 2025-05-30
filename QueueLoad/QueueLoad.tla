---- MODULE QueueLoad ----

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    TaskImpact_Common,        (*  Load impact of a common task. *)
    TaskImpact_Rare,          (*  Load impact of a rare, high-impact task. *)
    TaskImpact_Movement,      (*  Player/avatar movement updates *)
    TaskImpact_Interaction,   (*  Object interaction events *)
    TaskImpact_WorldLoad,     (*  Loading world assets/geometry *)
    TaskImpact_NetworkSync,   (*  Network state synchronization *)
    TaskImpact_Physics,       (*  Physics simulation updates *)
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

(* Invariant to test queue capacity limits - model checking will fail when queue gets too long *)
QueueCapacityInvariant ==
    Len(cell_data.requestQueue) <= 10

(* Invariant to test entity growth limits *)
EntityCapacityInvariant ==
    cell_data.numEntities <= 100  (* Adjust this limit to test different thresholds *)

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

(* -------------------------------- SPECIFICATION AND THEOREM -------------------------------- *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

THEOREM Spec => [](TypeOK)

=============================================================================

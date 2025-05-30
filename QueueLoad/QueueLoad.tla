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
    BaselineEntities          (*  Initial entity count for the root cell. *)

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
ASSUME A_ImpactHierarchy ==
    TaskImpact_Rare >= TaskImpact_Common
ASSUME A_MaxEntitiesSensible ==
    MaxEntitiesPerCell >= BaselineEntities
ASSUME A_MaxQueueSensible ==
    MaxQueueLengthPerCell > 0

VARIABLES 
    cell_data,        (*  Record for the single cell: [numEntities: Nat, requestQueue: Seq(Nat)] *)
    overload_state,   (*  Track if cell is overloaded: BOOLEAN *)
    merge_eligible    (*  Track if cell is eligible for merge: BOOLEAN *)

vars == <<cell_data, overload_state, merge_eligible>>

(*  ----------------------------- TYPE DEFINITIONS AND HELPERS ----------------------------- *)
CellType == [numEntities : Nat,
             requestQueue : Seq(Nat) ] (*  Nat here is TaskImpact *)

TypeOK ==
    /\ cell_data \in CellType
    /\ cell_data.numEntities >= 0
    /\ \A i \in 1..Len(cell_data.requestQueue) : cell_data.requestQueue[i] \in Nat \ {0}
    /\ overload_state \in BOOLEAN
    /\ merge_eligible \in BOOLEAN

(* Helper functions for load management *)
IsOverloaded(cell) ==
    cell.numEntities > MaxEntitiesPerCell \/ Len(cell.requestQueue) > MaxQueueLengthPerCell

IsMergeEligible(cell) ==
    cell.numEntities < MinEntitiesForMerge /\ Len(cell.requestQueue) < MinQueueLengthForMerge

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

(*  --------------------------------------- ACTIONS ---------------------------------------- *)

(*  --- Actions to simulate task generation and enqueueing --- *)
EnqueueTask(task_impact) ==
    /\ task_impact \in Nat \ {0}
    /\ cell_data' = [cell_data EXCEPT !.requestQueue = Append(cell_data.requestQueue, task_impact)]
    /\ overload_state' = IsOverloaded(cell_data')
    /\ merge_eligible' = IsMergeEligible(cell_data')

AddEntitiesToCell(entity_increment) ==
    /\ entity_increment \in Nat \ {0}
    /\ cell_data' = [cell_data EXCEPT !.numEntities = cell_data.numEntities + entity_increment]
    /\ overload_state' = IsOverloaded(cell_data')
    /\ merge_eligible' = IsMergeEligible(cell_data')

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

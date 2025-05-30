---- MODULE MultiTypeTreePartitioningAV1_3D_QueueLoad ----

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Regions, RootRegion, MaxDepth, MinBlockSize, RegionShapeType, PartitionStrategies

    MaxEntitiesPerCell,       \* Max entities a cell can hold before considering a split (static density).
    MinEntitiesForMerge,    \* If sum of children's entities is below this, merging is considered.

    MaxQueueLengthPerCell,    \* Max request queue length a cell can have before needing a split.
    MinQueueLengthForMerge,   \* If sum of children's queue lengths is below this, merging is considered.

    TaskImpact_Common,        \* Load impact of a common task.
    TaskImpact_Rare,          \* Load impact of a rare, high-impact task.

    CellProcessingCapacity,   \* Max total task impact processed by a cell in one ProcessCellWork step.
    BaselineEntities          \* Initial entity count for the root cell.


ASSUMPTIONS
    A_RootRegionInRegions :: RootRegion \in Regions
    A_MaxDepthPositive    :: MaxDepth \in Nat /\ MaxDepth > 0
    A_MinBlockSizePositive:: MinBlockSize \in Pos
    A_RegionShapeType     :: RegionShapeType = {"Cube", "RectPrism"}
    A_Strategies          :: PartitionStrategies = {"OctreeSplit", "BinarySplitX", "BinarySplitY", "BinarySplitZ"}
    A_RegionsNonEmpty     :: Regions /= {}
    \* Load constant assumptions
    A_EntityConstantsPositive:: /\ MaxEntitiesPerCell \in Pos
                              /\ MinEntitiesForMerge \in Nat
                              /\ BaselineEntities \in Nat
    A_QueueConstantsPositive :: /\ MaxQueueLengthPerCell \in Pos
                              /\ MinQueueLengthForMerge \in Nat
                              /\ TaskImpact_Common \in Pos
                              /\ TaskImpact_Rare \in Pos
                              /\ CellProcessingCapacity \in Pos
    A_ImpactHierarchy        :: TaskImpact_Rare >= TaskImpact_Common
    A_MaxEntitiesSensible  :: MaxEntitiesPerCell >= BaselineEntities
    A_MaxQueueSensible     :: MaxQueueLengthPerCell > 0


VARIABLES
    cells,            \* Set of cell records.
    activePartitions, \* Set of cell IDs that are current leaf nodes.
    next_cell_id      \* Counter for unique cell IDs.

vars == <<cells, activePartitions, next_cell_id>>

----------------------------- ABSTRACT REGION LOGIC (as before) -----------------------------
CONSTANT GetRegionShape(region \in Regions) : RegionShapeType
CONSTANT GetRegionDimensions(region \in Regions) : Seq(Int)
CONSTANT SplitFunction(region \in Regions, strategy \in PartitionStrategies) : Seq(Regions)
CONSTANT RegionsCover(regionSet \subseteq Regions, targetRegion \in Regions) : BOOLEAN
CONSTANT RegionsDisjoint(regionSet \subseteq Regions) : BOOLEAN
CONSTANT RegionContainedIn(region1 \in Regions, region2 \in Regions) : BOOLEAN

AXIOMS "Properties of Abstract Region Logic" (Same as before, ensures geometric consistency)
    Axiom_RegionDimsLength :: \A r \in Regions : Len(GetRegionDimensions(r)) = 3
    Axiom_RegionDimsPositive :: \A r \in Regions : \A i \in 1..3 : GetRegionDimensions(r)[i] \in Pos
    Axiom_RootShape :: GetRegionShape(RootRegion) = "Cube"
    Axiom_RootDimsAreMinSizeOrLarger :: \A i \in 1..3 : GetRegionDimensions(RootRegion)[i] >= MinBlockSize
    Axiom_SplitCoverage :: \A r \in Regions, s \in PartitionStrategies : Len(SplitFunction(r,s)) > 0 => RegionsCover(AsSet(SplitFunction(r,s)), r)
    Axiom_SplitDisjoint :: \A r \in Regions, s \in PartitionStrategies : Len(SplitFunction(r,s)) > 0 => RegionsDisjoint(AsSet(SplitFunction(r,s)))
    Axiom_ChildContainedInParent :: \A r \in Regions, s \in PartitionStrategies, child_r \in AsSet(SplitFunction(r,s)) : RegionContainedIn(child_r, r)
    Axiom_RootCover :: RegionsCover({RootRegion}, RootRegion)
    Axiom_OctreeSplit_ParentShape :: \A r \in Regions : Len(SplitFunction(r, "OctreeSplit")) > 0 => GetRegionShape(r) = "Cube"
    Axiom_OctreeSplit_ChildShape :: \A r \in Regions, child_r \in AsSet(SplitFunction(r, "OctreeSplit")) : GetRegionShape(child_r) = "Cube"
    Axiom_OctreeSplit_ChildDimensions :: \A r \in Regions: LET parent_dims == GetRegionDimensions(r) IN \A child_r \in AsSet(SplitFunction(r, "OctreeSplit")) : LET child_dims == GetRegionDimensions(child_r) IN /\ child_dims[1] = parent_dims[1] / 2 /\ child_dims[2] = parent_dims[2] / 2 /\ child_dims[3] = parent_dims[3] / 2
    Axiom_OctreeSplit_NumChildren :: \A r \in Regions : GetRegionShape(r) = "Cube" /\ (GetRegionDimensions(r)[1] / 2 >= MinBlockSize) => Len(SplitFunction(r, "OctreeSplit")) = 8 \/ Len(SplitFunction(r, "OctreeSplit")) = 0
    Axiom_BinarySplitX_ParentShape :: \A r \in Regions : Len(SplitFunction(r, "BinarySplitX")) > 0 => GetRegionShape(r) \in {"Cube", "RectPrism"}
    Axiom_BinarySplitX_ChildDimensions :: \A r \in Regions: LET parent_dims == GetRegionDimensions(r) IN \A child_r \in AsSet(SplitFunction(r, "BinarySplitX")) : LET child_dims == GetRegionDimensions(child_r) IN /\ child_dims[1] = parent_dims[1] / 2 /\ child_dims[2] = parent_dims[2] /\ child_dims[3] = parent_dims[3]
    Axiom_BinarySplitX_NumChildren :: \A r \in Regions : (GetRegionDimensions(r)[1] / 2 >= MinBlockSize) => Len(SplitFunction(r, "BinarySplitX")) = 2 \/ Len(SplitFunction(r, "BinarySplitX")) = 0
    Axiom_BinarySplitY_ParentShape :: \A r \in Regions : Len(SplitFunction(r, "BinarySplitY")) > 0 => GetRegionShape(r) \in {"Cube", "RectPrism"}
    Axiom_BinarySplitY_ChildDimensions :: \A r \in Regions: LET parent_dims == GetRegionDimensions(r) IN \A child_r \in AsSet(SplitFunction(r, "BinarySplitY")) : LET child_dims == GetRegionDimensions(child_r) IN /\ child_dims[1] = parent_dims[1] /\ child_dims[2] = parent_dims[2] / 2 /\ child_dims[3] = parent_dims[3]
    Axiom_BinarySplitY_NumChildren :: \A r \in Regions : (GetRegionDimensions(r)[2] / 2 >= MinBlockSize) => Len(SplitFunction(r, "BinarySplitY")) = 2 \/ Len(SplitFunction(r, "BinarySplitY")) = 0
    Axiom_BinarySplitZ_ParentShape :: \A r \in Regions : Len(SplitFunction(r, "BinarySplitZ")) > 0 => GetRegionShape(r) \in {"Cube", "RectPrism"}
    Axiom_BinarySplitZ_ChildDimensions :: \A r \in Regions: LET parent_dims == GetRegionDimensions(r) IN \A child_r \in AsSet(SplitFunction(r, "BinarySplitZ")) : LET child_dims == GetRegionDimensions(child_r) IN /\ child_dims[1] = parent_dims[1] /\ child_dims[2] = parent_dims[2] /\ child_dims[3] = parent_dims[3] / 2
    Axiom_BinarySplitZ_NumChildren :: \A r \in Regions : (GetRegionDimensions(r)[3] / 2 >= MinBlockSize) => Len(SplitFunction(r, "BinarySplitZ")) = 2 \/ Len(SplitFunction(r, "BinarySplitZ")) = 0

----------------------------- TYPE DEFINITIONS AND HELPERS -----------------------------
CellType == [id: Nat, region: Regions, parent: Nat \union {NIL}, children: SUBSET Nat,
             level: -1..MaxDepth, strategyUsed: PartitionStrategies \union {NIL},
             numEntities : Nat,
             requestQueue : Seq(Nat) ] \* Nat here is TaskImpact

TypeOK ==
    /\ cells \subseteq CellType
    /\ \A c \in cells : c.numEntities >= 0
    /\ \A c \in cells : \A task_impact \in AsSet(c.requestQueue) : task_impact \in Pos \* Task impacts are positive
    /\ activePartitions \subseteq {c.id : c \in cells}
    /\ next_cell_id \in Nat

Cell(cid, c_set) == CHOOSE c \in c_set : c.id = cid

SumSet(S) == IF S = {} THEN 0 ELSE LET x = CHOOSE y \in S : TRUE IN x + SumSet(S \ {x})

\* Helper to concatenate queues of a set of children cells
ConcatenateChildrenQueues(children_ids_set, c_set) ==
    LET GetQueue(cid) == Cell(cid, c_set).requestQueue
    IN IF children_ids_set = {} THEN
        << >>
    ELSE \* This needs a defined order or a more complex fold. For simplicity, we can pick one and append.
         \* A proper way is to convert set to seq first, then fold.
         \* For now, let's assume a way to iterate and append:
         LET cid = CHOOSE id \in children_ids_set : TRUE
         IN GetQueue(cid) \o ConcatenateChildrenQueues(children_ids_set \ {cid}, c_set)

------------------------------------ INITIALIZATION ------------------------------------
Init ==
    /\ next_cell_id = 1
    /\ LET root_cell == [ id           |-> 0,
                          region       |-> RootRegion,
                          parent       |-> NIL,
                          children     |-> {},
                          level        |-> 0,
                          strategyUsed |-> NIL,
                          numEntities  |-> BaselineEntities,
                          requestQueue |-> << >> ]
       IN cells = {root_cell}
    /\ activePartitions = {0}

--------------------------------------- ACTIONS ----------------------------------------

\* --- Actions to simulate task generation and enqueueing ---
EnqueueTask(cell_id_to_load, task_impact) ==
    /\ cell_id_to_load \in activePartitions
    /\ task_impact \in Pos
    /\ LET cell == Cell(cell_id_to_load, cells)
       IN /\ cells' = (cells \ {cell}) \cup {[cell EXCEPT !.requestQueue = Append(cell.requestQueue, task_impact)]}
          /\ UNCHANGED <<activePartitions, next_cell_id, vars["cells"][!"numEntities"]>>  \* numEntities not changed by task enqueue.

AddEntitiesToCell(cell_id_to_load, entity_increment) ==
    /\ cell_id_to_load \in activePartitions
    /\ entity_increment \in Pos
    /\ LET cell == Cell(cell_id_to_load, cells)
       IN /\ cells' = (cells \ {cell}) \cup {[cell EXCEPT !.numEntities = cell.numEntities + entity_increment]}
          /\ UNCHANGED <<activePartitions, next_cell_id, vars["cells"][!"requestQueue"]>>

GenerateCommonTaskActivity ==
    /\ activePartitions /= {}
    /\ \E cell_id \in activePartitions : EnqueueTask(cell_id, TaskImpact_Common)

GenerateRareTaskActivity ==
    /\ activePartitions /= {}
    /\ \E cell_id \in activePartitions : EnqueueTask(cell_id, TaskImpact_Rare)

GenerateEntityArrival == \* Action to increase numEntities
    /\ activePartitions /= {}
    /\ \E cell_id \in activePartitions : AddEntitiesToCell(cell_id, 1) \* Adds 1 entity, can be parameterized


\* --- Action to simulate cell processing its queue ---
ProcessCellWork(cell_id_to_process) ==
    /\ cell_id_to_process \in activePartitions
    /\ LET cell == Cell(cell_id_to_process, cells)
       IN /\ Len(cell.requestQueue) > 0
          /\ LET processed_impact_sum = 0
                 tasks_to_remove_count = 0
                 temp_queue = cell.requestQueue
                 \* Iterate through queue to see how many tasks can be processed
                 \* This is procedural. A functional way in TLA+:
                 \* Find k such that Sum of first k task_impacts <= CellProcessingCapacity
                 \* And Sum of first k+1 task_impacts > CellProcessingCapacity
                 \* For simplicity, let's process a fixed number of tasks if total impact allows, or fewer.
                 \* Or, more simply, process up to N tasks OR total impact X.
                 \* Let's process tasks whose cumulative impact is within capacity.
                 CanProcess(q, capacity_left, count) == \* Returns number of tasks processed from head.
                     IF q = << >> THEN count
                     ELSE IF Head(q) <= capacity_left THEN CanProcess(Tail(q), capacity_left - Head(q), count + 1)
                     ELSE count
                 num_processed_tasks == CanProcess(cell.requestQueue, CellProcessingCapacity, 0)
             IN /\ cells' = (cells \ {cell}) \cup
                           {[cell EXCEPT !.requestQueue = SubSeq(cell.requestQueue, num_processed_tasks + 1, Len(cell.requestQueue))]}
                /\ UNCHANGED <<activePartitions, next_cell_id, vars["cells"][!"numEntities"]>>


\* --- Modified Split action with load/queue consideration ---
Split(cell_id_to_split, strategy) ==
    /\ cell_id_to_split \in activePartitions
    /\ LET parent_cell == Cell(cell_id_to_split, cells)
       parent_region == parent_cell.region
       parent_shape == GetRegionShape(parent_region)
       parent_dims == GetRegionDimensions(parent_region)
       IN /\ (parent_cell.numEntities > MaxEntitiesPerCell \/ Len(parent_cell.requestQueue) > MaxQueueLengthPerCell)  \* <--- LOAD/QUEUE PRECONDITION
          /\ parent_cell.level < MaxDepth
          /\ strategy \in PartitionStrategies
          /\ CASE strategy OF \* Dimension/shape preconditions
                "OctreeSplit" -> /\ parent_shape = "Cube" /\ parent_dims[1] / 2 >= MinBlockSize /\ parent_dims[2] / 2 >= MinBlockSize /\ parent_dims[3] / 2 >= MinBlockSize
             [] "BinarySplitX" -> parent_dims[1] / 2 >= MinBlockSize
             [] "BinarySplitY" -> parent_dims[2] / 2 >= MinBlockSize
             [] "BinarySplitZ" -> parent_dims[3] / 2 >= MinBlockSize
             [] OTHER -> FALSE
          /\ LET new_region_seq == SplitFunction(parent_region, strategy)
             IN /\ Len(new_region_seq) > 0
                /\ LET num_children == Len(new_region_seq)
                       child_entities == IF num_children > 0 THEN parent_cell.numEntities / num_children ELSE BaselineEntities
                       \* For simplicity, children start with empty queues. Parent's queue is implicitly "resolved" by split.
                       new_children_records ==
                           { [ id           |-> next_cell_id + i - 1,
                               region       |-> new_region_seq[i],
                               parent       |-> cell_id_to_split,
                               children     |-> {},
                               level        |-> parent_cell.level + 1,
                               strategyUsed |-> NIL,
                               numEntities  |-> child_entities,
                               requestQueue |-> << >>
                             ] : i \in 1..num_children }
                   new_children_ids == {r.id : r \in new_children_records}
                   IN /\ cells' = (cells \ {parent_cell}) \cup
                                 {[parent_cell EXCEPT !.children = new_children_ids, !.strategyUsed = strategy]} \cup \* Parent still has its old queue/entities
                                 new_children_records
                      /\ activePartitions' = (activePartitions \ {cell_id_to_split}) \cup new_children_ids
                      /\ next_cell_id' = next_cell_id + num_children

\* --- Modified Merge action with load/queue consideration ---
Merge(parent_id_to_activate) ==
    /\ parent_id_to_activate \notin activePartitions
    /\ LET parent_cell_record == Cell(parent_id_to_activate, cells) \* Temp name to avoid conflict with !.
       IN /\ parent_cell_record.children /= {}
          /\ \A child_id \in parent_cell_record.children : child_id \in activePartitions
          /\ LET children_entity_counts == {Cell(child_id, cells).numEntities : child_id \in parent_cell_record.children}
                 sum_children_entities == SumSet(children_entity_counts)
                 children_queues_lengths == {Len(Cell(child_id, cells).requestQueue) : child_id \in parent_cell_record.children}
                 sum_children_queue_lengths == SumSet(children_queues_lengths)
             IN /\ sum_children_entities < MinEntitiesForMerge
                /\ sum_children_queue_lengths < MinQueueLengthForMerge
                /\ LET children_ids_to_remove == parent_cell_record.children
                       \* Concatenate queues. This needs a deterministic way.
                       \* For simplicity, assuming an operator ConcatAllQueues(set_of_child_ids, current_cells)
                       merged_queue == ConcatenateChildrenQueues(children_ids_to_remove, cells)
                       updated_parent_record == [parent_cell_record EXCEPT
                                                     !.children = {},
                                                     !.strategyUsed = NIL,
                                                     !.numEntities = sum_children_entities,
                                                     !.requestQueue = merged_queue ]
                   IN /\ cells' = ({c \in cells : c.id \notin children_ids_to_remove} \setminus {parent_cell_record}) \cup {updated_parent_record}
                      /\ activePartitions' = (activePartitions \ children_ids_to_remove) \cup {parent_id_to_activate}
                      /\ UNCHANGED <<next_cell_id>>

Next ==
    \/ (\E cell_id \in activePartitions, strategy \in PartitionStrategies : Split(cell_id, strategy))
    \/ (\E parent_id \in {c.id : c \in cells WHERE Cardinality(Cell(c.id,cells).children)>0 } : Merge(parent_id))
    \/ GenerateCommonTaskActivity
    \/ GenerateRareTaskActivity
    \/ GenerateEntityArrival
    \/ (\E cell_id \in activePartitions : ProcessCellWork(cell_id))


------------------------------------ INVARIANTS ------------------------------------
Invariant_CellStructure == (* Same as before *)
    /\ \A c \in cells:
        /\ (c.parent /= NIL => c.parent \in {p.id : p \in cells})
        /\ (c.parent /= NIL => c.id \in Cell(c.parent, cells).children)
        /\ \A child_id \in c.children : child_id \in {ch.id : ch \in cells}
        /\ \A child_id \in c.children : Cell(child_id, cells).parent = c.id
        /\ (c.parent = NIL => c.level = 0)
        /\ (c.parent /= NIL => c.level = Cell(c.parent, cells).level + 1)
        /\ c.level <= MaxDepth
        /\ (c.id \in activePartitions => Cardinality(c.children) = 0)
        /\ (c.id \notin activePartitions /\ c.level < MaxDepth => Cardinality(c.children) > 0)
        /\ (Cardinality(c.children) > 0 => c.strategyUsed \in PartitionStrategies)
        /\ (Cardinality(c.children) = 0 => c.strategyUsed = NIL)

Invariant_ActivePartitionProperties == (* Same as before *)
    /\ RegionsCover({Cell(id, cells).region : id \in activePartitions}, RootRegion)
    /\ RegionsDisjoint({Cell(id, cells).region : id \in activePartitions})

Invariant_RegionProperties ==  (* Same as before *)
    \A c \in cells :
        /\ Len(GetRegionDimensions(c.region)) = 3
        /\ \A i \in 1..3 : GetRegionDimensions(c.region)[i] \in Pos
        /\ GetRegionShape(c.region) \in RegionShapeType

Invariant_BlockMinSize == (* Same as before *)
    \A act_id \in activePartitions :
        LET cell == Cell(act_id, cells)
            dims == GetRegionDimensions(cell.region)
        IN /\ dims[1] >= MinBlockSize
           /\ dims[2] >= MinBlockSize
           /\ dims[3] >= MinBlockSize

\* --- New Invariant for Queue and Entity Management ---
IsSplitPossibleForCell(cell_record) ==
    cell_record.level < MaxDepth /\
    (\E strategy \in PartitionStrategies :
        LET parent_shape == GetRegionShape(cell_record.region), parent_dims == GetRegionDimensions(cell_record.region) IN
        CASE strategy OF
            "OctreeSplit" -> /\ parent_shape = "Cube" /\ parent_dims[1] / 2 >= MinBlockSize /\ parent_dims[2] / 2 >= MinBlockSize /\ parent_dims[3] / 2 >= MinBlockSize
         [] "BinarySplitX" -> parent_dims[1] / 2 >= MinBlockSize
         [] "BinarySplitY" -> parent_dims[2] / 2 >= MinBlockSize
         [] "BinarySplitZ" -> parent_dims[3] / 2 >= MinBlockSize
         [] OTHER -> FALSE
    )

Invariant_OverloadManagement ==
    \A act_id \in activePartitions :
      LET cell == Cell(act_id, cells) IN
        IF cell.numEntities > MaxEntitiesPerCell \/ Len(cell.requestQueue) > MaxQueueLengthPerCell THEN
            IsSplitPossibleForCell(cell)
        ELSE TRUE

-------------------------------- SPECIFICATION AND THEOREM --------------------------------
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

THEOREM Spec => [](TypeOK /\ Invariant_CellStructure /\ Invariant_ActivePartitionProperties /\ Invariant_RegionProperties /\ Invariant_BlockMinSize /\ Invariant_OverloadManagement)

=============================================================================

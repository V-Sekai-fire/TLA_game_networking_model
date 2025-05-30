# VR Game Infrastructure Protocol Verification

This directory contains TLA+ model configurations for verifying the logical correctness of VR game networking protocols under different resource constraints.

## TLA+ Model Purpose

**Primary Goal**: Find logical errors in protocol design through formal verification
- Aggressive abstraction of complex systems into bounded models
- Focus on correctness properties (safety, liveness) rather than performance
- Small, bounded parameter spaces to enable exhaustive state exploration

**Not For**: Performance testing or realistic load simulation (use dedicated simulation tools for that)

## Configuration Files

### QueueLoad-1ops.cfg - **Lower Capacity Bound**
- **Database capacity**: 2 ops/step (more constrained processing)
- **Queue limit**: 2 items per cell (bounded queues)
- **Channels**: 2+1+1+1 = 5 total channels (bounded concurrency)
- **Use case**: Verify protocol correctness under tight resource constraints

### QueueLoad-10ops.cfg - **Higher Capacity Bound**
- **Database capacity**: 5 ops/step (bounded processing)
- **Queue limit**: 2 items per cell (same bounded queues)
- **Channels**: 2+1+1+1 = 5 total channels (same bounded concurrency)
- **Use case**: Verify protocol correctness under moderate resource constraints

## Bounded Model Design

| Config | DB Ops/Step | Queue Limit | Total Channels | Protocol Behavior | Verification Focus |
|--------|-------------|-------------|----------------|-------------------|-------------------|
| 1ops   | 2           | 2           | 5              | Aggressive resource contention | Resource starvation scenarios |
| 10ops  | 5           | 2           | 5              | Graceful degradation under load | Overload handling correctness |

## Verification Results

- **1ops config**: Protocol handles 2 entities correctly, fails as designed at capacity limit
- **10ops config**: Protocol handles 5 entities correctly, fails as designed under moderate constraints

The model successfully validates that the protocol:
1. **Maintains safety invariants** under different resource constraints
2. **Fails predictably** when capacity limits are exceeded (no silent corruption)
3. **Handles bounded queues correctly** without overflows or underflows

## Aggressive Abstraction Strategy

- **Entity count**: Bounded to prevent state explosion (max 25)
- **Queue sizes**: Small, fixed limits (2 items per cell)
- **Channel counts**: Minimal realistic numbers (2+1+1+1 = 5)
- **Database ops**: Simple integer operations per step
- **Task generation**: Fixed multiplier (5 tasks per entity) for deterministic behavior

This abstraction enables **exhaustive state exploration** to find edge cases and protocol violations that might be missed in performance simulations.

## Usage

```bash
# Test minimal configuration
just run  # Runs both 1ops and 10ops configs

# Or run individually:
tlc QueueLoad-1ops.cfg
tlc QueueLoad-10ops.cfg
```

## Key Design Principles

- **Bounded state space** prevents state explosion during model checking
- **Small parameter values** enable exhaustive exploration within reasonable time
- **Aggressive abstraction** focuses on protocol correctness, not realistic performance
- **Invariant violations** reveal logical errors in the protocol design

Each configuration represents a different stress test for the protocol's correctness under varying resource constraints.
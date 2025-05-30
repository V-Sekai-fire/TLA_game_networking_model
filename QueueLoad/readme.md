# VR Game Infrastructure Scaling Configurations

This directory contains TLA+ model configurations that demonstrate infrastructure scaling gradients for VR game networking.

## Configuration Files

### QueueLoad-1ops.cfg - **Medium Capacity Configuration**
- **Database capacity**: 5 ops/step (50 ops/second)
- **Queue limit**: 2 items per cell
- **Channels**: 2+1+1+1 = 5 total channels
- **Channel queues**: 2 items each
- **Target capacity**: ~50 entities
- **Use case**: Medium infrastructure under heavy load test

### QueueLoad-10ops.cfg - **Low Capacity Configuration**
- **Database capacity**: 2 ops/step (20 ops/second)
- **Queue limit**: 2 items per cell
- **Channels**: 2+1+1+1 = 5 total channels
- **Channel queues**: 2 items each
- **Target capacity**: ~20 entities
- **Use case**: Resource-constrained environment under heavy load test

## Infrastructure Scaling Pattern

| Config | DB Ops/Step | Queue Limit | Total Channels | Max Entities (Measured) | Ops/Second |
|--------|-------------|-------------|----------------|-------------------------|------------|
| 1ops   | 5           | 2           | 5              | 6 (fails at 7)         | 50         |
| 10ops  | 2           | 2           | 5              | 3 (fails at 4)         | 20         |

## Model Testing Results

- **1ops config**: Can sustain 6 entities, fails when growing to 7 entities (task size 35 > capacity 25)
- **10ops config**: Can sustain 3 entities, fails when growing to 4 entities (task size 20 > capacity 10)

The simulation demonstrates that DATABASE_OPS_PER_STEP × 5 directly controls maximum sustainable entity count via the OverloadManagementInvariant.

## Usage

```bash
# Test minimal configuration
just run  # Runs both 1ops and 10ops configs

# Or run individually:
tlc QueueLoad-1ops.cfg
tlc QueueLoad-10ops.cfg
```

## Key Scaling Relationships

- **Database capacity scales linearly** with entity count
- **Queue limits scale with latency tolerance** (VR vs non-VR)
- **Channel count scales with concurrent users** 
- **Channel queue depth scales with burst tolerance**

Each configuration represents a realistic infrastructure tier for different deployment scales.
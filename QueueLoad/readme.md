# VR Game Infrastructure Scaling Configurations

This directory contains TLA+ model configurations that demonstrate infrastructure scaling gradients for VR game networking.

## Configuration Files

### QueueLoad-1ops.cfg - **Minimal Test Configuration**
- **Database capacity**: 1 op/step (10 ops/second)
- **Queue limit**: 1 item (ultra-tight latency constraint)
- **Channels**: Minimal configuration
- **Target capacity**: ~10 entities
- **Use case**: Basic model validation and testing

### QueueLoad-10ops.cfg - **Baseline Infrastructure**
- **Database capacity**: 10 ops/step (100 ops/second)
- **Queue limit**: 5 items (tight latency constraint) 
- **Channels**: 2+1+1+1 = 5 total channels
- **Channel queues**: 2 items each
- **Target capacity**: ~50-100 entities
- **Use case**: Development/testing environment

## Infrastructure Scaling Pattern

| Config | DB Ops/Step | Queue Limit | Total Channels | Est. Entities | Ops/Second |
|--------|-------------|-------------|----------------|---------------|------------|
| 1ops   | 1           | 1           | Minimal        | ~10           | 10         |
| 10ops  | 10          | 5           | 5              | ~100          | 100        |

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
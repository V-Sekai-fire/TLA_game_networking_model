# VR Game Infrastructure Scaling Configurations

This directory contains TLA+ model configurations that demonstrate infrastructure scaling gradients for VR game networking.

## Configuration Files

### QueueLoad-10ops.cfg - **Baseline Infrastructure**
- **Database capacity**: 10 ops/step (100 ops/second)
- **Queue limit**: 5 items (tight latency constraint) 
- **Channels**: 2+1+1+1 = 5 total channels
- **Channel queues**: 2 items each
- **Target capacity**: ~50-100 entities
- **Use case**: Development/testing environment

### QueueLoad-50ops.cfg - **Medium Infrastructure** 
- **Database capacity**: 50 ops/step (500 ops/second)
- **Queue limit**: 10 items (moderate latency)
- **Channels**: 3+2+2+2 = 9 total channels  
- **Channel queues**: 3 items each
- **Target capacity**: ~200-500 entities
- **Use case**: Small production deployment

### QueueLoad-200ops.cfg - **Large Infrastructure**
- **Database capacity**: 200 ops/step (2,000 ops/second)
- **Queue limit**: 25 items (relaxed latency)
- **Channels**: 4+3+3+3 = 13 total channels
- **Channel queues**: 5 items each  
- **Target capacity**: ~1,000-2,000 entities
- **Use case**: Regional game server

### QueueLoad-1000ops.cfg - **Enterprise Infrastructure**
- **Database capacity**: 1000 ops/step (10,000 ops/second)
- **Queue limit**: 100 items (high throughput)
- **Channels**: 8+4+4+4 = 20 total channels
- **Channel queues**: 10 items each
- **Target capacity**: ~10,000+ entities  
- **Use case**: Global game server

## Infrastructure Scaling Pattern

| Config | DB Ops/Step | Queue Limit | Total Channels | Est. Entities | Ops/Second |
|--------|-------------|-------------|----------------|---------------|------------|
| 10ops  | 10          | 5           | 5              | ~100          | 100        |
| 50ops  | 50          | 10          | 9              | ~500          | 500        |
| 200ops | 200         | 25          | 13             | ~2,000        | 2,000      |
| 1000ops| 1000        | 100         | 20             | ~10,000       | 10,000     |

## Usage

```bash
# Test baseline capacity
tlc QueueLoad-10ops.cfg

# Test medium capacity  
tlc QueueLoad-50ops.cfg

# Test large capacity
tlc QueueLoad-200ops.cfg

# Test enterprise capacity
tlc QueueLoad-1000ops.cfg
```

## Key Scaling Relationships

- **Database capacity scales linearly** with entity count
- **Queue limits scale with latency tolerance** (VR vs non-VR)
- **Channel count scales with concurrent users** 
- **Channel queue depth scales with burst tolerance**

Each configuration represents a realistic infrastructure tier for different deployment scales.
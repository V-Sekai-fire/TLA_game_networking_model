# Optimized Final Plan: Low-Cost Simulation of Raft + Parallel Commits System

#### **1. Simplify the Model**

- **3-node cluster** (1 leader, 2 followers)
- **Abstract networking** use async channels
- **Discrete time steps** (3ms increments instead of 1ms).

#### **2. Reuse Existing Specs**

- **Leverage pre-built TLA+ modules**:
  - [Raft (Ongardie)](https://github.com/ongardie/raft.tla) for consensus logic.
  - [Pluscal/TLA+ modeling of Hybrid Logical Clocks and Hybrid Vector Clocks](https://github.com/muratdem/HLC) for hybrid clocks.
  - [Parallel Commits](https://github.com/oxidecomputer/cockroach/blob/release-22.1-oxide/docs/tla-plus/ParallelCommits/ParallelCommits.tla)

#### **3. Prioritize Critical Properties**

- **Verify safety only**: Linearizability and HLC causal order.
- **Test only critical failures**: Leader crash and 1-network partition.

#### **4. Optimize TLC Configuration**

- **Symmetry reduction**: Treat followers as interchangeable.
- **Limit transactions**: 3 concurrent ops instead of 500.
- **Constrain latency**: `ASSUME latency ≤ 16`.

#### **5. Incremental Verification**

1. **Phase 1**: Verify Raft alone with latency bounds.
2. **Phase 2**: Add parallel commits and check conflicts.
3. **Phase 3**: Integrate HLC causal ordering.

---

### **Deliverables**

1. **Minimal Integrated Model**:

   ```tla
   EXTENDS Raft, Integers
   VARIABLES committed, hlc, latency

   ParallelCommit ==
     ∧ LeaderAppendLog
     ∧ ∀ n ∈ Followers : SendIntent(n)
     ∧ WaitForQuorum(2/3)
     ∧ UpdateHLC()
     ∧ latency' = latency + 3 \* ms

   ASSUME MaxLatency == latency ≤ 16
   ```

2. **TLC Configuration**:
   ```bash
   tlc -workers 8 -depth 100 -config clusters=3 Model.tla
   ```

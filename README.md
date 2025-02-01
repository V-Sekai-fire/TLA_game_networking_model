# vsk-networking-model-checker

Here’s the updated **table** with a **Communication Complexity** attribute added, along with **votes (0-100)** for all attributes. Higher scores indicate better performance or suitability.

| **Proposal**                           | **Linearizability** | **Fault Tolerance** | **Space Complexity** | **Time Complexity** | **Complexity** | **Scalability** | **Communication Load** | **Communication Complexity** | **Use Case**                                                                 |
| -------------------------------------- | ------------------- | ------------------- | -------------------- | ------------------- | -------------- | --------------- | ---------------------- | ---------------------------- | ---------------------------------------------------------------------------- |
| **Distributed Consensus Algorithm**    | ✅ (100)            | ✅ (100)            | High (30)            | High (40)           | High (30)      | High (90)       | High (30)              | High (30)                    | Strict linearizability and fault tolerance in distributed systems.           |
| (e.g., Raft or Paxos)                  |                     |                     |                      |                     |                |                 |                        |                              |                                                                              |
| **Leader-Based Event Synchronization** | ✅ (100)            | ✅ (80)             | Moderate (70)        | Moderate (70)       | Moderate (60)  | Moderate (70)   | Moderate (60)          | Moderate (60)                | Simpler than full consensus; maintains linearizability with a single leader. |
| **Multi-Primary Replication**          | ❌ (30)             | ✅ (90)             | High (50)            | Moderate (60)       | Moderate (50)  | High (80)       | High (40)              | High (40)                    | High availability and load balancing; sacrifices linearizability.            |
| with Conflict Resolution               |                     |                     |                      |                     |                |                 |                        |                              |                                                                              |
| **Sharded Scene Tree**                 | ✅ (80)             | ✅ (90)             | High (60)            | High (50)           | High (50)      | High (80)       | Moderate (50)          | Moderate (50)                | Large scene trees with independent sub-trees; requires shard management.     |
| with Centralized Coordination          |                     |                     |                      |                     |                |                 |                        |                              |                                                                              |
| **Full State Replication**             | ❌ (20)             | ✅ (70)             | Low (90)             | Low (80)            | Low (80)       | Low (50)        | High (20)              | Low (80)                     | Simple, infrequently updated scene trees; inefficient for real-time updates. |
| with Quorum                            |                     |                     |                      |                     |                |                 |                        |                              |                                                                              |

---

### **Key Attributes Explained with Scoring**

1. **Linearizability**:

   - ✅ (100): Ensures strong consistency (all operations appear to occur in a globally consistent order).
   - ❌ (20-30): Sacrifices linearizability for availability or simplicity.

2. **Fault Tolerance**:

   - ✅ (70-100): Can tolerate server failures and continue operating.
   - ❌ (0-50): Vulnerable to single points of failure.

3. **Space Complexity**:

   - Low (90): Minimal memory or storage overhead.
   - Moderate (50-70): Moderate memory or storage overhead.
   - High (30-50): Significant memory or storage overhead.

4. **Time Complexity**:

   - Low (80): Minimal latency or processing overhead.
   - Moderate (50-70): Moderate latency or processing overhead.
   - High (30-50): Significant latency or processing overhead.

5. **Complexity**:

   - Low (80): Easy to implement and maintain.
   - Moderate (50-70): Requires careful design and implementation.
   - High (30-50): Involves advanced distributed systems concepts and significant overhead.

6. **Scalability**:

   - Low (50): Suitable for small or simple systems.
   - Moderate (70): Handles moderate load and complexity.
   - High (80-90): Designed for large, distributed systems with high load.

7. **Communication Load**:

   - Low (80): Minimal network traffic between servers.
   - Moderate (50-70): Moderate network traffic between servers.
   - High (20-40): Significant network traffic between servers.

8. **Communication Complexity**:
   - Low (80): Simple communication protocols with minimal coordination.
   - Moderate (50-70): Moderate coordination and protocol complexity.
   - High (30-50): Complex coordination and protocol requirements.

---

### **Recommendation**

For **clustering servers** with **linearizability**, the **Distributed Consensus Algorithm (e.g., Raft or Paxos)** is the best choice, despite its high space, time, communication load, and communication complexity. It provides strong consistency, fault tolerance, and scalability, making it ideal for distributed systems. If you want a simpler solution, consider **Leader-Based Event Synchronization**, which maintains linearizability with lower complexity, moderate communication load, and moderate communication complexity but may introduce a single point of failure (the leader).

If you can tolerate eventual consistency, **Multi-Primary Replication with Conflict Resolution** is a viable option for high availability and load balancing. However, it does not guarantee strict linearizability and has high communication load and complexity.

## Referenced works

https://github.com/ongardie/raft.tla/blob/master/raft.tla

https://aws.amazon.com/builders-library/reliability-and-constant-work

https://github.com/oxidecomputer/cockroach/blob/release-22.1-oxide/docs/tla-plus/ParallelCommits/ParallelCommits.tla

https://www.cockroachlabs.com/blog/parallel-commits/

https://github.com/eBay/NuRaft

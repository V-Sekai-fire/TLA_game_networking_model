# **Component Synopsis**

#### **1. Godot Client (C++)**

- **Role**: Capture VR input, render synchronized node trees.
- **Key Features**:
  - Shared memory buffer for RISC-V VM communication.
  - Vulkan rendering pipeline optimized for 90 FPS.
- **Latency Budget**: 25ms (Input + Apply & Render).

---

#### **2. libriscv VM (C++)**

- **Role**: Execute user mods safely in a RISC-V sandbox.
- **Key Features**:
  - 3ns function call overhead.
  - JIT/AOT compilation for mods.
  - Syscall filtering and memory isolation.
- **Latency Budget**: 2.003ms (Call + Execution).

---

#### **3. Networking Layer (QUIC/HTTP3)**

- **Role**: Transmit node updates between clients and leader.
- **Key Features**:
  - 0-RTT handshake reuse.
  - Packet prioritization (DSCP for Raft traffic).
- **Latency Budget**: 3ms (RPC to Leader).

---

#### **4. Leader (Elixir)**

- **Role**: Coordinate Raft consensus and parallel commits.
- **Key Features**:
  - Raft log replication with dynamic quorums.
  - Hybrid Logical Clock (HLC) for global ordering.
- **Latency Budget**: 11ms (Raft + Commit + HLC).

---

#### **5. Followers (Elixir)**

- **Role**: Replicate logs and store intent states.
- **Key Features**:
  - Crash recovery via Raft snapshots.
  - Intent garbage collection.
- **Latency Budget**: Included in Leader’s 11ms.

---

#### **6. Hybrid Logical Clock (HLC)**

- **Role**: Generate causally ordered timestamps.
- **Key Features**:
  - NTP-synced with 1ms precision.
  - Embedded in Raft entries.
- **Latency Budget**: 1ms.

---

#### **7. Parallel Commit Protocol**

- **Role**: Ensure atomic commits across followers.
- **Key Features**:
  - Intent writes with quorum ACKs.
  - Conflict resolution via HLC timestamps.
- **Latency Budget**: 6ms.

# Readme

The core problem you're tackling for **V-Sekai** is: **How to design and implement a backend system capable of supporting an Open World Survival Craft (OWSC) game with the massive scale, deep persistence, and complex player-driven dynamics envisioned for V-Sekai, while simultaneously meeting the ultra-low latency and high immersion demands of Virtual Reality.**

This breaks down into several interconnected challenges:

1.  **Immense Data Volume & Granularity (V-Sekai Scale):** Persistently storing and managing the state of potentially millions of player-built structures, vehicles, resources, and items across a vast, multi-region world. Each entity can have a detailed and frequently changing state, and VR's tangibility might increase the expectation for fine-grained persistence within the V-Sekai world.
2.  **Extreme Transactional Throughput & Concurrency (V-Sekai Scale):** Handling many hundreds to thousands of concurrent player actions per second globally (logistics, building, combat, resource changes). These actions all require atomic and consistent updates to the persistent V-Sekai world state, often involving shared resources.
3.  **Ultra-Low Latency for VR Immersion in V-Sekai:** Ensuring that player interactions within V-Sekai provide immediate feedback (ideally sub-20ms for critical loops) to maintain presence and avoid VR sickness. This is despite the underlying complexity and scale of data operations needed to support the V-Sekai simulation.
4.  **Strong Data Consistency & Integrity for V-Sekai:** Guaranteeing that the shared V-Sekai world state is accurate and consistent for all players, especially during collaborative or contentious interactions, over campaigns that can last for weeks or months. Data corruption or desynchronization is highly detrimental.
5.  **Scalability & Availability for V-Sekai:** Designing a system that can reliably scale to support thousands of concurrent VR players in V-Sekai and remain highly available throughout long-duration game worlds.

## Proposed Technology Stack & Architectural Approach

To address the aforementioned challenges, the following MIT-compatible (or similarly permissive, e.g., Apache 2.0, BSD) technology stack and architectural considerations are proposed:

**Core Backend Technologies:**

- **Elixir (Apache 2.0 License):**
  - Leverage OTP (Open Telecom Platform) for massive concurrency, fault tolerance, and distributed state management.
  - Use GenServers/Agents for managing individual player states, game entities, or regional logic, enabling high responsiveness for critical interactions.
  - Addresses: _Extreme Transactional Throughput & Concurrency_, _Ultra-Low Latency (for in-memory operations)_, _Scalability & Availability_.
- **Phoenix Framework (MIT License):**
  - Utilize Phoenix Channels for ultra-low latency, real-time bidirectional communication between Godot clients and the Elixir backend.
  - Addresses: _Ultra-Low Latency for VR Immersion_.
- **FoundationDB (Apache 2.0 License) with `ecto_foundationdb` (Apache 2.0 License):**
  - Serve as the primary persistent datastore. FoundationDB offers distributed, transactional key-value storage with strong ACID guarantees (strict serializability).
  - Ecto provides a powerful and familiar way to model, query, and transact with this data from Elixir.
  - Addresses: _Immense Data Volume & Granularity_, _Extreme Transactional Throughput & Concurrency_, _Strong Data Consistency & Integrity_, _Scalability & Availability_. The atomic `ProcessInputsAndUpdateWorld` transaction described in `ExtendedWorldState.tla` can be directly implemented using FoundationDB's transactional capabilities.

**Architectural Principles:**

- **Tiered State Management:**
  1.  **Ultra-Hot Data (In-Memory Elixir Processes):** For sub-20ms critical loops, manage state directly in Elixir GenServers/Agents. This state is ultimately persisted to FoundationDB.
  2.  **Warm Data (Cached in Regional Elixir Processes):** For consistent, low-latency operations for specific game systems or regions, frequently accessed data can be cached within regional Elixir processes. This state is read from and ultimately persisted to FoundationDB.
  3.  **Cold/Persistent Data (FoundationDB):** The authoritative, globally consistent, and durable store for all game state.
- **Sharding/Regionalization:** The game world can be sharded, with different sets of Elixir processes (potentially managing cached data regionally) responsible for distinct areas, all persisting to the global FoundationDB instance.
- **Asynchronous Operations:** For non-critical updates or background tasks, leverage Elixir's message passing to offload work and maintain responsiveness.

This combination aims to provide the necessary tools to build a backend that is scalable, resilient, consistent, and performant enough for the ambitious goals of V-Sekai, while adhering to permissive licensing. The system design can mirror the state transitions and data structures (like `worldEntities`, `entityState`, `playerInputs`) defined in `ExtendedWorldState.tla`.

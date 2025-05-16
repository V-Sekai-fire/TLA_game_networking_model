# Readme

This project outlines the backend design for V-Sekai, an Open World Survival Craft (OWSC) game with a focus on massive scale, deep persistence, and low-latency VR immersion.

## Core Problem & Challenges

[Details in Problem and Challenges](./problem_and_challenges.md)

## Proposed Technology Stack & Architectural Approach

[Details in Technology and Architecture](./technology_and_architecture.md)

## Explain the project in five levels of complexity

**Level 1: To a Child**

Imagine we're building a giant, magical LEGO world online where many people can play together in virtual reality, like wearing special goggles. My job is to make sure that when you build a cool LEGO castle, it stays there, and when your friend opens a door in your castle, you see it open right away, super fast! We need special computer magic to remember everything everyone builds and to make sure it all works smoothly even if thousands of kids are playing at the same time.

**Level 2: To a Teenager**

We're designing the server-side backend for a massive multiplayer online VR game. Think of something like Minecraft or Valheim, but in VR, and potentially way bigger, with a persistent world where everything players do sticks around. The challenge is handling tons of players interacting in real-time – building, crafting, fighting – all while keeping the VR experience super smooth and responsive, because lag in VR is a big problem. We need to store a huge amount of data about the game world and player actions, and process it all very quickly and reliably.

**Level 3: To an Undergrad (Computer Science)**

We're architecting a distributed backend system for an Open World Survival Craft game with VR support, focusing on high scalability, strong data consistency, and low-latency communication. The core problem involves managing persistent world state for a large number of concurrent users, where actions like building, resource gathering, and entity interactions must be transactional and reflected globally with minimal delay. We're looking at a technology stack likely involving Elixir/OTP for its concurrency and fault tolerance, WebRTC Data Channels for real-time messaging over UDP to VR clients, and a distributed database like FoundationDB for its ACID guarantees and ability to handle large-scale transactional workloads. The architecture will likely employ tiered state management (hot in-memory state in Elixir, warm cached state, and cold persistent state in FoundationDB) and sharding to distribute load.

**Level 4: To a Grad Student (Distributed Systems / Game Engineering)**

The project aims to define a backend architecture for a V-Sekai, a large-scale, persistent OWSC VR game, addressing challenges in distributed state management, transactional consistency at scale, and sub-20ms latency for critical VR interaction loops. We're proposing a stack centered around Elixir/OTP for its actor model and soft real-time capabilities, leveraging WebRTC Data Channels for client-server communication over UDP. The persistence layer will be FoundationDB, chosen for its strict serializability and proven scalability, accessed via an Ecto adapter. Key architectural patterns include tiered state management (GenServers for ultra-hot state, potentially regional caching for warm state, and FoundationDB as the source of truth), and world sharding where Elixir processes manage distinct regions while FoundationDB provides a unified global view. The goal is to ensure that operations like `ProcessInputsAndUpdateWorld`, as conceptualized in formal models like TLA+, can be implemented atomically and efficiently across the distributed system, supporting a deeply persistent and player-driven emergent world.

**Level 5: To a Colleague (Expert in Backend/Distributed Systems)**

We're tackling the backend for V-Sekai, an OWSC VR title. The core constraints are massive scale (potentially millions of fine-grained entities), deep persistence (weeks/months long campaigns), and VR's stringent low-latency requirements (sub-20ms for critical loops). The proposed solution leverages Elixir/OTP for its concurrency model (GenServers managing entity/player state or regional logic) and WebRTC Data Channels for low-latency, bidirectional client comms over UDP. FoundationDB is the cornerstone for persistence, providing strict serializability for complex, multi-key transactions essential for consistent world state updates (e.g., atomic `ProcessInputsAndUpdateWorld` from our TLA+ spec). The architecture emphasizes tiered state: Elixir processes for ultra-hot data, potentially regional caches (backed by FDB) for warm data, and FDB as the cold, authoritative store. We'll use sharding at the Elixir application layer, with FoundationDB handling the underlying distributed storage and transactional integrity across shards. The primary focus is on achieving strong consistency and high availability without compromising the low-latency demands of VR, ensuring that player interactions with the persistent, dynamic world are immediate and reliable. We're aiming for a design that can scale horizontally and maintain integrity under high concurrent load, with permissive licensing (Apache 2.0, MIT) for all core components.

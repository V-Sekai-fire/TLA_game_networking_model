# Load Testing Estimation for V-Sekai Backend

This document outlines a preliminary approach to estimating and planning load tests for the V-Sekai backend system. The goal is to identify potential bottlenecks, validate scalability claims, and ensure the system can handle expected (and unexpected) user loads while maintaining performance and stability.

## 1. Goals of Load Testing

- Determine the maximum concurrent user (CCU) capacity of the current architecture.
- Identify performance bottlenecks in the Elixir/OTP application layer.
- Measure the transactional throughput and latency of FoundationDB under various load conditions.
- Assess the performance of WebRTC Data Channels for real-time communication.
- Validate the effectiveness of the tiered state management and sharding strategies.
- Ensure system stability and resource utilization (CPU, memory, network, disk I/O) under sustained peak load.
- Determine breaking points and recovery behavior.

## 2. Key Metrics to Measure

- **Concurrent Users (CCU):** Maximum sustainable CCU.
- **Request/Transaction Rate:**
  - Player actions per second (e.g., movement updates, interactions, crafting).
  - FoundationDB transactions per second.
- **Latency:**
  - End-to-end latency for critical player interactions (e.g., build, combat).
  - WebRTC message delivery times.
  - FoundationDB transaction commit times.
  - API response times from Elixir services.
- **Error Rates:** Percentage of failed requests or transactions.
- **Resource Utilization:**
  - CPU usage (Elixir nodes, FoundationDB cluster).
  - Memory usage (Elixir nodes, FoundationDB cluster).
  - Network I/O.
  - Disk I/O (FoundationDB).
- **Elixir/OTP Specific Metrics:**
  - Process counts and memory usage per process.
  - Message queue lengths.
  - ETS/Mnesia table performance (if used for caching beyond GenServer state).

## 3. Load Test Scenarios

Simulate realistic user behavior and edge cases.

- **Scenario 1: Baseline CCU & Interactions**
  - Simulate a moderate number of users (e.g., 100, 500 CCU) performing common actions: moving, basic interactions, light resource gathering.
- **Scenario 2: High CCU & Mixed Interactions**
  - Gradually increase CCU (e.g., 1k, 5k, 10k+) with a mix of activities: building, combat, crafting, social interactions in concentrated areas.
- **Scenario 3: Regional Hotspots / Sharding Test**
  - Concentrate a large number of users and activities within a single shard or game region to test sharding effectiveness and inter-process communication.
- **Scenario 4: Mass Entity Updates**
  - Simulate events causing updates to a large number of game entities simultaneously (e.g., environmental effects, large-scale NPC behavior).
- **Scenario 5: Stress Test / Breaking Point**
  - Continuously increase load until system performance degrades significantly or failures occur, to identify the absolute limits.
- **Scenario 6: Soak Test / Stability**
  - Run a sustained moderate-to-high load for an extended period (e.g., 6-12 hours) to check for memory leaks, resource exhaustion, or performance degradation over time.

## 4. Estimated Peak Loads (Initial Guesses - To Be Refined)

These are very rough initial targets and should be refined based on game design and business goals.

- **Target CCU:**
  - Initial Launch: 1,000 - 5,000 CCU
  - Growth Target: 10,000 - 50,000+ CCU
- **Player Actions per Second (per player):**
  - Average: 0.5 - 2 actions/sec (movement, simple interactions)
  - Peak (e.g., combat): 5 - 10 actions/sec
- **Total Transactions per Second (Global):**
  - Calculated based on CCU and actions/sec. E.g., 5,000 CCU \* 1 action/sec = 5,000 transactions/sec.
- **Data per Player:**
  - Active state: Kilobytes
  - Persistent state: Megabytes (potentially, over time)

## 5. Tools & Infrastructure for Load Testing

- **Load Generation Tools:**
  - Custom Elixir scripts: To simulate game client behavior and interact with the backend via WebRTC.
  - k6 (JavaScript, Go): Good for API endpoint testing if any HTTP/WebSocket signaling is involved.
  - Tsung (Erlang): Powerful distributed load testing tool, good fit for Erlang/Elixir ecosystem.
  - Locust (Python): User-friendly, scriptable in Python.
- **Monitoring & Profiling:**
  - Prometheus & Grafana: For collecting and visualizing metrics from Elixir (via `telemetry_metrics_prometheus`), FoundationDB, and system resources.
  - Elixir's built-in tools: `:observer`, `:etop`, `:cprof`, `:fprof`.
  - FoundationDB monitoring: `fdbcli --exec status`, FDB's own metrics.
- **Test Environment:**
  - A dedicated, production-like environment.
  - Sufficiently powerful machines for load generators.
  - Ability to scale up/down the backend infrastructure (Elixir nodes, FoundationDB cluster).
  - Consider using cloud providers for easily scalable load generation infrastructure.

## 6. Next Steps

- Refine load estimations based on detailed game mechanics.
- Develop realistic user simulation scripts.
- Set up a dedicated load testing environment.
- Conduct initial baseline tests and iterate.

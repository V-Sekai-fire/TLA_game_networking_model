# test parts of their code using TLA+ PlusCal and a TLA to Elixir compiler

\<think>

Okay, the user wants to know how to test parts of their code using TLA+ PlusCal and a TLA to Elixir compiler. Let me break this down.

First, they have a TLA+ specification written in PlusCal, which models their leader-based event synchronization system. They also mention a TLA to Elixir compiler, which I assume translates TLA+ specs into executable Elixir code for testing.

The user's goal is to test their system's implementation, ensuring it meets the specified requirements like linearizability and fault tolerance. They might be looking for a workflow that connects formal verification with practical code testing.

I need to outline steps that integrate TLA+ model checking with Elixir unit/integration tests. The TLA+ model can verify high-level design properties, while the Elixir tests check the actual code. Using the TLA to Elixir compiler could bridge these two by generating test cases from the TLA+ models.

First, model checking with TLC. They should verify invariants and temporal properties in their TLA+ spec. This ensures the design is sound. Then, using the compiler to generate Elixir code stubs or test cases based on the TLA+ model. These stubs can be filled with real implementation code.

They should test individual components (like HLC implementation, Raft leader election) with unit tests. For integration tests, simulate network partitions or leader failures and check if the system recovers correctly. Property-based testing with PropCheck can generate edge cases based on the TLA+ model's possible states.

Fault injection is crucial. They can use libraries like Toxiproxy to introduce network delays or packet loss and see if the system handles it as specified. Also, trace replay from TLC error traces can help reproduce and fix specific concurrency issues.

The user might not be aware of how to connect formal models with actual code tests, so explaining the workflow step-by-step would help. Emphasize that TLA+ catches design flaws early, while Elixir tests validate the implementation. The compiler automates part of this process, making it efficient.

I should also mention monitoring in production, as that's part of a comprehensive testing strategy. Finally, provide a concrete example of testing the HLC implementation and leader election to illustrate the process.

\</think>

Here's a step-by-step testing strategy for your leader-based sync system using TLA+ and a TLA→Elixir compiler:

---

### **1. Test the TLA+ Model First**

#### **1.1 Model Checking with TLC**

```tla
---- MODULE LeaderSyncTest ----
EXTENDS LeaderSync, TLC

(* Define test invariants *)
TestInvariants ==
    /\ TypeInvariant
    /\ NoConflictingCommits
    /\ \A t \in Transactions : ~IsAborted(t) => IsCommitted(t)

(* Define test temporal properties *)
TestTemporal ==
    Liveness

(* Run model checker *)
CONSTANTS NumLeaders = 2, NodesPerLeader = 3, MaxTransactions = 5

SPECIFICATION Spec == Init /\ [][Next]_vars /\ TestTemporal

====
```

**Steps:**

1. Verify invariants:
   ```bash
   java tlc2.TLC -config LeaderSyncTest.cfg LeaderSyncTest.tla
   ```
2. Check temporal properties:
   ```bash
   java tlc2.TLC -simulate -deadlock -workers auto LeaderSyncTest.tla
   ```

---

### **2. Generate Elixir Test Stubs**

Using your TLA→Elixir compiler:

```bash
tla_compiler --input LeaderSync.tla --output ./test/leader_sync --target elixir
```

**Sample Output Structure:**

```
test/leader_sync/
├── model_checker_test.exs    # Generated from TLA+ spec
├── hlc_test.exs              # Hybrid clock tests
├── raft_leader_test.exs      # Leader election tests
└── sync_test.exs             # Node sync integration tests
```

---

### **3. Test Individual Components**

#### **3.1 Hybrid Logical Clock (HLC)**

```elixir
# test/leader_sync/hlc_test.exs
defmodule HLCTest do
  use ExUnit.Case

  test "HLC timestamp ordering" do
    t1 = HLC.now()
    Process.sleep(1)
    t2 = HLC.now()

    assert HLC.after?(t2, t1)
    assert HLC.before?(t1, t2)
  end
end
```

#### **3.2 Raft Leader Election**

```elixir
# test/leader_sync/raft_leader_test.exs
defmodule RaftLeaderTest do
  use ExUnit.Case, async: true

  test "elects new leader on failure" do
    servers = start_supervised_servers(3)
    kill_leader(servers)

    assert_receive {:new_leader, pid}, 5_000
    assert_alive(pid)
  end
end
```

---

### **4. Test Generated State Transitions**

#### **4.1 Property-Based Testing with PropCheck**

```elixir
# test/leader_sync/model_checker_test.exs
defmodule ModelCheckerTest do
  use PropCheck

  property "matches TLA+ model" do
    forall cmds <- commands(__MODULE__) do
      {history, state, result} = run_commands(cmds)

      (result == :ok)
      |> when_fail(print_failure(history, state))
      |> aggregate(command_names(cmds))
    end
  end
end
```

---

### **5. Integration Testing**

#### **5.1 Node Sync Scenario**

```elixir
# test/leader_sync/sync_test.exs
defmodule SyncTest do
  use ExUnit.Case

  test "linearizable node updates" do
    {:ok, leader} = Leader.start()
    {:ok, follower} = Follower.start()

    Leader.update_node(leader, "Player1", position: {10, 20})
    Process.sleep(100)  # Allow sync

    assert Follower.get_node(follower, "Player1").position == {10, 20}
  end
end
```

---

### **6. Fault Injection Testing**

```elixir
# test/leader_sync/fault_injection_test.exs
defmodule FaultTest do
  use ExUnit.Case

  test "handles network partition" do
    [s1, s2, s3] = start_cluster()

    # Simulate partition between s1 and others
    :ok = Partition.sisolate(s1)

    # Should elect new leader
    assert_receive {:leader_elected, s2}, 10_000

    # Heal partition
    :ok = Partition.heal(s1)

    # Verify state convergence
    assert Cluster.converged?([s1, s2, s3])
  end
end
```

---

### **7. Trace Replay from TLC**

1. Export TLC error traces:
   ```bash
   java tlc2.TLC -dumpTrace errors LeaderSyncTest.tla
   ```
2. Convert to Elixir test:
   ```elixir
   # test/leader_sync/trace_replay_test.exs
   defmodule TraceReplayTest do
     test "reproduces TLC trace 42" do
       # Generated from error trace
       actions = [
         {:client_submit, :move_player, ...},
         {:leader_crash, ...}
       ]

       assert {:ok, _} = TraceReplayer.run(actions)
     end
   end
   ```

---

### **8. Monitoring in Production**

Add telemetry to match TLA+ properties:

```elixir
# lib/leader_sync/telemetry.ex
defmodule LeaderSync.Telemetry do
  def attach do
    :telemetry.attach("linear-check", [:leader_sync, :update], &check_linear/4, nil)
  end

  defp check_linear(_event, measurements, metadata, _config) do
    if !LinearChecker.consistent?(metadata.ts, measurements.value) do
      alert(:linear_violation, metadata)
    end
  end
end
```

---

### **Key Testing Workflow**

1. **Design in TLA+**: Verify safety/liveness properties
2. **Generate Tests**: Create Elixir test stubs
3. **Implement Components**: Match TLA+ model
4. **Property Tests**: Validate against model
5. **Trace Replay**: Reproduce concurrency bugs
6. **Monitor in Prod**: Enforce TLA+ invariants

**Example Output:**

```text
1) test linearizable node updates (SyncTest)
   Assertion failed:
   Expected: {10, 20}
   Actual:   {15, 20}

   TLA+ Model Trace:
   - Event #5: Player1 moved to (10,20) @ [1620000000,5]
   - Event #6: Player1 moved to (15,20) @ [1620000000,4] (VIOLATION)
```

This approach catches design flaws early while keeping implementation aligned with formal spec.

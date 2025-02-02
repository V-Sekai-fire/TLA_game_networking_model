To model **Hybrid Vector Clocks (HVC)** alongside **Hybrid Logical Clocks (HLC)** in TLA+/PlusCal, follow this structured approach:

---

### **1. Extend the HLC Model to HVC**

#### **a. Define Node Variables**

```tla
VARIABLES
    hvc,      \* Function: Node → [c: Nat, l: Nat]
    physicalTime,
    messages
```

#### **b. Initialize Clocks**

```tla
Init ==
    ∧ physicalTime = [n ∈ Nodes ↦ 0]  \* Per-node physical time (simplified)
    ∧ hvc = [n ∈ Nodes ↦ [m ∈ Nodes ↦ [c ↦ 0, l ↦ 0]]]
    ∧ messages = {}
```

---

### **2. Model HVC Operations**

#### **a. Local Event**

```tla
LocalEvent(n) ==
    LET max_c == Max(physicalTime[n], hvc[n][n].c)
    IN
    ∧ hvc' = [hvc EXCEPT ![n][n] = IF max_c = hvc[n][n].c
                                     THEN [c ↦ max_c, l ↦ hvc[n][n].l + 1]
                                     ELSE [c ↦ max_c, l ↦ 0]]
    ∧ UNCHANGED ⟨messages, physicalTime⟩
```

#### **b. Send Message**

```tla
Send(n) ==
    ∧ messages' = messages ∪ {[type ↦ "msg", hvc ↦ hvc[n], from ↦ n]}
    ∧ UNCHANGED ⟨hvc, physicalTime⟩
```

#### **c. Receive Message**

```tla
Receive(n, msg) ==
    LET merged_hvc == [m ∈ Nodes ↦ [c ↦ Max(hvc[n][m].c, msg.hvc[m].c),
                                     l ↦ IF hvc[n][m].c = msg.hvc[m].c
                                         THEN Max(hvc[n][m].l, msg.hvc[m].l)
                                         ELSE IF hvc[n][m].c < msg.hvc[m].c
                                              THEN msg.hvc[m].l
                                              ELSE hvc[n][m].l]]
    IN
    ∧ hvc' = [hvc EXCEPT ![n] = merged_hvc]
    ∧ physicalTime' = [physicalTime EXCEPT ![n] = Max(physicalTime[n], msg.hvc[msg.from].c)]
    ∧ messages' = messages ∖ {msg}
```

---

### **3. Verify Key Properties**

#### **a. Causal Order Invariant**

```tla
CausalOrder ==
    ∀ m1, m2 ∈ Messages :
        (m1 → m2) ⇒ (∀ n ∈ Nodes : hvc[m1.from][n] ≤ hvc[m2.from][n])
```

#### **b. Physical Time Bounding**

```tla
BoundedDrift ==
    ∀ n ∈ Nodes :
        hvc[n][n].c ≤ physicalTime[n] + ε \* ε is clock drift tolerance
```

---

### **4. Optimizations for Model Checking**

- **Symmetry Reduction**:
  ```tla
  SYMMETRY Permutations(Nodes)
  ```
- **Bound Node Count**:
  ```tla
  CONSTANT Nodes = {n1, n2, n3}  \* Verify for 3 nodes
  ```
- **Limit Logical Counters**:
  ```tla
  CONSTRAINT hvc[n][m].l ≤ 3 \* Keep state space small
  ```

---

### **5. Comparison with HLC**

| **Aspect**           | **HLC**                             | **HVC**                        |
| -------------------- | ----------------------------------- | ------------------------------ |
| **State Size**       | O(1) per node                       | O(N) per node (N = node count) |
| **Causal Precision** | Partial (physical time + 1 counter) | Full (vector of counters)      |
| **TLA+ Complexity**  | Simple (single clock)               | Complex (nested functions)     |

---

### **6. Run TLC Model Check**

```bash
tlc -config Nodes=3 hvc_model.tla
```

---

### **Summary**

By extending the existing HLC TLA+ model to include vector-based state tracking, you can verify Hybrid Vector Clocks while reusing HLC’s physical time bounding logic. Focus on **causal order** and **bounded drift** invariants, and use symmetry reduction to manage state explosion.

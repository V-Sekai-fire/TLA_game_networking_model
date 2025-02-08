# Copyright (c) 2025-present. This file is part of V-Sekai https://v-sekai.org/.
# K. S. Ernest (Fire) Lee
# BoundedCounter.tla
# SPDX-License-Identifier: MIT
------------------------------- MODULE BoundedCounter -------------------------------
EXTENDS Naturals, TLC

CONSTANT MAX_VALUE

VARIABLE count

Init == count = 0
Next == count' = IF count < MAX_VALUE THEN count + 1 ELSE count
Spec == Init /\ [][Next]_count /\ WF_count(Next)

CountTypeInvariant == count \in Nat
TerminationProperty == <>[](count = MAX_VALUE)
MaxValueInvariant == MAX_VALUE = 5
================================================================================

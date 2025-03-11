------------------------------ MODULE CyberneticSystem ------------------------------
EXTENDS Integers, TLC, PhaseHandling

VARIABLES location, disposition, threat_level, phase

Locations == {"start", "env_study", "death", "end"} 
              \cup { "phase" \o ToString(i) : i \in 1..NumPhases }

Init ==
    /\ location = "start"
    /\ disposition = 0
    /\ threat_level = 0
    /\ phase = 1

Next ==
    \/ (* Start state transitions *)
       /\ location = "start"
       /\ \/ (* Go directly to first phase *)
             location' = "phase1"
             /\ UNCHANGED <<disposition, threat_level, phase>>
          \/ (* Environmental study path *)
             location' = "env_study"
             /\ threat_level' = threat_level + 1 
             /\ UNCHANGED <<disposition, phase>>
    
    \/ (* Environmental study to first phase *)
       /\ location = "env_study"
       /\ location' = "phase1"
       /\ threat_level' = threat_level + 1
       /\ UNCHANGED <<disposition, phase>>
    
    \/ (* Phase handling using imported logic *)
       /\ location \in { "phase" \o ToString(i) : i \in 1..NumPhases }
       /\ \/ (* Successful phase completion *)
             HandlePhase(phase, disposition, threat_level, 
                        disposition', threat_level', phase')
             /\ location' = IF phase' = NumPhases 
                            THEN "end" 
                            ELSE "phase" \o ToString(phase')
          \/ (* Threat threshold exceeded *)
             threat_level >= CASE phase = 1 -> 3
                             [] phase = 2 -> 4
                             [] phase = NumPhases -> 5
                             [] phase \in 3..(NumPhases-1) -> 5
             /\ location' = "death" 
             /\ UNCHANGED <<disposition, threat_level, phase>>
    
    \/ (* End state loop back *)
       /\ location = "end"
       /\ location' = "start"
       /\ disposition' = 0
       /\ threat_level' = 0
       /\ phase' = 1
    
    \/ (* Final termination *)
       /\ location' = "end"
       /\ location' = "death"
       /\ UNCHANGED <<disposition, threat_level, phase>>

Termination ==
    <> (location \in {"death", "end"}) 

TypeOK == 
    /\ location \in Locations
    /\ disposition \in 0..15
    /\ threat_level \in 0..15
    /\ phase \in Phases
    /\ EffectivePhases \subseteq {"1:BRIBE", "1:CHARM", "1:THREATEN", "1:HACK",
                                  "2:BRIBE", "2:CHARM", "2:THREATEN", "2:HACK",
                                  "3:BRIBE", "3:CHARM", "3:THREATEN", "3:HACK"}

Spec == Init /\ [][Next]_<<location, disposition, threat_level, phase>>
=============================================================================

------------------------------ MODULE PhaseHandling ------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS EffectivePhases, NumPhases

EffectivePhaseSet == {"BRIBE", "CHARM", "THREATEN", "HACK"}
Phases == 1..NumPhases

PhaseAction(p) == 
    LET prefix == ToString(p) \o ":"
        str    == CHOOSE s \in EffectivePhases: prefix = SubSeq(s, 1, Len(prefix))
    IN  SubSeq(str, Len(prefix) + 1, Len(str))

HandlePhase(currPhase, currDisp, currThreat, nextDisp, nextThreat, nextPhase) ==
    LET action == PhaseAction(currPhase) IN
    \/ /\ action \in EffectivePhaseSet
       /\ nextDisp = currDisp + CASE currPhase = 1 -> 2
                                 [] currPhase = 2 -> 2
                                 [] currPhase = NumPhases -> 3
                                 [] currPhase \in 3..(NumPhases-1) -> 1
       /\ nextThreat = currThreat
       /\ nextPhase = IF currPhase < NumPhases THEN currPhase + 1 ELSE currPhase
    \/ /\ action \notin EffectivePhaseSet
       /\ nextThreat = currThreat + 3
       /\ nextDisp = currDisp
       /\ nextPhase = currPhase
=============================================================================

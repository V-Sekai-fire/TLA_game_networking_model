-------------------- MODULE HybridLogicClock -------------------
(*
 * Murat Demirbas <muratdemirbas@gmail.com> https://github.com/muratdem/HLC.git
 * SPDX-License-Identifier: MIT 
 *)

EXTENDS Integers
CONSTANT N, STOP, EPS
ASSUME N \in Nat \ {0,1}
Procs == 1..N

SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j

VARIABLES pt, msg, pc, l, c

vars == << pt, msg, pc, l, c >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ pt = [j \in Procs |-> 0]
        /\ msg = [j \in Procs |-> <<0,0>>]
        (* Process j *)
        /\ l = [self \in Procs |-> 0]
        /\ c = [self \in Procs |-> 0]
        /\ pc = [self \in ProcSet |-> "J0"]

J0(self) == /\ pc[self] = "J0"
            /\ IF pt[self] < STOP
                  THEN /\ \/ /\ pc' = [pc EXCEPT ![self] = "Recv"]
                          \/ /\ pc' = [pc EXCEPT ![self] = "Send"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << pt, msg, l, c >>

Recv(self) == /\ pc[self] = "Recv"
              /\ (\A k \in Procs: pt[self] < pt[k]+ EPS)
              /\ pt' = [pt EXCEPT ![self] = pt[self] +1]
              /\ IF l[self]>pt'[self] /\ l[self]=msg[self][1]
                    THEN /\ c' = [c EXCEPT ![self] = SetMax({c[self], msg[self][2]})+1]
                    ELSE /\ IF l[self]>pt'[self]
                               THEN /\ c' = [c EXCEPT ![self] = c[self]+1]
                               ELSE /\ IF l[self]<msg[self][1]
                                          THEN /\ c' = [c EXCEPT ![self] = msg[self][2]+1]
                                          ELSE /\ c' = [c EXCEPT ![self] = 0]
              /\ l' = [l EXCEPT ![self] = SetMax({pt'[self], l[self], msg[self][1]})]
              /\ pc' = [pc EXCEPT ![self] = "J0"]
              /\ msg' = msg

Send(self) == /\ pc[self] = "Send"
              /\ (\A k \in Procs: pt[self] < pt[k]+ EPS)
              /\ pt' = [pt EXCEPT ![self] = pt[self] +1]
              /\ IF l[self]>=pt'[self]
                    THEN /\ c' = [c EXCEPT ![self] = c[self]+1]
                         /\ l' = l
                    ELSE /\ l' = [l EXCEPT ![self] = pt'[self]]
                         /\ c' = [c EXCEPT ![self] = 0]
              /\ \E k \in Procs \ {self}:
                   msg' = [msg EXCEPT ![k] = <<l'[self],c'[self]>>]
              /\ pc' = [pc EXCEPT ![self] = "J0"]

j(self) == J0(self) \/ Recv(self) \/ Send(self)

Next == (\E self \in Procs: j(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(j(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

TypeOK == (\A k \in Procs: l[k] >= pt[k])
Sync == (\A k,m \in Procs: pt[k] <= pt[m]+EPS)
Boundedl == (\A k \in Procs: l[k] < pt[k] + EPS) 
Boundedc == (\A k \in Procs: c[k] < N*(EPS+1)) 

==================================================

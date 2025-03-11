---- MODULE CyberneticSystem_TTrace_1741724865 ----
EXTENDS CyberneticSystem, Sequences, TLCExt, Toolbox, Naturals, TLC

_expression ==
    LET CyberneticSystem_TEExpression == INSTANCE CyberneticSystem_TEExpression
    IN CyberneticSystem_TEExpression!expression
----

_trace ==
    LET CyberneticSystem_TETrace == INSTANCE CyberneticSystem_TETrace
    IN CyberneticSystem_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        phase = (3)
        /\
        threat_level = (0)
        /\
        disposition = (4)
        /\
        location = ("end")
    )
----

_init ==
    /\ location = _TETrace[1].location
    /\ disposition = _TETrace[1].disposition
    /\ threat_level = _TETrace[1].threat_level
    /\ phase = _TETrace[1].phase
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ location  = _TETrace[i].location
        /\ location' = _TETrace[j].location
        /\ disposition  = _TETrace[i].disposition
        /\ disposition' = _TETrace[j].disposition
        /\ threat_level  = _TETrace[i].threat_level
        /\ threat_level' = _TETrace[j].threat_level
        /\ phase  = _TETrace[i].phase
        /\ phase' = _TETrace[j].phase

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("CyberneticSystem_TTrace_1741724865.json", _TETrace)

=============================================================================

 Note that you can extract this module `CyberneticSystem_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `CyberneticSystem_TEExpression.tla` file takes precedence 
  over the module `CyberneticSystem_TEExpression` below).

---- MODULE CyberneticSystem_TEExpression ----
EXTENDS CyberneticSystem, Sequences, TLCExt, Toolbox, Naturals, TLC

expression == 
    [
        \* To hide variables of the `CyberneticSystem` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        location |-> location
        ,disposition |-> disposition
        ,threat_level |-> threat_level
        ,phase |-> phase
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_locationUnchanged |-> location = location'
        
        \* Format the `location` variable as Json value.
        \* ,_locationJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(location)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_locationModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].location # _TETrace[s-1].location
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE CyberneticSystem_TETrace ----
\*EXTENDS CyberneticSystem, IOUtils, TLC
\*
\*trace == IODeserialize("CyberneticSystem_TTrace_1741724865.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE CyberneticSystem_TETrace ----
EXTENDS CyberneticSystem, TLC

trace == 
    <<
    ([phase |-> 1,threat_level |-> 0,disposition |-> 0,location |-> "start"]),
    ([phase |-> 1,threat_level |-> 0,disposition |-> 0,location |-> "phase1"]),
    ([phase |-> 2,threat_level |-> 0,disposition |-> 2,location |-> "phase2"]),
    ([phase |-> 3,threat_level |-> 0,disposition |-> 4,location |-> "end"])
    >>
----


=============================================================================

---- CONFIG CyberneticSystem_TTrace_1741724865 ----
CONSTANTS
    NumPhases = 3
    EffectivePhases = { "1:CHARM" , "2:THREATEN" , "3:HACK" }

INVARIANT
    _inv

CHECK_DEADLOCK
    \* CHECK_DEADLOCK off because of PROPERTY or INVARIANT above.
    FALSE

INIT
    _init

NEXT
    _next

CONSTANT
    _TETrace <- _trace

ALIAS
    _expression
=============================================================================
\* Generated on Tue Mar 11 13:27:46 PDT 2025
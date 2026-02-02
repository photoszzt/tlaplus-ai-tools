---- MODULE Counter_TTrace_1769924579 ----
EXTENDS Sequences, TLCExt, Counter, Toolbox, Naturals, TLC

_expression ==
    LET Counter_TEExpression == INSTANCE Counter_TEExpression
    IN Counter_TEExpression!expression
----

_trace ==
    LET Counter_TETrace == INSTANCE Counter_TETrace
    IN Counter_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        x = (11)
    )
----

_init ==
    /\ x = _TETrace[1].x
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ x  = _TETrace[i].x
        /\ x' = _TETrace[j].x

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("Counter_TTrace_1769924579.json", _TETrace)

=============================================================================

 Note that you can extract this module `Counter_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `Counter_TEExpression.tla` file takes precedence 
  over the module `Counter_TEExpression` below).

---- MODULE Counter_TEExpression ----
EXTENDS Sequences, TLCExt, Counter, Toolbox, Naturals, TLC

expression == 
    [
        \* To hide variables of the `Counter` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        x |-> x
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_xUnchanged |-> x = x'
        
        \* Format the `x` variable as Json value.
        \* ,_xJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(x)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_xModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].x # _TETrace[s-1].x
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE Counter_TETrace ----
\*EXTENDS IOUtils, Counter, TLC
\*
\*trace == IODeserialize("Counter_TTrace_1769924579.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE Counter_TETrace ----
EXTENDS Counter, TLC

trace == 
    <<
    ([x |-> 0]),
    ([x |-> 1]),
    ([x |-> 2]),
    ([x |-> 3]),
    ([x |-> 4]),
    ([x |-> 5]),
    ([x |-> 6]),
    ([x |-> 7]),
    ([x |-> 8]),
    ([x |-> 9]),
    ([x |-> 10]),
    ([x |-> 11])
    >>
----


=============================================================================

---- CONFIG Counter_TTrace_1769924579 ----

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
\* Generated on Sun Feb 01 05:42:59 UTC 2026
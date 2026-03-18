---- MODULE QueueRefinement ----
\* Refinement mapping: proves ConcreteQueue refines AbstractQueue.
\*
\* The concrete two-pointer circular buffer implementation is shown to
\* correctly implement the abstract sequence-based queue specification.

EXTENDS Naturals, Sequences

CONSTANT MaxLen
CONSTANT Items

VARIABLES buf, head, tail, count

\* Instantiate the concrete spec
Concrete == INSTANCE ConcreteQueue

\* Refinement mapping: map concrete state to abstract state
\* The abstract queue is the logical contents extracted from the circular buffer
Abstract == INSTANCE AbstractQueue WITH queue <- Concrete!QueueContents

\* The concrete specification
Spec == Concrete!Spec

\* Refinement property: every behavior of Spec is a behavior of Abstract!Spec
Refinement == Abstract!Spec

====
\* TLC Configuration:
\*   SPECIFICATION Spec
\*   PROPERTY Refinement
\*   CONSTANT MaxLen = 3
\*   CONSTANT Items = {1, 2, 3}

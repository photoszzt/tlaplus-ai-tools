---- MODULE Counter ----
\*******************************************************************************
\* Simple counter specification demonstrating TLA+ basics
\*
\* This spec models a counter that:
\* - Starts at 0
\* - Increments by 1 each step
\* - Stops at MaxValue
\*******************************************************************************

EXTENDS Naturals

CONSTANT MaxValue       \* Maximum value the counter can reach
ASSUME MaxValue \in Nat \* MaxValue must be a natural number

VARIABLE count          \* Current counter value

\* Type invariant - defines valid values for state variables
TypeInvariant == count \in 0..MaxValue

\* Initial state - counter starts at 0
Init == count = 0

\* Actions defining state transitions

\* Increment: Add 1 to counter if below maximum
Increment ==
    /\ count < MaxValue       \* Guard: only increment if below max
    /\ count' = count + 1     \* Action: increment by 1

\* ReachMax: Stay at maximum value when reached
ReachMax ==
    /\ count = MaxValue       \* Guard: only when at maximum
    /\ count' = count         \* Action: stay at same value

\* Next: Choose any enabled action
Next ==
    \/ Increment
    \/ ReachMax

\* Complete specification with stuttering
Spec ==
    /\ Init                   \* Start in initial state
    /\ [][Next]_<<count>>     \* Execute Next or stutter

\* Safety properties to verify

\* Count never exceeds maximum
BoundInvariant == count <= MaxValue

\* Count is always non-negative
NonNegative == count >= 0

====

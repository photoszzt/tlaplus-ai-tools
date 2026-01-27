---- MODULE SimpleLock ----
\*******************************************************************************
\* Simple mutual exclusion lock specification
\*
\* This spec models a basic lock that:
\* - Can be in "unlocked" or "locked" state
\* - Allows acquiring when unlocked
\* - Allows releasing when locked
\*******************************************************************************

EXTENDS Naturals

VARIABLE
    locked,         \* Boolean: is lock currently held?
    holder          \* Natural: ID of process holding lock (0 = none)

CONSTANT NumProcesses
ASSUME NumProcesses \in Nat /\ NumProcesses > 0

Processes == 1..NumProcesses

\* Type invariant
TypeInvariant ==
    /\ locked \in BOOLEAN
    /\ holder \in 0..NumProcesses

\* Initial state - lock is free
Init ==
    /\ locked = FALSE
    /\ holder = 0

\* Actions

\* Process p acquires the lock
Acquire(p) ==
    /\ p \in Processes
    /\ locked = FALSE         \* Guard: lock must be free
    /\ locked' = TRUE         \* Take the lock
    /\ holder' = p            \* Record who has it

\* Process p releases the lock
Release(p) ==
    /\ p \in Processes
    /\ locked = TRUE          \* Guard: lock must be held
    /\ holder = p             \* Guard: only holder can release
    /\ locked' = FALSE        \* Release the lock
    /\ holder' = 0            \* Clear holder

\* Next: Any process can acquire or release
Next ==
    \/ \E p \in Processes : Acquire(p)
    \/ \E p \in Processes : Release(p)

\* Specification
Spec == Init /\ [][Next]_<<locked, holder>>

\* Safety properties

\* Mutual exclusion: when locked, exactly one process holds it
MutualExclusion ==
    locked => (holder \in Processes)

\* Lock consistency: holder is 0 iff lock is free
LockConsistency ==
    (locked = FALSE) <=> (holder = 0)

====

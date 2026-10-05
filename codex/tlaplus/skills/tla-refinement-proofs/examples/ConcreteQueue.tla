---- MODULE ConcreteQueue ----
\* Concrete queue implementation using a fixed-size array with head and tail pointers.
\* This is a two-pointer circular buffer that refines AbstractQueue.

EXTENDS Naturals, Sequences

CONSTANT MaxLen  \* Maximum queue length (array size)
CONSTANT Items   \* Set of items that can be enqueued

VARIABLES buf,   \* Fixed-size array (function 1..MaxLen -> Items)
          head,  \* Index of the next slot to dequeue from (1-based)
          tail,  \* Index of the next free slot to enqueue into (1-based)
          count  \* Number of items currently in the queue

vars == <<buf, head, tail, count>>

TypeInvariant ==
    /\ buf \in [1..MaxLen -> Items \cup {"-"}]
    /\ head \in 1..MaxLen
    /\ tail \in 1..MaxLen
    /\ count \in 0..MaxLen

Init ==
    /\ buf = [i \in 1..MaxLen |-> "-"]
    /\ head = 1
    /\ tail = 1
    /\ count = 0

Enqueue(item) ==
    /\ count < MaxLen
    /\ buf' = [buf EXCEPT ![tail] = item]
    /\ tail' = IF tail = MaxLen THEN 1 ELSE tail + 1
    /\ count' = count + 1
    /\ UNCHANGED head

Dequeue ==
    /\ count > 0
    /\ buf' = [buf EXCEPT ![head] = "-"]
    /\ head' = IF head = MaxLen THEN 1 ELSE head + 1
    /\ count' = count - 1
    /\ UNCHANGED tail

Next ==
    \/ \E item \in Items : Enqueue(item)
    \/ Dequeue

Spec == Init /\ [][Next]_vars

\* Helper: extract the logical queue contents as a sequence
\* for the refinement mapping
QueueContents ==
    IF count = 0
    THEN << >>
    ELSE LET indices == [i \in 1..count |->
             IF head + i - 1 <= MaxLen
             THEN head + i - 1
             ELSE head + i - 1 - MaxLen]
         IN [i \in 1..count |-> buf[indices[i]]]

====

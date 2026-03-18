---- MODULE AbstractQueue ----
\* Abstract queue specification using a sequence.
\* This serves as the high-level spec that concrete implementations must refine.

EXTENDS Naturals, Sequences

CONSTANT MaxLen  \* Maximum queue length
CONSTANT Items   \* Set of items that can be enqueued

VARIABLE queue

TypeInvariant == queue \in Seq(Items) /\ Len(queue) <= MaxLen

Init == queue = << >>

Enqueue(item) ==
    /\ Len(queue) < MaxLen
    /\ queue' = Append(queue, item)

Dequeue ==
    /\ Len(queue) > 0
    /\ queue' = Tail(queue)

Next ==
    \/ \E item \in Items : Enqueue(item)
    \/ Dequeue

Spec == Init /\ [][Next]_queue

====

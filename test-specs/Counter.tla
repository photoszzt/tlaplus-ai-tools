---- MODULE Counter ----
EXTENDS Integers

VARIABLE x

Init == x = 0

Next == x' = x + 1

Spec == Init /\ [][Next]_x

TypeOK == x \in Nat

Inv == x <= 10
====

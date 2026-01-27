---- MODULE SimpleValid ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x + 1
====

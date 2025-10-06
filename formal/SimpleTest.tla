---- MODULE SimpleTest ----
EXTENDS Naturals

CONSTANT N

VARIABLE x

Init == x = 0

Next == x' = (x + 1) % (N + 1)

Spec == Init /\ [][Next]_x

TypeInvariant == x \in 0..N

====

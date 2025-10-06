---- MODULE TestNyxStream ----
EXTENDS Naturals

CONSTANT N

VARIABLE x

Init == x = 0

Next == x' = (x + 1) % N

Spec == Init /\ [][Next]_x

TypeOK == x \in 0..(N-1)

====

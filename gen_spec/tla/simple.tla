---- MODULE simple ----
EXTENDS TLC, Integers

VARIABLE i

Init == i = 0
Next == i' = IF i < 10 THEN i + 1 ELSE i
Spec ==
    /\ Init
    /\ [][Next]_i

DoesNotWork == <>TRUE
====
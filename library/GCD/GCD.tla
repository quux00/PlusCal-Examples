-------------------------- MODULE GCD ---------------------------
EXTENDS Integers

Divides(p, n) == \E q \in Int : n = q * p

DivisorsOf(n) == {p \in Int: Divides(p, n)}

SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j

GCD(m, n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))

=================================================================
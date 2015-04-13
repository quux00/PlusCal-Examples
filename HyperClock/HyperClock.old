----------------------------- MODULE HyperClock -----------------------------
EXTENDS Integers

(*
--algorithm Clock {
    variable b \in {0,1};
  {
    while (TRUE) {
      b := (b+1) % 2;
    }
  }
}
*)
\* BEGIN TRANSLATION
VARIABLE b

vars == << b >>

Init == (* Global variables *)
        /\ b \in {0,1}

Next == b' = (b+1) % 2

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
=============================================================================
 

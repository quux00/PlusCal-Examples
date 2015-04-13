--------------------------- MODULE HyperEuclid -----------------------------
EXTENDS Integers, GCD, TLC
CONSTANTS M, N

ASSUME /\ M \in Nat \ {0}
       /\ N \in Nat \ {0}
       
(***************************************************************************
--fair algorithm HyperEuclid {
    variables x \in 1..M, y \in 1..N,
              x0 = x, y0 = y;
  {
    while (x # y) {
      if (x < y) {
        y := y - x;
      } else {
        x := x - y;
      }
    };
    assert (x = y) /\ (x = GCD(x0,y0));
  }  
}

***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES x, y, x0, y0, pc

vars == << x, y, x0, y0, pc >>

Init == (* Global variables *)
        /\ x \in 1..M
        /\ y \in 1..N
        /\ x0 = x
        /\ y0 = y
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF x # y
               THEN /\ IF x < y
                          THEN /\ y' = y - x
                               /\ x' = x
                          ELSE /\ x' = x - y
                               /\ y' = y
                    /\ pc' = "Lbl_1"
               ELSE /\ Assert((x = y) /\ (x = GCD(x0,y0)), 
                              "Failure of assertion at line 20, column 5.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << x, y >>
         /\ UNCHANGED << x0, y0 >>

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

----------------------------------------------------------------------------

PartialCorrectness == (pc = "Done") => (x = y) /\ (x = GCD(M,N))
       
============================================================================

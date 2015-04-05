----------------------- MODULE HourClock -------------------------
EXTENDS Naturals, TLC

(*
--algorithm HourClock {
  variables hr = 0, clockHours = {1 ..12};
  {
    hr := 0;    \* TODO: how tell it to randomly choose a value in clockHours?
    while (TRUE) {
      hr := (hr % 12) + 1;
      print <<hr>>;
      assert (hr \in clockHours);
    };
  } \* end master code block
} \* end algorithm
*)

\* BEGIN TRANSLATION
VARIABLES hr, clockHours, pc

vars == << hr, clockHours, pc >>

Init == (* Global variables *)
        /\ hr = 0
        /\ clockHours = {1 ..12}
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ hr' = 0
         /\ pc' = "Lbl_2"
         /\ UNCHANGED clockHours

Lbl_2 == /\ pc = "Lbl_2"
         /\ hr' = (hr % 12) + 1
         /\ PrintT(<<hr'>>)
         /\ Assert((hr' \in clockHours), 
                   "Failure of assertion at line 12, column 7.")
         /\ pc' = "Lbl_2"
         /\ UNCHANGED clockHours

Next == Lbl_1 \/ Lbl_2
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
==================================================================

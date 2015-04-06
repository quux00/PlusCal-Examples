---------------------- MODULE AsyncInterface -----------------------
EXTENDS Naturals, TLC
\*CONSTANT Data

\* Based on the AsynchInterface TLA+ example in Ch. 3 of "Specifying Systems"

(*
--algorithm AsyncInterface {
  variables 
    val \in 0..100, 
    rdy \in 0..1,
    ack \in 0..1;
    
    process (Send = "send")
    {
      s00:  while (TRUE) {
      s01:    await rdy = ack;
      s02:    val := 44;  \* how choose a random val?
              rdy := 1 - rdy;
        
              print <<ack, rdy, "Send">>;
              \* TypeInvariant
              assert (val \in 0..100) /\ 
                     (rdy \in 0..1) /\ 
                     (ack \in 0..1) 
            }    
    }; \* end process Send
    
    
    process (Recv = "recv")
    {
      r00:  while (TRUE) {
      r01:    await rdy # ack;
      r02:    ack := 1 - ack;
  
              print <<ack, rdy, "Recv">>;
              \* TypeInvariant
              assert (val \in 0..100) /\ 
                     (rdy \in 0..1) /\ 
                     (ack \in 0..1)
            }       
    }; \* end process Recv
    
} \* end algorithm
*)
\* BEGIN TRANSLATION
VARIABLES val, rdy, ack, pc

vars == << val, rdy, ack, pc >>

ProcSet == {"send"} \cup {"recv"}

Init == (* Global variables *)
        /\ val \in 0..100
        /\ rdy \in 0..1
        /\ ack \in 0..1
        /\ pc = [self \in ProcSet |-> CASE self = "send" -> "s00"
                                        [] self = "recv" -> "r00"]

s00 == /\ pc["send"] = "s00"
       /\ pc' = [pc EXCEPT !["send"] = "s01"]
       /\ UNCHANGED << val, rdy, ack >>

s01 == /\ pc["send"] = "s01"
       /\ rdy = ack
       /\ pc' = [pc EXCEPT !["send"] = "s02"]
       /\ UNCHANGED << val, rdy, ack >>

s02 == /\ pc["send"] = "s02"
       /\ val' = 44
       /\ rdy' = 1 - rdy
       /\ PrintT(<<ack, rdy', "Send">>)
       /\ Assert((val' \in 0..100) /\
                 (rdy' \in 0..1) /\
                 (ack \in 0..1), 
                 "Failure of assertion at line 23, column 15.")
       /\ pc' = [pc EXCEPT !["send"] = "s00"]
       /\ ack' = ack

Send == s00 \/ s01 \/ s02

r00 == /\ pc["recv"] = "r00"
       /\ pc' = [pc EXCEPT !["recv"] = "r01"]
       /\ UNCHANGED << val, rdy, ack >>

r01 == /\ pc["recv"] = "r01"
       /\ rdy # ack
       /\ pc' = [pc EXCEPT !["recv"] = "r02"]
       /\ UNCHANGED << val, rdy, ack >>

r02 == /\ pc["recv"] = "r02"
       /\ ack' = 1 - ack
       /\ PrintT(<<ack', rdy, "Recv">>)
       /\ Assert((val \in 0..100) /\
                 (rdy \in 0..1) /\
                 (ack' \in 0..1), 
                 "Failure of assertion at line 38, column 15.")
       /\ pc' = [pc EXCEPT !["recv"] = "r00"]
       /\ UNCHANGED << val, rdy >>

Recv == r00 \/ r01 \/ r02

Next == Send \/ Recv

Spec == Init /\ [][Next]_vars

\* END TRANSLATION


====================================================================

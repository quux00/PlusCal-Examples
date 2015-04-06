--------------------- MODULE AsyncInterfaceChan ---------------------
EXTENDS Naturals, TLC
\*CONSTANT Data  \* TODO: how specify Data as a range in the Model Checker?

\* Based on the AsynchInterface TLA+ example in Ch. 3 of "Specifying Systems"

(*
--algorithm AsyncInterfaceChan {
  variables 
       chan \in [val : 0..100,
                 rdy : 0..1,
                 ack : 0..1];
                 
    process (Send = "send")
      variable oldrdy;
    {
      s00:  while (TRUE) {
      s01:    await chan.rdy = chan.ack;
      s02:    oldrdy := chan.rdy;
              chan.rdy := 1 - chan.rdy;
              \* We don't assign chan.val here -> we let TLC pick all
              \* possible vals between 0 and 100
               
              print <<chan, "Send">>;
              assert (chan.val \in 0..100); 
              assert (chan.rdy \in 0..1); 
              assert (chan.ack \in 0..1);
              assert (chan.rdy # oldrdy);
              assert (chan.rdy # chan.ack);
            }    
    }; \* end process Send
    
    
    process (Recv = "recv")
      variable oldack;
    {
      r00:  while (TRUE) {
      r01:    await chan.rdy # chan.ack;
      r02:    oldack := chan.ack;
              chan.ack := 1 - chan.ack;
  
              print <<chan, "Recv">>;
              \* TypeInvariants
              assert (chan.val \in 0..100); 
              assert (chan.rdy \in 0..1); 
              assert (chan.ack \in 0..1);
              assert (chan.ack # oldack);
              assert (chan.rdy = chan.ack);
            }       
    }; \* end process Recv
    
} \* end algorithm
*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES chan, pc, oldrdy, oldack

vars == << chan, pc, oldrdy, oldack >>

ProcSet == {"send"} \cup {"recv"}

Init == (* Global variables *)
        /\ chan \in [val : 0..100,
                     rdy : 0..1,
                     ack : 0..1]
        (* Process Send *)
        /\ oldrdy = defaultInitValue
        (* Process Recv *)
        /\ oldack = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = "send" -> "s00"
                                        [] self = "recv" -> "r00"]

s00 == /\ pc["send"] = "s00"
       /\ pc' = [pc EXCEPT !["send"] = "s01"]
       /\ UNCHANGED << chan, oldrdy, oldack >>

s01 == /\ pc["send"] = "s01"
       /\ chan.rdy = chan.ack
       /\ pc' = [pc EXCEPT !["send"] = "s02"]
       /\ UNCHANGED << chan, oldrdy, oldack >>

s02 == /\ pc["send"] = "s02"
       /\ oldrdy' = chan.rdy
       /\ chan' = [chan EXCEPT !.rdy = 1 - chan.rdy]
       /\ PrintT(<<chan', "Send">>)
       /\ Assert((chan'.val \in 0..100), 
                 "Failure of assertion at line 25, column 15.")
       /\ Assert((chan'.rdy \in 0..1), 
                 "Failure of assertion at line 26, column 15.")
       /\ Assert((chan'.ack \in 0..1), 
                 "Failure of assertion at line 27, column 15.")
       /\ Assert((chan'.rdy # oldrdy'), 
                 "Failure of assertion at line 28, column 15.")
       /\ Assert((chan'.rdy # chan'.ack), 
                 "Failure of assertion at line 29, column 15.")
       /\ pc' = [pc EXCEPT !["send"] = "s00"]
       /\ UNCHANGED oldack

Send == s00 \/ s01 \/ s02

r00 == /\ pc["recv"] = "r00"
       /\ pc' = [pc EXCEPT !["recv"] = "r01"]
       /\ UNCHANGED << chan, oldrdy, oldack >>

r01 == /\ pc["recv"] = "r01"
       /\ chan.rdy # chan.ack
       /\ pc' = [pc EXCEPT !["recv"] = "r02"]
       /\ UNCHANGED << chan, oldrdy, oldack >>

r02 == /\ pc["recv"] = "r02"
       /\ oldack' = chan.ack
       /\ chan' = [chan EXCEPT !.ack = 1 - chan.ack]
       /\ PrintT(<<chan', "Recv">>)
       /\ Assert((chan'.val \in 0..100), 
                 "Failure of assertion at line 44, column 15.")
       /\ Assert((chan'.rdy \in 0..1), 
                 "Failure of assertion at line 45, column 15.")
       /\ Assert((chan'.ack \in 0..1), 
                 "Failure of assertion at line 46, column 15.")
       /\ Assert((chan'.ack # oldack'), 
                 "Failure of assertion at line 47, column 15.")
       /\ Assert((chan'.rdy = chan'.ack), 
                 "Failure of assertion at line 48, column 15.")
       /\ pc' = [pc EXCEPT !["recv"] = "r00"]
       /\ UNCHANGED oldrdy

Recv == r00 \/ r01 \/ r02

Next == Send \/ Recv

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
====================================================================

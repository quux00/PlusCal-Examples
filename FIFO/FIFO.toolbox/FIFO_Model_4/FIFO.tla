------------------------ MODULE FIFO --------------------------
EXTENDS Naturals, Sequences, TLC
CONSTANT MaxBufSize

(************************************************)
(* Based on FIFO in Ch. 4 of Specifying Systems *)
(* but modified to have Recvr pull from Buffer  *)
(* rather than have Buffer push to Recvr.       *)
(************************************************)

(*
--algorithm FIFO {
  variables
    valSet = 0..3,
    inchan \in [val : valSet,
                rdy : 0..1,
                ack : 0..1],
                
    outchan \in [val : valSet,
                 rdy : 0..1,
                 ack : 0..1];
                 
    q = <<>>;  \* internal queue of the Buffer - a sequence of vals 

  macro CheckInvariants(chan) {
    assert (chan.val \in valSet); 
    assert (chan.rdy \in 0..1); 
    assert (chan.ack \in 0..1);
    assert (q \in Seq(valSet));
  }

  process (SSend = "ssend")
    variable oldrdy;
  {    
    ss0:  while (TRUE) {
    ss1:    await inchan.rdy = inchan.ack;
    ss2:    oldrdy := inchan.rdy;
            inchan.rdy := 1 - inchan.rdy;
            \* We do not assign chan.val here -> we let TLC pick all
            \* possible vals between in valSet
             
            print <<inchan, "SSend">>;
            CheckInvariants(inchan);
            assert (inchan.rdy # oldrdy);
            assert (inchan.rdy # inchan.ack);
          }    
    
  }; \* end process SSend

  process (BufRecv = "bufrecv")
        variable oldack;
  {
    br0:  while (TRUE) {
    br1:    await inchan.rdy # inchan.ack /\ Len(q) < MaxBufSize;
    br2:    oldack := inchan.ack;
            inchan.ack := 1 - inchan.ack;
            q := Append(q, inchan.val);
            \* q := q \o inchan.val;

            print <<inchan, "BufRecv", q>>;
            CheckInvariants(inchan);
            assert (inchan.ack # oldack);
            assert (inchan.rdy = inchan.ack);
          }       
  }; \* end process BufRecv

  process (BufSend = "bufsend")
    variable oldrdy;
  {    
    bs0:  while (TRUE) {
    bs1:    await outchan.rdy = outchan.ack;
    bs2:    oldrdy := outchan.rdy;
            outchan.rdy := 1 - outchan.rdy;
            \* We do not assign chan.val here -> we let TLC pick all
            \* possible vals between in valSet
             
            print <<outchan, "BufSend">>;
            CheckInvariants(outchan);
            assert (outchan.rdy # oldrdy);
            assert (outchan.rdy # outchan.ack);
          }    
    
  }; \* end process BufSend


  process (RRecv = "rrecv")
        variable oldack, rval;
  {
    rr0:  while (TRUE) {
    rr1:    await outchan.rdy # outchan.ack /\ Len(q) > 0;
    rr2:    oldack := outchan.ack;
            outchan.ack := 1 - outchan.ack;
            rval := Head(q);
            q := Tail(q);

            print <<outchan, "RRecv", rval>>;
            CheckInvariants(outchan);
            assert (outchan.ack # oldack);
            assert (outchan.rdy = outchan.ack);
          }       
  }; \* end process RRecv

}
*)
\* BEGIN TRANSLATION
\* Process variable oldrdy of process SSend at line 33 col 14 changed to oldrdy_
\* Process variable oldack of process BufRecv at line 51 col 18 changed to oldack_
CONSTANT defaultInitValue
VARIABLES valSet, inchan, outchan, q, pc, oldrdy_, oldack_, oldrdy, oldack, 
          rval

vars == << valSet, inchan, outchan, q, pc, oldrdy_, oldack_, oldrdy, oldack, 
           rval >>

ProcSet == {"ssend"} \cup {"bufrecv"} \cup {"bufsend"} \cup {"rrecv"}

Init == (* Global variables *)
        /\ valSet = 0..3
        /\ inchan \in [val : valSet,
                       rdy : 0..1,
                       ack : 0..1]
        /\ outchan \in [val : valSet,
                        rdy : 0..1,
                        ack : 0..1]
        /\ q = <<>>
        (* Process SSend *)
        /\ oldrdy_ = defaultInitValue
        (* Process BufRecv *)
        /\ oldack_ = defaultInitValue
        (* Process BufSend *)
        /\ oldrdy = defaultInitValue
        (* Process RRecv *)
        /\ oldack = defaultInitValue
        /\ rval = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = "ssend" -> "ss0"
                                        [] self = "bufrecv" -> "br0"
                                        [] self = "bufsend" -> "bs0"
                                        [] self = "rrecv" -> "rr0"]

ss0 == /\ pc["ssend"] = "ss0"
       /\ pc' = [pc EXCEPT !["ssend"] = "ss1"]
       /\ UNCHANGED << valSet, inchan, outchan, q, oldrdy_, oldack_, oldrdy, 
                       oldack, rval >>

ss1 == /\ pc["ssend"] = "ss1"
       /\ inchan.rdy = inchan.ack
       /\ pc' = [pc EXCEPT !["ssend"] = "ss2"]
       /\ UNCHANGED << valSet, inchan, outchan, q, oldrdy_, oldack_, oldrdy, 
                       oldack, rval >>

ss2 == /\ pc["ssend"] = "ss2"
       /\ oldrdy_' = inchan.rdy
       /\ inchan' = [inchan EXCEPT !.rdy = 1 - inchan.rdy]
       /\ PrintT(<<inchan', "SSend">>)
       /\ Assert((inchan'.val \in valSet), 
                 "Failure of assertion at line 26, column 5 of macro called at line 43, column 13.")
       /\ Assert((inchan'.rdy \in 0..1), 
                 "Failure of assertion at line 27, column 5 of macro called at line 43, column 13.")
       /\ Assert((inchan'.ack \in 0..1), 
                 "Failure of assertion at line 28, column 5 of macro called at line 43, column 13.")
       /\ Assert((q \in Seq(valSet)), 
                 "Failure of assertion at line 29, column 5 of macro called at line 43, column 13.")
       /\ Assert((inchan'.rdy # oldrdy_'), 
                 "Failure of assertion at line 44, column 13.")
       /\ Assert((inchan'.rdy # inchan'.ack), 
                 "Failure of assertion at line 45, column 13.")
       /\ pc' = [pc EXCEPT !["ssend"] = "ss0"]
       /\ UNCHANGED << valSet, outchan, q, oldack_, oldrdy, oldack, rval >>

SSend == ss0 \/ ss1 \/ ss2

br0 == /\ pc["bufrecv"] = "br0"
       /\ pc' = [pc EXCEPT !["bufrecv"] = "br1"]
       /\ UNCHANGED << valSet, inchan, outchan, q, oldrdy_, oldack_, oldrdy, 
                       oldack, rval >>

br1 == /\ pc["bufrecv"] = "br1"
       /\ inchan.rdy # inchan.ack /\ Len(q) < MaxBufSize
       /\ pc' = [pc EXCEPT !["bufrecv"] = "br2"]
       /\ UNCHANGED << valSet, inchan, outchan, q, oldrdy_, oldack_, oldrdy, 
                       oldack, rval >>

br2 == /\ pc["bufrecv"] = "br2"
       /\ oldack_' = inchan.ack
       /\ inchan' = [inchan EXCEPT !.ack = 1 - inchan.ack]
       /\ q' = Append(q, inchan'.val)
       /\ PrintT(<<inchan', "BufRecv", q'>>)
       /\ Assert((inchan'.val \in valSet), 
                 "Failure of assertion at line 26, column 5 of macro called at line 61, column 13.")
       /\ Assert((inchan'.rdy \in 0..1), 
                 "Failure of assertion at line 27, column 5 of macro called at line 61, column 13.")
       /\ Assert((inchan'.ack \in 0..1), 
                 "Failure of assertion at line 28, column 5 of macro called at line 61, column 13.")
       /\ Assert((q' \in Seq(valSet)), 
                 "Failure of assertion at line 29, column 5 of macro called at line 61, column 13.")
       /\ Assert((inchan'.ack # oldack_'), 
                 "Failure of assertion at line 62, column 13.")
       /\ Assert((inchan'.rdy = inchan'.ack), 
                 "Failure of assertion at line 63, column 13.")
       /\ pc' = [pc EXCEPT !["bufrecv"] = "br0"]
       /\ UNCHANGED << valSet, outchan, oldrdy_, oldrdy, oldack, rval >>

BufRecv == br0 \/ br1 \/ br2

bs0 == /\ pc["bufsend"] = "bs0"
       /\ pc' = [pc EXCEPT !["bufsend"] = "bs1"]
       /\ UNCHANGED << valSet, inchan, outchan, q, oldrdy_, oldack_, oldrdy, 
                       oldack, rval >>

bs1 == /\ pc["bufsend"] = "bs1"
       /\ outchan.rdy = outchan.ack
       /\ pc' = [pc EXCEPT !["bufsend"] = "bs2"]
       /\ UNCHANGED << valSet, inchan, outchan, q, oldrdy_, oldack_, oldrdy, 
                       oldack, rval >>

bs2 == /\ pc["bufsend"] = "bs2"
       /\ oldrdy' = outchan.rdy
       /\ outchan' = [outchan EXCEPT !.rdy = 1 - outchan.rdy]
       /\ PrintT(<<outchan', "BufSend">>)
       /\ Assert((outchan'.val \in valSet), 
                 "Failure of assertion at line 26, column 5 of macro called at line 78, column 13.")
       /\ Assert((outchan'.rdy \in 0..1), 
                 "Failure of assertion at line 27, column 5 of macro called at line 78, column 13.")
       /\ Assert((outchan'.ack \in 0..1), 
                 "Failure of assertion at line 28, column 5 of macro called at line 78, column 13.")
       /\ Assert((q \in Seq(valSet)), 
                 "Failure of assertion at line 29, column 5 of macro called at line 78, column 13.")
       /\ Assert((outchan'.rdy # oldrdy'), 
                 "Failure of assertion at line 79, column 13.")
       /\ Assert((outchan'.rdy # outchan'.ack), 
                 "Failure of assertion at line 80, column 13.")
       /\ pc' = [pc EXCEPT !["bufsend"] = "bs0"]
       /\ UNCHANGED << valSet, inchan, q, oldrdy_, oldack_, oldack, rval >>

BufSend == bs0 \/ bs1 \/ bs2

rr0 == /\ pc["rrecv"] = "rr0"
       /\ pc' = [pc EXCEPT !["rrecv"] = "rr1"]
       /\ UNCHANGED << valSet, inchan, outchan, q, oldrdy_, oldack_, oldrdy, 
                       oldack, rval >>

rr1 == /\ pc["rrecv"] = "rr1"
       /\ outchan.rdy # outchan.ack /\ Len(q) > 0
       /\ pc' = [pc EXCEPT !["rrecv"] = "rr2"]
       /\ UNCHANGED << valSet, inchan, outchan, q, oldrdy_, oldack_, oldrdy, 
                       oldack, rval >>

rr2 == /\ pc["rrecv"] = "rr2"
       /\ oldack' = outchan.ack
       /\ outchan' = [outchan EXCEPT !.ack = 1 - outchan.ack]
       /\ rval' = Head(q)
       /\ q' = Tail(q)
       /\ PrintT(<<outchan', "RRecv", rval'>>)
       /\ Assert((outchan'.val \in valSet), 
                 "Failure of assertion at line 26, column 5 of macro called at line 97, column 13.")
       /\ Assert((outchan'.rdy \in 0..1), 
                 "Failure of assertion at line 27, column 5 of macro called at line 97, column 13.")
       /\ Assert((outchan'.ack \in 0..1), 
                 "Failure of assertion at line 28, column 5 of macro called at line 97, column 13.")
       /\ Assert((q' \in Seq(valSet)), 
                 "Failure of assertion at line 29, column 5 of macro called at line 97, column 13.")
       /\ Assert((outchan'.ack # oldack'), 
                 "Failure of assertion at line 98, column 13.")
       /\ Assert((outchan'.rdy = outchan'.ack), 
                 "Failure of assertion at line 99, column 13.")
       /\ pc' = [pc EXCEPT !["rrecv"] = "rr0"]
       /\ UNCHANGED << valSet, inchan, oldrdy_, oldack_, oldrdy >>

RRecv == rr0 \/ rr1 \/ rr2

Next == SSend \/ BufRecv \/ BufSend \/ RRecv

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=================================================================

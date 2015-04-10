-------------------------- MODULE TE4 ---------------------------
EXTENDS Integers, Sequences, TLC
CONSTANTS Msg, RingBufSz
ASSUME RingBufSz \in Int

AppendAll(to, from) == [j \in 1..(Len(from) + Len(to)) |-> IF j <= Len(to) THEN to[j] ELSE from[j-Len(to)]]


(******************************************************)
(*     Translation Engine 4 Algorithm Abstraction     *)
(******************************************************)


(*
--algorithm TE4 {
  variables
    source = << >>,       \* starting source of messages
    sentUnacked = << >>,  \* msgs sent from JMS -> Inbounder, but unacked
    ackChan = << >>,      \* acks from Outbounder -> JMS, ack vals == uid
    sentAcked = << >>,    \* msgs sent from JMS -> Inbounder and acked by Outbounder
    ringBuffer = << >>,   \* RingBuffer is modeled as a simple FIFO
    dummy = "REMOVE ME";


  macro TransferAll(to, from) {
    to := AppendAll(to, from);
    from := << >>;  \* drained
  }

  macro TransferOne(to, from) {
    to := Append(to, Head(from));
    from := Tail(from);    
  }

  process (Inbounder = "inbounder") 
    variables inmsg;
  {
  in1:  while (TRUE) {
          \* TODO: when there are multiple JMSSources, need a `with` clause here to randomly choose one
          await Len(sentUnacked) > 0 /\ Len(ringBuffer) < RingBufSz;  \* could increase to larger # to ensure batching

          if ( (RingBufSz - Len(ringBuffer)) >= Len(sentUnacked) ) {
            print <<ringBuffer, "<=RB==== BEFORE Drain ===SA=>", sentUnacked>>;          
            TransferAll(ringBuffer, sentUnacked);  \* simulates putting on in batches          
            print <<ringBuffer, "<=RB==== AFTER Drain ===SA=>", sentUnacked>>;
            
           } else {
            print <<ringBuffer, "<=RB==== ++BEFORE SendFirst ===SA=>", sentUnacked>>;
            TransferOne(ringBuffer, sentUnacked);
            print <<ringBuffer, "<=RB==== ++AFTER SendFirst ===SA=>", sentUnacked>>;
          }
        }
  };  \* end process Inbounder

  process (JMSSource = "jmsSource")  \* TODO: there can be multiples of these
    variables uid = 0, inmsg, ack;
  {
  js1:  while (TRUE) {
          either with (msg \in Msg) {
            (* JMS queue receives messages from unspecified upstream system (Live) *)
            source := Append(source, <<uid, msg>>);
            \* print <<uid, msg>>;
            uid := uid + 1;
            
          } or {
            (* send messages to Inbounder *)
            await Len(source) > 0;
            inmsg := Head(source);
            source := Tail(source);
            sentUnacked := Append(sentUnacked, inmsg);
            \* print <<"sent, unacked:", inmsg>>;
            
          } or {
            (* read acks from Outbounder *)
            await Len(ackChan) > 0;
            ack := Head(ackChan);
            ackChan := Tail(ackChan);
            inmsg := Head(sentUnacked);
            \* ensure that acks return in order and match next unacked msg
            assert ack = inmsg[1];
            sentUnacked := Tail(sentUnacked);
            sentAcked := Append(sentAcked, inmsg);
            \* print <<" .... ACK RECVD:", ack>>
          };
        }
  }; \* end process JMSSource
}
*)
\* BEGIN TRANSLATION
\* Process variable inmsg of process Inbounder at line 36 col 15 changed to inmsg_
CONSTANT defaultInitValue
VARIABLES source, sentUnacked, ackChan, sentAcked, ringBuffer, dummy, inmsg_, 
          uid, inmsg, ack

vars == << source, sentUnacked, ackChan, sentAcked, ringBuffer, dummy, inmsg_, 
           uid, inmsg, ack >>

ProcSet == {"inbounder"} \cup {"jmsSource"}

Init == (* Global variables *)
        /\ source = << >>
        /\ sentUnacked = << >>
        /\ ackChan = << >>
        /\ sentAcked = << >>
        /\ ringBuffer = << >>
        /\ dummy = "REMOVE ME"
        (* Process Inbounder *)
        /\ inmsg_ = defaultInitValue
        (* Process JMSSource *)
        /\ uid = 0
        /\ inmsg = defaultInitValue
        /\ ack = defaultInitValue

Inbounder == /\ Len(sentUnacked) > 0 /\ Len(ringBuffer) < RingBufSz
             /\ IF (RingBufSz - Len(ringBuffer)) >= Len(sentUnacked)
                   THEN /\ PrintT(<<ringBuffer, "<=RB==== BEFORE Drain ===SA=>", sentUnacked>>)
                        /\ ringBuffer' = AppendAll(ringBuffer, sentUnacked)
                        /\ sentUnacked' = << >>
                        /\ PrintT(<<ringBuffer', "<=RB==== AFTER Drain ===SA=>", sentUnacked'>>)
                   ELSE /\ PrintT(<<ringBuffer, "<=RB==== ++BEFORE SendFirst ===SA=>", sentUnacked>>)
                        /\ ringBuffer' = Append(ringBuffer, Head(sentUnacked))
                        /\ sentUnacked' = Tail(sentUnacked)
                        /\ PrintT(<<ringBuffer', "<=RB==== ++AFTER SendFirst ===SA=>", sentUnacked'>>)
             /\ UNCHANGED << source, ackChan, sentAcked, dummy, inmsg_, uid, 
                             inmsg, ack >>

JMSSource == /\ \/ /\ \E msg \in Msg:
                        /\ source' = Append(source, <<uid, msg>>)
                        /\ uid' = uid + 1
                   /\ UNCHANGED <<sentUnacked, ackChan, sentAcked, inmsg, ack>>
                \/ /\ Len(source) > 0
                   /\ inmsg' = Head(source)
                   /\ source' = Tail(source)
                   /\ sentUnacked' = Append(sentUnacked, inmsg')
                   /\ UNCHANGED <<ackChan, sentAcked, uid, ack>>
                \/ /\ Len(ackChan) > 0
                   /\ ack' = Head(ackChan)
                   /\ ackChan' = Tail(ackChan)
                   /\ inmsg' = Head(sentUnacked)
                   /\ Assert(ack' = inmsg'[1], 
                             "Failure of assertion at line 81, column 13.")
                   /\ sentUnacked' = Tail(sentUnacked)
                   /\ sentAcked' = Append(sentAcked, inmsg')
                   /\ UNCHANGED <<source, uid>>
             /\ UNCHANGED << ringBuffer, dummy, inmsg_ >>

Next == Inbounder \/ JMSSource

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=================================================================

-------------------------- MODULE TE4 ---------------------------
EXTENDS Integers, Sequences, TLC
CONSTANTS Msg, RingBufSz
ASSUME RingBufSz \in Int

AppendAll(to, from) == [j \in 1..(Len(to) + Len(from)) |-> IF j <= Len(to) THEN to[j] ELSE from[j-Len(to)]]

(*-------------------------------------------------------------------------*)
(* SendAcks returns a new version of the ack channel,                      *)
(* with the acks vals in from appended to it                               *)
(*    to => seq of uids (ack vals)                                         *)
(*  from => seq of <<uid, msg>>, so this plucks record[1] (the uid/ackval) *)
(*-------------------------------------------------------------------------*)
SendAcks(to, from) == [j \in 1..(Len(to) + Len(from)) |-> IF j <= Len(to) THEN to[j] ELSE from[j-Len(to)][1]]


(******************************************************)
(*     Translation Engine 4 Algorithm Abstraction     *)
(******************************************************)

(*
--algorithm TE4 {
  variables
    qSource = << >>,       \* starting source of messages
    qSentUnacked = << >>,  \* msgs sent from JMS -> Inbounder, but unacked
    ackChan = << >>,       \* acks from Outbounder -> JMS, ack vals == uid
    qSentAcked = << >>,    \* msgs sent from JMS -> Inbounder and acked by Outbounder
    qRingBuffer = << >>,   \* RingBuffer is modeled as a simple FIFO
    qRcvdUnacked = << >>,  \* RingBuf -> Outbounder before acked
    qRcvdAcked = << >>,    \* final sink of messages
    outBatchSize = 4,      \* size of batches as pulled from RingBuffer
    qEmpty = << >>;

  macro CopyAll(to, from) {
    to := AppendAll(to, from);    
  }

  macro TransferAll(to, from) {
    to := AppendAll(to, from);
    from := << >>;
  }

  macro TransferOne(to, from) {
    to := Append(to, Head(from));
    from := Tail(from);    
  }
  
  \* transfer (append) all entries on `from` seq to both `to1` and `to2` seqs
  macro DuplexTransferAll(to1, to2, from) {
    to1 := AppendAll(to1, from);
    to2 := AppendAll(to2, from);
    from := << >>;  
  }
  
  \* transfer (append) one entry on `from` seq to both `to1` and `to2` seqs
  macro DuplexTransferOne(to1, to2, from) {
    to1 := Append(to1, Head(from));
    to2 := Append(to2, Head(from));
    from := Tail(from);  
  }

  process (Outbounder = "outbounder")
    variables ackBuf = << >>;  \* nextEvent, 
  {
  ob1:  while (TRUE) {
          await Len(qRingBuffer) > 0;
          \* nextEvent := Head(qRingBuffer);  \** TODO: why do we need this?
          \** TODO: need to have multiple sinks and route the output to the correct one ...
          TransferOne(qRcvdUnacked, qRingBuffer);
          \* if endOfBatch=true, then send acks
          if (((uid + 1) % outBatchSize) = 0) {
  ob2:      ackChan := SendAcks(ackChan, qRcvdUnacked);
            TransferAll(qRcvdAcked, qRcvdUnacked);
            print <<"OUTBOUNDER: qRcvdAcked", qRcvdAcked>>;
          };
        } 
  }; \* end process Outbounder

  process (Inbounder = "inbounder") 
  {
  ib1:  while (TRUE) {
          \* TODO: when there are multiple JMSSources, need a `with` clause here to randomly choose one
          await Len(qSource) > 0 /\ Len(qRingBuffer) < RingBufSz;  \* could increase to larger # to ensure batching

          (* get messages from JMSSource -> RingBuffer *)
          if ( (RingBufSz - Len(qRingBuffer)) >= Len(qSentUnacked) ) {
            DuplexTransferAll(qSentUnacked, qRingBuffer, qSource);
          } else {
            DuplexTransferOne(qSentUnacked, qRingBuffer, qSource);
          };
        }
  };  \* end process Inbounder

  process (JMSSource = "jmsSource")  \* TODO: there can be multiples of these
    variables uid = 0, inmsg, ack;
  {
  js1:  while (TRUE) {
          either with (msg \in Msg) {
            (* JMS queue receives messages from unspecified upstream system (Live) *)
            qSource := Append(qSource, <<uid, msg>>);
            \* print <<uid, msg>>;
            uid := uid + 1;
            
          } or {
            (* read acks from Outbounder *)
            await Len(ackChan) > 0;
            ack := Head(ackChan);
            ackChan := Tail(ackChan);
            inmsg := Head(qSentUnacked);
            \* ensure that acks return in order and match next unacked msg
            assert ack = inmsg[1];
            qSentUnacked := Tail(qSentUnacked);
            qSentAcked := Append(qSentAcked, inmsg);
            \* print <<" .... ACK RECVD:", ack>>
          };
        }
  }; \* end process JMSSource
}
*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES qSource, qSentUnacked, ackChan, qSentAcked, qRingBuffer, 
          qRcvdUnacked, qRcvdAcked, outBatchSize, qEmpty, pc, ackBuf, uid, 
          inmsg, ack

vars == << qSource, qSentUnacked, ackChan, qSentAcked, qRingBuffer, 
           qRcvdUnacked, qRcvdAcked, outBatchSize, qEmpty, pc, ackBuf, uid, 
           inmsg, ack >>

ProcSet == {"outbounder"} \cup {"inbounder"} \cup {"jmsSource"}

Init == (* Global variables *)
        /\ qSource = << >>
        /\ qSentUnacked = << >>
        /\ ackChan = << >>
        /\ qSentAcked = << >>
        /\ qRingBuffer = << >>
        /\ qRcvdUnacked = << >>
        /\ qRcvdAcked = << >>
        /\ outBatchSize = 4
        /\ qEmpty = << >>
        (* Process Outbounder *)
        /\ ackBuf = << >>
        (* Process JMSSource *)
        /\ uid = 0
        /\ inmsg = defaultInitValue
        /\ ack = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = "outbounder" -> "ob1"
                                        [] self = "inbounder" -> "ib1"
                                        [] self = "jmsSource" -> "js1"]

ob1 == /\ pc["outbounder"] = "ob1"
       /\ Len(qRingBuffer) > 0
       /\ qRcvdUnacked' = Append(qRcvdUnacked, Head(qRingBuffer))
       /\ qRingBuffer' = Tail(qRingBuffer)
       /\ IF ((uid + 1) % outBatchSize) = 0
             THEN /\ pc' = [pc EXCEPT !["outbounder"] = "ob2"]
             ELSE /\ pc' = [pc EXCEPT !["outbounder"] = "ob1"]
       /\ UNCHANGED << qSource, qSentUnacked, ackChan, qSentAcked, qRcvdAcked, 
                       outBatchSize, qEmpty, ackBuf, uid, inmsg, ack >>

ob2 == /\ pc["outbounder"] = "ob2"
       /\ ackChan' = SendAcks(ackChan, qRcvdUnacked)
       /\ qRcvdAcked' = AppendAll(qRcvdAcked, qRcvdUnacked)
       /\ qRcvdUnacked' = << >>
       /\ PrintT(<<"OUTBOUNDER: qRcvdAcked", qRcvdAcked'>>)
       /\ pc' = [pc EXCEPT !["outbounder"] = "ob1"]
       /\ UNCHANGED << qSource, qSentUnacked, qSentAcked, qRingBuffer, 
                       outBatchSize, qEmpty, ackBuf, uid, inmsg, ack >>

Outbounder == ob1 \/ ob2

ib1 == /\ pc["inbounder"] = "ib1"
       /\ Len(qSource) > 0 /\ Len(qRingBuffer) < RingBufSz
       /\ IF (RingBufSz - Len(qRingBuffer)) >= Len(qSentUnacked)
             THEN /\ qSentUnacked' = AppendAll(qSentUnacked, qSource)
                  /\ qRingBuffer' = AppendAll(qRingBuffer, qSource)
                  /\ qSource' = << >>
             ELSE /\ qSentUnacked' = Append(qSentUnacked, Head(qSource))
                  /\ qRingBuffer' = Append(qRingBuffer, Head(qSource))
                  /\ qSource' = Tail(qSource)
       /\ pc' = [pc EXCEPT !["inbounder"] = "ib1"]
       /\ UNCHANGED << ackChan, qSentAcked, qRcvdUnacked, qRcvdAcked, 
                       outBatchSize, qEmpty, ackBuf, uid, inmsg, ack >>

Inbounder == ib1

js1 == /\ pc["jmsSource"] = "js1"
       /\ \/ /\ \E msg \in Msg:
                  /\ qSource' = Append(qSource, <<uid, msg>>)
                  /\ uid' = uid + 1
             /\ UNCHANGED <<qSentUnacked, ackChan, qSentAcked, inmsg, ack>>
          \/ /\ Len(ackChan) > 0
             /\ ack' = Head(ackChan)
             /\ ackChan' = Tail(ackChan)
             /\ inmsg' = Head(qSentUnacked)
             /\ Assert(ack' = inmsg'[1], 
                       "Failure of assertion at line 113, column 13.")
             /\ qSentUnacked' = Tail(qSentUnacked)
             /\ qSentAcked' = Append(qSentAcked, inmsg')
             /\ UNCHANGED <<qSource, uid>>
       /\ pc' = [pc EXCEPT !["jmsSource"] = "js1"]
       /\ UNCHANGED << qRingBuffer, qRcvdUnacked, qRcvdAcked, outBatchSize, 
                       qEmpty, ackBuf >>

JMSSource == js1

Next == Outbounder \/ Inbounder \/ JMSSource

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=================================================================

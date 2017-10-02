-------------------- MODULE hlcnaive2 -------------------
EXTENDS Integers
CONSTANT N, STOP, EPSILON
ASSUME N \in Nat \ {0,1}
Procs == 1..N

SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j

(* Hybrid Logical Clocks naive algorithm
--algorithm hlcnaive2 {
  \* shared/auxiliary variables; initially physical clocks are set to 0
  variable pt = [j \in Procs |-> 0], msg= [j \in Procs |-> 0];

  fair process (j \in Procs)
  variable lc=0;
   { J0: while (pt[self] < STOP)
         { either 
            \* local or receive event
	        LRec:{\* phy clocks cannot diverge more than EPSILON thanks to NTP
         	      await(\A k \in Procs: pt[self] < pt[k]+ EPSILON);
                  pt[self] := pt[self] +1;
                  \* j also receives the msg if any
                  lc:= SetMax({pt[self], lc+1, msg[self]+1}); 
		          } 
	        or \* send event
	        Send:{ \* phy clocks cannot diverge more than EPSILON thanks to NTP
                  await(\A k \in Procs: pt[self] < pt[k]+ EPSILON);
                  pt[self] := pt[self] +1;
                  lc := SetMax({lc+1, pt[self]});
                  \* write the message to k
                  with (k \in Procs \ {self}) {msg[k] := lc} 
	              } 		 
	     }\* end while
   }\* end process
}\* end alg
*)
\* BEGIN TRANSLATION
VARIABLES pt, msg, pc, lc

vars == << pt, msg, pc, lc >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ pt = [j \in Procs |-> 0]
        /\ msg = [j \in Procs |-> 0]
        (* Process j *)
        /\ lc = [self \in Procs |-> 0]
        /\ pc = [self \in ProcSet |-> "J0"]

J0(self) == /\ pc[self] = "J0"
            /\ IF pt[self] < STOP
                  THEN /\ \/ /\ pc' = [pc EXCEPT ![self] = "LRec"]
                          \/ /\ pc' = [pc EXCEPT ![self] = "Send"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << pt, msg, lc >>

LRec(self) == /\ pc[self] = "LRec"
              /\ (\A k \in Procs: pt[self] < pt[k]+ EPSILON)
              /\ pt' = [pt EXCEPT ![self] = pt[self] +1]
              /\ lc' = [lc EXCEPT ![self] = SetMax({pt'[self], lc[self]+1, msg[self]+1})]
              /\ pc' = [pc EXCEPT ![self] = "J0"]
              /\ msg' = msg

Send(self) == /\ pc[self] = "Send"
              /\ (\A k \in Procs: pt[self] < pt[k]+ EPSILON)
              /\ pt' = [pt EXCEPT ![self] = pt[self] +1]
              /\ lc' = [lc EXCEPT ![self] = SetMax({lc[self]+1, pt'[self]})]
              /\ \E k \in Procs \ {self}:
                   msg' = [msg EXCEPT ![k] = lc'[self]]
              /\ pc' = [pc EXCEPT ![self] = "J0"]

j(self) == J0(self) \/ LRec(self) \/ Send(self)

Next == (\E self \in Procs: j(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(j(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* Boundedness
TypeOK == (\A k \in Procs: lc[k] >= pt[k])
Sync == (\A k,l \in Procs: pt[k] <= pt[l]+EPSILON)
Bounded == (\A k \in Procs: lc[k] < pt[k] + N*(EPSILON+1)) \* this is violated!!! in general unbounded!
\* Stabilization

==================================================

\* Hi-lock: (("\\\\\\*.+$" (0 (quote org-level-3) t)))
\* Hi-lock: (("^.*\\(?:==\\).*$" (0 (quote org-level-1) t)))
-------------------- MODULE vc -------------------
EXTENDS Integers
CONSTANT N, STOP, EPSILON
ASSUME N \in Nat \ {0,1}
Procs == 1..N

SetMax(S) == CHOOSE i \in S : \A k \in S : i >= k

(* Vector Clocks, augmentedtime algorithm
--algorithm vca {
\* initially physical clock is set to 0
  variable  pt = [j \in Procs |-> 0], msg= [j \in Procs |-> {}];

  define{
  VCPrune(v1,p) == {c \in v1: c.val>p-EPSILON /\ (\A d \in v1: d.node=c.node => d.val<=c.val)}
  VCget(v1,s) == CHOOSE c \in v1: c.node=s \* is there a way to return c.val?
  VCCget(v1,s) == IF (\E c \in v1: c.node=s) THEN (CHOOSE c \in v1: c.node=s) ELSE [node|->s, val|->0]
  VCless(v1,s) ==  {c \in v1: c.node#s}
  }

  fair process (j \in Procs)
  variable vc= {[node |-> self, val|->0]};
  { J0: while (pt[self] < STOP)
        { either \* local or receive event
	        J1:{ \* phy clocks cannot diverge more than EPSILON
         	     await(\A k \in Procs: pt[self] < pt[k]+EPSILON); 
                 pt[self] := pt[self] +1;
                 vc := VCPrune(vc \union msg[self] \union {[node|->self, val|->SetMax({pt[self], VCget(vc,self).val+1, VCCget(msg[self],self).val+1})]}, pt[self]);                 
		   } 
	        or \* send event
	        J2:{ \* phy clocks cannot diverge more than EPSILON
                 await(\A k \in Procs: pt[self] < pt[k]+EPSILON); 
	             pt[self] := pt[self] +1;
		         vc:= VCless(vc,self) \union {[node|->self, val|->SetMax({VCget(vc,self).val+1, pt[self]})]};
		         \* write the message to k
		         with (k \in Procs \ {self}) {msg[k] := vc} 
	           } 		 
	    }    
   }
}
*)
\* BEGIN TRANSLATION
VARIABLES pt, msg, pc

(* define statement *)
VCPrune(v1,p) == {c \in v1: c.val>p-EPSILON /\ (\A d \in v1: d.node=c.node => d.val<=c.val)}
VCget(v1,s) == CHOOSE c \in v1: c.node=s
VCCget(v1,s) == IF (\E c \in v1: c.node=s) THEN (CHOOSE c \in v1: c.node=s) ELSE [node|->s, val|->0]
VCless(v1,s) ==  {c \in v1: c.node#s}

VARIABLE vc

vars == << pt, msg, pc, vc >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ pt = [j \in Procs |-> 0]
        /\ msg = [j \in Procs |-> {}]
        (* Process j *)
        /\ vc = [self \in Procs |-> {[node |-> self, val|->0]}]
        /\ pc = [self \in ProcSet |-> "J0"]

J0(self) == /\ pc[self] = "J0"
            /\ IF pt[self] < STOP
                  THEN /\ \/ /\ pc' = [pc EXCEPT ![self] = "J1"]
                          \/ /\ pc' = [pc EXCEPT ![self] = "J2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << pt, msg, vc >>

J1(self) == /\ pc[self] = "J1"
            /\ (\A k \in Procs: pt[self] < pt[k]+EPSILON)
            /\ pt' = [pt EXCEPT ![self] = pt[self] +1]
            /\ vc' = [vc EXCEPT ![self] = VCPrune(vc[self] \union msg[self] \union {[node|->self, val|->SetMax({pt'[self], VCget(vc[self],self).val+1, VCCget(msg[self],self).val+1})]}, pt'[self])]
            /\ pc' = [pc EXCEPT ![self] = "J0"]
            /\ msg' = msg

J2(self) == /\ pc[self] = "J2"
            /\ (\A k \in Procs: pt[self] < pt[k]+EPSILON)
            /\ pt' = [pt EXCEPT ![self] = pt[self] +1]
            /\ vc' = [vc EXCEPT ![self] = VCless(vc[self],self) \union {[node|->self, val|->SetMax({VCget(vc[self],self).val+1, pt'[self]})]}]
            /\ \E k \in Procs \ {self}:
                 msg' = [msg EXCEPT ![k] = vc'[self]]
            /\ pc' = [pc EXCEPT ![self] = "J0"]

j(self) == J0(self) \/ J1(self) \/ J2(self)

Next == (\E self \in Procs: j(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(j(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* Boundedness
VCCOK == (\A k \in Procs: VCget(vc[k],k).val >= pt[k] /\ VCget(vc[k],k).val <= pt[k] +EPSILON)
TypeOK == (\A k \in Procs: (\A v \in vc[k]: v.val >= pt[k] -EPSILON))
Sync == (\A k,l \in Procs: pt[k] <= pt[l] +EPSILON)
VCprop == (\A k,l \in Procs: VCget(vc[k],k).val >= VCCget(vc[l],k).val)
\* Stabilization 
==================================================
Add tests for stabilization ???

\* Using a set of <node,val> pairs to represent VC succinctly.

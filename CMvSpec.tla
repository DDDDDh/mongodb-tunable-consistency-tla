------------------------------ MODULE CMvSpec ------------------------------
(***************************************************************************
 TLA+ Specification for causal consistency model CMv
 ***************************************************************************)
 
EXTENDS Naturals, Sequences, TLC, Functions, RelationUtils, SequencesExt, FiniteSetsExt

InitVal == 0

RECURSIVE Seq2OpSet(_)
Seq2OpSet(s) == \* Transform a sequence s into the set of ops in s
    IF s = <<>> THEN {}
    ELSE LET h == Head(s)
             t == Tail(s)
         IN  h \cup Seq2OpSet(t)   
         

Ops(h, clients) ==
    UNION { Seq2OpSet(h[c]): c \in clients }
\* The program order of h \in History is a union of total orders among operations in the same session    
PO(h, clients) == UNION {Seq2Rel(h[c]): c \in clients }      
-------------------------------------------------
(*
  Auxiliary definitions for the axioms used in the definitions of causal consistency
*)

\* The set of operations that preceed o \in Operation in program order in history h \in History
StrictPOPast(h, clients, o) == InverseImage(PO(h, clients), o)
POPast(h, clients, o) == StrictPOPast(h, clients, o) \cup {o} \* Original definition in paper, including itself

\* The set of operations that preceed o \in Operation in causal order co
StrictCausalPast(co, o) == InverseImage(co, o)
CausalPast(co, o) == StrictCausalPast(co, o) \cup {o} \* Original definition in paper, including itself

\* The restriction of causal order co to the operations in the causal past of operation o \in Operation
StrictCausalHist(co, o) == co | StrictCausalPast(co, o)
CausalHist(co, o) == co | CausalPast(co, o) \* Original definition in paper

\* The restriction of arbitration arb to the operations in the causal past of operation o \in Operation
StrictCausalArb(co, arb, o) == arb | StrictCausalPast(co, o)
CausalArb(co, arb, o) == arb | CausalPast(co, o) \* Original definition in paper
-------------------------------------------------
(*
  Axioms used in the defintions of causal consistency
*)
RWRegSemantics(seq, o) == \* Is o \in Operation legal when it is appended to seq
    IF o.type = "write" THEN TRUE ELSE 
    LET wseq == SelectSeq(seq, LAMBDA op : op.type = "write" /\ op.key = o.key)
         IN  IF wseq = <<>> THEN o.val = InitVal
             ELSE o.val = wseq[Len(wseq)].val

PreSeq(seq, o) == \* All of the operations before o in sequence seq
    LET so == Seq2Rel(seq)
    IN SelectSeq(seq, LAMBDA op: <<op, o>> \in so)

RWRegSemanticsOperations(seq, ops) == \* For ops \subseteq Range(seq), is \A o \in ops legal 
    \A o \in ops:
        LET preSeq == PreSeq(seq, o)
        IN RWRegSemantics(preSeq, o)

AxCausalValue(co, o) ==
    LET seqs == AllLinearExtensions(StrictCausalHist(co, o), StrictCausalPast(co, o))
    IN  \E seq \in seqs: RWRegSemantics(seq, o)

AxCausalSeq(h, clients, co, o) ==
    LET popast == POPast(h, clients, o)
        seqs == AllLinearExtensions(CausalHist(co, o), CausalPast(co, o))
    IN  \E seq \in seqs: RWRegSemanticsOperations(seq, popast)

AxCausalArb(co, arb, o) == 
    LET seq == AnyLinearExtension(StrictCausalArb(co, arb, o), StrictCausalPast(co, o)) \* it is unique
    IN  RWRegSemantics(seq, o)

CMv(h, clients) ==
    LET ops == Ops(h, clients)
    IN \E co \in StrictPartialOrderSubset(ops): \* To do 
        /\ Respect(co, PO(h, clients))
        /\ \E arb \in {Seq2Rel(le) : le \in AllLinearExtensions(co, ops)}:
            /\ \A o \in ops: AxCausalArb(co, arb, o)
        /\ \A o \in ops: AxCausalSeq(h, clients, co, o)    


=============================================================================
\* Modification History
\* Last modified Sun Jul 31 20:39:57 CST 2022 by dh
\* Created Sun Jul 31 10:58:26 CST 2022 by dh

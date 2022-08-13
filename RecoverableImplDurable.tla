----------------------- MODULE RecoverableImplDurable -----------------------
EXTENDS MongoDBCC_Recoverable
-----------------------------------------------------------------------------

RECURSIVE RebuildSeq(_)
RebuildSeq(seq) ==
    IF seq = <<>> THEN <<>>
        ELSE LET head == Head(seq)
             IN LET newMsg == [ type |-> head.type, s |-> head.s, aot |-> head.aot, ct |-> head.ct ]
                IN <<newMsg>> \o RebuildSeq(Tail(seq))
                
                            
RebuildState(state, server) ==
    [s \in server |-> [s0 \in server |-> [p |-> state[s][s0].p, l |-> state[s][s0].l ] ] ]

RebuildCp(cp, nodes) ==
    [s \in nodes |-> [ p |-> cp[s].p, l |-> cp[s].l ] ]     
        
DURABLE == INSTANCE MongoDBCC_Durable WITH State <- RebuildState(State, Server),
                                           Cp <- RebuildCp(Cp, Server \cup Client)

THEOREM Refinement == Spec => DURABLE!Spec 

=============================================================================
\* Modification History
\* Last modified Sat Aug 13 19:14:47 CST 2022 by dh
\* Created Sat Aug 13 17:58:14 CST 2022 by dh

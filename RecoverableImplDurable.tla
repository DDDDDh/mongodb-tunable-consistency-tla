----------------------- MODULE RecoverableImplDurable -----------------------
EXTENDS MongoDBCC_Recoverable
-----------------------------------------------------------------------------

RebuildSingleCp(cp) ==
    [ p |-> cp.p, l |-> cp.l ]

RECURSIVE RebuildSeq(_)
RebuildSeq(seq) ==
    IF seq = <<>> THEN <<>>
    ELSE LET head == Head(seq)
          IN LET newMsg == [ type |-> head.type, s |-> head.s, aot |-> head.aot, ct |-> head.ct, cp |-> RebuildSingleCp(head.cp) ]
              IN <<newMsg>> \o RebuildSeq(Tail(seq))
                
RECURSIVE RebuildOplog(_)
RebuildOplog(oplog) ==
    IF oplog = <<>> THEN <<>>
    ELSE LET head == Head(oplog)
         IN  LET newLog == [ k |-> head.k, v |-> head.v, ot |-> head.ot ]
             IN  <<newLog>> \o RebuildOplog(Tail(oplog))
        
                         
RebuildState(state, server) ==
    [s \in server |-> [s0 \in server |-> [p |-> state[s][s0].p, l |-> state[s][s0].l ] ] ]

RebuildState2(state, server) ==
    [s \in server |-> [ p |-> state[s].p, l |-> state[s].l ] ]    

RebuildCp(cp, nodes) ==
    [s \in nodes |-> [ p |-> cp[s].p, l |-> cp[s].l ] ]     
        
DURABLE == INSTANCE MongoDBCC_Durable WITH \*State <- RebuildState(State, Server),
                                           State <- [s \in Server |-> RebuildState2(State[s], Server)],
                                           Cp <- RebuildCp(Cp, Server \cup Client),
                                           ServerMsg <- [ s \in Server |-> RebuildSeq(ServerMsg[s])],
                                           Oplog <- [ s \in Server |-> RebuildOplog(Oplog[s])] 

THEOREM Refinement == Spec => DURABLE!Spec 

=============================================================================
\* Modification History
\* Last modified Sun Aug 14 19:50:09 CST 2022 by dh
\* Created Sat Aug 13 17:58:14 CST 2022 by dh

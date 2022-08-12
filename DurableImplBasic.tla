-------------------------- MODULE DurableImplBasic --------------------------
EXTENDS MongoDBCC_Durable
-----------------------------------------------------------------------------

RECURSIVE RebuildSeq(_)
RebuildSeq(seq) ==
    IF seq = <<>> THEN <<>>
        ELSE LET head == Head(seq)
             IN LET newMsg == [ type |-> head.type, s |-> head.s, aot |-> head.aot, ct |-> head.ct ]
                IN <<newMsg>> \o RebuildSeq(Tail(seq))

BASIC == INSTANCE MongoDBCC_Basic WITH ServerMsg <- [ s \in Server |-> RebuildSeq(ServerMsg[s])]

THEOREM Refinement == Spec => BASIC!Spec 

=============================================================================
\* Modification History
\* Last modified Fri Aug 12 20:49:09 CST 2022 by dh
\* Created Fri Aug 12 16:58:09 CST 2022 by dh

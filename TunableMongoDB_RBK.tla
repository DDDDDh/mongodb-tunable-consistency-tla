------------------------- MODULE TunableMongoDB_RBK -------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* constants and variables
CONSTANTS Client, Server,       \* the set of clients and servers
          Key, Value,           \* the set of keys and values
          Nil,                  \* model value, place holder
          OpTimes,              \* op count at most
          PtStop,               \* max physical time
          WriteNumber,          \* Para: writeConcern number -> should be set even when w:maj
          ReadConcern,          \* Para: read concern
          ReadPreference,       \* Para: read preference
          WriteConcern          \* Para: write concern

VARIABLES Primary,        \* Primary node
          Secondary,      \* secondary nodes
          Oplog,          \* oplog[s]: oplog at server[s]
          Store,          \* store[s]: data stored at server[s]
          Ct,             \* Ct[s]: cluster time at node s
          Ot,             \* Ot[s]: the last applied operation time at server s
          ServerMsg,      \* ServerMsg[s]: the channel of heartbeat msgs at server s
          Pt,             \* Pt[s]: physical time at server s
          Cp,             \* Cp[s]: majority commit point at server s
          State,          \* State[s]: the latest Ot of all servers that server s knows
          CurrentTerm,    \* CurrentTerm[s]: current election term at server s 
                          \* -> updated in update_position, heartbeat and replicate
          ReadyToServe,   \* equal to 0 before any primary is elected
          SyncSource,     \* sync source of server node s     
          \* Following are the Tunable related vars
          BlockedClient,  \* BlockedClient: Client operations in progress
          BlockedThread,  \* BlockedThread: blocked user thread and content
          History,        \* History[c]: History sequence at client c
          InMsgc,         \* InMsgc[c]: the channel of messages at client c \in Client
          InMsgs,         \* InMsgc[s]: the channel of messages at server s \in Server 
          OpCount,        \* OpCount[c]: op count for client c  
          SnapshotTable   \* SnapshotTable[s] : snapshot mapping table at server s  
          
-----------------------------------------------------------------------------          
\* group related vars to optimize code
electionVars == <<Primary, Secondary>>              \* vars that are related to election  
storageVars == <<Oplog, Store>>                     \* vars that are related to storage
messageVar == <<ServerMsg>>                         \* var that is related to message
servernodeVars == <<Ot, SyncSource>>                    \* vars that each server node holds for itself
learnableVars == <<Ct, State, Cp, CurrentTerm>>     \* vars that must learn from msgs
timeVar == <<Pt>>                                   \* var that is used for timing
functionalVar == <<ReadyToServe>>                   \* var that is used for some extra function  
clientnodeVars == <<History, OpCount>>

serverVars == <<electionVars, storageVars, messageVar, servernodeVars, learnableVars, timeVar, functionalVar>>
tunableVars == <<BlockedClient, BlockedThread, History, InMsgc, InMsgs, OpCount, SnapshotTable>>        
-----------------------------------------------------------------------------
ASSUME Cardinality(Client) >= 1  \* at least one client
ASSUME Cardinality(Server) >= 2  \* at least one primary and one secondary
ASSUME Cardinality(Key) >= 1  \* at least one object
ASSUME Cardinality(Value) >= 2  \* at least two values to update
ASSUME ReadConcern \in {"local", "majority", "linearizable"}
ASSUME WriteConcern \in {"zero", "num", "majority"}
ASSUME ReadPreference \in {"primary", "secondary"}
ASSUME WriteNumber <= Cardinality(Server) \* w:num cannot be greater than server number
-----------------------------------------------------------------------------
\* Helpers
HLCLt(x, y) == IF x.p < y.p
                THEN TRUE
               ELSE IF x.p = y.p
                THEN IF x.l < y.l
                        THEN TRUE
                     ELSE FALSE
                ELSE FALSE
                
HLCMin(x, y) == IF HLCLt(x, y) THEN x ELSE y
HLCMax(x, y) == IF HLCLt(x, y) THEN y ELSE x
HLCType == [ p : Nat, l : Nat ]
HLCMinSet(s) == CHOOSE x \in s: \A y \in s: ~HLCLt(y, x)   
Min(x, y) == IF x < y THEN x ELSE y
Max(x, y) == IF x > y THEN x ELSE y

vars == <<Primary, Secondary, Oplog, Store, Ct, Ot, InMsgc, 
          InMsgs, ServerMsg, BlockedClient, BlockedThread, 
          OpCount, Pt, Cp, State, SnapshotTable, 
          History, CurrentTerm, ReadyToServe, SyncSource>>
\* snapshot helpers
RECURSIVE SelectSnapshot_rec(_, _, _)
SelectSnapshot_rec(stable, cp, index) ==
    IF HLCLt(cp, stable[index].ot) THEN stable[index - 1].store
    ELSE IF index = Len(stable) THEN stable[index].store
    ELSE SelectSnapshot_rec(stable, cp, index + 1)
    
SelectSnapshot(stable, cp) == SelectSnapshot_rec(stable, cp, 1)

LogTerm(i, index) == IF index = 0 THEN 0 ELSE Oplog[i][index].term   
LastTerm(i) == CurrentTerm[i]  \*LastTerm(i) == LogTerm(i, Len(Oplog[i]))   
                              
\* Is node i ahead of node j
NotBehind(i, j) == \/ LastTerm(i) > LastTerm(j)
                   \/ /\ LastTerm(i) = LastTerm(j)
                      /\ Len(Oplog[i]) >= Len(Oplog[j])                           

IsMajority(servers) == Cardinality(servers) * 2 > Cardinality(Server)
                                      
\* Return the maximum value from a set, or undefined if the set is empty.
MaxVal(s) == CHOOSE x \in s : \A y \in s : x >= y                            

\* clock
MaxPt == LET x == CHOOSE s \in Server: \A s1 \in Server \ {s}:
                            Pt[s] >= Pt[s1] IN Pt[x]      
                            
Tick(s) == Ct' = IF Ct[s].p >= Pt[s] THEN [ Ct EXCEPT ![s] = [ p |-> @.p, l |-> @.l+1] ]
                                     ELSE [ Ct EXCEPT ![s] = [ p |-> Pt[s], l |-> 0] ]  

\* heartbeat - Only Primary node sends heartbeat once advance pt
BroadcastHeartbeat(s) == 
    LET msg == [ type|-> "heartbeat", s |-> s, aot |-> Ot[s], 
                 ct |-> Ct[s], cp |-> Cp[s], term |-> CurrentTerm[s] ]
    IN ServerMsg' = [x \in Server |-> IF x = s THEN ServerMsg[x]
                                               ELSE Append(ServerMsg[x], msg)]     
                                                                                                                             
\* Can node i sync from node j?
CanSyncFrom(i, j) ==
    /\ Len(Oplog[i]) < Len(Oplog[j])
    /\ LastTerm(i) = LogTerm(j, Len(Oplog[i]))
    
\* Oplog entries needed to replicate from j to i
ReplicateOplog(i, j) ==     
    LET len_i == Len(Oplog[i])
        len_j == Len(Oplog[j])
    IN IF i \in Secondary /\ len_i < len_j
                        THEN SubSeq(Oplog[j], len_i + 1, len_j)
                        ELSE <<>>

\* Can node i rollback its log based on j's log
CanRollback(i, j) == /\ Len(Oplog[i]) > 0       
                     /\ Len(Oplog[j]) > 0
                     /\ CurrentTerm[i] < CurrentTerm[j]
                     /\ \/ Len(Oplog[i]) > Len(Oplog[j])
                        \/ /\ Len(Oplog[i]) <= Len(Oplog[j])
                           /\ CurrentTerm[i] /= LogTerm(j, Len(Oplog[i]))
                           
\* Returns the highest common index between two divergent logs. 
\* If there is no common index between the logs, returns 0.
RollbackCommonPoint(i, j) == 
    LET commonIndices == {k \in DOMAIN Oplog[i] : 
                            /\ k <= Len(Oplog[j])
                            /\ Oplog[i][k] = Oplog[j][k]} IN
        IF commonIndices = {} THEN 0 ELSE MaxVal(commonIndices)    
        
\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}
QuorumAgreeInSameTerm(states) == 
    LET quorums == {Q \in Quorum :
                    \* Make sure all nodes in quorum have actually applied some entries.
                    /\ \/ \A s \in Q : states[s].p > 0
                       \/ /\ \A s \in Q : states[s].p = 0
                          /\ \A s \in Q : states[s].l > 0
                    \* Make sure every applied entry in quorum has the same term.
                    /\ \A s, t \in Q : 
                       s # t => states[s].term = states[s].term} 
    IN quorums            

ReplicatedServers(states, ot) ==
    LET serverSet == {subServers \in SUBSET(Server): \A s \in subServers: LET stateTime == [p|-> states[s].p, l|-> states[s].l]
                                                                          IN  ~HLCLt(stateTime, ot)}
    IN  CHOOSE maxSet \in serverSet: \A otherSet \in serverSet: Cardinality(otherSet) < Cardinality(maxSet)
 
 \* Compute a new common point according to new update position msg
ComputeNewCp(s) == 
    \* primary node: compute new mcp
    IF s \in Primary THEN 
        LET quorumAgree == QuorumAgreeInSameTerm(State[s]) IN
        IF  Cardinality(quorumAgree) > 0 
            THEN LET QuorumSet == CHOOSE i \in quorumAgree: TRUE
                     serverInQuorum == CHOOSE j \in QuorumSet: TRUE
                     termOfQuorum == State[s][serverInQuorum].term \* never commit log entries from previous terms
                     StateSet == {[p |-> State[s][j].p, l |-> State[s][j].l]: j \in QuorumSet}
                     newCommitPoint == HLCMinSet(StateSet)
                 IN  IF termOfQuorum = CurrentTerm[s]
                        THEN [p |-> newCommitPoint.p, l |-> newCommitPoint.l, term |-> termOfQuorum]
                     ELSE Cp[s]
          ELSE Cp[s]
    \* secondary node: update mcp   
    ELSE IF Len(ServerMsg[s]) /= 0 THEN
            LET msgCP == [ p |-> ServerMsg[s][1].cp.p, l |-> ServerMsg[s][1].cp.l ] IN 
            IF /\ ~ HLCLt(msgCP, Cp[s])
               /\ ~ HLCLt(Ot[s], msgCP)
               \* The term of cp must equal to the CurrentTerm of that node to advance it
               /\ ServerMsg[s][1].term = CurrentTerm[s] 
               THEN ServerMsg[s][1].cp
            ELSE Cp[s]
         ELSE Cp[s]
         
GetNewState(s, d, np, nl, nterm) == 
    LET newSubState == [p |-> np, l |-> nl, term |-> nterm] 
        sState == State[s]
    IN  [sState EXCEPT ![d] = newSubState]    
                                                      
-----------------------------------------------------------------------------
\* Init Part  
InitPrimary == Primary = {CHOOSE s \in Server: TRUE}
InitSecondary == Secondary = Server \ Primary
InitOplog == Oplog = [ s \in Server |-> <<>> ]
InitStore == Store = [ n \in Server \cup Client  |-> [ k \in Key |-> Nil ] ]
InitCt == Ct = [ n \in Server \cup Client |-> [ p |-> 0, l |-> 0 ] ]
InitOt == Ot = [ n \in Server \cup Client |-> [ p |-> 0, l |-> 0 ] ]
InitInMsgc == InMsgc = [ c \in Client |-> <<>> ]
InitInMsgs == InMsgs = [ s \in Server |-> <<>> ]
InitServerMsg == ServerMsg = [ s \in Server |-> <<>> ]
InitBlockedClient == BlockedClient = {}
InitBlockedThread == BlockedThread = [s \in Client |-> Nil ] 
InitOpCount == OpCount = [ c \in Client |-> OpTimes ]
InitPt == Pt = [ s \in Server |-> 1 ]
InitCp == Cp = [ n \in Server \cup Client |-> [ p |-> 0, l |-> 0 ] ]
InitState == State = [ s \in Server |-> [ s0 \in Server |-> 
                                              [ p |-> 0, l |-> 0, term |-> 0 ] ] ]
InitSnap == SnapshotTable = [ s \in Server |-> <<[ ot |-> [ p |-> 0, l |-> 0 ], 
                                                   store |-> [ k \in Key |-> Nil] ] >>]  
InitHistory == History = [c \in Client |-> <<>>]  \* History operation seq is empty  
InitCurrentTerm == CurrentTerm = [s \in Server |-> 0] 
InitReadyToServe == ReadyToServe = 0
InitSyncSource == SyncSource = [ s \in Server |-> Nil]                                                                              

Init == 
    /\ InitPrimary /\ InitSecondary /\ InitOplog /\ InitStore /\ InitCt 
    /\ InitOt /\ InitPt /\ InitCp /\ InitInMsgc /\ InitInMsgs 
    /\ InitServerMsg /\ InitBlockedClient /\ InitBlockedThread /\ InitOpCount
    /\ InitState /\ InitSnap /\ InitHistory /\ InitCurrentTerm /\ InitReadyToServe
    /\ InitSyncSource
     
-----------------------------------------------------------------------------
\* Next State Actions  
\* Replication Protocol: possible actions 
\* snapshot periodly
Snapshot == 
    /\ ReadyToServe > 0
    /\ \E s \in Server:
            SnapshotTable' =  [ SnapshotTable EXCEPT ![s] = 
                                Append(@, [ot |-> Ot[s], store |-> Store[s] ]) ]  
                               \* create a new snapshot
    /\ UNCHANGED <<serverVars, InMsgc, InMsgs, BlockedClient, BlockedThread, OpCount, History>>                                             

Stepdown == 
    /\ ReadyToServe > 0
    /\ \E s \in Primary:
        /\ Primary' = Primary \ {s}
        /\ Secondary' = Secondary \cup {s}
    /\ UNCHANGED <<storageVars, servernodeVars, Ct, messageVar, timeVar, Cp, State, CurrentTerm, functionalVar, tunableVars>>

\* There are majority nodes agree to elect node i to become primary                            
ElectPrimary ==
    /\ ReadyToServe > 0
    /\ \E i \in Server: \E majorNodes \in SUBSET(Server):
        /\ \A j \in majorNodes: /\ NotBehind(i, j)
                                /\ CurrentTerm[i] >= CurrentTerm[j]
        /\ IsMajority(majorNodes)         
       \* voted nodes for i cannot be primary anymore
        /\ Primary' = LET possiblePrimary == Primary \ majorNodes
                      IN possiblePrimary \cup {i}
       \* add voted nodes into secondaries          
        /\ Secondary' = LET possibleSecondary == Secondary \cup majorNodes
                        IN possibleSecondary \ {i}                                           
        /\ CurrentTerm' = [index \in Server |-> IF index \in (majorNodes \cup {i})
                                                THEN CurrentTerm[i] + 1
                                                ELSE CurrentTerm[index]]
        \* A primary node do not have any sync source                                        
        /\ SyncSource' = [SyncSource EXCEPT ![i] = Nil ]
    /\ UNCHANGED <<storageVars, Ct, Ot, messageVar, timeVar, Cp, State, functionalVar, tunableVars>> 
    
TurnOnReadyToServe ==
    /\ ReadyToServe = 0
    /\ \E s \in Primary:
        /\ CurrentTerm' = [CurrentTerm EXCEPT ![s] = CurrentTerm[s] + 1]
\*        /\ CurrentTerm' = [s \in Server |-> 1] ?
        /\ ReadyToServe' = ReadyToServe + 1
    /\ UNCHANGED<<electionVars, storageVars, servernodeVars, Ct, messageVar, timeVar, Cp, State, tunableVars>>     

AdvanceCp ==
    /\ ReadyToServe > 0
    /\ \E s \in Primary:
        LET newCp == ComputeNewCp(s)
        IN Cp' = [ Cp EXCEPT ![s] = newCp]
    /\ UNCHANGED <<electionVars, storageVars, servernodeVars, Ct, messageVar, timeVar, State, CurrentTerm, functionalVar, tunableVars>>                                              
                                                                                                                                                                                                  
\*注意：heartbeat没有更新oplog，没有更新Ot，也没有更新store状态                                                                                                                                                                                                       
ServerTakeHeartbeat ==
    /\ ReadyToServe > 0
    /\ \E s \in Server:
        /\ Len(ServerMsg[s]) /= 0  \* message channel is not empty
        /\ ServerMsg[s][1].type = "heartbeat"
        /\ CurrentTerm[s] = ServerMsg[s][1].term \* only consider heartbeat msg in same term
        /\ Ct' = [ Ct EXCEPT ![s] = HLCMax(Ct[s], ServerMsg[s][1].ct) ]
        /\ State' = LET newState == GetNewState(s, ServerMsg[s][1].s, ServerMsg[s][1].aot.p, ServerMsg[s][1].aot.l,ServerMsg[s][1].term)
                    IN  [ State EXCEPT ![s] = newState]
        /\ Cp' = LET newcp == ComputeNewCp(s)
                 IN [ Cp EXCEPT ![s] = newcp ]
       /\ ServerMsg' = [ ServerMsg EXCEPT ![s] = Tail(@) ]
       /\ CurrentTerm' = [CurrentTerm EXCEPT ![s] = Max(CurrentTerm[s], ServerMsg[s][1].term)]         
    /\ UNCHANGED <<electionVars, storageVars, servernodeVars, timeVar, functionalVar, tunableVars>>

ServerTakeUpdatePosition == 
    /\ ReadyToServe > 0
    /\ \E s \in Server:
        /\ Len(ServerMsg[s]) /= 0  \* message channel is not empty
        /\ ServerMsg[s][1].type = "update_position"
        /\ Ct' = [ Ct EXCEPT ![s] = HLCMax(Ct[s], ServerMsg[s][1].ct) ] \* update ct accordingly
        /\ State' = LET newState == GetNewState(s, ServerMsg[s][1].s, ServerMsg[s][1].aot.p, ServerMsg[s][1].aot.l,ServerMsg[s][1].term)
                    IN  [ State EXCEPT ![s] = newState]
        /\ Cp' = LET newcp == ComputeNewCp(s)
                 IN [ Cp EXCEPT ![s] = newcp ]    
       /\ CurrentTerm' = [CurrentTerm EXCEPT ![s] = Max(CurrentTerm[s], ServerMsg[s][1].term)]             
       /\ ServerMsg' = LET newServerMsg == [ServerMsg EXCEPT ![s] = Tail(@)]
                       IN  ( LET  appendMsg == [ type |-> "update_position", s |-> ServerMsg[s][1].s, aot |-> ServerMsg[s][1].aot, 
                                          ct |-> ServerMsg[s][1].ct, cp |-> ServerMsg[s][1].cp, term |-> ServerMsg[s][1].term ]
                             IN ( LET newMsg == IF s \in Primary \/ SyncSource[s] = Nil
                                                    THEN newServerMsg \* If s is primary, accept the msg, else forward it to its sync source
                                                ELSE [newServerMsg EXCEPT ![SyncSource[s]] = Append(newServerMsg[SyncSource[s]], appendMsg)]
                                  IN newMsg))
    /\ UNCHANGED <<electionVars, storageVars, servernodeVars, timeVar, functionalVar, tunableVars>>                   
                  
NTPSync == \* simplify NTP protocal
    /\ ReadyToServe > 0
    /\ Pt' = [ s \in Server |-> MaxPt ] 
    /\ UNCHANGED <<electionVars, storageVars, servernodeVars, learnableVars, messageVar, functionalVar, tunableVars>>

AdvancePt == 
    /\ ReadyToServe > 0
    /\ \E s \in Server:  
           /\ s \in Primary                    \* for simplicity
           /\ Pt[s] <= PtStop 
           /\ Pt' = [ Pt EXCEPT ![s] = @+1 ] \* advance physical time
           /\ BroadcastHeartbeat(s)          \* broadcast heartbeat periodly
    /\ UNCHANGED <<electionVars, storageVars, servernodeVars, learnableVars, functionalVar, tunableVars>>
                                     
\* Replication                                     
\* Idea: 进行replicate的时候，首先进行canSyncFrom的判断，拥有更多log且大于等于term的才能作为同步源
\* 其次，开始同步之后，把当前节点的同步源设置为SyncSource[s]，随后向SyncSource的信道里加入UpdatePosition消息
\* 最后，关于UpdatePosition的转发，需要加入一个额外的action，如果自己的信道里有type为updatePosition的消息，则向上层节点转发
\* Replicate oplog from node j to node i, and update related structures accordingly
 Replicate == 
    /\ ReadyToServe > 0
    /\ \E i, j \in Server: 
        /\ CanSyncFrom(i, j) \* i can sync from j only need not to rollback
        /\ i \in Secondary
        /\ ReplicateOplog(i, j) /= <<>>
        /\ Oplog' = [Oplog EXCEPT ![i] = @ \o ReplicateOplog(i, j)]
        /\ Store' = [Store EXCEPT ![i] =  Store[j]]
        /\ Ct' = [Ct EXCEPT ![i] = HLCMax(Ct[i], Ct[j])] \* update Ct[i] 
        /\ Ot' = [Ot EXCEPT ![i] = HLCMax(Ot[i], Ot[j])] \* update Ot[i]    
        /\ Cp' = [Cp EXCEPT ![i] = HLCMax(Cp[i], Cp[j])] \* update Cp[i]
        /\ CurrentTerm' = [CurrentTerm EXCEPT ![i] = Max(CurrentTerm[i], CurrentTerm[j])] \* update CurrentTerm
        /\ State' = LET newState == GetNewState(i, j, Ot[j].p, Ot[j].l, CurrentTerm[j])
                    IN  [ State EXCEPT ![i] = newState]  \* update j's state i knows 
        /\ LET msg == [ type |-> "update_position", s |-> i, aot |-> Ot'[i], ct |-> Ct'[i], cp |-> Cp'[i], term |-> CurrentTerm'[i] ]
           IN ServerMsg' = [ ServerMsg EXCEPT ![j] = Append(ServerMsg[j], msg) ]
        /\ SyncSource' = [SyncSource EXCEPT ![i] = j] 
    /\ UNCHANGED <<electionVars, timeVar, functionalVar, tunableVars>>                    
                    
\* Rollback i's oplog and recover it to j's state   
\* Recover to j's state immediately to prevent internal client request  
RollbackAndRecover ==
    /\ ReadyToServe > 0
    /\ \E i, j \in Server:
        /\ i \in Secondary
        /\ CanRollback(i, j)
        /\ LET cmp == RollbackCommonPoint(i, j)  IN
           LET commonLog == SubSeq(Oplog[i], 1, cmp)
               appendLog == SubSeq(Oplog[j], cmp+1, Len(Oplog[j]))
           IN Oplog' = [Oplog EXCEPT ![i] = commonLog \o appendLog]
        /\ CurrentTerm' = [CurrentTerm EXCEPT ![i] = Max(CurrentTerm[i], CurrentTerm[j])] \* update CurrentTerm                                
        /\ Store' = [Store EXCEPT ![i] =  Store[j]]
        /\ Ct' = [Ct EXCEPT ![i] = HLCMax(Ct[i], Ct[j])] \* update Ct[i] 
        /\ Ot' = [Ot EXCEPT ![i] = HLCMax(Ot[i], Ot[j])] \* update Ot[i] 
        /\ Cp' = [Cp EXCEPT ![i] = HLCMax(Cp[i], Cp[j])] \* update Cp[i]
        /\ State' = 
            LET newStatei == [p |-> Ot'[i].p, l |-> Ot'[i].l, term |-> CurrentTerm'[i]]
                newStatej == [p |-> Ot[j].p, l |-> Ot[j].l,term |-> CurrentTerm[j]]
            IN LET SubHbState == State[i]
                   hb == [ SubHbState EXCEPT ![i] = newStatei ] \* update i's self state (used in mcp computation
                   hb1 == [hb EXCEPT ![j] = newStatej ] \* update j's state i knows 
               IN [ State EXCEPT ![i] = hb1]
        /\ LET msg == [ type |-> "update_position", s |-> i, aot |-> Ot'[i], ct |-> Ct'[i], cp |-> Cp'[i], term |-> CurrentTerm'[i] ]
           IN ServerMsg' = [ ServerMsg EXCEPT ![j] = Append(ServerMsg[j], msg) ]
        /\ SyncSource' = [SyncSource EXCEPT ![i] = j]  
    /\ UNCHANGED <<electionVars, timeVar, functionalVar, tunableVars>>                     
    
----------------------------------------------------------------------------- 
\* Tunable Protocol: Server Actions                 
\* Server Get
ServerGetReply_sleep ==
    /\ ReadyToServe > 0
    /\ \E s \in Server:
       /\ Len(InMsgs[s]) /= 0
       /\ InMsgs[s][1].op = "get"
       /\ IF InMsgs[s][1].rc = "linearizable"
            THEN  /\ s \in Primary
                  /\ Tick(s)  \* advance cluster time
                  /\ Oplog' = [ Oplog EXCEPT ![s] = Append(@, <<Nil, Nil, Ct'[s]>>)]
                    \* append noop operation to oplog[s]
                  /\ Ot' = [ Ot EXCEPT ![s] =  Ct'[s] ] 
                    \* advance the last applied operation time Ot[s]
                  /\ State' = LET newState == GetNewState(s, s, Ot'[s].p, Ot'[s].l, CurrentTerm[s])      
                              IN  [State EXCEPT ![s] = newState]      \* update primary state
                  /\ InMsgs' = [ InMsgs EXCEPT ![s] = Tail(@) ]
                  /\ BlockedThread' = [BlockedThread EXCEPT ![InMsgs[s][1].c] = 
                                       [type |-> "read", rc |-> InMsgs[s][1].rc, ot|-> Ct'[s], s |-> s, 
                                       k |->InMsgs[s][1].k, v |-> Store[s][InMsgs[s][1].k] ] ] 
                     \* add the user thread to BlockedThread[c]                      
          ELSE /\ Ct' = [ Ct EXCEPT ![s] = HLCMax(Ct[s], InMsgs[s][1].ct) ] \*rc = local or major  
               /\ BlockedThread' = [BlockedThread EXCEPT ![InMsgs[s][1].c] = 
                            [type |-> "read", rc |-> InMsgs[s][1].rc, s |-> s, k |-> InMsgs[s][1].k, ot |-> InMsgs[s][1].ot]]
               /\ Oplog' = Oplog
               /\ Ot' = Ot
               /\ State' = State
       /\ InMsgs' = [ InMsgs EXCEPT ![s] = Tail(@)]
    /\ UNCHANGED <<electionVars, functionalVar, Cp, CurrentTerm, messageVar, SyncSource, Store, timeVar,
                   InMsgc, BlockedClient, clientnodeVars, SnapshotTable>>
                   
ServerGetReply_wake == 
    /\ ReadyToServe > 0
    /\ \E c \in Client:
       /\ BlockedThread[c] /= Nil
       /\ BlockedThread[c].type ="read"
       /\ IF BlockedThread[c].rc = "linearizable"
            THEN /\ ~ HLCLt(Cp[BlockedThread[c].s], BlockedThread[c].ot) \* wait until cp[s] >= target ot 
                 /\ InMsgc' = [ InMsgc EXCEPT ![c] = Append(@, [ op |-> "get", 
                                k |-> BlockedThread[c].k, v |-> BlockedThread[c].v, 
                                ct |-> Ct[BlockedThread[c].s], ot|->BlockedThread[c].ot ])] 
          ELSE /\ ~ HLCLt(Ot[BlockedThread[c].s], BlockedThread[c].ot) \* wait until Ot[s] >= target ot  
               /\ IF BlockedThread[c].rc = "local"
                    THEN InMsgc' = [ InMsgc EXCEPT ![c] = Append(@, [ op |-> "get", k |-> BlockedThread[c].k, 
                                     v |-> Store[BlockedThread[c].s][BlockedThread[c].k], 
                                     ct |-> Ct[BlockedThread[c].s], ot |-> Ot[BlockedThread[c].s]])]
                  ELSE InMsgc' = [ InMsgc EXCEPT ![c] = Append(@, [ op |-> "get", k |-> BlockedThread[c].k,  \* rc = majority
                                   v |->SelectSnapshot(SnapshotTable[BlockedThread[c].s], Cp[BlockedThread[c].s])[BlockedThread[c].k], 
                                   ct |-> Ct[BlockedThread[c].s], ot |-> Cp[BlockedThread[c].s]])]
       /\ BlockedThread' = [BlockedThread EXCEPT ![c] = Nil]
    /\ UNCHANGED <<serverVars, clientnodeVars, BlockedClient, InMsgs, SnapshotTable>>                
       
\* Server Put 注意：只有收到写操作时才会记录server的oplog
ServerPutReply_sleep == 
    /\ ReadyToServe > 0
    /\ \E s \in Primary:
        /\ Len(InMsgs[s]) /= 0
        /\ InMsgs[s][1].op = "put"
        /\ Tick(s)
        /\ Ot' = [ Ot EXCEPT ![s] =  Ct'[s] ] \* advance the last applied operation time Ot[s]
        /\ Store' = [ Store EXCEPT ![s][InMsgs[s][1].k] = InMsgs[s][1].v ] \* append operation to oplog[s]
        /\ Oplog' = LET entry == [k |-> InMsgs[s][1].k, v |-> InMsgs[s][1].v, 
                                  ot |-> Ot'[s], term |-> CurrentTerm[s]]
                        newLog == Append(Oplog[s], entry)
                    IN [Oplog EXCEPT ![s] = newLog] 
        /\ State' = LET newState == GetNewState(s, s, Ot'[s].p, Ot'[s].l, CurrentTerm[s])      
                    IN  [State EXCEPT ![s] = newState]      \* update primary state    
        /\ IF InMsgs[s][1].wc = "zero" \* If w:0, do not sleep
            THEN BlockedThread' = BlockedThread
           ELSE BlockedThread' = [BlockedThread EXCEPT ![InMsgs[s][1].c] = [type |-> "write", wc |-> InMsgs[s][1].wc,
                                   numnode |-> InMsgs[s][1].num, ot |-> Ot'[s], s |-> s, 
                                   k |->InMsgs[s][1].k, v |-> InMsgs[s][1].v ] ] \* add the user History to BlockedThread[c]          
        /\ InMsgs' = [ InMsgs EXCEPT ![s] = Tail(@)] 
    /\ UNCHANGED <<electionVars, functionalVar, Cp, CurrentTerm, messageVar, SyncSource, timeVar,
                   InMsgc, BlockedClient, clientnodeVars, SnapshotTable>> 
                                   
ServerPutReply_wake ==
    /\ ReadyToServe > 0
    /\ \E c \in Client:
        /\ BlockedThread[c] /=  Nil
        /\ BlockedThread[c].type = "write"
        /\ IF BlockedThread[c].wc = "num" \* w:num
            THEN LET replicatedServers == ReplicatedServers(State[BlockedThread[c].s], BlockedThread[c].ot)
                 IN  Cardinality(replicatedServers) >= BlockedThread[c].numnode
           ELSE ~ HLCLt(Cp[BlockedThread[c].s], BlockedThread[c].ot) \* w:majority
        /\ InMsgc' = [ InMsgc EXCEPT ![c] =  Append(@, [ op |-> "put", 
                       ct |-> Ct[BlockedThread[c].s], ot |-> BlockedThread[c].ot, 
                       k|-> BlockedThread[c].k, v |-> BlockedThread[c].v]) ] 
        /\ BlockedThread' =  [ BlockedThread EXCEPT ![c] = Nil ] \* remove blocked state     
    /\ UNCHANGED <<serverVars, clientnodeVars, BlockedClient, InMsgs, SnapshotTable>>               
          
----------------------------------------------------------------------------- 
\* Tunable Protocol: Client Actions      
\* Client Get
ClientGetRequest ==
    /\ ReadyToServe > 0
    /\ \E k \in Key, c \in Client \ BlockedClient: 
        /\ IF ReadConcern = "linearizable" \* In this case, read can only be sent to primary
           THEN \E s \in Primary:
                InMsgs' = [InMsgs EXCEPT ![s] = Append(@,
                [op |-> "get", c |-> c, rc |-> ReadConcern, k |-> k, ct |-> Ct[c], ot |-> Ot[c]])]
           ELSE IF ReadPreference = "primary" \* rp can be only primary or secondary
                    THEN \E s \in Primary:
                         InMsgs' = [InMsgs EXCEPT ![s] = Append(@,
                         [op |-> "get", c |-> c, rc |-> ReadConcern, k |-> k, ct |-> Ct[c], ot |-> Ot[c]])]
                ELSE \E s \in Secondary:
                     InMsgs' = [InMsgs EXCEPT ![s] = Append(@,
                     [op |-> "get", c |-> c, rc |-> ReadConcern, k |-> k, ct |-> Ct[c], ot |-> Ot[c]])]
        /\ BlockedClient' = BlockedClient \cup {c}          
    /\ UNCHANGED <<serverVars, clientnodeVars, BlockedThread, InMsgc, SnapshotTable>>    

\* Client Put    
ClientPutRequest == 
    /\ ReadyToServe > 0
    /\ \E k \in Key, v \in Value, c \in Client \ BlockedClient, s \in Primary:
        /\ OpCount[c] /= 0
        /\ InMsgs' = [InMsgs EXCEPT ![s] = Append(@, 
                        [op |-> "put", c |-> c, wc |-> WriteConcern, num |-> WriteNumber, k |-> k, v |-> v, ct |-> Ct[c]])]
        /\ IF WriteConcern = "zero" \*If w:0, decrease op count and record history
            THEN /\ OpCount' = [ OpCount EXCEPT ![c] = @-1 ]
                 /\ History' = [History EXCEPT ![c] = Append(@, [ op |-> "put", ts |-> Ot[c], k |-> k, v |-> v])]
                 /\ BlockedClient' = BlockedClient
           ELSE /\ BlockedClient' = BlockedClient \cup {c} \*Else wait for server reply
                /\ OpCount' = OpCount
                /\ History' = History
    /\ UNCHANGED <<serverVars, BlockedThread, InMsgc, SnapshotTable>>       

\* do we need to update Ct[c] here?                                                 
ClientGetResponse ==
    /\ ReadyToServe > 0
    /\ \E c \in Client:
        /\ OpCount[c] /= 0          \* client c has operation times
        /\ Len(InMsgc[c]) /= 0      \* message channel is not empty
        /\ InMsgc[c][1].op = "get"  \* msg type: get
        /\ Store' = [ Store EXCEPT ![c][InMsgc[c][1].k] = InMsgc[c][1].v ]  \* store data
        /\ History' = [ History EXCEPT ![c] = Append(@, [ op |-> "get", 
                        ts |-> InMsgc[c][1].ot, k |-> InMsgc[c][1].k, v |-> InMsgc[c][1].v ]) ]    
        /\ InMsgc' = [ InMsgc EXCEPT ![c] = Tail(@) ]
        /\ BlockedClient' = IF Len(InMsgc'[c]) = 0
                                THEN BlockedClient \ {c}
                            ELSE BlockedClient  \* remove blocked state
        /\ OpCount' = [ OpCount EXCEPT ![c] = @-1 ]
    /\ UNCHANGED <<electionVars, functionalVar, learnableVars, messageVar, servernodeVars, Oplog, timeVar,
                   BlockedThread, InMsgs, SnapshotTable>>
                   
ClientPutResponse ==
    /\ ReadyToServe > 0
    /\ \E c \in Client:
        /\ OpCount[c] /= 0          \* client c has operation times
        /\ Len(InMsgc[c]) /= 0      \* message channel is not empty
        /\ InMsgc[c][1].op = "put"  \* msg type: put
        /\ Ct' = [ Ct EXCEPT ![c] = HLCMax(@, InMsgc[c][1].ct) ]
        /\ Ot' = [ Ot EXCEPT ![c] = HLCMax(@, InMsgc[c][1].ot) ] \* Update Ot to record "my write" ot
        /\ History' = [History EXCEPT ![c] = Append(@, [ op 
                        |-> "put", ts |-> InMsgc[c][1].ot, k |-> InMsgc[c][1].k, v |-> InMsgc[c][1].v ]) ]         
        /\ InMsgc' = [ InMsgc EXCEPT ![c] = Tail(@) ]
        /\ BlockedClient' = IF Len(InMsgc'[c]) = 0
                                THEN BlockedClient \ {c}
                            ELSE BlockedClient  \* remove blocked state
        /\ OpCount' = [ OpCount EXCEPT ![c] = @-1 ]
    /\ UNCHANGED <<electionVars, functionalVar, Cp, CurrentTerm, State, messageVar, SyncSource, storageVars, timeVar,
                   BlockedThread, InMsgs, SnapshotTable>>
                
-----------------------------------------------------------------------------
\* Action Wrapper   
\* all possible server get actions                     
ServerGetReply == \/ ServerGetReply_sleep 
                  \/ ServerGetReply_wake

\* all possible server put actions                 
ServerPutReply == \/ ServerPutReply_sleep
                  \/ ServerPutReply_wake                  
-----------------------------------------------------------------------------   
\* Next state for all configurations
Next == \/ ClientGetRequest \/ ClientPutRequest
        \/ ClientGetResponse \/ ClientPutResponse
        \/ ServerGetReply \/ ServerPutReply
        \/ Replicate 
        \/ AdvancePt
        \/ ServerTakeHeartbeat
        \/ ServerTakeUpdatePosition
        \/ Snapshot
        \/ Stepdown
        \/ RollbackAndRecover
        \/ TurnOnReadyToServe
        \/ ElectPrimary
        \/ AdvanceCp
        \/ NTPSync
        
Spec == Init /\ [][Next]_vars       

-----------------------------------------------------------------------------
\* Causal Specifications
MonotonicRead == \A c \in Client: \A i,j \in DOMAIN History[c]:
                    /\ i<j 
                    /\ History[c][i].op = "get"
                    /\ History[c][j].op = "get"
                    => ~ HLCLt(History[c][j].ts, History[c][i].ts)
   
MonotonicWrite == \A c \in Client: \A i,j \in DOMAIN History[c]:
                    /\ i<j 
                    /\ History[c][i].op = "put"
                    /\ History[c][j].op = "put"
                    => ~ HLCLt(History[c][j].ts, History[c][i].ts)   
                    
ReadYourWrite == \A c \in Client: \A i,j \in DOMAIN History[c]:
                /\ i < j
                /\ History[c][i].op = "put"
                /\ History[c][j].op = "get"
                => ~ HLCLt(History[c][j].ts, History[c][i].ts)
                
WriteFollowRead == \A c \in Client: \A i,j \in DOMAIN History[c]:
                /\ i < j
                /\ History[c][i].op = "get"
                /\ History[c][j].op = "put"
                => ~ HLCLt(History[c][j].ts, History[c][i].ts)
=============================================================================
\* Modification History
\* Last modified Thu May 19 11:54:21 CST 2022 by dh
\* Created Thu Mar 31 20:33:19 CST 2022 by dh

----------------------- MODULE MongoDBCC_Recoverable -----------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC, CMvSpec

\* constants and variables
CONSTANTS Client, Server,       \* the set of clients and servers
          Key, Value,           \* the set of keys and values
          Nil,                  \* model value, place holder
          OpTimes,              \* op count at most
          PtStop                \* max physical time

VARIABLES Primary,        \* Primary node
          Secondary,      \* secondary nodes
          Oplog,          \* oplog[s]: oplog at server[s]
          Store,          \* store[s]: data stored at server[s]
          Ct,             \* Ct[s]: cluster time at node s
          Ot,             \* Ot[s]: the last applied operation time at server s
          ServerMsg,      \* ServerMsg[s]: the channel of heartbeat msgs at server s
          Pt,             \* Pt[s]: physical time at server s
          State,          \* State[s]: the latest Ot of all servers that server s knows
          SyncSource,     \* sync source of server node s     
          BlockedClient,  \* BlockedClient: Client operations in progress
          BlockedThread,  \* BlockedThread: blocked user thread and content
          History,        \* History[c]: History sequence at client c
          Messages,       \* Message channels
          OpCount,        \* OpCount[c]: op count for client c  
          Cp,             \* Cp[s]: majority commit point at server s
          SnapshotTable,  \* SnapshotTable[s] : snapshot mapping table at server s  
          CurrentTerm     \* CurrentTerm[s]: current election term at server s 
                          \* -> updated in update_position, heartbeat and replicate
          
-----------------------------------------------------------------------------          
\* group related vars to optimize code
electionVars == <<Primary, Secondary>>              \* vars that are related to election  
storageVars == <<Oplog, Store>>                     \* vars that are related to storage
messageVar == <<ServerMsg>>                         \* var that is related to message
servernodeVars == <<Ot, SyncSource>>                \* vars that each server node holds for itself
learnableVars == <<Ct, State, Cp, CurrentTerm>>     \* vars that must learn from msgs
timeVar == <<Pt>>                                   \* var that is used for timing 
clientnodeVars == <<History, OpCount>>

serverVars == <<electionVars, storageVars, messageVar, servernodeVars, learnableVars, timeVar>>
tunableVars == <<BlockedClient, BlockedThread, History, Messages, OpCount, SnapshotTable>>  

vars == <<Primary, Secondary, Oplog, Store, Ct, Ot, Messages, 
          ServerMsg, BlockedClient, BlockedThread, OpCount, Pt, Cp, 
          State, SnapshotTable, History, CurrentTerm, SyncSource>>      
-----------------------------------------------------------------------------
ASSUME Cardinality(Client) >= 1  \* at least one client
ASSUME Cardinality(Server) >= 2  \* at least one primary and one secondary
ASSUME Cardinality(Key) >= 1     \* at least one object
ASSUME Cardinality(Value) >= 2   \* at least two values to update
-----------------------------------------------------------------------------
\* Helpers
HLCLt(x, y) == IF x.p < y.p THEN TRUE
               ELSE IF x.p = y.p THEN IF x.l < y.l THEN TRUE
                                      ELSE FALSE
                    ELSE FALSE
                
HLCMin(x, y) == IF HLCLt(x, y) THEN x ELSE y
HLCMax(x, y) == IF HLCLt(x, y) THEN y ELSE x
HLCType == [ p : Nat, l : Nat ]
HLCMinSet(s) == CHOOSE x \in s: \A y \in s: ~HLCLt(y, x)   
Min(x, y) == IF x < y THEN x ELSE y
Max(x, y) == IF x > y THEN x ELSE y

\* snapshot helpers
RECURSIVE SelectSnapshotIndex_Rec(_, _, _)
SelectSnapshotIndex_Rec(stable, cp, index) ==
    IF index > Len(stable) THEN Nil \* cannot find such snapshot at cp
    ELSE IF HLCLt(stable[index], cp) THEN SelectSnapshotIndex_Rec(stable, cp, index + 1) \* go further
         ELSE IF HLCLt(cp, stable[index]) THEN Nil
              ELSE index \* match
              
SelectSnapshot(stable, cp) == LET index == SelectSnapshotIndex_Rec(stable, cp, 1)
                              IN  IF index /= Nil THEN stable[index].store  
                                  ELSE Nil
                                  
SelectSnapshotIndex(stable, cp) == SelectSnapshotIndex_Rec(stable, cp, 1)

\* The election term of each oplog entry
LogTerm(i, index) == IF index = 0 THEN 0 ELSE Oplog[i][index].term   
LastTerm(i) == LogTerm(i, Len(Oplog[i]))   
                              
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
                                     
\* Server s update its Ct according to msgCt and then tick                                     
UpdateAndTick(s, msgCt) ==
    LET newCt == [ Ct EXCEPT ![s] = HLCMax(Ct[s], msgCt) ] \* Update ct first according to msg
    IN  Ct' = IF newCt[s].p >= Pt[s] THEN [ newCt EXCEPT ![s] = [ p |-> @.p, l |-> @.l+1] ]
                                     ELSE [ newCt EXCEPT ![s] = [ p |-> Pt[s], l |-> 0] ]                  

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
                     /\ LastTerm(i) < LastTerm(j)
                     /\ \/ Len(Oplog[i]) > Len(Oplog[j])
                        \/ /\ Len(Oplog[i]) <= Len(Oplog[j])
                           /\ LastTerm(i) /= LogTerm(j, Len(Oplog[i]))
                           
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

\* The set of servers whose replicate progress are greater than ot
ReplicatedServers(states, ot) ==
    LET serverSet == {subServers \in SUBSET(Server): \A s \in subServers: LET stateTime == [p|-> states[s].p, l|-> states[s].l]
                                                                          IN  ~HLCLt(stateTime, ot)}
    IN  CHOOSE maxSet \in serverSet: \A otherSet \in serverSet: Cardinality(otherSet) <= Cardinality(maxSet)
 
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
InitServerMsg == ServerMsg = [ s \in Server |-> <<>> ]
InitPt == Pt = [ s \in Server |-> 1 ]
InitState == State = [ s \in Server |-> [ s0 \in Server |-> 
                                              [ p |-> 0, l |-> 0, term |-> 0 ] ] ]
InitSyncSource == SyncSource = [ s \in Server |-> Nil] 
InitBlockedClient == BlockedClient = {}
InitBlockedThread == BlockedThread = [s \in Client |-> Nil ] 
InitHistory == History = [c \in Client |-> <<>>]  \* History operation seq is empty  
InitMessages == Messages = {}
InitOpCount == OpCount = [ c \in Client |-> OpTimes ]
InitCp == Cp = [ n \in Server \cup Client |-> [ p |-> 0, l |-> 0, term |-> 0 ] ]
InitSnap == SnapshotTable = [ s \in Server |-> <<[ ot |-> [ p |-> 0, l |-> 0 ], 
                                                   store |-> [ k \in Key |-> Nil] ] >>]  
InitCurrentTerm == CurrentTerm = [ p \in Primary |-> 1 ] @@ [ s \in Server |-> 0 ] 
                                                                             

Init == 
    /\ InitPrimary /\ InitSecondary /\ InitOplog /\ InitStore /\ InitCt 
    /\ InitOt /\ InitPt  /\ InitServerMsg /\ InitState 
    /\ InitSyncSource /\ InitBlockedClient /\ InitBlockedThread 
    /\ InitHistory /\ InitMessages /\ InitOpCount
    /\ InitCp /\ InitSnap /\ InitCurrentTerm 
     
-----------------------------------------------------------------------------
\* Next State Actions  
\* Replication Protocol: possible actions 

\* snapshot periodly
Snapshot == 
    /\ \E s \in Server:      
       LET SnapshotIndex == SelectSnapshotIndex(SnapshotTable[s], Ot[s]) 
       IN  IF SnapshotIndex /= Nil
               THEN SnapshotTable' = [ SnapshotTable EXCEPT ![s][SnapshotIndex] = [ot |-> Ot[s], store |-> Store[s] ] ]
           ELSE SnapshotTable' = [ SnapshotTable EXCEPT ![s] =  \* create a new snapshot     
                                   Append(@, [ot |-> Ot[s], store |-> Store[s] ]) ]  
    /\ UNCHANGED <<serverVars, Messages, BlockedClient, BlockedThread, OpCount, History>> 
      
\* A primary node steps down to secondary
Stepdown == 
    /\ \E s \in Primary:
        /\ Primary' = Primary \ {s}
        /\ Secondary' = Secondary \cup {s}
    /\ UNCHANGED <<storageVars, servernodeVars, Ct, messageVar, timeVar, Cp, State, CurrentTerm, tunableVars>>

\* There are majority nodes agree to elect node i to become primary                            
ElectPrimary ==
    /\ \E i \in Server: \E majorNodes \in SUBSET(Server):
        /\ IsMajority(majorNodes) 
        /\ \A j \in majorNodes: /\ NotBehind(i, j)
                                /\ CurrentTerm[i] >= CurrentTerm[j]
       \* voted nodes for i cannot be primary anymore
        /\ Primary' = LET possiblePrimary == Primary \ majorNodes
                      IN possiblePrimary \cup {i}
       \* add voted nodes into secondaries          
        /\ Secondary' = LET possibleSecondary == Secondary \cup majorNodes
                        IN possibleSecondary \ {i}    
       \* advance the term of voted nodes by magic                                                        
        /\ CurrentTerm' = [index \in Server |-> IF index \in (majorNodes \cup {i})
                                                THEN CurrentTerm[i] + 1
                                                ELSE CurrentTerm[index]]
       \* perform noop                                         
        /\ Oplog' = LET entry == [k |-> Nil, v |-> Nil, 
                                  ot |-> Ot'[i], term |-> CurrentTerm'[i]]
                        newLog == Append(Oplog[i], entry)
                    IN [Oplog EXCEPT ![i] = newLog]                                         
        \* A primary node do not have any sync source                                        
        /\ SyncSource' = [SyncSource EXCEPT ![i] = Nil ]
    /\ UNCHANGED <<Store, Ct, Ot, messageVar, timeVar, Cp, State, tunableVars>> 

\* A primary node advance its commit point
AdvanceCp ==
    /\ \E s \in Primary:
        LET newCp == ComputeNewCp(s)
        IN Cp' = [ Cp EXCEPT ![s] = newCp]
    /\ UNCHANGED <<electionVars, storageVars, servernodeVars, Ct, messageVar, timeVar, State, CurrentTerm, tunableVars>>                                              
                                                                                                                                                                                                  
\*注意：heartbeat没有更新oplog，没有更新Ot，也没有更新store状态     
\* A server node deal with heartbeat msg                                                                                                                                                                                                  
ServerTakeHeartbeat ==
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
    /\ UNCHANGED <<electionVars, storageVars, servernodeVars, timeVar, CurrentTerm, tunableVars>>

\* A server node deal with update position msg
ServerTakeUpdatePosition == 
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
    /\ UNCHANGED <<electionVars, storageVars, servernodeVars, timeVar, tunableVars>>                   
                  
\* simplify NTP protocal                  
NTPSync == 
    /\ Pt' = [ s \in Server |-> MaxPt ] 
    /\ UNCHANGED <<electionVars, storageVars, servernodeVars, learnableVars, messageVar, tunableVars>>

\* A primary node advance its physical time
AdvancePt == 
    /\ \E s \in Server:  
           /\ s \in Primary                    \* for simplicity
           /\ Pt[s] <= PtStop 
           /\ Pt' = [ Pt EXCEPT ![s] = @+1 ] \* advance physical time
           /\ BroadcastHeartbeat(s)          \* broadcast heartbeat periodly
    /\ UNCHANGED <<electionVars, storageVars, servernodeVars, learnableVars, tunableVars>>
                                     
\* Replication                                     
\* Idea: 进行replicate的时候，首先进行canSyncFrom的判断，拥有更多log且大于等于term的才能作为同步源
\* 其次，开始同步之后，把当前节点的同步源设置为SyncSource[s]，随后向SyncSource的信道里加入UpdatePosition消息
\* 最后，关于UpdatePosition的转发，如果自己的信道里有type为updatePosition的消息，则向上层节点转发
\* Replicate oplog from node j to node i, and update related structures accordingly
 Replicate == 
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
    /\ UNCHANGED <<electionVars, timeVar, tunableVars>>                    
                    
\* Rollback i's oplog and recover it to j's state   
\* Recover to j's state immediately to prevent internal client request  
RollbackAndRecover ==
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
    /\ UNCHANGED <<electionVars, timeVar, tunableVars>>                     
    
----------------------------------------------------------------------------- 
\* Server Actions                 
\* Server Get
ServerGetReply_sleep ==
    /\ \E s \in Server, m \in Messages:
       /\ m.type = "get"
       /\ m.dest = s
       /\ Ct' = [ Ct EXCEPT ![s] = HLCMax(Ct[s], m.ct) ] \*rc = major  
       /\ BlockedThread' = [BlockedThread EXCEPT ![m.c] = 
                            [type |-> "read", s |-> s, k |-> m.k, ot |-> m.ot]]
       /\ Messages' = Messages \ {m}
    /\ UNCHANGED <<electionVars, Cp, CurrentTerm, messageVar, SyncSource, Store, timeVar, Oplog, Ot, State,
                   BlockedClient, clientnodeVars, SnapshotTable>>
                   
ServerGetReply_wake == 
    /\ \E c \in Client:
       /\ BlockedThread[c] /= Nil
       /\ BlockedThread[c].type ="read"
       /\ ~ HLCLt(Cp[BlockedThread[c].s], BlockedThread[c].ot) \* wait until cp[s] >= target ot 
       /\ ~ HLCLt(Ot[BlockedThread[c].s], Cp[BlockedThread[c].s]) \* wait until Ot[s] >= Cp[s] to ensure an availiable snapshot
       /\ SelectSnapshotIndex(SnapshotTable[BlockedThread[c].s], Cp[BlockedThread[c].s]) /= Nil \* exist related snapshot
       /\ Messages' = LET otTime == [ p|-> Cp[BlockedThread[c].s].p, l |-> Cp[BlockedThread[c].s].l ]
                      IN  LET m == [type |-> "get_reply", dest |-> c, k |-> BlockedThread[c].k, 
                                v |-> SelectSnapshot(SnapshotTable[BlockedThread[c].s], Cp[BlockedThread[c].s])[BlockedThread[c].k],
                                ct |-> Ct[BlockedThread[c].s], ot |-> otTime ] \* read from snapshot table
                          IN  Messages \cup {m}                                              
       /\ BlockedThread' = [BlockedThread EXCEPT ![c] = Nil]
    /\ UNCHANGED <<serverVars, clientnodeVars, BlockedClient,  SnapshotTable>>                
       
\* Server Put 注意：只有收到写操作时才会记录server的oplog
ServerPutReply_sleep == 
    /\ \E s \in Primary, m \in Messages:
        /\ m.type = "put"
        /\ m.dest = s
        /\ UpdateAndTick(s, m.ct)
        /\ Ot' = [ Ot EXCEPT ![s] =  Ct'[s] ] \* advance the last applied operation time Ot[s]
        /\ Store' = [ Store EXCEPT ![s][m.k] = m.v ] \* append operation to oplog[s]
        /\ Oplog' = LET entry == [k |-> m.k, v |-> m.v, 
                                  ot |-> Ot'[s], term |-> CurrentTerm[s]]
                        newLog == Append(Oplog[s], entry)
                    IN [Oplog EXCEPT ![s] = newLog] 
        /\ State' = LET newState == GetNewState(s, s, Ot'[s].p, Ot'[s].l, CurrentTerm[s])      
                    IN  [State EXCEPT ![s] = newState]      \* update primary state    
        /\ BlockedThread' = [BlockedThread EXCEPT ![m.c] = [type |-> "write",
                                   ot |-> Ot'[s], s |-> s, k |-> m.k, v |-> m.v ] ] \* add the user History to BlockedThread[c]          
        /\ Messages' = Messages \ {m}
    /\ UNCHANGED <<electionVars, Cp, CurrentTerm, messageVar, SyncSource, timeVar,
                   BlockedClient, clientnodeVars, SnapshotTable>> 
                                   
ServerPutReply_wake ==
    /\ \E c \in Client:
        /\ BlockedThread[c] /=  Nil
        /\ BlockedThread[c].type = "write"
        /\ ~ HLCLt(Cp[BlockedThread[c].s], BlockedThread[c].ot) \* w:majority
        /\ Messages' = LET newMsgs == [ type |-> "put_reply", dest |-> c, ot |-> BlockedThread[c].ot, ct |-> Ct[BlockedThread[c].s], 
                                        k |-> BlockedThread[c].k, v |-> BlockedThread[c].v ]
                       IN  Messages \cup {newMsgs}   
        /\ BlockedThread' =  [ BlockedThread EXCEPT ![c] = Nil ] \* remove blocked state     
    /\ UNCHANGED <<serverVars, clientnodeVars, BlockedClient, SnapshotTable>>               
          
----------------------------------------------------------------------------- 
\* Client Actions      
\* Client Get
ClientGetRequest ==
    /\ \E k \in Key, c \in Client \ BlockedClient, s \in Server: 
        /\ OpCount[c] /= 0
        /\ LET m == [ type |-> "get", dest |-> s, c |-> c, k |-> k, ct |-> Ct[c], ot |-> Ot[c]]
           IN  Messages' = Messages \cup {m}
        /\ BlockedClient' = BlockedClient \cup {c}          
    /\ UNCHANGED <<serverVars, clientnodeVars, BlockedThread, SnapshotTable>>  

ClientGetResponse ==  
    /\ \E c \in Client, m \in Messages:
       /\ OpCount[c] /= 0
       /\ m.type = "get_reply"
       /\ m.dest = c
       /\ Ct' = [ Ct EXCEPT ![c] = HLCMax(@, m.ct) ]
       /\ Ot' = [ Ot EXCEPT ![c] = HLCMax(@, m.ot) ]
       /\ Store' = [ Store EXCEPT ![c][m.k] = m.v ]
       /\ History' = [ History EXCEPT ![c] = Append (@, [ type |-> "get", 
                       ts |-> m.ot, k |-> m.k, v |-> m.v]) ]
       /\ Messages' = Messages \ {m}
       /\ BlockedClient' = BlockedClient \ {c}
       /\ OpCount' = [ OpCount EXCEPT ![c] = @-1 ]                
    /\ UNCHANGED <<electionVars, Oplog, messageVar, SyncSource, State, Cp, CurrentTerm, SnapshotTable, timeVar, BlockedThread>>     

\* Client Put    
ClientPutRequest == 
    /\ \E k \in Key, v \in Value, c \in Client \ BlockedClient, s \in Primary:
        /\ OpCount[c] /= 0
        /\ LET m == [ type |-> "put", dest |-> s, c |-> c, k |-> k, v |-> v, ct |-> Ct[c] ] 
           IN  Messages' = Messages \cup {m}
        /\ BlockedClient' = BlockedClient \cup {c} \* wait for server reply
    /\ UNCHANGED <<serverVars, BlockedThread, clientnodeVars, SnapshotTable>>     
                 
ClientPutResponse ==  
    /\ \E c \in Client, m \in Messages:
       /\ OpCount[c] /= 0
       /\ m.type = "put_reply"
       /\ m.dest = c
       /\ Ct' = [ Ct EXCEPT ![c] = HLCMax(@, m.ct) ]
       /\ Ot' = [ Ot EXCEPT ![c] = HLCMax(@, m.ot) ]
       /\ History' = [ History EXCEPT ![c] = Append (@, [ type |-> "put", 
                       ts |-> m.ot, k |-> m.k, v |-> m.v]) ]
       /\ Messages' = Messages \ {m}
       /\ BlockedClient' = BlockedClient \ {c}
       /\ OpCount' = [ OpCount EXCEPT ![c] = @-1 ]                
    /\ UNCHANGED <<electionVars, storageVars, messageVar, SyncSource, State, Cp, CurrentTerm, SnapshotTable, timeVar, BlockedThread>>                      
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
        \/ NTPSync
        \/ ServerTakeHeartbeat
        \/ ServerTakeUpdatePosition
        \/ AdvanceCp
        \/ Snapshot
        \/ Stepdown
        \/ RollbackAndRecover
        \/ ElectPrimary
              
Spec == Init /\ [][Next]_vars     
\*
\*DURABLE == INSTANCE MongoDBCC_Durable
\*
\*THEOREM Refinement == Spec => DURABLE!Spec     

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

\* CMv Specification (test)
CMvSatisification == 
                  \*/\ CMv(History, Client)
                  \/ \A c \in Client: Len(History[c]) < 2
                  \/ \E c \in Client: Len(History[c]) > 7
                  \/ CMvDef(History, Client)
=============================================================================
\* Modification History
\* Last modified Fri Aug 19 21:22:31 CST 2022 by dh
\* Created Fri Aug 05 15:50:01 CST 2022 by dh

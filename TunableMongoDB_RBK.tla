\* Optimise idea: use readConcern and writeConcern as 'concernVars' to act as constants
\* And then use 'CASE' to switch between different combinations [ref:cosmos_client]

\* Optimise idea: group variables by their function [ref:RaftMongo]

------------------------- MODULE TunableMongoDB_RBK -------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* constants and variables
CONSTANTS Client, Server,   \* the set of clients and servers
          Key, Value,      \* the set of keys and values
          Nil,            \* model value, place holder
          OpTimes,        \* op count at most
          PtStop,          \* max physical time
          Number            \* writeConcern number

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
servernodeVars == <<Ot, SyncSource, SnapshotTable>>                    \* vars that each server node holds for itself
learnableVars == <<Ct, State, Cp, CurrentTerm>>     \* vars that must learn from msgs
timeVar == <<Pt>>                                   \* var that is used for timing
functionalVar == <<ReadyToServe>>                   \* var that is used for some extra function  
clientnodeVars == <<History, OpCount>>

tmessageVars == <<InMsgc, InMsgs>>
tfunctionalVars == <<BlockedClient, BlockedThread>>


serverVars == <<electionVars, storageVars, messageVar, servernodeVars, learnableVars, timeVar, functionalVar>>
tunableVars == <<BlockedClient, BlockedThread, History, InMsgc, InMsgs, OpCount, SnapshotTable>>        
              
-----------------------------------------------------------------------------
ASSUME Cardinality(Client) >= 1  \* at least one client
ASSUME Cardinality(Server) >= 2  \* at least one primary and one secondary
ASSUME Cardinality(Key) >= 1  \* at least one object
ASSUME Cardinality(Value) >= 2  \* at least two values to update

\* Helpers
-----------------------------------------------------------------------------
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
LastTerm(i) == CurrentTerm[i]          
\*LastTerm(i) == LogTerm(i, Len(Oplog[i]))                               
                            
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

\* heartbeat
\* Only Primary node sends heartbeat once advance pt
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
    
    
                    
 
 \* compute a new common point according to new update position msg
ComputeNewCp(s) == 
    \* primary node: compute new mcp
    IF s \in Primary THEN 
        LET quorumAgree == QuorumAgreeInSameTerm(State[s]) IN
        IF  Cardinality(quorumAgree) > 0 
            THEN LET QuorumSet == CHOOSE i \in quorumAgree: TRUE
                     serverInQuorum == CHOOSE j \in QuorumSet: TRUE
                     termOfQuorum == State[s][serverInQuorum].term 
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
                                 
\* Init Part                       
-----------------------------------------------------------------------------
InitPrimary == Primary = CHOOSE s \in Server: TRUE
InitSecondary == Secondary = Server \ {Primary}
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
    
\* Next State Actions  
\* Replication Protocol: possible actions  
-----------------------------------------------------------------------------
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
    /\ UNCHANGED <<storageVars, serverVars, Ct, messageVar, timeVar, Cp, State, CurrentTerm, functionalVar, tunableVars>>

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
    /\ UNCHANGED<<electionVars, storageVars, serverVars, Ct, messageVar, timeVar, Cp, State, tunableVars>>     

AdvanceCp ==
    /\ ReadyToServe > 0
    /\ \E s \in Primary:
        LET newCp == ComputeNewCp(s)
        IN Cp' = [ Cp EXCEPT ![s] = newCp]
    /\ UNCHANGED <<electionVars, storageVars, serverVars, Ct, messageVar, timeVar, State, CurrentTerm, functionalVar, tunableVars>>                                              
                                                                                                                                                                                                  
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
    /\ UNCHANGED <<electionVars, storageVars, serverVars, timeVar, functionalVar, tunableVars>>

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
    /\ UNCHANGED <<electionVars, storageVars, serverVars, timeVar, functionalVar, tunableVars>>                   
                  
NTPSync == \* simplify NTP protocal
    /\ ReadyToServe > 0
    /\ Pt' = [ s \in Server |-> MaxPt ] 
    /\ UNCHANGED <<electionVars, storageVars, serverVars, learnableVars, messageVar, functionalVar, tunableVars>>

AdvancePt == 
    /\ ReadyToServe > 0
    /\ \E s \in Server:  
           /\ s \in Primary                    \* for simplicity
           /\ Pt[s] <= PtStop 
           /\ Pt' = [ Pt EXCEPT ![s] = @+1 ] \* advance physical time
           /\ BroadcastHeartbeat(s)          \* broadcast heartbeat periodly
    /\ UNCHANGED <<electionVars, storageVars, serverVars, learnableVars, functionalVar, tunableVars>>
                                     
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
    
\* Tunable Protocol: Server Actions
-----------------------------------------------------------------------------                  
\* Server Get

ServerGetReply_local_sleep ==
    /\ ReadyToServe > 0
    /\ \E s \in Server:
        /\ Len(InMsgs[s]) /= 0        \* message channel is not empty
        /\ InMsgs[s][1].op = "get"    \* msg type: get
        /\ InMsgs[s][1].rc = "local"  \* Read Concern: local
        /\ Ct' = [ Ct EXCEPT ![s] = HLCMax(Ct[s], InMsgs[s][1].ct) ] \* Update Ct according to InMsg
        /\ BlockedThread' = [BlockedThread EXCEPT ![InMsgs[s][1].c] = 
                            [type |-> "read_local", s |-> s, k |-> InMsgs[s][1].k, ot |-> InMsgs[s][1].ot]]
        /\ InMsgs' = [ InMsgs EXCEPT ![s] = Tail(@) ]
    /\ UNCHANGED <<electionVars, functionalVar, messageVar, servernodeVars, storageVars, timeVar,
                   Cp, CurrentTerm, State, BlockedClient, clientnodeVars, InMsgc, SnapshotTable>>
                   
        
ServerGetReply_local_wake ==
    /\ ReadyToServe > 0
    /\ \E c \in Client:
        /\ BlockedThread[c] /= Nil
        /\ BlockedThread[c].type = "read_local"
        /\ ~ HLCLt(Ot[BlockedThread[c].s], BlockedThread[c].ot) \* wait until Ot[s] >= target ot               
        /\ InMsgc' = [ InMsgc EXCEPT ![c] = Append(@, [ op |-> "get", k |-> BlockedThread[c].k, v |->
                        Store[BlockedThread[c].s][BlockedThread[c].k], 
                        ct |-> Ct[BlockedThread[c].s], ot |-> Ot[BlockedThread[c].s]])]
            \* send msg to client   
        /\ BlockedThread' = [BlockedThread EXCEPT ![c] = Nil]
    /\ UNCHANGED <<serverVars, clientnodeVars, BlockedClient, InMsgs, SnapshotTable>>                    
                               
ServerGetReply_majority_sleep ==
    /\ ReadyToServe > 0
    /\ \E s \in Server:
        /\ Len(InMsgs[s]) /= 0       \* message channel is not empty
        /\ InMsgs[s][1].op = "get"   \* msg type: get
        /\ InMsgs[s][1].rc = "major" \* Read Concern: majority
        /\ Ct' = [ Ct EXCEPT ![s] = HLCMax(Ct[s], InMsgs[s][1].ct) ]
        /\ BlockedThread' = [BlockedThread EXCEPT ![InMsgs[s][1].c] = 
                            [type |-> "read_major", s |-> s, k |-> InMsgs[s][1].k, ot |-> InMsgs[s][1].ot]]
        /\ InMsgs' = [ InMsgs EXCEPT ![s] = Tail(@) ]
    /\ UNCHANGED<<electionVars, functionalVar, messageVar, servernodeVars, storageVars, timeVar,
                   Cp, CurrentTerm, State, BlockedClient, clientnodeVars, InMsgc, SnapshotTable>>
                  
ServerGetReply_majority_wake ==        
    /\ ReadyToServe > 0 
    /\ \E c \in Client:
        /\ BlockedThread[c] /= Nil
        /\ BlockedThread[c].type = "read_major"
        /\ ~ HLCLt(Ot[BlockedThread[c].s], BlockedThread[c].ot) \* wait until Ot[s] >= target ot  
        /\ InMsgc' = [ InMsgc EXCEPT ![c] = Append(@, [ op |-> "get", k |-> BlockedThread[c].k, v |-> 
                        SelectSnapshot(SnapshotTable[BlockedThread[c].s], Cp[BlockedThread[c].s])[BlockedThread[c].k], 
                        ct |-> Ct[BlockedThread[c].s], ot |-> Cp[BlockedThread[c].s]])]
            \* send msg to client  
        /\ BlockedThread' = [BlockedThread EXCEPT ![c] = Nil]        
    /\ UNCHANGED <<serverVars, clientnodeVars, BlockedClient, InMsgs, SnapshotTable>>          
          
ServerGetReply_linearizable_sleep ==
    /\ ReadyToServe > 0
    /\ \E s \in Server:
        /\ s = Primary
        /\ Len(InMsgs[s]) /= 0
        /\ InMsgs[s][1].op = "get"
        /\ InMsgs[s][1].rc = "linea" \* Read Concern: linearizable
        /\ Tick(s)  \* advance cluster time
        /\ Oplog' = [ Oplog EXCEPT ![s] =
                    Append(@, <<Nil, Nil, Ct'[s]>>)]
                    \* append noop operation to oplog[s]
        /\ Ot' = [ Ot EXCEPT ![s] =  Ct'[s] ] 
                    \* advance the last applied operation time Ot[s]
        /\ State' = LET newState == GetNewState(s, s, Ot'[s].p, Ot'[s].l, CurrentTerm[s])      
                    IN  [State EXCEPT ![s] = newState]      \* update primary state
        /\ InMsgs' = [ InMsgs EXCEPT ![s] = Tail(@) ]
        /\ BlockedThread' = [BlockedThread EXCEPT ![InMsgs[s][1].c] = 
                            [type |-> "read_linea", ot|-> Ct'[s], s |-> s, k 
                            |->InMsgs[s][1].k, v |-> Store[s][InMsgs[s][1].k] ] ] 
                     \* add the user thread to BlockedThread[c]                                                             
    /\ UNCHANGED <<electionVars, functionalVar, Cp, CurrentTerm, messageVar, SyncSource, Store, timeVar,
                   InMsgc, BlockedClient, clientnodeVars, SnapshotTable>> 
                  
ServerGetReply_linearizable_wake ==
      /\ ReadyToServe > 0
      /\ \E c \in Client:
        /\ BlockedThread[c] /= Nil
        /\ BlockedThread[c].type = "read_linea"
        /\  ~ HLCLt(Cp[BlockedThread[c].s], BlockedThread[c].ot) \* cp[s] >= target ot     
        /\ InMsgc' = [ InMsgc EXCEPT ![c] = Append(@, [ op |-> "get", k 
                       |-> BlockedThread[c].k, v |-> BlockedThread[c].v, ct
                       |-> Ct[BlockedThread[c].s], ot|->BlockedThread[c].ot ])] 
        /\ BlockedThread' =  [ BlockedThread EXCEPT ![c] = Nil ] \* remove blocked state
      /\ UNCHANGED <<serverVars, clientnodeVars, BlockedClient, InMsgs, SnapshotTable>> 
                      
\* Server Put
\* 注意：只有收到写操作时才会记录server的oplog

ServerPutReply_zero ==
    /\ ReadyToServe > 0
    /\ \E s \in Primary:
        /\ Len(InMsgs[s]) /= 0       \* message channel is not empty
        /\ InMsgs[s][1].op = "put"   \* msg type: put
        /\ InMsgs[s][1].wc = "zero"  \* Write Concern: 0
        /\ Tick(s)                   \* advance cluster time
        /\ Ot' = [ Ot EXCEPT ![s] =  Ct'[s] ]
                         \* advance the last applied operation time Ot[s]
        /\ Store' = [ Store EXCEPT ![s][InMsgs[s][1].k] = InMsgs[s][1].v ]
                    \* append operation to oplog[s]
        /\ Oplog' = LET entry == [k |-> InMsgs[s][1].k, v |-> InMsgs[s][1].v, 
                                  ot |-> Ot'[s], term |-> CurrentTerm[s]]
                        newLog == Append(Oplog[s], entry)
                    IN [Oplog EXCEPT ![s] = newLog]            
        /\ State' = LET newState == GetNewState(s, s, Ot'[s].p, Ot'[s].l, CurrentTerm[s])      
                    IN  [State EXCEPT ![s] = newState]      \* update primary state               
        /\ InMsgs' = [ InMsgs EXCEPT ![s] = Tail(@)]      
    /\ UNCHANGED <<electionVars, functionalVar, Cp, CurrentTerm, messageVar, SyncSource, timeVar, 
                   BlockedClient, BlockedThread, clientnodeVars, InMsgc,SnapshotTable>>
                 
ServerPutReply_number_sleep ==
    /\ ReadyToServe > 0
    /\ \E s \in Primary:
        /\ Len(InMsgs[s]) /= 0       \* message channel is not empty
        /\ InMsgs[s][1].op = "put"   \* msg type: put
        /\ InMsgs[s][1].wc = "num"   \* Write Concern: num
        /\ Tick(s)                   \* advance cluster time
        /\ Ot' = [ Ot EXCEPT ![s] =  Ct'[s] ]
                         \* advance the last applied operation time Ot[s]
        /\ Store' = [ Store EXCEPT ![s][InMsgs[s][1].k] = InMsgs[s][1].v ]
        /\ LET entry == [ k |-> InMsgs[s][1].k, v |-> InMsgs[s][1].v, 
                          ot |-> Ot'[s], term |-> CurrentTerm[s] ]
               newLog == Append(Oplog[s], entry)
           IN Oplog' = [ Oplog EXCEPT ![s] = newLog ]
        /\ State' = LET newState == GetNewState(s, s, Ot'[s].p, Ot'[s].l, CurrentTerm[s])      
                    IN  [State EXCEPT ![s] = newState]      \* update primary state     
        /\ BlockedThread' = [ BlockedThread EXCEPT ![InMsgs[s][1].c] = [ type |-> "write_num", 
                              ot |-> Ot'[s], s |-> s, numnode |-> InMsgs[s][1].num,
                              k |->InMsgs[s][1].k, v |-> InMsgs[s][1].v ] ] 
                      \* add the user History to BlockedThread[c]            
        /\ InMsgs' = [ InMsgs EXCEPT ![s] = Tail(@) ]       
    /\ UNCHANGED <<electionVars, functionalVar, Cp, CurrentTerm, messageVar, SyncSource, timeVar,
                   InMsgc, BlockedClient, clientnodeVars, SnapshotTable>>              
 
ServerPutReply_number_wake ==
      /\ ReadyToServe > 0     
      /\ \E c \in Client:
        /\ BlockedThread[c] /=  Nil
        /\ BlockedThread[c].type = "write_num"
        /\ LET serverSet == ReplicatedServers(State[BlockedThread[c].s], BlockedThread[c].ot)
           IN  Cardinality(serverSet) >= BlockedThread[c].numnode
\*        /\  ~ HLCLt(CalState[Cardinality(Server) - BlockedThread[c].numnode + 1],
\*                    BlockedThread[c].ot)  \* CalState[s][n- num + 1] >= target ot
        /\ InMsgc' = [ InMsgc EXCEPT ![c] =  Append(@, [ op |-> "put", ct 
                       |-> Ct[BlockedThread[c].s], ot |-> BlockedThread[c].ot, k|-> BlockedThread[c].k, v |-> BlockedThread[c].v]) ] 
        /\ BlockedThread' =  [ BlockedThread EXCEPT ![c] = Nil ] 
                                                       \* remove blocked state
      /\ UNCHANGED <<serverVars, clientnodeVars, BlockedClient, InMsgs, SnapshotTable>>
       
(***************************************************************************
DH modified: Add k and v message when block thread, and return them when wake
 ***************************************************************************)  
ServerPutReply_majority_sleep == 
    /\ ReadyToServe > 0
    /\ \E s \in Primary:
        /\ Len(InMsgs[s]) /= 0
        /\ InMsgs[s][1].op = "put"
        /\ InMsgs[s][1].wc = "major"        
        /\ Tick(s)
        /\ Ot' = [ Ot EXCEPT ![s] =  Ct'[s] ]
        /\ Store' = [ Store EXCEPT ![s][InMsgs[s][1].k] = InMsgs[s][1].v ]
        /\ Oplog' = 
            LET entry == [k |-> InMsgs[s][1].k, v |-> InMsgs[s][1].v, ot |-> Ot'[s], term |-> CurrentTerm[s]]
                newLog == Append(Oplog[s], entry)
            IN  [ Oplog EXCEPT ![s] = newLog ]
        /\ State' = LET newState == GetNewState(s, s, Ot'[s].p, Ot'[s].l, CurrentTerm[s])      
                    IN  [State EXCEPT ![s] = newState]      \* update primary state              
        /\ BlockedThread' = [BlockedThread EXCEPT ![InMsgs[s][1].c] = [type |-> "write_major", ot
                     |-> Ot'[s], s |-> s, k |->InMsgs[s][1].k, v |-> InMsgs[s][1].v ] ]               
        /\ InMsgs' = [ InMsgs EXCEPT ![s] = Tail(@) ]       
    /\ UNCHANGED <<electionVars, functionalVar, Cp, CurrentTerm, messageVar, SyncSource, timeVar,
                   InMsgc, BlockedClient, clientnodeVars, SnapshotTable>>
    
ServerPutReply_majority_wake ==    
      /\ ReadyToServe > 0
      /\ \E c \in Client:
        /\ BlockedThread[c] /=  Nil        
        /\ BlockedThread[c].type = "write_major"
        /\  ~ HLCLt(Cp[BlockedThread[c].s], BlockedThread[c].ot)      
        /\ InMsgc' = [ InMsgc EXCEPT ![c] = 
            Append(@, [ op |-> "put", ct |-> Ct[BlockedThread[c].s], ot |-> BlockedThread[c].ot, 
                        k |-> BlockedThread[c].k, v |-> BlockedThread[c].v ]) ]  
        /\ BlockedThread' =  [ BlockedThread EXCEPT ![c] = Nil ]  
      /\ UNCHANGED <<serverVars, clientnodeVars, BlockedClient, InMsgs, SnapshotTable>>  

\* Tunable Protocol: Client Actions                
----------------------------------------------------------------------------- 
\* Client Get

ClientGetRequest_local_primary ==
    /\ ReadyToServe > 0
    /\ \E k \in Key, c \in Client \ BlockedClient, s \in Primary:
        /\ InMsgs' = [ InMsgs EXCEPT ![s] = Append(@,
            [ op |-> "get", c |-> c, rc |-> "local", k |-> k, ct |-> Ct[c], ot |-> Ot[c]])]
        /\ BlockedClient' = BlockedClient \cup {c}
    /\ UNCHANGED <<serverVars, clientnodeVars, BlockedThread, InMsgc, SnapshotTable>>

ClientGetRequest_local_secondary ==
    /\ ReadyToServe > 0
    /\ \E k \in Key, c \in Client \ BlockedClient, s \in Secondary:
        /\ InMsgs' = [ InMsgs EXCEPT ![s] = Append(@,
            [ op |-> "get", c |-> c, rc |-> "local", k |-> k, ct |-> Ct[c], ot |-> Ot[c]])]
        /\ BlockedClient' = BlockedClient \cup {c}
    /\ UNCHANGED <<serverVars, clientnodeVars, BlockedThread, InMsgc, SnapshotTable>>
                       
ClientGetRequest_majority_primary ==     
    /\ ReadyToServe > 0              
    /\ \E k \in Key, c \in Client \ BlockedClient, s \in Primary:
        /\ InMsgs' = [ InMsgs EXCEPT ![s] = Append(@,
            [ op |-> "get", c |-> c, rc |-> "major", k |-> k, ct |-> Ct[c], ot |-> Ot[c]])]
        /\ BlockedClient' = BlockedClient \cup {c}
    /\ UNCHANGED  <<serverVars, clientnodeVars, BlockedThread, InMsgc, SnapshotTable>>

ClientGetRequest_majority_secondary ==    
    /\ ReadyToServe > 0               
    /\ \E k \in Key, c \in Client \ BlockedClient, s \in Secondary:
        /\ InMsgs' = [ InMsgs EXCEPT ![s] = Append(@,
            [ op |-> "get", c |-> c, rc |-> "major", k |-> k, ct |-> Ct[c], ot |-> Ot[c]])]
        /\ BlockedClient' = BlockedClient \cup {c}
    /\ UNCHANGED  <<serverVars, clientnodeVars, BlockedThread, InMsgc, SnapshotTable>>
                       
ClientGetRequest_linearizable ==      
    /\ ReadyToServe > 0             
    /\ \E k \in Key, c \in Client \ BlockedClient, s \in Primary:
        /\ InMsgs' = [ InMsgs EXCEPT ![s] = Append(@,
            [ op |-> "get", c |-> c, rc |-> "linea", k |-> k, ct |-> Ct[c], ot |-> Ot[c]])]
        /\ BlockedClient' = BlockedClient \cup {c}
    /\ UNCHANGED  <<serverVars, clientnodeVars, BlockedThread, InMsgc, SnapshotTable>>
    
\* Client Put    
(***************************************************************************
DH modified: change the state of history when write with w:0
 ***************************************************************************)
ClientPutRequest_zero ==
    /\ ReadyToServe > 0
    /\ \E k \in Key, v \in Value, c \in Client \ BlockedClient, s \in Primary:
        /\ OpCount[c] /= 0
        /\ InMsgs' = [ InMsgs EXCEPT ![s] = 
            Append(@, [ op |-> "put", c |-> c, wc |-> "zero", k
                       |-> k, v |-> v, ct |-> Ct[c]])]
        /\ OpCount' = [ OpCount EXCEPT ![c] = @-1 ]    
        /\ History' = [History EXCEPT ![c] = Append(@, [ op |-> "put", ts |-> InMsgc[c][1].ot, k |-> k, v |-> v ]) ]        
    /\ UNCHANGED <<serverVars, BlockedClient, BlockedThread, InMsgc, SnapshotTable>>
                   
ClientPutRequest_number ==
    /\ ReadyToServe > 0
    /\ \E k \in Key, v \in Value, c \in Client \ BlockedClient, num \in Number, s \in Primary:
        /\ InMsgs' = [ InMsgs EXCEPT ![s] = 
            Append(@, [ op |-> "put", c |-> c, wc |-> "num", num |-> num, k |-> k, v |-> v, ct |-> Ct[c]])]
        /\ BlockedClient' = BlockedClient \cup {c}
    /\ UNCHANGED <<serverVars, clientnodeVars, BlockedThread, InMsgc, SnapshotTable>> 
                                                                           
ClientPutRequest_majority ==
    /\ ReadyToServe > 0
    /\ \E k \in Key, v \in Value, c \in Client \ BlockedClient, s \in Primary:
        /\ InMsgs' = [ InMsgs EXCEPT ![s] = 
            Append(@, [ op |-> "put", c |-> c, wc |-> "major", k |-> k, v |-> v, ct |-> Ct[c]])]
        /\ BlockedClient' = BlockedClient \cup {c}
    /\ UNCHANGED <<serverVars, clientnodeVars, BlockedThread, InMsgc, SnapshotTable>>

                   
(***************************************************************************
DH modified: record the k and v in msg to history
 ***************************************************************************)                                   
ClientGetResponse ==
    /\ ReadyToServe > 0
    /\ \E c \in Client:
        /\ OpCount[c] /= 0          \* client c has operation times
        /\ Len(InMsgc[c]) /= 0      \* message channel is not empty
        /\ InMsgc[c][1].op = "get"  \* msg type: get
        /\ Store' = [ Store EXCEPT ![c][InMsgc[c][1].k] = InMsgc[c][1].v ] 
            \* store data
        /\ History' = [ History EXCEPT ![c] = Append(@, [ op |-> "get", 
                        ts |-> InMsgc[c][1].ot, k |-> InMsgc[c][1].k, v |-> InMsgc[c][1].v ]) ]    
                        
        /\ InMsgc' = [ InMsgc EXCEPT ![c] = Tail(@) ]
        /\ BlockedClient' = IF Len(InMsgc'[c]) = 0
                            THEN BlockedClient \ {c}
                            ELSE BlockedClient  \* remove blocked state
        /\ OpCount' = [ OpCount EXCEPT ![c] = @-1 ]
    /\ UNCHANGED <<electionVars, functionalVar, learnableVars, messageVar, servernodeVars, Oplog, timeVar,
                   BlockedThread, InMsgs, SnapshotTable>>
                   
(***************************************************************************
DH modified: record the k and v in msg to history， record ot from server
 ***************************************************************************)     

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

\* Action Wrapper                   
-----------------------------------------------------------------------------

ClientGetRequest_local == \/ ClientGetRequest_local_primary 
                          \/ ClientGetRequest_local_secondary
ClientGetRequest_majority == \/ ClientGetRequest_majority_primary 
                             \/ ClientGetRequest_majority_secondary

\* all possible client get actions      
ClientGetRequest == \/ ClientGetRequest_local 
                    \/ ClientGetRequest_majority 
                    \/ ClientGetRequest_linearizable

\* all possible clent put actions                          
ClientPutRequest == \/ ClientPutRequest_zero
                    \/ ClientPutRequest_number
                    \/ ClientPutRequest_majority

\* all possible server get actions                     
ServerGetReply == \/ ServerGetReply_local_sleep 
                  \/ ServerGetReply_local_wake
                  \/ ServerGetReply_majority_sleep
                  \/ ServerGetReply_majority_wake 
                  \/ ServerGetReply_linearizable_sleep
                  \/ ServerGetReply_linearizable_wake  

\* all possible server put actions                 
ServerPutReply == \/ ServerPutReply_zero 
                  \/ ServerPutReply_number_sleep 
                  \/ ServerPutReply_majority_sleep
                  \/ ServerPutReply_number_wake  
                  \/ ServerPutReply_majority_wake
                                                            
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
        
Spec == Init /\ [][Next]_vars       
 
Next_Except_ClientRequset == \/ ClientGetResponse
                             \/ ClientPutResponse
                             \/ ServerGetReply        
                             \/ ServerPutReply
                             \/ Replicate
                             \/ AdvancePt
                             \/ ServerTakeHeartbeat
                             \/ ServerTakeUpdatePosition
                             \/ Snapshot
                             \/ Stepdown
                             \/ RollbackAndRecover
                             \/ TurnOnReadyToServe
                             \/ ElectPrimary
                             
ClientRequset_1 == \/ ClientPutRequest_majority   
                   \/ ClientGetRequest_local_primary  

ClientRequset_2 == \/ ClientPutRequest_majority   
                   \/ ClientGetRequest_local_secondary 

ClientRequset_3 == \/ ClientPutRequest_majority   
                   \/ ClientGetRequest_majority_primary

ClientRequset_4 == \/ ClientPutRequest_majority   
                   \/ ClientGetRequest_majority_secondary

ClientRequset_5 == \/ ClientPutRequest_majority   
                   \/ ClientGetRequest_linearizable

ClientRequset_6 == \/ ClientPutRequest_number  
                   \/ ClientGetRequest_local_primary  

ClientRequset_7 == \/ ClientPutRequest_number  
                   \/ ClientGetRequest_local_secondary 

ClientRequset_8 == \/ ClientPutRequest_number   
                   \/ ClientGetRequest_majority_primary

ClientRequset_9 == \/ ClientPutRequest_number  
                   \/ ClientGetRequest_majority_secondary

ClientRequset_10 == \/ ClientPutRequest_number  
                    \/ ClientGetRequest_linearizable          
                   
Next1 == \/ Next_Except_ClientRequset 
         \/ ClientRequset_1

Next2 == \/ Next_Except_ClientRequset 
         \/ ClientRequset_2

Next3 == \/ Next_Except_ClientRequset 
         \/ ClientRequset_3

Next4 == \/ Next_Except_ClientRequset 
         \/ ClientRequset_4
         
Next5 == \/ Next_Except_ClientRequset 
         \/ ClientRequset_5

Next6 == \/ Next_Except_ClientRequset 
         \/ ClientRequset_6

Next7 == \/ Next_Except_ClientRequset 
         \/ ClientRequset_7

Next8 == \/ Next_Except_ClientRequset 
         \/ ClientRequset_8        
         
Next9 == \/ Next_Except_ClientRequset 
         \/ ClientRequset_9  
  
Next10 == \/ Next_Except_ClientRequset 
          \/ ClientRequset_10                                                                                                                                                                                                    
                
Spec1 == Init /\ [][Next1]_vars
Spec2 == Init /\ [][Next2]_vars
Spec3 == Init /\ [][Next3]_vars
Spec4 == Init /\ [][Next4]_vars
Spec5 == Init /\ [][Next5]_vars
Spec6 == Init /\ [][Next6]_vars
Spec7 == Init /\ [][Next7]_vars
Spec8 == Init /\ [][Next8]_vars
Spec9 == Init /\ [][Next9]_vars
Spec10 == Init /\ [][Next10]_vars

\* Causal Specifications
-----------------------------------------------------------------------------
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
\* Last modified Mon May 16 15:35:40 CST 2022 by dh
\* Created Thu Mar 31 20:33:19 CST 2022 by dh

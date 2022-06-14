----------------------- MODULE TunableMongoDB_Durable -----------------------
\* Basic MongoDB xxx protocol in the failure-free deployment with durable guarantee
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
          SyncSource,      \* SyncSource[s]: sync source of server node s
          \* Following are the Tunable related vars
          BlockedClient,
          BlockedThread,
          History,
          Messages,
          OpCount,
          SnapshotTable
          
-----------------------------------------------------------------------------          
\* group related vars to optimize code
electionVars == <<Primary, Secondary>>              \* vars that are related to election  
storageVars == <<Oplog, Store>>                     \* vars that are related to storage
messageVar == <<ServerMsg>>                         \* var that is related to message
servernodeVars == <<Ot, SyncSource>>                    \* vars that each server node holds for itself
learnableVars == <<Ct, State, Cp, CurrentTerm>>     \* vars that must learn from msgs
timeVar == <<Pt>>                                   \* var that is used for timing

serverVars == <<electionVars, storageVars, messageVar, servernodeVars, learnableVars, timeVar>>
tunableVars == <<BlockedClient, BlockedThread, History, Messages, OpCount, SnapshotTable>>
-----------------------------------------------------------------------------
ASSUME Cardinality(Client) >= 1  \* at least one clinet
ASSUME Cardinality(Server) >= 2  \* at least one primary and one secondary
ASSUME Cardinality(Key) >= 1     \* at least one object
ASSUME Cardinality(Value) >= 2   \* at least two values to update
ASSUME ReadConcern \in {"local", "majority", "linearizable"}
ASSUME WriteConcern \in {"zero", "num", "majority"}
ASSUME ReadPreference \in {"primary", "secondary"}
ASSUME WriteNumber <= Cardinality(Server) \* w:num cannot be greater than server number
-----------------------------------------------------------------------------
\* Helpers
HLCLt(x, y) == IF x.p < y.p THEN TRUE
               ELSE IF x.p = y.p
                       THEN IF x.l < y.l THEN TRUE
                            ELSE FALSE
                    ELSE FALSE
                
HLCMin(x, y) == IF HLCLt(x, y) THEN x ELSE y
HLCMax(x, y) == IF HLCLt(x, y) THEN y ELSE x
HLCType == [ p : Nat, l : Nat ]
HLCMinSet(s) == CHOOSE x \in s: \A y \in s: ~HLCLt(y, x)    
Min(x, y) == IF x < y THEN x ELSE y
Max(x, y) == IF x > y THEN x ELSE y

vars == <<Primary, Secondary, Oplog, Store, Ct, Ot, ServerMsg, 
          Pt, Cp, CurrentTerm, State, SyncSource, BlockedClient, BlockedThread,
          History, Messages, OpCount, SnapshotTable>>
        
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
                            
Tick(s) == Ct' = IF Ct[s].p >= Pt[s] 
                    THEN [ Ct EXCEPT ![s] = [ p |-> @.p, l |-> @.l+1] ]
                 ELSE [ Ct EXCEPT ![s] = [ p |-> Pt[s], l |-> 0] ]  
                 
UpdateAndTick(s, msgCt) ==
    LET newCt == [ Ct EXCEPT ![s] = HLCMax(Ct[s], msgCt) ] \* Update ct first according to msg
    IN  Ct' = IF newCt[s].p >= Pt[s] THEN [ newCt EXCEPT ![s] = [ p |-> @.p, l |-> @.l+1] ]
                                     ELSE [ newCt EXCEPT ![s] = [ p |-> Pt[s], l |-> 0] ]                                   

\* heartbeat
\* Only Primary node sends heartbeat once advance pt
BroadcastHeartbeat(s) == 
    LET msg == [ type|-> "heartbeat", s |-> s, aot |-> Ot[s], 
                 ct |-> Ct[s], cp |-> Cp[s], term |-> CurrentTerm[s] ]
    IN ServerMsg' = [x \in Server |-> IF x = s THEN ServerMsg[x]
                                               ELSE Append(ServerMsg[x], msg)]                                                                                   

\* Can node i sync from node j?
CanSyncFrom(i, j) == /\ Len(Oplog[i]) < Len(Oplog[j])
                     /\ LastTerm(i) = LogTerm(j, Len(Oplog[i]))
    
\* Oplog entries needed to replicate from j to i
ReplicateOplog(i, j) ==     
    LET len_i == Len(Oplog[i])
        len_j == Len(Oplog[j])
    IN IF i \in Secondary /\ len_i < len_j
                        THEN SubSeq(Oplog[j], len_i + 1, len_j)
                        ELSE <<>>
                        
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
           
\* Init Part                       
-----------------------------------------------------------------------------
InitPrimary == Primary = {CHOOSE s \in Server: TRUE}
InitSecondary == Secondary = Server \ Primary
InitOplog == Oplog = [ s \in Server |-> <<>> ]
InitStore == Store = [ n \in Server \cup Client  |-> [ k \in Key |-> Nil ] ]
InitCt == Ct = [ n \in Server \cup Client |-> [ p |-> 0, l |-> 0 ] ]
InitOt == Ot = [ n \in Server \cup Client |-> [ p |-> 0, l |-> 0 ] ]
InitServerMsg == ServerMsg = [ s \in Server |-> <<>> ]
InitPt == Pt = [ s \in Server |-> 1 ]
InitCp == Cp = [ n \in Server \cup Client |-> [ p |-> 0, l |-> 0 ] ]
InitState == State = [ s \in Server |-> [ s0 \in Server |-> 
                                              [ p |-> 0, l |-> 0] ] ] 
InitSyncSource == SyncSource = [ s \in Server |-> Nil]    
InitBlockedClient == BlockedClient = {}
InitBlockedThread == BlockedThread = [ s \in Client |-> Nil ]
InitHistory == History = [ c \in Client |-> <<>> ]
InitMessages == Messages = {}
InitOpCount == OpCount = [ c \in Client |-> OpTimes ]   
InitSnap == SnapshotTable = [ s \in Server |-> <<[ ot |-> [ p |-> 0, l |-> 0 ], 
                                                   store |-> [ k \in Key |-> Nil] ] >>]
InitCurrentTerm == CurrentTerm = [ p \in Primary |-> 1 ] @@ [ s \in Server |-> 0 ]                                                                  

Init == 
    /\ InitPrimary /\ InitSecondary /\ InitOplog /\ InitStore /\ InitCt 
    /\ InitOt /\ InitPt /\ InitCp /\ InitServerMsg /\ InitState
    /\ InitSyncSource /\ InitBlockedClient /\ InitBlockedThread
    /\ InitHistory /\ InitMessages /\ InitOpCount /\ InitSnap
    /\ InitCurrentTerm
    
\* Next State Actions  
\* Replication Protocol: possible actions  
-----------------------------------------------------------------------------                                                           
\* Todo: Stepdown when receiving a higher term heartbeat           

\* snapshot periodly
Snapshot == 
    /\ \E s \in Server:
            SnapshotTable' =  [ SnapshotTable EXCEPT ![s] = 
                                Append(@, [ot |-> Ot[s], store |-> Store[s] ]) ]  
                               \* create a new snapshot
    /\ UNCHANGED <<serverVars, Messages, BlockedClient, BlockedThread, OpCount, History>>                        

AdvanceCp ==
    /\ \E s \in Primary:
        LET newCp == ComputeNewCp(s)
        IN Cp' = [ Cp EXCEPT ![s] = newCp]
    /\ UNCHANGED <<electionVars, storageVars, servernodeVars, Ct, messageVar, timeVar, State, CurrentTerm, tunableVars>>                                
           
\*注意：heartbeat没有更新oplog，没有更新Ot，也没有更新store状态                                                                                                                                                                                                       
ServerTakeHeartbeat ==
    /\ \E s \in Server:
        /\ Len(ServerMsg[s]) /= 0  \* message channel is not empty
        /\ ServerMsg[s][1].type = "heartbeat"
        /\ CurrentTerm[s] = ServerMsg[s][1].term
        /\ Ct' = [ Ct EXCEPT ![s] = HLCMax(Ct[s], ServerMsg[s][1].ct) ]          
        /\ State' = LET newState == GetNewState(s, ServerMsg[s][1].s, ServerMsg[s][1].aot.p, ServerMsg[s][1].aot.l, ServerMsg[s][1].term)
                    IN  [State EXCEPT ![s] = newState]
        /\ Cp' = LET newcp == ComputeNewCp(s)
                 IN [ Cp EXCEPT ![s] = newcp ]
       /\ ServerMsg' = [ ServerMsg EXCEPT ![s] = Tail(@) ]    
\*       /\ CurrentTerm' = [CurrentTerm EXCEPT ![s] = Max(CurrentTerm[s], ServerMsg[s][1].term)]  \* -> 因为之前的判断，这里根本不会触发   
    /\ UNCHANGED <<electionVars, storageVars, servernodeVars, timeVar, CurrentTerm, tunableVars>>

ServerTakeUpdatePosition == 
    /\ \E s \in Server:
        /\ Len(ServerMsg[s]) /= 0  \* message channel is not empty
        /\ ServerMsg[s][1].type = "update_position"
        /\ Ct' = [ Ct EXCEPT ![s] = HLCMax(Ct[s], ServerMsg[s][1].ct) ] \* update ct accordingly
        /\ State' = LET newState == GetNewState(s, ServerMsg[s][1].s, ServerMsg[s][1].aot.p, ServerMsg[s][1].aot.l, ServerMsg[s][1].term)
                    IN  [State EXCEPT ![s] = newState]
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

NTPSync == \* simplify NTP protocal
    /\ Pt' = [ s \in Server |-> MaxPt ] 
    /\ UNCHANGED <<electionVars, storageVars, servernodeVars, learnableVars, messageVar, tunableVars>>

AdvancePt == 
    /\ \E s \in Server:  
           /\ s \in Primary                    \* for simplicity
           /\ Pt[s] <= PtStop 
           /\ Pt' = [ Pt EXCEPT ![s] = @+1 ] \* advance physical time
           /\ BroadcastHeartbeat(s)          \* broadcast heartbeat periodly
    /\ UNCHANGED <<electionVars, storageVars, servernodeVars, learnableVars, tunableVars>>
               
\* Replicate oplog from node j to node i, and update related structures accordingly
 Replicate == 
    /\ \E i, j \in Server: 
        /\ CanSyncFrom(i, j) \* i can sync from j
        /\ i \in Secondary
        /\ ReplicateOplog(i, j) /= <<>>
        /\ Oplog' = [Oplog EXCEPT ![i] = @ \o ReplicateOplog(i, j)]
        /\ Store' = [Store EXCEPT ![i] =  Store[j]]
        /\ Ct' = [Ct EXCEPT ![i] = HLCMax(Ct[i], Ct[j])] \* update Ct[i] 
        /\ Ot' = [Ot EXCEPT ![i] = HLCMax(Ot[i], Ot[j])] \* update Ot[i]    
        /\ Cp' = [Cp EXCEPT ![i] = HLCMax(Cp[i], Cp[j])] \* update Cp[i]
        /\ CurrentTerm' = [CurrentTerm EXCEPT ![i] = Max(CurrentTerm[i], CurrentTerm[j])] \* update CurrentTerm
        /\ State' = LET newState == GetNewState(i, j, Ot[j].p, Ot[j].l, CurrentTerm[j]) \* update j's state i knows 
                    IN [State EXCEPT ![i] = newState]
        /\ LET msg == [ type |-> "update_position", s |-> i, aot |-> Ot'[i], ct |-> Ct'[i], cp |-> Cp'[i], term |-> CurrentTerm'[i]]
           IN ServerMsg' = [ ServerMsg EXCEPT ![j] = Append(ServerMsg[j], msg) ]
        /\ SyncSource' = [SyncSource EXCEPT ![i] = j] 
    /\ UNCHANGED <<electionVars, timeVar, tunableVars>>        
       
----------------------------------------------------------------------------- 
ServerPutReply_sleep == 
    /\ \E s \in Primary, m \in Messages:
        /\ m.type = "put"
        /\ m.dest = s
        /\ UpdateAndTick(s, m.ct)
        /\ Ot' = [ Ot EXCEPT ![s] =  Ct'[s] ] \* advance the last applied operation time Ot[s]
        /\ Store' = [ Store EXCEPT ![s][m.k] = m.v ] \* append operation to oplog[s]
        /\ Oplog' = LET entry == [k |-> m.k, v |-> m.v, ot |-> Ot'[s], term |-> CurrentTerm[s]]
                        newLog == Append(Oplog[s], entry)
                    IN [Oplog EXCEPT ![s] = newLog] 
        /\ State' = LET newState == GetNewState(s, s, Ot'[s].p, Ot'[s].l, CurrentTerm[s])      
                    IN  [State EXCEPT ![s] = newState]      \* update primary state    
        /\ IF m.wc = "zero" \* If w:0, do not sleep
            THEN BlockedThread' = BlockedThread
           ELSE BlockedThread' = [BlockedThread EXCEPT ![m.c] = [type |-> "write", wc |-> m.wc,
                                   numnode |-> m.num, ot |-> Ot'[s], s |-> s, 
                                   k |-> m.k, v |-> m.v ] ] \* add the user History to BlockedThread[c]          
        /\ Messages' = Messages \ {m}
    /\ UNCHANGED <<electionVars, Cp, CurrentTerm, messageVar, SyncSource, timeVar,
                   BlockedClient, History, OpCount, SnapshotTable>> 
                                   
ServerPutReply_wake ==
    /\ \E c \in Client:
        /\ BlockedThread[c] /=  Nil
        /\ BlockedThread[c].type = "write"
        /\ IF BlockedThread[c].wc = "num" \* w:num
            THEN LET replicatedServers == ReplicatedServers(State[BlockedThread[c].s], BlockedThread[c].ot)
                 IN  Cardinality(replicatedServers) >= BlockedThread[c].numnode
           ELSE ~ HLCLt(Cp[BlockedThread[c].s], BlockedThread[c].ot) \* w:majority
        /\ Messages' = LET newMsgs == [ type |-> "put_reply", dest |-> c, ot |-> BlockedThread[c].ot, ct |-> Ct[BlockedThread[c].s], 
                                        k |-> BlockedThread[c].k, v |-> BlockedThread[c].v ]
                       IN  Messages \cup {newMsgs}   
        /\ BlockedThread' =  [ BlockedThread EXCEPT ![c] = Nil ] \* remove blocked state     
    /\ UNCHANGED <<serverVars, History, OpCount, BlockedClient, SnapshotTable>>                   
    
ServerGetReply_sleep ==
    /\ \E s \in Server, m \in Messages:
       /\ m.type = "get"
       /\ m.dest = s
       /\ IF m.rc = "linearizable"
            THEN  /\ s \in Primary
                  /\ UpdateAndTick(s, m.ct)  \* advance cluster time
                  /\ Oplog' = LET entry == [k |-> Nil, v |-> Nil, ot |-> Ct'[s], term |-> CurrentTerm[s]]
                                  newLog == Append(Oplog[s], entry)
                              IN  [Oplog EXCEPT ![s] = newLog] 
                    \* append noop operation to oplog[s]
                  /\ Ot' = [ Ot EXCEPT ![s] =  Ct'[s] ] 
                    \* advance the last applied operation time Ot[s]
                  /\ State' = LET newState == GetNewState(s, s, Ot'[s].p, Ot'[s].l, CurrentTerm[s])      
                              IN  [State EXCEPT ![s] = newState]      \* update primary state
                  /\ BlockedThread' = [BlockedThread EXCEPT ![m.c] = 
                                       [type |-> "read", rc |-> m.rc, ot|-> Ct'[s], s |-> s, 
                                       k |->m.k, v |-> Store[s][m.k] ] ] 
                     \* add the user thread to BlockedThread[c]                      
          ELSE /\ Ct' = [ Ct EXCEPT ![s] = HLCMax(Ct[s], m.ct) ] \*rc = local or major  
               /\ BlockedThread' = [BlockedThread EXCEPT ![m.c] = 
                            [type |-> "read", rc |-> m.rc, s |-> s, k |-> m.k, ot |-> m.ot]]
               /\ Oplog' = Oplog
               /\ Ot' = Ot
               /\ State' = State
       /\ Messages' = Messages \ {m}
    /\ UNCHANGED <<electionVars, Cp, CurrentTerm, messageVar, SyncSource, Store, timeVar,
                   BlockedClient, History, OpCount, SnapshotTable>>  

ServerGetReply_wake == 
    /\ \E c \in Client:
       /\ BlockedThread[c] /= Nil
       /\ BlockedThread[c].type = "read"
       /\ IF BlockedThread[c].rc = "linearizable"
            THEN /\ ~ HLCLt(Cp[BlockedThread[c].s], BlockedThread[c].ot) \* wait until cp[s] >= target ot 
                 /\ Messages' = LET m == [type |-> "get_reply", dest |-> c, k |-> BlockedThread[c].k, 
                                    v |-> BlockedThread[c].v, ct |-> Ct[BlockedThread[c].s], ot |-> BlockedThread[c].ot ]
                                IN  Messages \cup {m}
          ELSE /\ ~ HLCLt(Ot[BlockedThread[c].s], BlockedThread[c].ot) \* wait until Ot[s] >= target ot  
               /\ IF BlockedThread[c].rc = "local"
                    THEN Messages' = LET m == [type |-> "get_reply", dest |-> c, k |-> BlockedThread[c].k, 
                                         v |-> Store[BlockedThread[c].s][BlockedThread[c].k], ct |-> Ct[BlockedThread[c].s], ot |-> Ot[BlockedThread[c].s] ]
                                     IN  Messages \cup {m}
                  ELSE Messages' = LET m == [type |-> "get_reply", dest |-> c, k |-> BlockedThread[c].k, 
                                       v |-> SelectSnapshot(SnapshotTable[BlockedThread[c].s], Cp[BlockedThread[c].s])[BlockedThread[c].k],
                                       ct |-> Ct[BlockedThread[c].s], ot |-> Cp[BlockedThread[c].s] ] \* rc = majority
                                   IN  Messages \cup {m}                   
       /\ BlockedThread' = [ BlockedThread EXCEPT ![c] = Nil ]               
    /\ UNCHANGED <<serverVars, History, OpCount, BlockedClient, SnapshotTable>>                    
                  
ServerPutAndGet == \/ ServerPutReply_sleep \/ ServerPutReply_wake      
                   \/ ServerGetReply_sleep \/ ServerGetReply_wake 

----------------------------------------------------------------------------- 
ClientPutRequest ==
    /\ \E k \in Key, v \in Value, c \in Client \ BlockedClient, s \in Primary:
        /\ OpCount[c] /= 0
        /\ LET m == [ type |-> "put", dest |-> s, c |-> c, wc |-> WriteConcern, num |-> WriteNumber, k |-> k, v |-> v, ct |-> Ct[c] ] 
           IN  Messages' = Messages \cup {m}
        /\ IF WriteConcern = "zero" \*If w:0, decrease op count and record history
            THEN /\ OpCount' = [ OpCount EXCEPT ![c] = @-1 ]
                 /\ History' = [History EXCEPT ![c] = Append(@, [ op |-> "put", ts |-> Ot[c], k |-> k, v |-> v])]
                 /\ BlockedClient' = BlockedClient
           ELSE /\ BlockedClient' = BlockedClient \cup {c} \*Else wait for server reply
                /\ OpCount' = OpCount
                /\ History' = History   
    /\ UNCHANGED <<serverVars, BlockedThread, History, OpCount, SnapshotTable>>               

ClientPutResponse ==  
    /\ \E c \in Client, m \in Messages:
       /\ OpCount[c] /= 0
       /\ m.type = "put_reply"
       /\ m.dest = c
       /\ Ct' = [ Ct EXCEPT ![c] = HLCMax(@, m.ct) ]
       /\ Ot' = [ Ot EXCEPT ![c] = HLCMax(@, m.ot) ]
       /\ History' = [ History EXCEPT ![c] = Append (@, [ op |-> "put", 
                       ts |-> m.ot, k |-> m.k, v |-> m.v]) ]
       /\ Messages' = Messages \ {m}
       /\ BlockedClient' = BlockedClient \ {c}
       /\ OpCount' = [ OpCount EXCEPT ![c] = @-1 ]                
    /\ UNCHANGED <<electionVars, storageVars, messageVar, SyncSource, State, Cp, CurrentTerm, SnapshotTable, timeVar, BlockedThread>>
    
ClientGetRequest ==
    /\ \E k \in Key, c \in Client \ BlockedClient: 
        /\ OpCount[c] /= 0
        /\ IF ReadConcern = "linearizable" \* In this case, read can only be sent to primary
           THEN \E s \in Primary:
                LET m == [ type |-> "get", dest |-> s, c |-> c, rc |-> ReadConcern, k |-> k, ct |-> Ct[c], ot |-> Ot[c]]
                IN  Messages' = Messages \cup {m}
           ELSE IF ReadPreference = "primary" \* rp can be only primary or secondary
                    THEN \E s \in Primary:
                        LET m == [ type |-> "get", dest |-> s, c |-> c, rc |-> ReadConcern, k |-> k, ct |-> Ct[c], ot |-> Ot[c]]
                        IN  Messages' = Messages \cup {m}
                ELSE \E s \in Secondary:
                     LET m == [ type |-> "get", dest |-> s, c |-> c, rc |-> ReadConcern, k |-> k, ct |-> Ct[c], ot |-> Ot[c]]
                     IN  Messages' = Messages \cup {m}
        /\ BlockedClient' = BlockedClient \cup {c}          
    /\ UNCHANGED <<serverVars, History, OpCount, BlockedThread, SnapshotTable>>       

ClientGetResponse ==  
    /\ \E c \in Client, m \in Messages:
       /\ OpCount[c] /= 0
       /\ m.type = "get_reply"
       /\ m.dest = c
       /\ Ct' = [ Ct EXCEPT ![c] = HLCMax(@, m.ct) ]
       /\ Ot' = [ Ot EXCEPT ![c] = HLCMax(@, m.ot) ]
       /\ Store' = [ Store EXCEPT ![c][m.k] = m.v ]
       /\ History' = [ History EXCEPT ![c] = Append (@, [ op |-> "get", 
                       ts |-> m.ot, k |-> m.k, v |-> m.v]) ]
       /\ Messages' = Messages \ {m}
       /\ BlockedClient' = BlockedClient \ {c}
       /\ OpCount' = [ OpCount EXCEPT ![c] = @-1 ]                
    /\ UNCHANGED <<electionVars, Oplog, messageVar, SyncSource, State, Cp, CurrentTerm, SnapshotTable, timeVar, BlockedThread>>
    
ClientPutAndGet == \/ ClientPutRequest \/ ClientPutResponse
                   \/ ClientGetRequest \/ ClientGetResponse  

----------------------------------------------------------------------------- 
\*Simulate the situation that the primary node crash and suddently back to the state in Cp[s]
PrimaryCrashAndBack ==
    /\ \E s \in Primary:
       /\ Len(Oplog[s]) > 2 \* there is sth in the log
       /\ HLCLt([p |-> 0, l |-> 0], Cp[s])
       /\ Ot' = [ Ot EXCEPT ![s] = Cp[s] ]
       /\ Ct' = [ Ct EXCEPT ![s] = Cp[s] ]
       /\ Store' = [ Store EXCEPT ![s] = SelectSnapshot(SnapshotTable[s], Cp[s])]
       /\ Oplog' = LET logTail == CHOOSE n \in 1..Len(Oplog[s]): Oplog[s][n].ot = Cp[s]
                   IN  SubSeq(Oplog, 1, logTail)
       /\ State' = LET newState == GetNewState(s, s, Ot'[s].p, Ot'[s].l, CurrentTerm[s])      
                   IN  [State EXCEPT ![s] = newState]      \* update primary state
    /\ UNCHANGED <<electionVars, ServerMsg, Pt, Cp, CurrentTerm, SyncSource, tunableVars>>

-----------------------------------------------------------------------------                 
\* Next state for all configurations
Next == \/ Replicate
        \/ AdvancePt
        \/ AdvanceCp
        \/ ServerTakeHeartbeat
        \/ ServerTakeUpdatePosition
        \/ ServerPutAndGet
        \/ ClientPutAndGet
        \/ NTPSync
        \/ PrimaryCrashAndBack
        \/ Snapshot
        
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
\* Last modified Mon Jun 13 15:19:31 CST 2022 by dh
\* Created Wed May 25 16:43:04 CST 2022 by dh

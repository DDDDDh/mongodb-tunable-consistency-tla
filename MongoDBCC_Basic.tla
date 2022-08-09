-------------------------- MODULE MongoDBCC_Basic --------------------------
\* Basic MongoDB causal consistency protocol in the failure-free deployment

EXTENDS Naturals, FiniteSets, Sequences, TLC, CMvSpec

\* constants and variables
CONSTANTS Client, Server,   \* the set of clients and servers
          Key, Value,       \* the set of keys and values
          Nil,              \* model value, place holder
          OpTimes,          \* op count at most
          PtStop            \* max physical time

VARIABLES Primary,          \* Primary node
          Secondary,        \* secondary nodes
          Oplog,            \* oplog[s]: oplog at server[s]
          Store,            \* store[s]: data stored at server[s]
          Ct,               \* Ct[s]: cluster time at node s
          Ot,               \* Ot[s]: the last applied operation time at server s
          ServerMsg,        \* ServerMsg[s]: the channel of heartbeat msgs at server s
          Pt,               \* Pt[s]: physical time at server s
          State,            \* State[s]: the latest Ot of all servers that server s knows   
          SyncSource,       \* SyncSource[s]: sync source of server node s
          BlockedClient,    \* Functional var: mark a blocked client before it receive reply from server
          BlockedThread,    \* Functional var: mark a blocked server thread before it can return to client
          History,          \* Client history to record operations
          Messages,         \* Message channels in the system
          OpCount           \* OpCount[c]: left op times at client c
          
-----------------------------------------------------------------------------          
\* group related vars to optimize code
electionVars == <<Primary, Secondary>>              \* vars that are related to election  
storageVars == <<Oplog, Store>>                     \* vars that are related to storage
messageVar == <<ServerMsg>>                         \* var that is related to message
servernodeVars == <<Ot, SyncSource>>                \* vars that each server node holds for itself
learnableVars == <<Ct, State>>                      \* vars that must learn from msgs
timeVar == <<Pt>>                                   \* var that is used for timing

serverVars == <<electionVars, storageVars, messageVar, servernodeVars, learnableVars, timeVar>>
tunableVars == <<BlockedClient, BlockedThread, History, Messages, OpCount>>

vars == <<Primary, Secondary, Oplog, Store, Ct, Ot, messageVar, 
          Pt, State, SyncSource, BlockedClient, BlockedThread,
          History, Messages, OpCount>>
-----------------------------------------------------------------------------
ASSUME Cardinality(Client) >= 1  \* at least one clinet
ASSUME Cardinality(Server) >= 2  \* at least one primary and one secondary
ASSUME Cardinality(Key) >= 1     \* at least one object
ASSUME Cardinality(Value) >= 2   \* at least two values to update
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
          
\* Is node i ahead of node j
NotBehind(i, j) == Len(Oplog[i]) >= Len(Oplog[j])                           

IsMajority(servers) == Cardinality(servers) * 2 > Cardinality(Server)
                                      
\* Return the maximum value from a set, or undefined if the set is empty.
MaxVal(s) == CHOOSE x \in s : \A y \in s : x >= y        
                
\* clock
MaxPt == LET x == CHOOSE s \in Server: \A s1 \in Server \ {s}:
                            Pt[s] >= Pt[s1] 
         IN Pt[x]      
                            
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
    LET msg == [ type|-> "heartbeat", s |-> s, aot |-> Ot[s], ct |-> Ct[s]]
    IN ServerMsg' = [x \in Server |-> IF x = s THEN ServerMsg[x]
                                               ELSE Append(ServerMsg[x], msg)]                                                                                   

\* Can node i sync from node j? Since basic is failure free case, we can only compare the log length
CanSyncFrom(i, j) == Len(Oplog[i]) < Len(Oplog[j])
   
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
        
QuorumAgree(states) == 
    LET quorums == {Q \in Quorum :
                    \* Make sure all nodes in quorum have actually applied some entries.
                    \/ \A s \in Q : states[s].p > 0
                    \/ /\ \A s \in Q : states[s].p = 0
                       /\ \A s \in Q : states[s].l > 0}
    IN quorums   

\* Helper function to compute new state for state view of d at s by np and nl
GetNewState(s, d, np, nl) == 
    LET newSubState == [p |-> np, l |-> nl] 
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
InitState == State = [ s \in Server |-> [ s0 \in Server |-> [ p |-> 0, l |-> 0] ] ] 
InitSyncSource == SyncSource = [ s \in Server |-> Nil]    
InitBlockedClient == BlockedClient = {}
InitBlockedThread == BlockedThread = [ c \in Client |-> Nil ]
InitHistory == History = [ c \in Client |-> <<>> ]
InitMessages == Messages = {}
InitOpCount == OpCount = [ c \in Client |-> OpTimes ]                                                                  

Init == 
    /\ InitPrimary /\ InitSecondary /\ InitOplog /\ InitStore /\ InitCt 
    /\ InitOt /\ InitPt /\ InitServerMsg /\ InitState
    /\ InitSyncSource /\ InitBlockedClient /\ InitBlockedThread
    /\ InitHistory /\ InitMessages /\ InitOpCount
    
\* Next State Actions  
\* Replication Protocol: possible actions  
-----------------------------------------------------------------------------                                                           
\* Todo: Stepdown when receiving a higher term heartbeat                            

\*注意：heartbeat没有更新oplog，没有更新Ot，也没有更新store状态                                                                                                                                                                                                       
ServerTakeHeartbeat ==
    /\ \E s \in Server:
        /\ Len(ServerMsg[s]) /= 0  \* message channel is not empty
        /\ ServerMsg[s][1].type = "heartbeat"
        /\ Ct' = [ Ct EXCEPT ![s] = HLCMax(Ct[s], ServerMsg[s][1].ct) ]          
        /\ State' = LET newState == GetNewState(s, ServerMsg[s][1].s, ServerMsg[s][1].aot.p, ServerMsg[s][1].aot.l)
                    IN  [State EXCEPT ![s] = newState]
       /\ ServerMsg' = [ ServerMsg EXCEPT ![s] = Tail(@) ]       
    /\ UNCHANGED <<electionVars, storageVars, servernodeVars, timeVar, tunableVars>>

\*UpdatePosition is a special type of heartbeat
ServerTakeUpdatePosition == 
    /\ \E s \in Server:
        /\ Len(ServerMsg[s]) /= 0  \* message channel is not empty
        /\ ServerMsg[s][1].type = "update_position"
        /\ Ct' = [ Ct EXCEPT ![s] = HLCMax(Ct[s], ServerMsg[s][1].ct) ] \* update ct accordingly
        /\ State' = LET newState == GetNewState(s, ServerMsg[s][1].s, ServerMsg[s][1].aot.p, ServerMsg[s][1].aot.l)
                    IN  [State EXCEPT ![s] = newState]             
        /\ ServerMsg' = LET newServerMsg == [ServerMsg EXCEPT ![s] = Tail(@)]
                       IN  ( LET  appendMsg == [ type |-> "update_position", s |-> ServerMsg[s][1].s, aot |-> ServerMsg[s][1].aot, 
                                                ct |-> ServerMsg[s][1].ct ]
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
        /\ State' = 
            LET newStatei == [p |-> Ot'[i].p, l |-> Ot'[i].l]
                newStatej == [p |-> Ot[j].p, l |-> Ot[j].l]
            IN LET SubHbState == State[i]
                   hb == [ SubHbState EXCEPT ![i] = newStatei ] \* update i's self state (used in mcp computation
                   hb1 == [hb EXCEPT ![j] = newStatej ] \* update j's state i knows 
               IN [ State EXCEPT ![i] = hb1]            
        /\ LET msg == [ type |-> "update_position", s |-> i, aot |-> Ot'[i], ct |-> Ct'[i]]
           IN ServerMsg' = [ ServerMsg EXCEPT ![j] = Append(ServerMsg[j], msg) ]
        /\ SyncSource' = [SyncSource EXCEPT ![i] = j] 
    /\ UNCHANGED <<electionVars, timeVar, tunableVars>>        
       
----------------------------------------------------------------------------- 
ServerPutReply ==
    /\ \E s \in Primary, m \in Messages:
       /\ m.type = "put"
       /\ m.dest = s
       /\ UpdateAndTick(s, m.ct)
       /\ Ot' = [ Ot EXCEPT ![s] = Ct'[s] ]
       /\ Store' = [ Store EXCEPT ![s][m.k] = m.v ] 
       /\ Oplog' = LET entry == [ k|-> m.k, v |-> m.v, ot |-> Ot'[s]]
                        newLog == Append(Oplog[s], entry)
                   IN  [ Oplog EXCEPT ![s] = newLog ]
       /\ State' = LET newState == GetNewState(s, s, Ot'[s].p, Ot'[s].l) 
                   IN  [State EXCEPT ![s] = newState]              
       /\ Messages' = LET newMsgs == Messages \ {m}
                          newM == [type |-> "put_reply", dest |-> m.c, ot |-> Ot'[s], ct |-> Ct'[s], k |-> m.k, v |-> m.v]
                      IN  newMsgs \cup {newM}
    /\ UNCHANGED <<electionVars, messageVar, SyncSource, timeVar, BlockedClient, BlockedThread, History, OpCount>>                      
    
ServerGetReply_sleep ==
    /\ \E s \in Server, m \in Messages:
       /\ m.type = "get"
       /\ m.dest = s
       /\ Ct' = [ Ct EXCEPT ![s] = HLCMax(Ct[s], m.ct)]
       /\ BlockedThread' = [BlockedThread EXCEPT ![m.c] = [type |-> "read", s |-> s, k |-> m.k, ot |-> m.ot]]
       /\ Messages' = Messages \ {m}
    /\ UNCHANGED <<electionVars, storageVars, messageVar, servernodeVars, State, timeVar, BlockedClient, History, OpCount>>  

ServerGetReply_wake == 
    /\ \E c \in Client:
       /\ BlockedThread[c] /= Nil
       /\ BlockedThread[c].type = "read"
       /\ ~ HLCLt(Ot[BlockedThread[c].s], BlockedThread[c].ot) \* wait until
       /\ Messages' = LET m == [type |-> "get_reply", dest |-> c, k |-> BlockedThread[c].k, 
                                v |-> Store[BlockedThread[c].s][BlockedThread[c].k], 
                                ct |-> Ct[BlockedThread[c].s], ot |-> Ot[BlockedThread[c].s]]
                      IN  Messages \cup {m}
       /\ BlockedThread' = [ BlockedThread EXCEPT ![c] = Nil ]               
    /\UNCHANGED <<electionVars, storageVars, messageVar, servernodeVars, learnableVars, timeVar,
                  BlockedClient, History, OpCount>>    
                  
ServerPutAndGet == \/ ServerPutReply      
                   \/ ServerGetReply_sleep \/ ServerGetReply_wake 

----------------------------------------------------------------------------- 
ClientPutRequest ==
    /\ \E k \in Key, v \in Value, c \in Client \ BlockedClient, s \in Primary:
        /\ OpCount[c] /= 0
        /\ LET m == [ type |-> "put", dest |-> s, c |-> c, k |-> k, v |-> v, ct |-> Ct[c] ] 
           IN  Messages' = Messages \cup {m}
        /\ BlockedClient' = BlockedClient \cup {c}
    /\ UNCHANGED <<serverVars, BlockedThread, History, OpCount>>       

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
    /\ UNCHANGED <<electionVars, storageVars, messageVar, SyncSource, State, timeVar, BlockedThread>>
    
 ClientGetRequest ==
    /\ \E k \in Key, c \in Client \ BlockedClient, s \in Server:
        /\ OpCount[c] /= 0
        /\ LET m == [ type |-> "get", dest |-> s, c |-> c, k |-> k, ct |-> Ct[c], ot |-> Ot[c]]
           IN  Messages' = Messages \cup {m}
        /\ BlockedClient' = BlockedClient \cup {c}              
    /\ UNCHANGED <<serverVars, BlockedThread, History, OpCount>>
    
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
    /\ UNCHANGED <<electionVars, Oplog, messageVar, SyncSource, State, timeVar, BlockedThread>>
    
ClientPutAndGet == \/ ClientPutRequest \/ ClientPutResponse
                   \/ ClientGetRequest \/ ClientGetResponse  

-----------------------------------------------------------------------------                   
\* Next state for all configurations
Next == \/ Replicate
        \/ AdvancePt
        \/ ServerTakeHeartbeat
        \/ ServerTakeUpdatePosition
        \/ ServerPutAndGet
        \/ ClientPutAndGet
        \/ NTPSync
        
Spec == Init /\ [][Next]_vars      
-----------------------------------------------------------------------------
\* Causal Specifications
MonotonicRead == \A c \in Client: \A i,j \in DOMAIN History[c]:
                    /\ i<j 
                    /\ History[c][i].type = "get"
                    /\ History[c][j].type = "get"
                    => ~ HLCLt(History[c][j].ts, History[c][i].ts)
   
MonotonicWrite == \A c \in Client: \A i,j \in DOMAIN History[c]:
                    /\ i<j 
                    /\ History[c][i].type = "put"
                    /\ History[c][j].type = "put"
                    => ~ HLCLt(History[c][j].ts, History[c][i].ts)   
                    
ReadYourWrite == \A c \in Client: \A i,j \in DOMAIN History[c]:
                /\ i < j
                /\ History[c][i].type = "put"
                /\ History[c][j].type = "get"
                => ~ HLCLt(History[c][j].ts, History[c][i].ts)
                
WriteFollowRead == \A c \in Client: \A i,j \in DOMAIN History[c]:
                /\ i < j
                /\ History[c][i].type = "get"
                /\ History[c][j].type = "put"
                => ~ HLCLt(History[c][j].ts, History[c][i].ts)
                
\* CMv Specification (test)
CMvSatisification == 
                  \*/\ CMv(History, Client)
                  \/ \A c \in Client: Len(History[c]) <= 2
                  \/ \E c \in Client: Len(History[c]) > 7
                  \/ CMvDef(History, Client)
               
=============================================================================
\* Modification History
\* Last modified Mon Aug 08 18:11:20 CST 2022 by dh
\* Created Fri Aug 05 10:02:28 CST 2022 by dh

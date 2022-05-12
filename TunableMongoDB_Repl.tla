\* To fix: 消息存在延迟，比如说新的主当选之后收到旧主的heartbeat之类

------------------------ MODULE TunableMongoDB_Repl ------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* constants and variables
CONSTANTS Client, Server,   \* the set of clients and servers
          Key, Value,      \* the set of keys and values
          Nil,            \* model value, place holder
          PtStop          \* max physical time

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
          SyncSource      \* SyncSource[s]: sync source of server node s
          
-----------------------------------------------------------------------------          
\* group related vars to optimize code
electionVars == <<Primary, Secondary>>              \* vars that are related to election  
storageVars == <<Oplog, Store>>                     \* vars that are related to storage
messageVar == <<ServerMsg>>                         \* var that is related to message
serverVars == <<Ot, SyncSource>>                    \* vars that each server node holds for itself
learnableVars == <<Ct, State, Cp, CurrentTerm>>     \* vars that must learn from msgs
timeVar == <<Pt>>                                   \* var that is used for timing
functionalVar == <<ReadyToServe>>                   \* var that is used for some extra function

-----------------------------------------------------------------------------
ASSUME Cardinality(Client) >= 1  \* at least one clinet
ASSUME Cardinality(Server) >= 2  \* at least one primary and one secondary
ASSUME Cardinality(Key) >= 1     \* at least one object
ASSUME Cardinality(Value) >= 2   \* at least two values to update

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
Min(x, y) == IF x < y THEN x ELSE y
Max(x, y) == IF x > y THEN x ELSE y

vars == <<Primary, Secondary, Oplog, Store, Ct, Ot, messageVar, 
          Pt, Cp, State, CurrentTerm, ReadyToServe, SyncSource>>

RECURSIVE CreateState(_,_) \* init state
CreateState(len, seq) == 
    IF len = 0 THEN seq
    ELSE CreateState(len - 1, Append(seq, [ p |-> 0, l |-> 0 ]))

LogTerm(i, index) == IF index = 0 THEN 0 ELSE Oplog[i][index].term   
LastTerm(i) == CurrentTerm[i]                                       
                            
\* Is node i ahead of node j
NotBehind(i, j) == \/ LastTerm(i) > LastTerm(j)
                   \/ /\ LastTerm(i) = LastTerm(j)
                      /\ Len(Oplog[i]) >= Len(Oplog[j])                           

IsMajority(servers) == Cardinality(servers) * 2 > Cardinality(Server)
                                      
\* Return the maximum value from a set, or undefined if the set is empty.
MaxVal(s) == CHOOSE x \in s : \A y \in s : x >= y        
HLCMinSet(s) == CHOOSE x \in s: \A y \in s: ~HLCLt(y, x)                    

\* clock

MaxPt == LET x == CHOOSE s \in Server: \A s1 \in Server \ {s}:
                            Pt[s] >= Pt[s1] 
         IN Pt[x]      
                            
Tick(s) == Ct' = IF Ct[s].p >= Pt[s] 
                    THEN [ Ct EXCEPT ![s] = [ p |-> @.p, l |-> @.l+1] ]
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
                     /\ 
                        \/ Len(Oplog[i]) > Len(Oplog[j])
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
                                              [ p |-> 0, l |-> 0, term |-> 0] ] ] 
InitCurrentTerm == CurrentTerm = [s \in Server |-> 0] 
InitReadyToServe == ReadyToServe = 0
InitSyncSource == SyncSource = [ s \in Server |-> Nil]                                                                              

Init == 
    /\ InitPrimary /\ InitSecondary /\ InitOplog /\ InitStore /\ InitCt 
    /\ InitOt /\ InitPt /\ InitCp 
    /\ InitServerMsg 
    /\ InitState /\ InitCurrentTerm /\ InitReadyToServe
    /\ InitSyncSource
    
\* Next State Actions  
\* Replication Protocol: possible actions  
-----------------------------------------------------------------------------                                           
TurnOnReadyToServe ==
    /\ ReadyToServe = 0
    /\ \E s \in Primary:
        /\ CurrentTerm' = [CurrentTerm EXCEPT ![s] = CurrentTerm[s] + 1]
\*        /\ CurrentTerm' = [s \in Server |-> 1]
        /\ ReadyToServe' = ReadyToServe + 1
    /\ UNCHANGED<<electionVars, storageVars, serverVars, Ct, messageVar, timeVar, Cp, State>> 

Stepdown == 
    /\ ReadyToServe > 0
    /\ \E s \in Primary:
        /\ Primary' = Primary \ {s}
        /\ Secondary' = Secondary \cup {s}
    /\ UNCHANGED <<storageVars, serverVars, Ct, messageVar, timeVar, Cp, State, CurrentTerm, functionalVar>>
                            
\* Todo: Stepdown when receiving a higher term heartbeat                            

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
    /\ UNCHANGED <<storageVars, Ct, Ot, messageVar, timeVar, Cp, State, functionalVar>> 
            
AdvanceCp ==
    /\ ReadyToServe > 0
    /\ \E s \in Primary:
        LET newCp == 
            LET quorumAgree == QuorumAgreeInSameTerm(State[s]) 
            IN  IF Cardinality(quorumAgree) > 0 
                    THEN LET QuorumSet == CHOOSE i \in quorumAgree: TRUE
                             serverInQuorum == CHOOSE j \in QuorumSet: TRUE
                             termOfQuorum == State[s][serverInQuorum].term 
                             StateSet == {[p |-> State[s][j].p, l |-> State[s][j].l]: j \in QuorumSet}
                             newCommitPoint == HLCMinSet(StateSet)
                             oldCommitPoint == [p |-> Cp[s].p, l |-> Cp[s].l]
                             \* newCp must be greater than current Cp for primary to advance it
                         IN IF termOfQuorum = CurrentTerm[s] /\ HLCLt(oldCommitPoint, newCommitPoint)
                                THEN [p |-> newCommitPoint.p, l |-> newCommitPoint.l, term |-> termOfQuorum]
                            ELSE Cp[s]
                ELSE Cp[s]
        IN Cp' = [ Cp EXCEPT ![s] = newCp]
    /\ UNCHANGED <<electionVars, storageVars, serverVars, Ct, messageVar, timeVar, State, CurrentTerm, functionalVar>>                                
           
\*注意：heartbeat没有更新oplog，没有更新Ot，也没有更新store状态                                                                                                                                                                                                       
ServerTakeHeartbeat ==
    /\ ReadyToServe > 0
    /\ \E s \in Server:
        /\ Len(ServerMsg[s]) /= 0  \* message channel is not empty
        /\ ServerMsg[s][1].type = "heartbeat"
        /\ CurrentTerm[s] = ServerMsg[s][1].term
        /\ Ct' = [ Ct EXCEPT ![s] = HLCMax(Ct[s], ServerMsg[s][1].ct) ]
        /\ State' = 
            LET newState == [
                    p |-> ServerMsg[s][1].aot.p,
                    l |-> ServerMsg[s][1].aot.l,
                    term |-> ServerMsg[s][1].term
                ]
            IN LET SubHbState == State[s]
                   hb == [ SubHbState EXCEPT ![ServerMsg[s][1].s] = newState ]
               IN [ State EXCEPT ![s] = hb]
        /\ Cp' = LET newcp ==
                 \* primary node: compute new mcp
                    IF s \in Primary THEN 
                        LET quorumAgree == QuorumAgreeInSameTerm(State[s]) IN
                            IF Cardinality(quorumAgree) > 0 
                                THEN LET QuorumSet == CHOOSE i \in quorumAgree: TRUE
                                         serverInQuorum == CHOOSE j \in QuorumSet: TRUE
                                         termOfQuorum == State[s][serverInQuorum].term 
                                         StateSet == {[p |-> State[s][j].p, l |-> State[s][j].l]: j \in QuorumSet}
                                         newCommitPoint == HLCMinSet(StateSet)
                                     IN IF termOfQuorum = CurrentTerm[s]
                                            THEN  
                                                 [p |-> newCommitPoint.p, l |-> newCommitPoint.l, term |-> termOfQuorum]
                                         ELSE Cp[s]
                            ELSE Cp[s]
                 \* secondary node: update mcp   
                    ELSE IF LET msgCP == [ p |-> ServerMsg[s][1].cp.p, l |-> ServerMsg[s][1].cp.l ] IN
                            /\ ~ HLCLt(msgCP, Cp[s])
                            /\ ~ HLCLt(Ot[s], msgCP)
                            \* The term of cp must equal to the CurrentTerm of that node to advance it
                            /\ ServerMsg[s][1].term = CurrentTerm[s] 
                        THEN ServerMsg[s][1].cp
                        ELSE Cp[s]
                 IN [ Cp EXCEPT ![s] = newcp ]
       /\ ServerMsg' = [ ServerMsg EXCEPT ![s] = Tail(@) ]
       /\ CurrentTerm' = [CurrentTerm EXCEPT ![s] = Max(CurrentTerm[s], ServerMsg[s][1].term)]         
    /\ UNCHANGED <<Primary, electionVars, storageVars, serverVars, timeVar, functionalVar>>

ServerTakeUpdatePosition == 
    /\ ReadyToServe > 0
    /\ \E s \in Server:
        /\ Len(ServerMsg[s]) /= 0  \* message channel is not empty
        /\ ServerMsg[s][1].type = "update_position"
        /\ Ct' = [ Ct EXCEPT ![s] = HLCMax(Ct[s], ServerMsg[s][1].ct) ] \* update ct accordingly
        /\ State' = 
            LET newState == [
                    p |-> ServerMsg[s][1].aot.p,
                    l |-> ServerMsg[s][1].aot.l,
                    term |-> ServerMsg[s][1].term
                ]
            IN LET SubHbState == State[s]
                   hb == [ SubHbState EXCEPT ![ServerMsg[s][1].s] = newState ]
               IN [ State EXCEPT ![s] = hb]
        /\ Cp' = LET newcp ==
                 \* primary node: compute new mcp
                    IF s \in Primary THEN 
                        LET quorumAgree == QuorumAgreeInSameTerm(State[s]) IN
                            IF Cardinality(quorumAgree) > 0 
                                THEN LET QuorumSet == CHOOSE i \in quorumAgree: TRUE
                                         serverInQuorum == CHOOSE j \in QuorumSet: TRUE
                                         termOfQuorum == State[s][serverInQuorum].term 
                                         StateSet == {[p |-> State[s][j].p, l |-> State[s][j].l]: j \in QuorumSet}
                                         newCommitPoint == HLCMinSet(StateSet)
                                     IN IF termOfQuorum = CurrentTerm[s]
                                            THEN  
                                                 [p |-> newCommitPoint.p, l |-> newCommitPoint.l, term |-> termOfQuorum]
                                         ELSE Cp[s]
                            ELSE Cp[s]
                 \* secondary node: update mcp   
                    ELSE IF LET msgCP == [ p |-> ServerMsg[s][1].cp.p, l |-> ServerMsg[s][1].cp.l ] IN
                            /\ ~ HLCLt(msgCP, Cp[s])
                            /\ ~ HLCLt(Ot[s], msgCP)
                         THEN ServerMsg[s][1].cp
                         ELSE Cp[s]
                 IN [ Cp EXCEPT ![s] = newcp ]    
       /\ CurrentTerm' = [CurrentTerm EXCEPT ![s] = Max(CurrentTerm[s], ServerMsg[s][1].term)]             
       /\ ServerMsg' = LET newServerMsg == [ServerMsg EXCEPT ![s] = Tail(@)]
                       IN  ( LET  appendMsg == [ type |-> "update_position", s |-> ServerMsg[s][1].s, aot |-> ServerMsg[s][1].aot, 
                                          ct |-> ServerMsg[s][1].ct, cp |-> ServerMsg[s][1].cp, term |-> ServerMsg[s][1].term ]
                             IN ( LET newMsg == IF s \in Primary \/ SyncSource[s] = Nil
                                                    THEN newServerMsg \* If s is primary, accept the msg, else forward it to its sync source
                                                ELSE [newServerMsg EXCEPT ![SyncSource[s]] = Append(newServerMsg[SyncSource[s]], appendMsg)]
                                  IN newMsg))
    /\ UNCHANGED <<electionVars, storageVars, serverVars, timeVar, functionalVar>>

NTPSync == \* simplify NTP protocal
    /\ ReadyToServe > 0
    /\ Pt' = [ s \in Server |-> MaxPt ] 
    /\ UNCHANGED <<electionVars, storageVars, serverVars, learnableVars, messageVar, functionalVar>>

AdvancePt == 
    /\ ReadyToServe > 0
    /\ \E s \in Server:  
           /\ s \in Primary                    \* for simplicity
           /\ Pt[s] <= PtStop 
           /\ Pt' = [ Pt EXCEPT ![s] = @+1 ] \* advance physical time
           /\ BroadcastHeartbeat(s)          \* broadcast heartbeat periodly
    /\ UNCHANGED <<electionVars, storageVars, serverVars, learnableVars, functionalVar>>
               
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
        /\ State' = 
            LET newState == [
                    p |-> Ot[j].p,
                    l |-> Ot[j].l,
                    term |-> CurrentTerm[j]
                ]
            IN LET SubHbState == State[i]
                   hb == [ SubHbState EXCEPT ![j] = newState ]
               IN [ State EXCEPT ![i] = hb] \* update j's state i knows 
        /\ LET msg == [ type |-> "update_position", s |-> i, aot |-> Ot'[i], ct |-> Ct'[i], cp |-> Cp'[i], term |-> CurrentTerm'[i] ]
           IN ServerMsg' = [ ServerMsg EXCEPT ![j] = Append(ServerMsg[j], msg) ]
        /\ SyncSource' = [SyncSource EXCEPT ![i] = j] 
    /\ UNCHANGED <<electionVars, timeVar, functionalVar>>
                   
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
            LET newStatei == [
                    p |-> Ot'[i].p,
                    l |-> Ot'[j].l,
                    term |-> CurrentTerm'[i]
                ]
                newStatej == [
                    p |-> Ot[j].p,
                    l |-> Ot[j].l,
                    term |-> CurrentTerm[j]
                ]
            IN LET SubHbState == State[i]
                   hb == [ SubHbState EXCEPT ![i] = newStatei ] \* update i's self state (used in mcp computation
                   hb1 == [hb EXCEPT ![j] = newStatej ] \* update j's state i knows 
               IN [ State EXCEPT ![i] = hb1]
        /\ LET msg == [ type |-> "update_position", s |-> i, aot |-> Ot'[i], ct |-> Ct'[i], cp |-> Cp'[i], term |-> CurrentTerm'[i] ]
           IN ServerMsg' = [ ServerMsg EXCEPT ![j] = Append(ServerMsg[j], msg) ]
        /\ SyncSource' = [SyncSource EXCEPT ![i] = j]  
    /\ UNCHANGED <<electionVars, timeVar, functionalVar>> 
                    
ClientRequest ==
    /\ ReadyToServe > 0
    /\ \E s \in Server, k \in Key, v \in Value:
        /\ s \in Primary
        /\ Tick(s)
        /\ Ot' = [Ot EXCEPT ![s] = Ct'[s]]
        /\ Store' = [Store EXCEPT ![s][k] = v]
        /\ Oplog' = LET entry == [ k|-> k, v |-> v, ot |-> Ot'[s], term |-> CurrentTerm[s]]
                        newLog == Append(Oplog[s], entry)
                    IN  [ Oplog EXCEPT ![s] = newLog ]
        /\ State' =
            LET newState == [
                    p |-> Ot'[s].p,
                    l |-> Ot'[s].l,
                    term |-> CurrentTerm[s]
                ]
            IN LET SubHbState == State[s]
                   hb == [ SubHbState EXCEPT ![s] = newState ]
               IN [ State EXCEPT ![s] = hb] \* update i's state            
    /\ UNCHANGED <<electionVars, messageVar, timeVar, Cp, CurrentTerm, functionalVar, SyncSource>>       
                  
\* Next state for all configurations
Next == \/ Replicate
        \/ AdvancePt
        \/ AdvanceCp
        \/ ServerTakeHeartbeat
        \/ ServerTakeUpdatePosition
        \/ Stepdown
        \/ RollbackAndRecover
        \/ TurnOnReadyToServe
        \/ ElectPrimary
        \/ ClientRequest
        \/ NTPSync
        
Spec == Init /\ [][Next]_vars      
-----------------------------------------------------------------------------
\*Properties to check?

IsLogPrefix(i, j) ==
    /\ Len(Oplog[i]) <= Len(Oplog[j])
    /\ Oplog[i] = SubSeq(Oplog[j], 1, Len(Oplog[i]))

\* If two logs have the same last log entry term, then one is a prefix of the other (from Will 
LastTermsEquivalentImplyPrefixes == 
    \A i, j \in Server:
        LogTerm(i, Len(Oplog[i])) = LogTerm(j, Len(Oplog[j])) =>
        IsLogPrefix(i, j) \/ IsLogPrefix(j, i)    
\* Check whether terms are incremented monotoniclly (from Will
 TermsMonotonic ==
    [][\A s \in Server: CurrentTerm'[s] >= CurrentTerm[s]]_vars

\* Check the log in Primary node is append only (from Will
PrimaryAppendOnly == 
    [][\A s \in Server: s \in Primary => Len(Oplog'[s]) >= Len(Oplog[s])]_vars    
 
\* Never rollback oplog before common point (from Will & Raft Mongo
NeverRollbackCommonPoint ==
    \E i, j \in Server: CanRollback(i, j) =>
        LET commonPoint == RollbackCommonPoint(i, j)
            lastOplog == Oplog[i][commonPoint]
        IN HLCLt(Cp[i], lastOplog.ot)

\* Eventually log correctness (from Will
EventuallyLogsConverge == <>[][\A s, t \in Server: s /= t => Oplog[s] = Oplog[t]]_vars
EventuallyLogsNonEmpty == <>(\E s \in Server: Len(Oplog[s]) > 0)

\* (from RaftMongo
TwoPrimariesInSameTerm ==
    \E i, j \in Server:
        /\ i /= j
        /\CurrentTerm[i] = CurrentTerm[j]
        /\ i \in Primary
        /\ j \in Primary

NoTwoPrimariesInSameTerm == ~TwoPrimariesInSameTerm      

\* Check if there is any cycle of sync source path (from RaftMongo Sync
SyncSourceCycleTwoNode ==
    \E s, t \in Server:
        /\ s /= t
        /\ SyncSource[s] = t
        /\ SyncSource[t] = s

BoundedSeq(s, n) == [1..n -> s]

SyncSourcePaths ==
    { p \in BoundedSeq(Server, Cardinality(Server)):
        \A i \in 1..(Len(p)-1): SyncSource[p[i]] = p[i+1]}

SyncSourcePath(i, j) ==
    \E p \in SyncSourcePaths:
        /\ Len(p) > 1
        /\ p[1] = i
        /\ p[Len(p)] = j                

SyncSourceCycle ==
    \E s \in Server: SyncSourcePath(s, s)
    
NonTrivialSyncCycle == SyncSourceCycle /\ ~SyncSourceCycleTwoNode
NoNonTrivialSyncCycle == ~NonTrivialSyncCycle    
=============================================================================
\* Modification History
\* Last modified Thu May 12 16:06:07 CST 2022 by dh
\* Created Mon Apr 18 11:38:53 CST 2022 by dh

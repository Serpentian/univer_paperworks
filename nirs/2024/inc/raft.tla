--------------------------------- MODULE Raft ---------------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Server
CONSTANTS Value
CONSTANTS Follower, Candidate, Leader
CONSTANTS Nil
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse
CONSTANTS EqualTerm, LessOrEqualTerm
CONSTANTS MaxElections, MaxRestarts

----
\* Global variables
VARIABLE messages
VARIABLE acked
VARIABLE electionCtr, restartCtr
auxVars == <<acked, electionCtr, restartCtr>>
----
\* Per server variables (functions with domain Server).
VARIABLE currentTerm
VARIABLE state
VARIABLE votedFor
serverVars == <<currentTerm, state, votedFor>>

VARIABLE log
VARIABLE commitIndex
logVars == <<log, commitIndex>>

VARIABLE votesGranted
candidateVars == <<votesGranted>>

VARIABLE nextIndex
VARIABLE matchIndex
VARIABLE pendingResponse
leaderVars == <<nextIndex, matchIndex, pendingResponse>>
----
\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messages, serverVars, candidateVars, leaderVars, logVars, auxVars>>
view == <<messages, serverVars, candidateVars, leaderVars, logVars >>
symmServers == Permutations(Server)
symmValues == Permutations(Value)
----

\* Helpers
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

_SendNoRestriction(m) ==
    IF m \in DOMAIN messages
    THEN messages' = [messages EXCEPT ![m] = @ + 1]
    ELSE messages' = messages @@ (m :> 1)

_SendOnce(m) ==
    /\ m \notin DOMAIN messages
    /\ messages' = messages @@ (m :> 1)

Send(m) ==
    IF /\ m.mtype = AppendEntriesRequest
       /\ m.mentries = <<>>
    THEN _SendOnce(m)
    ELSE _SendNoRestriction(m)

SendMultipleOnce(msgs) ==
    /\ \A m \in msgs : m \notin DOMAIN messages
    /\ messages' = messages @@ [msg \in msgs |-> 1]

Duplicate(m) ==
    /\ m \in DOMAIN messages
    /\ messages' = [messages EXCEPT ![m] = @ + 1]

Discard(m) ==
    /\ m \in DOMAIN messages
    /\ messages[m] > 0 \* message must exist
    /\ messages' = [messages EXCEPT ![m] = @ - 1]

Reply(response, request) ==
    /\ messages[request] > 0 \* request must exist
    /\ \/ /\ response \notin DOMAIN messages \* response does not exist, so add it
          /\ messages' = [messages EXCEPT ![request] = @ - 1] @@ (response :> 1)
       \/ /\ response \in DOMAIN messages \* response was sent previously, so increment delivery counter
          /\ messages' = [messages EXCEPT ![request] = @ - 1,
                                          ![response] = @ + 1]

ReceivableMessage(m, mtype, term_match) ==
    /\ messages[m] > 0
    /\ m.mtype = mtype
    /\ \/ /\ term_match = EqualTerm
          /\ m.mterm = currentTerm[m.mdest]
       \/ /\ term_match = LessOrEqualTerm
          /\ m.mterm <= currentTerm[m.mdest]

Min(s) == CHOOSE x \in s : \A y \in s : x <= y
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

----
\* Define initial values for all variables
InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state       = [i \in Server |-> Follower]
                  /\ votedFor    = [i \in Server |-> Nil]
InitCandidateVars == votesGranted   = [i \in Server |-> {}]
InitLeaderVars == /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
                  /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
InitLogVars == /\ log             = [i \in Server |-> << >>]
               /\ commitIndex     = [i \in Server |-> 0]
               /\ pendingResponse = [i \in Server |-> [j \in Server |-> FALSE]]
InitAuxVars == /\ electionCtr = 0
               /\ restartCtr = 0
               /\ acked = [v \in Value |-> Nil]

Init == /\ messages = [m \in {} |-> 0]
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars
        /\ InitAuxVars

----
\* Define state transitions
Restart(i) ==
    /\ restartCtr < MaxRestarts
    /\ state'           = [state EXCEPT ![i] = Follower]
    /\ votesGranted'    = [votesGranted EXCEPT ![i] = {}]
    /\ nextIndex'       = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'      = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ pendingResponse' = [pendingResponse EXCEPT ![i] = [j \in Server |-> FALSE]]
    /\ commitIndex'     = [commitIndex EXCEPT ![i] = 0]
    /\ restartCtr'      = restartCtr + 1
    /\ UNCHANGED <<messages, currentTerm, votedFor, log, acked, electionCtr>>

RequestVote(i) ==
    /\ electionCtr < MaxElections
    /\ state[i] \in {Follower, Candidate}
    /\ state' = [state EXCEPT ![i] = Candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i] \* votes for itself
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {i}] \* votes for itself
    /\ electionCtr' = electionCtr + 1
    /\ SendMultipleOnce(
           {[mtype         |-> RequestVoteRequest,
             mterm         |-> currentTerm[i] + 1,
             mlastLogTerm  |-> LastTerm(log[i]),
             mlastLogIndex |-> Len(log[i]),
             msource       |-> i,
             mdest         |-> j] : j \in Server \ {i}})
    /\ UNCHANGED <<acked, leaderVars, logVars, restartCtr>>

AppendEntries(i, j) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ pendingResponse[i][j] = FALSE \* not already waiting for a response
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           prevLogTerm == IF prevLogIndex > 0 THEN
                              log[i][prevLogIndex].term
                          ELSE
                              0
           \* Send up to 1 entry, constrained by the end of the log.
           lastEntry == Min({Len(log[i]), nextIndex[i][j]})
           entries == SubSeq(log[i], nextIndex[i][j], lastEntry)
       IN
          /\ pendingResponse' = [pendingResponse EXCEPT ![i][j] = TRUE]
          /\ Send([mtype          |-> AppendEntriesRequest,
                   mterm          |-> currentTerm[i],
                   mprevLogIndex  |-> prevLogIndex,
                   mprevLogTerm   |-> prevLogTerm,
                   mentries       |-> entries,
                   mcommitIndex   |-> Min({commitIndex[i], lastEntry}),
                   msource        |-> i,
                   mdest          |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, nextIndex, matchIndex, logVars, auxVars>>

BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] =
                         [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] =
                         [j \in Server |-> 0]]
    /\ pendingResponse' = [pendingResponse EXCEPT ![i] =
                                [j \in Server |-> FALSE]]
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars,
                   auxVars, logVars>>

AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET \* The set of servers that agree up through index.
           Agree(index) == {i} \cup {k \in Server :
                                         /\ matchIndex[i][k] >= index }
           \* The maximum indexes for which a quorum agrees
           agreeIndexes == {index \in 1..Len(log[i]) :
                                Agree(index) \in Quorum}
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
              THEN
                  Max(agreeIndexes)
              ELSE
                  commitIndex[i]
       IN
          /\ commitIndex[i] < newCommitIndex \* only enabled if it actually advances
          /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
          /\ acked' = [v \in Value |->
                        IF acked[v] = FALSE
                        THEN v \in { log[i][index].value : index \in commitIndex[i]+1..newCommitIndex }
                        ELSE acked[v]]
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log,
                   pendingResponse, electionCtr, restartCtr>>

UpdateTerm ==
    \E m \in DOMAIN messages :
        /\ m.mterm > currentTerm[m.mdest]
        /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
        /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
        /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
           \* messages is unchanged so m can be processed further.
        /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>

HandleRequestVoteRequest ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
               logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                        \/ /\ m.mlastLogTerm = LastTerm(log[i])
                           /\ m.mlastLogIndex >= Len(log[i])
               grant == /\ m.mterm = currentTerm[i]
                        /\ logOk
                        /\ votedFor[i] \in {Nil, j}
            IN /\ m.mterm <= currentTerm[i]
               /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
                  \/ ~grant /\ UNCHANGED votedFor
               /\ Reply([mtype        |-> RequestVoteResponse,
                         mterm        |-> currentTerm[i],
                         mvoteGranted |-> grant,
                         msource      |-> i,
                         mdest        |-> j],
                         m)
               /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars,
                              logVars, auxVars>>

HandleRequestVoteResponse ==
    \E m \in DOMAIN messages :
        \* This tallies votes even when the current state is not Candidate, but
        \* they won't be looked at, so it doesn't matter.
        /\ ReceivableMessage(m, RequestVoteResponse, EqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
           IN
              /\ \/ /\ m.mvoteGranted
                    /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                              votesGranted[i] \cup {j}]
                 \/ /\ ~m.mvoteGranted
                    /\ UNCHANGED <<votesGranted>>
              /\ Discard(m)
              /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                             auxVars>>
LogOk(i, m) ==
    \/ m.mprevLogIndex = 0
    \/ /\ m.mprevLogIndex > 0
       /\ m.mprevLogIndex <= Len(log[i])
       /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term

RejectAppendEntriesRequest ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, AppendEntriesRequest, LessOrEqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
               logOk == LogOk(i, m)
           IN  /\ \/ m.mterm < currentTerm[i]
                  \/ /\ m.mterm = currentTerm[i]
                     /\ state[i] = Follower
                     /\ \lnot logOk
               /\ Reply([mtype           |-> AppendEntriesResponse,
                         mterm           |-> currentTerm[i],
                         msuccess        |-> FALSE,
                         mmatchIndex     |-> 0,
                         msource         |-> i,
                         mdest           |-> j],
                         m)
               /\ UNCHANGED <<state, candidateVars, leaderVars, serverVars,
                              logVars, auxVars>>

CanAppend(m, i) ==
    /\ m.mentries /= << >>
    /\ Len(log[i]) = m.mprevLogIndex

NeedsTruncation(m, i, index) ==
   \/ /\ m.mentries /= <<>>
      /\ Len(log[i]) >= index
   \/ /\ m.mentries = <<>>
      /\ Len(log[i]) > m.mprevLogIndex

TruncateLog(m, i) ==
    [index \in 1..m.mprevLogIndex |-> log[i][index]]

AcceptAppendEntriesRequest ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, AppendEntriesRequest, EqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
               logOk == LogOk(i, m)
               index == m.mprevLogIndex + 1
           IN
              /\ state[i] \in { Follower, Candidate }
              /\ logOk
              /\ LET new_log == CASE CanAppend(m, i) ->
                                        [log EXCEPT ![i] = Append(log[i], m.mentries[1])]
                                  [] NeedsTruncation(m, i , index) /\ m.mentries # <<>> ->
                                        [log EXCEPT ![i] = Append(TruncateLog(m, i), m.mentries[1])]
                                  [] NeedsTruncation(m, i , index) /\ m.mentries = <<>> ->
                                        [log EXCEPT ![i] = TruncateLog(m, i)]
                                  [] OTHER -> log
                 IN
                    /\ state' = [state EXCEPT ![i] = Follower]
                    /\ commitIndex' = [commitIndex EXCEPT ![i] =
                                              m.mcommitIndex]
                    /\ log' = new_log
                    /\ Reply([mtype           |-> AppendEntriesResponse,
                              mterm           |-> currentTerm[i],
                              msuccess        |-> TRUE,
                              mmatchIndex     |-> m.mprevLogIndex +
                                                    Len(m.mentries),
                              msource         |-> i,
                              mdest           |-> j],
                              m)
                    /\ UNCHANGED <<candidateVars, leaderVars, votedFor, currentTerm,
                                   auxVars>>

HandleAppendEntriesResponse ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, AppendEntriesResponse, EqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
           IN
              /\ \/ /\ m.msuccess \* successful
                    /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = m.mmatchIndex + 1]
                    /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
                 \/ /\ \lnot m.msuccess \* not successful
                    /\ nextIndex' = [nextIndex EXCEPT ![i][j] =
                                         Max({nextIndex[i][j] - 1, 1})]
                    /\ UNCHANGED <<matchIndex>>
              /\ pendingResponse' = [pendingResponse EXCEPT ![i][j] = FALSE]
              /\ Discard(m)
              /\ UNCHANGED <<serverVars, candidateVars, logVars, auxVars>>

----
\* Defines how the variables may transition.
Next ==
        \/ \E i \in Server : Restart(i)
        \/ \E i \in Server : RequestVote(i)
        \/ \E i \in Server : BecomeLeader(i)
        \/ \E i \in Server : AdvanceCommitIndex(i)
        \/ \E i,j \in Server : AppendEntries(i, j)
        \/ UpdateTerm
        \/ HandleRequestVoteRequest
        \/ HandleRequestVoteResponse
        \/ RejectAppendEntriesRequest
        \/ AcceptAppendEntriesRequest
        \/ HandleAppendEntriesResponse

NoStuttering ==
    WF_vars(Next)

Spec == Init /\ [][Next]_vars

LivenessSpec == Init /\ [][Next]_vars /\ NoStuttering

\* INVARIANTS -------------------------
MinCommitIndex(s1, s2) ==
    IF commitIndex[s1] < commitIndex[s2]
    THEN commitIndex[s1]
    ELSE commitIndex[s2]

NoLogDivergence ==
    \A s1, s2 \in Server :
        IF s1 = s2
        THEN TRUE
        ELSE
            LET lowest_common_ci == MinCommitIndex(s1, s2)
            IN IF lowest_common_ci > 0
               THEN \A index \in 1..lowest_common_ci : log[s1][index] = log[s2][index]
               ELSE TRUE

LeaderHasAllAckedValues ==
    \* for every acknowledged value
    \A v \in Value :
        IF acked[v] = TRUE
        THEN
            \* there does not exist a server that
            ~\E i \in Server :
                \* is a leader
                /\ state[i] = Leader
                \* and which is the newest leader (aka not stale)
                /\ ~\E l \in Server :
                    /\ l # i
                    /\ currentTerm[l] > currentTerm[i]
                \* and that is missing the value
                /\ ~\E index \in DOMAIN log[i] :
                    log[i][index].value = v
        ELSE TRUE

===============================================================================

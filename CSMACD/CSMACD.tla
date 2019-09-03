----------------------------- MODULE CSMACD ------------------------------------
EXTENDS Integers
CONSTANT Terminals, WaitTime
ASSUME WaitTime \subseteq (Nat \ {0})
VARIABLES bus, term, timers, now

vars == <<bus, term>>
--------------------------------------------------------------------------------
Ts == INSTANCE Timers

TypeInv ==
    /\ bus \in {"free", "busy", "collision", "done"}
    /\ term \in [Terminals -> [id : Nat, status : {"off", "waiting", "sending"}]]

Init ==
    /\ Ts!Init
    /\ bus = "free"
    /\ term \in [Terminals -> [id : Nat, status : {"off", "waiting", "sending"}]]
    /\ \A t \in Terminals : term[t].status = "off"
    /\ \A t1 \in Terminals : (\A t2 \in (Terminals \ {t1}) : term[t1].id # term[t2].id)

Collision == \E t1 \in Terminals : term[t1].status = "sending"
             /\ (\E t2 \in (Terminals \ {t1}) : term[t2].status = "sending")

--------------------------------------------------------------------------------

FreeSend(t) ==
    /\ bus = "free"
    /\ term[t].status = "off"
    /\ term' = [term EXCEPT ![t] = [id |-> @.id, status |-> "sending"]]
    /\ UNCHANGED <<bus, timers, now>>

BusySend(t) ==
    /\ bus # "free"
    /\ term[t].status = "off"
    /\ term' = [term EXCEPT ![t] = [id |-> @.id, status |-> "waiting"]]
    /\ \E lim \in WaitTime : Ts!Set(term[t].id, lim)
    /\ UNCHANGED <<bus, now>>

Send(t) == FreeSend(t) \/ BusySend(t)

AbortSend(t) ==
    /\ bus = "collision"
    /\ term[t].status = "sending"
    /\ term' = [term EXCEPT ![t] = [id |-> @.id, status |-> "waiting"]]
    /\ \E lim \in WaitTime : Ts!Set(term[t].id, lim)
    /\ UNCHANGED <<bus, now>>

FinishSend(t) ==
    /\ bus = "done"
    /\ term[t].status = "sending"
    /\ term' = [term EXCEPT ![t] = [id |-> @.id, status |-> "off"]]
    /\ UNCHANGED <<bus, timers, now>>

Wait(t) ==
    /\ term[t] = "waiting"
    /\ Ts!Start(term[t].id)
    /\ UNCHANGED<<bus, term, now>>

FinishWaitFree(t) ==
    /\ Ts!Timeout(term[t].id)
    /\ bus = "free"
    /\ term' = [term EXCEPT ![t] = [id |-> @.id, status |-> "sending"]]
    /\ UNCHANGED <<bus, now>>

FinishWaitBusy(t) ==
    /\ Ts!Timeout(term[t].id)
    /\ bus # "free"
    /\ \E lim \in WaitTime : Ts!Set(term[t].id, lim)
    /\ UNCHANGED <<bus, term, now>>

FinishWait(t) == FinishWaitFree(t) \/ FinishWaitBusy(t)

TermAction(t) == Send(t) \/ FinishSend(t) \/ AbortSend(t) \/ Wait(t) \/ FinishWait(t)

DetectFree ==
    /\ bus # "free"
    /\ \A t \in Terminals : term[t].status # "sending"
    /\ bus' = "free"
    /\ UNCHANGED <<timers, term, now>>

DetectBusy ==
    /\ bus # "busy"
    /\ ~Collision
    /\ \E t \in Terminals : term[t].status = "sending"
    /\ bus' = "busy"
    /\ UNCHANGED <<timers, term, now>>

DetectCollision ==
    /\ bus # "collision"
    /\ Collision
    /\ bus' = "collision"
    /\ UNCHANGED <<timers, term, now>>

DetectDone ==
    /\ bus = "busy"
    /\ ~Collision
    /\ bus' = "done"
    /\ UNCHANGED <<timers, term, now>>

Detection == DetectFree \/ DetectBusy \/ DetectCollision \/ DetectDone

Next == Detection \/ \E t \in Terminals : TermAction(t)

Liveness == WF_vars(DetectDone)

Spec == Init /\ [][Next]_vars /\ Liveness

--------------------------------------------------------------------------------
THEOREM Spec => Ts!Spec

THEOREM Spec => []TypeInv
================================================================================

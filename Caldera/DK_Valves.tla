---------------------------- MODULE DK_Valves ----------------------------------
VARIABLES red, entr, sal

vars == <<red, entr, sal>>
--------------------------------------------------------------------------------
TypeInv ==
    /\ {red, entr, sal} \subseteq {"open", "closed"}

Init ==
    /\ {red, entr, sal} \subseteq {"open", "closed"}
--------------------------------------------------------------------------------
changeRed(status) ==
    /\ red' = status
    /\ UNCHANGED <<entr, sal>>

changeEntr(status) ==
    /\ entr' = status
    /\ UNCHANGED <<red, sal>>

changeSal(status) ==
    /\ sal' = status
    /\ UNCHANGED <<entr, red>>

Next == \E st \in {"open", "closed"} :  \/ changeRed(st)
                                        \/ changeEntr(st)
                                        \/ changeSal(st)

Spec == Init /\ [][Next]_vars
--------------------------------------------------------------------------------
THEOREM Spec => []TypeInv
================================================================================

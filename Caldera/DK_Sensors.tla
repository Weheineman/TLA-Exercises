--------------------------- MODULE DK_Sensors ----------------------------------
EXTENDS Integers
VARIABLES temp, pres

vars == <<temp, pres>>
--------------------------------------------------------------------------------
TypeInv ==
    /\ {temp, pres} \subseteq Nat

Init ==
    /\ {temp, pres} \subseteq Nat
--------------------------------------------------------------------------------
SenseTemp(t) ==
    /\ temp' = t
    /\ UNCHANGED <<pres>>

SensePres(p) ==
    /\ pres' = p
    /\ UNCHANGED <<temp>>

Next == \E x \in Nat : SenseTemp(x) \/ SensePres(x)

Spec == Init /\ [][Next]_vars
--------------------------------------------------------------------------------
THEOREM Spec => []TypeInv
================================================================================

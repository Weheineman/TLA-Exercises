--------------------------- MODULE DK_Burner -----------------------------------
EXTENDS Integers
VARIABLES burn

CONSTANTS minBurn, maxBurn
ASSUME /\ {minBurn, maxBurn} \subseteq Nat
       /\ minBurn <= maxBurn

vars == <<burn>>
--------------------------------------------------------------------------------
TypeInv ==
    /\ burn \in Nat

BurnInv ==
    /\ minBurn <= burn
    /\ maxBurn >= burn

Init ==
    /\ burn \in Nat
    /\ burn = minBurn
--------------------------------------------------------------------------------
IncreaseBurn == burn' = IF burn = maxBurn THEN maxBurn ELSE burn - 1

DecreaseBurn == burn' = IF burn = minBurn THEN minBurn ELSE burn - 1

Next == IncreaseBurn \/ DecreaseBurn

Spec == Init /\ [][Next]_vars
--------------------------------------------------------------------------------
THEOREM Spec => [](TypeInv /\ BurnInv)
================================================================================

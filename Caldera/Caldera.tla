----------------------------- MODULE Caldera -----------------------------------
EXTENDS Integers
CONSTANT minTemp, maxTemp, minPres, maxPres, minBurn, maxBurn
ASSUME
    /\ {minTemp, maxTemp, minPres, maxPres, minBurn, maxBurn} \subseteq Nat
    /\ minTemp <= maxTemp
    /\ minPres <= maxPres
    /\ minBurn <= maxBurn
VARIABLES temp, pres, red, entr, sal, burn

vars == <<temp, pres, red, entr, sal, burn>>
--------------------------------------------------------------------------------
Sens == INSTANCE DK_Sensors

Valv == INSTANCE DK_Valves

Burn == INSTANCE DK_Burner

TypeInv ==
    /\ Sens!TypeInv
    /\ Valv!TypeInv
    /\ Burn!TypeInv

Init ==
    /\ Sens!Init
    /\ Valv!Init
    /\ Burn!Init
--------------------------------------------------------------------------------
EnvironmentChange ==
    /\ Sens!Next
    /\ UNCHANGED <<red, entr, sal, burn>>

IncreasePressure ==
    /\ pres < minPres
    /\ Valv!changeRed("open")
    /\ Valv!changeEntr("open")
    /\ Valv!changeSal("close")
    /\ UNCHANGED <<temp, pres, burn>>

DecreasePressure ==
    /\ pres > maxPres
    /\ Valv!changeRed("close")
    /\ Valv!changeEntr("close")
    /\ Valv!changeSal("open")
    /\ UNCHANGED <<temp, pres, burn>>

IncreaseTemp ==
    /\ temp < minTemp
    /\ Burn!IncreaseBurn
    /\ UNCHANGED <<temp, pres, red, entr, sal>>

DecreaseTemp ==
    /\ temp > maxTemp
    /\ Burn!DecreaseBurn
    /\ UNCHANGED <<temp, pres, red, entr, sal>>

SysResponse ==  \/ IncreasePressure
                \/ DecreasePressure
                \/ IncreaseTemp
                \/ DecreaseTemp

Next == EnvironmentChange \/ SysResponse

Liveness == /\ WF_vars(IncreasePressure)
            /\ WF_vars(DecreasePressure)
            /\ WF_vars(IncreaseTemp)
            /\ WF_vars(DecreaseTemp)

Spec == Init /\ [][Next]_vars /\ Liveness
--------------------------------------------------------------------------------
THEOREM Spec => Sens!Spec

THEOREM Spec => Valv!Spec

THEOREM Spec => Burn!Spec

THEOREM Spec => []TypeInv
================================================================================

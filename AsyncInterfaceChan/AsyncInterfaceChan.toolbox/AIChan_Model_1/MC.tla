---- MODULE MC ----
EXTENDS AsyncInterfaceChan, TLC

\* INIT definition @modelBehaviorNoSpec:0
init_1428281497447138000 ==
FALSE/\oldack = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1428281497457139000 ==
FALSE/\oldack' = oldack
----
=============================================================================
\* Modification History
\* Created Sun Apr 05 20:51:37 EDT 2015 by midpeter444

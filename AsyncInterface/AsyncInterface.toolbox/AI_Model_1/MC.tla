---- MODULE MC ----
EXTENDS AsyncInterface, TLC

\* INIT definition @modelBehaviorNoSpec:0
init_1428261670838121000 ==
FALSE/\val = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1428261670848122000 ==
FALSE/\val' = val
----
=============================================================================
\* Modification History
\* Created Sun Apr 05 15:21:10 EDT 2015 by midpeter444

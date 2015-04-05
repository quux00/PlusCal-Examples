---- MODULE MC ----
EXTENDS HourClock, TLC

\* INIT definition @modelBehaviorNoSpec:0
init_142824570021766000 ==
FALSE/\hr = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_142824570022767000 ==
FALSE/\hr' = hr
----
=============================================================================
\* Modification History
\* Created Sun Apr 05 10:55:00 EDT 2015 by midpeter444

---- MODULE MC ----
EXTENDS wire, TLC

\* INIT definition @modelBehaviorNoSpec:0
init_166765025378713000 ==
FALSE/\people = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_166765025378714000 ==
FALSE/\people' = people
----
=============================================================================
\* Modification History
\* Created Sat Nov 05 13:10:53 CET 2022 by pwc

---- MODULE MC ----
EXTENDS wire, TLC

\* Constant expression definition @modelExpressionEval
const_expr_166765031664124000 == 
1 + 2
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_166765031664124000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_166765031664125000 ==
FALSE/\people = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_166765031664126000 ==
FALSE/\people' = people
----
=============================================================================
\* Modification History
\* Created Sat Nov 05 13:11:56 CET 2022 by pwc

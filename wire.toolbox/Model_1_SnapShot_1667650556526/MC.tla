---- MODULE MC ----
EXTENDS wire, TLC

\* Constant expression definition @modelExpressionEval
const_expr_166765055550854000 == 
1 \in 0..10
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_166765055550854000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_166765055550855000 ==
FALSE/\people = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_166765055550856000 ==
FALSE/\people' = people
----
=============================================================================
\* Modification History
\* Created Sat Nov 05 13:15:55 CET 2022 by pwc

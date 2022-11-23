---- MODULE MC ----
EXTENDS wire, TLC

\* Constant expression definition @modelExpressionEval
const_expr_166765119166766000 == 
{x \in 1..10: x % 2 = 0}
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_166765119166766000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_166765119166767000 ==
FALSE/\people = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_166765119166768000 ==
FALSE/\people' = people
----
=============================================================================
\* Modification History
\* Created Sat Nov 05 13:26:31 CET 2022 by pwc

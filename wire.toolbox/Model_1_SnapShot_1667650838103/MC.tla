---- MODULE MC ----
EXTENDS wire, TLC

\* Constant expression definition @modelExpressionEval
const_expr_166765083708657000 == 
1..2 \ 2..3
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_166765083708657000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_166765083708658000 ==
FALSE/\people = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_166765083708659000 ==
FALSE/\people' = people
----
=============================================================================
\* Modification History
\* Created Sat Nov 05 13:20:37 CET 2022 by pwc

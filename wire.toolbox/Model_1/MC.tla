---- MODULE MC ----
EXTENDS wire, TLC

\* Constant expression definition @modelExpressionEval
const_expr_16677260566352000 == 
{x * 2: x \in 1..10}
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_16677260566352000>>)
----

=============================================================================
\* Modification History
\* Created Sun Nov 06 10:14:16 CET 2022 by pwc

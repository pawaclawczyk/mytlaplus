----------------------------- MODULE telephone -----------------------------

EXTENDS Sequences

(*

--algorithm telephone

variable
    to_send = <<1, 2, 3>>,
    received = <<>>,
    in_transit = {};

begin
    \* why "/=" not "<"?
    while Len(received) /= 3 do

        \* send
        if to_send /= <<>> then
            in_transit := in_transit \cup {Head(to_send)};   
        end if;
        
        \* receive
        either
            with msg \in in_transit do
                received := received \cup {msg};
                in_transit := in_transit \ {msg};
            end with;
        or
            skip;
        end either;

    end while;
end algorithm;

*)
\* BEGIN TRANSLATION (chksum(pcal) = "88c90535" /\ chksum(tla) = "6582969c")
VARIABLES to_send, received, in_transit, pc

vars == << to_send, received, in_transit, pc >>

Init == (* Global variables *)
        /\ to_send = <<1, 2, 3>>
        /\ received = <<>>
        /\ in_transit = {}
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF Len(received) /= 3
               THEN /\ IF to_send /= <<>>
                          THEN /\ in_transit' = (in_transit \cup {Head(to_send)})
                          ELSE /\ TRUE
                               /\ UNCHANGED in_transit
                    /\ \/ /\ pc' = "Lbl_2"
                       \/ /\ TRUE
                          /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED in_transit
         /\ UNCHANGED << to_send, received >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ \E msg \in in_transit:
              /\ received' = (received \cup {msg})
              /\ in_transit' = in_transit \ {msg}
         /\ pc' = "Lbl_1"
         /\ UNCHANGED to_send

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sun Nov 20 11:03:42 CET 2022 by pwc
\* Created Sun Nov 20 10:55:32 CET 2022 by pwc

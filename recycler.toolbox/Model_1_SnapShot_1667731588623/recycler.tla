------------------------------ MODULE recycler ------------------------------
EXTENDS Integers, FiniteSets, Sequences
(*--algorithm recycler
variables
    capacity = [recycling |-> 1..10, trash |-> 1..10],
    bins = [recycling |-> {}, trash |-> {}],
    count = [recycling |-> 0, trash |-> 0],
    item = [type: {"recycling", "trash"}, size: 1..6],
    items \in item \X item \X item \X item,
    curr;
define
    NoOverflow == capacity.recycling >= 0 /\ capacity.trash >= 0
    ValidCount == Cardinality(bins.recycling) = count.recycling /\ Cardinality(bins.trash) = count.trash
end define;
macro add_item(type) begin
    bins[type] := bins[type] \cup {curr};
    count[type] := count[type] + 1;
    capacity[type] := capacity[type] - curr.size; 
end macro;
begin
    while items /= <<>> do
        curr := Head(items);
        items := Tail(items);
        if curr.type = "recycling" /\ curr.size <= capacity.recycling then
            add_item("recycling")
        elsif curr.size <= capacity.trash then
            add_item("trash")
        end if;
    end while;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "23b0f544" /\ chksum(tla) = "27098d9f")
CONSTANT defaultInitValue
VARIABLES capacity, bins, count, item, items, curr, pc

(* define statement *)
NoOverflow == capacity.recycling >= 0 /\ capacity.trash >= 0
ValidCount == Cardinality(bins.recycling) = count.recycling /\ Cardinality(bins.trash) = count.trash


vars == << capacity, bins, count, item, items, curr, pc >>

Init == (* Global variables *)
        /\ capacity = [recycling |-> 1..10, trash |-> 1..10]
        /\ bins = [recycling |-> {}, trash |-> {}]
        /\ count = [recycling |-> 0, trash |-> 0]
        /\ item = [type: {"recycling", "trash"}, size: 1..6]
        /\ items \in item \X item \X item \X item
        /\ curr = defaultInitValue
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF items /= <<>>
               THEN /\ curr' = Head(items)
                    /\ items' = Tail(items)
                    /\ IF curr'.type = "recycling" /\ curr'.size <= capacity.recycling
                          THEN /\ bins' = [bins EXCEPT !["recycling"] = bins["recycling"] \cup {curr'}]
                               /\ count' = [count EXCEPT !["recycling"] = count["recycling"] + 1]
                               /\ capacity' = [capacity EXCEPT !["recycling"] = capacity["recycling"] - curr'.size]
                          ELSE /\ IF curr'.size <= capacity.trash
                                     THEN /\ bins' = [bins EXCEPT !["trash"] = bins["trash"] \cup {curr'}]
                                          /\ count' = [count EXCEPT !["trash"] = count["trash"] + 1]
                                          /\ capacity' = [capacity EXCEPT !["trash"] = capacity["trash"] - curr'.size]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << capacity, bins, 
                                                          count >>
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << capacity, bins, count, items, curr >>
         /\ item' = item

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Sun Nov 06 11:46:20 CET 2022 by pwc
\* Created Sun Nov 06 10:15:04 CET 2022 by pwc

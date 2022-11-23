------------------------------ MODULE recycler ------------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

(*--algorithm recycler

variables
    capacity \in [recycle: 1..10, trash: 1..10],
    bins = [recycle |-> {}, trash |-> {}],
    count = [recycle |-> 0, trash |-> 0],
    item = [type: {"recycle", "trash"}, size: 1..6],
    items \in item \X item \X item \X item,
    curr;

define
    NoOverflow == capacity.recycle >= 0 /\ capacity.trash >= 0
    ValidCount == Cardinality(bins.recycle) = count.recycle /\ Cardinality(bins.trash) = count.trash
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
        if curr.type = "recycle" /\ curr.size <= capacity.recycle then
            add_item("recycle")
        elsif curr.size <= capacity.trash then
            add_item("trash")
        end if;
    end while;
    assert capacity.trash >= 0 /\ capacity.recycle >= 0;
    assert Cardinality(bins.trash) = count.trash;
    assert Cardinality(bins.recycle) = count.recycle;
end algorithm;*)

\* BEGIN TRANSLATION (chksum(pcal) = "92ad3bce" /\ chksum(tla) = "1fd9bd06")
CONSTANT defaultInitValue
VARIABLES capacity, bins, count, item, items, curr, pc

(* define statement *)
NoOverflow == capacity.recycle >= 0 /\ capacity.trash >= 0
ValidCount == Cardinality(bins.recycle) = count.recycle /\ Cardinality(bins.trash) = count.trash


vars == << capacity, bins, count, item, items, curr, pc >>

Init == (* Global variables *)
        /\ capacity \in [recycle: 1..10, trash: 1..10]
        /\ bins = [recycle |-> {}, trash |-> {}]
        /\ count = [recycle |-> 0, trash |-> 0]
        /\ item = [type: {"recycle", "trash"}, size: 1..6]
        /\ items \in item \X item \X item \X item
        /\ curr = defaultInitValue
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF items /= <<>>
               THEN /\ curr' = Head(items)
                    /\ items' = Tail(items)
                    /\ IF curr'.type = "recycle" /\ curr'.size <= capacity.recycle
                          THEN /\ bins' = [bins EXCEPT !["recycle"] = bins["recycle"] \cup {curr'}]
                               /\ count' = [count EXCEPT !["recycle"] = count["recycle"] + 1]
                               /\ capacity' = [capacity EXCEPT !["recycle"] = capacity["recycle"] - curr'.size]
                          ELSE /\ IF curr'.size <= capacity.trash
                                     THEN /\ bins' = [bins EXCEPT !["trash"] = bins["trash"] \cup {curr'}]
                                          /\ count' = [count EXCEPT !["trash"] = count["trash"] + 1]
                                          /\ capacity' = [capacity EXCEPT !["trash"] = capacity["trash"] - curr'.size]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << capacity, bins, 
                                                          count >>
                    /\ pc' = "Lbl_1"
               ELSE /\ Assert(capacity.trash >= 0 /\ capacity.recycle >= 0, 
                              "Failure of assertion at line 36, column 5.")
                    /\ Assert(Cardinality(bins.trash) = count.trash, 
                              "Failure of assertion at line 37, column 5.")
                    /\ Assert(Cardinality(bins.recycle) = count.recycle, 
                              "Failure of assertion at line 38, column 5.")
                    /\ pc' = "Done"
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
\* Last modified Sun Nov 20 10:27:07 CET 2022 by pwc
\* Created Sun Nov 06 10:15:04 CET 2022 by pwc

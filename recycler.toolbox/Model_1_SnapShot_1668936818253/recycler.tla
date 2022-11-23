------------------------------ MODULE recycler ------------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

(*--algorithm recycler

variables
    capacity \in [recycle: 1..10, trash: 1..10],
    bins = [recycle |-> <<>>, trash |-> <<>>],
    count = [recycle |-> 0, trash |-> 0],
    item = [type: {"recycle", "trash"}, size: 1..6],
    items \in item \X item \X item \X item,
    curr;

macro add_item(type) begin
    bins[type] := Append(bins[type], curr);
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
    assert Len(bins.trash) = count.trash;
    assert Len(bins.recycle) = count.recycle;
end algorithm;*)

\* BEGIN TRANSLATION (chksum(pcal) = "cc27664f" /\ chksum(tla) = "7d68b25a")
CONSTANT defaultInitValue
VARIABLES capacity, bins, count, item, items, curr, pc

vars == << capacity, bins, count, item, items, curr, pc >>

Init == (* Global variables *)
        /\ capacity \in [recycle: 1..10, trash: 1..10]
        /\ bins = [recycle |-> <<>>, trash |-> <<>>]
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
                          THEN /\ bins' = [bins EXCEPT !["recycle"] = Append(bins["recycle"], curr')]
                               /\ count' = [count EXCEPT !["recycle"] = count["recycle"] + 1]
                               /\ capacity' = [capacity EXCEPT !["recycle"] = capacity["recycle"] - curr'.size]
                          ELSE /\ IF curr'.size <= capacity.trash
                                     THEN /\ bins' = [bins EXCEPT !["trash"] = Append(bins["trash"], curr')]
                                          /\ count' = [count EXCEPT !["trash"] = count["trash"] + 1]
                                          /\ capacity' = [capacity EXCEPT !["trash"] = capacity["trash"] - curr'.size]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << capacity, bins, 
                                                          count >>
                    /\ pc' = "Lbl_1"
               ELSE /\ Assert(capacity.trash >= 0 /\ capacity.recycle >= 0, 
                              "Failure of assertion at line 31, column 5.")
                    /\ Assert(Len(bins.trash) = count.trash, 
                              "Failure of assertion at line 32, column 5.")
                    /\ Assert(Len(bins.recycle) = count.recycle, 
                              "Failure of assertion at line 33, column 5.")
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
\* Last modified Sun Nov 20 10:33:09 CET 2022 by pwc
\* Created Sun Nov 06 10:15:04 CET 2022 by pwc

From Temporal Require Import Section13.TemporalUnit.

Inductive Category := DATE | TIME.

(* Table 21 - Unused rows are not displayed *)
(*>> Value       | Category <<*)
(*>> YEAR        | DATE <<*)
(*>> MONTH       | DATE <<*)
(*>> WEEK        | DATE <<*)
(*>> DAY         | DATE <<*)
(*>> HOUR        | TIME <<*)
(*>> MINUTE      | TIME <<*)
(*>> SECOND      | TIME <<*)
(*>> MILLISECOND | TIME <<*)
(*>> MICROSECOND | TIME <<*)
(*>> NANOSECOND  | TIME <<*)

(* 13.22 TemporalUnitCategory *)
Definition TemporalUnitCategory (unit' : TemporalUnit) : Category :=
  (*>> 1. Return the value from the "Category" column of the row of Table 21 in which unit is in the "Value" column. <<*)
  match unit' with
  | YEAR => DATE
  | MONTH => DATE
  | WEEK => DATE
  | DAY => DATE
  | HOUR => TIME
  | MINUTE => TIME
  | SECOND => TIME
  | MILLISECOND => TIME
  | MICROSECOND => TIME
  | NANOSECOND => TIME
  end.

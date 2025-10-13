From Stdlib Require Import ZArith.
From Temporal Require Import
  Section13.RoundingMode
  Section13.TemporalUnit.
Open Scope Z.

(* Table 21 - Unused rows are not displayed *)
(*>> Value       | Maximum duration rounding increment <<*)
(*>> YEAR        | UNSET <<*)
(*>> MONTH       | UNSET <<*)
(*>> WEEK        | UNSET <<*)
(*>> DAY         | UNSET <<*)
(*>> HOUR        | 24 <<*)
(*>> MINUTE      | 60 <<*)
(*>> SECOND      | 60 <<*)
(*>> MILLISECOND | 1000 <<*)
(*>> MICROSECOND | 1000 <<*)
(*>> NANOSECOND  | 1000 <<*)

Inductive RoundingIncrement := UNSET | ValuedRoundingIncrement (roundingIncrement : Z).

(* 13.23 MaximumTemporalDurationRoundingIncrement *)
Definition MaximumTemporalDurationRoundingIncrement (unit' : TemporalUnit) : RoundingIncrement :=
  (*>> 1. Return the value from the "Maximum duration rounding increment" column of the row of Table 21 in which unit is in the "Value" column. <<*)
  match unit' with
  | YEAR => UNSET
  | MONTH => UNSET
  | WEEK => UNSET
  | DAY => UNSET
  | HOUR => ValuedRoundingIncrement 24
  | MINUTE => ValuedRoundingIncrement 60
  | SECOND => ValuedRoundingIncrement 60
  | MILLISECOND => ValuedRoundingIncrement 1000 
  | MICROSECOND => ValuedRoundingIncrement 1000
  | NANOSECOND => ValuedRoundingIncrement 1000
  end.

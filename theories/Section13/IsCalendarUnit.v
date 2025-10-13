From Temporal Require Import
  Section13.TemporalUnit
  Section13.TemporalUnitEqb.

(* 13.21 IsCalendarUnit *) 
Definition IsCalendarUnit (unit' : TemporalUnit) : bool :=
  (*>> 1. If unit is year, return true. <<*)
  if TemporalUnitEqb unit' YEAR then true
  (*>> 2. If unit is month, return true. <<*)
  else if TemporalUnitEqb unit' MONTH then true
  (*>> 3. If unit is week, return true. <<*)
  else if TemporalUnitEqb unit' WEEK then true
  (*>> 4. Return false. <<*)
  else false.

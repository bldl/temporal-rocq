From Temporal Require Import TemporalUnit.

Definition TemporalUnitEqb (u1 u2 : TemporalUnit) : bool :=
  match u1, u2 with
  | YEAR, YEAR => true
  | MONTH, MONTH => true
  | WEEK, WEEK => true
  | DAY, DAY => true
  | HOUR, HOUR => true
  | MINUTE, MINUTE => true
  | SECOND, SECOND => true
  | MILLISECOND, MILLISECOND => true
  | MICROSECOND, MICROSECOND => true
  | NANOSECOND, NANOSECOND => true
  | _, _ => false
  end.

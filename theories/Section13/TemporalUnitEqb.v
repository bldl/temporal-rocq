From Temporal Require Import TemporalUnit.

Definition TemporalUnitEqb (u1 u2 : TemporalUnit) : bool :=
  match u1, u2 with
  | YEAR, YEAR => true
  | YEAR, _ => false
  | MONTH, MONTH => true
  | MONTH, _ => false
  | WEEK, WEEK => true
  | WEEK, _ => false
  | DAY, DAY => true
  | DAY, _ => false
  | HOUR, HOUR => true
  | HOUR, _ => false
  | MINUTE, MINUTE => true
  | MINUTE, _ => false
  | SECOND, SECOND => true
  | SECOND, _ => false
  | MILLISECOND, MILLISECOND => true
  | MILLISECOND, _ => false
  | MICROSECOND, MICROSECOND => true
  | MICROSECOND, _ => false
  | NANOSECOND, NANOSECOND => true
  | NANOSECOND, _ => false
  end.

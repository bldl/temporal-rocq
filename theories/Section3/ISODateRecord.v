From Stdlib Require Import ZArith.
From Temporal Require Import Section3.IsValidISODate.
Open Scope Z.

(* 3.5.1 ISODateRecord *)
Record ISODateRecord : Type :=
  mkISODateRecord {
    (*>> Field Name | Value                                 | Meaning <<*)
    (*>> [[Year]]  | an integer                             | The year in the ISO 8601 calendar. <<*)
    year : Z;
    (*>> [[Month]] | an integer between 1 and 12, inclusive | The number of the month in the ISO 8601 calendar. <<*)
    month : Z;
    month_valid : 1 <= month <= 12;
    (*>> [[Day]]   | an integer between 1 and 31, inclusive | The number of the day of the month in the ISO 8601 calendar. <<*)
    day : Z;
    day_valid : 1 <= day <= 31;
  }.

(* This seems to be the case but the spec does not explicitly state it yet. *)
Theorem ISODateRecord_IsValidISODate :
  forall (date : ISODateRecord),
  IsValidISODate (year date) (month date) (day date) = true.
Admitted.

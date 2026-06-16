From Stdlib Require Import ZArith.
From Temporal Require Import Section3.IsValidISODate.
Open Scope Z.

(* 3.5.1 ISODateRecord *)
Record ISODateRecord : Type :=
  mkISODateRecord {
    (*>> Field Name | Value                                 | Meaning <<*)
    (*>> [[Year]]  | an integer                             | The year in the ISO 8601 calendar. <<*)
    Year : Z;
    (*>> [[Month]] | an integer between 1 and 12, inclusive | The number of the month in the ISO 8601 calendar. <<*)
    Month : Z;
    (*>> [[Day]]   | an integer between 1 and 31, inclusive | The number of the day of the month in the ISO 8601 calendar. <<*)
    Day : Z;

    month_valid : 1 <= Month <= 12;
    day_valid : 1 <= Day <= 31;
    is_valid_ISO_date: IsValidISODate Year Month Day = true;
  }.

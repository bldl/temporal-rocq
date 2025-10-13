From Stdlib Require Import ZArith.
Open Scope Z.

(* 9.5.1 ISO Year-Month Records *)
Record ISOYearMonthRecord := 
  mkISOYearMonthRecord {
    (*>> Field Name | Value                                  | Meaning <<*)
    (*>> [[Year]]   | an integer                             | The year in the ISO 8601 calendar. <<*)
    year_ym : Z;
    (*>> [[Month]]  | an integer between 1 and 12, inclusive | The number of the month in the ISO 8601 calendar. <<*)
    month_ym : Z;
    month_valid_ym : 1 <= month_ym <= 12;
  }.

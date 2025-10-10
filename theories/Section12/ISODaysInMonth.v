From Stdlib Require Import ZArith Lia.
From Temporal Require Import Basic Sec13Def.
Open Scope Z.

(* 12.3.17 ISODaysInMonth *)
(*>> The abstract operation ISODaysInMonth takes arguments year (an integer) and
     month (an integer in the inclusive interval from 1 to 12) and returns a
     positive integer. It returns the number of days in the given year and month
     in the ISO 8601 calendar. It performs the following steps when called: <<*)
Definition ISODaysInMonth (year month : Z) (h : 1 <= month <= 12) : Z.
  refine (
    match month as m return (month = m -> Z) with
    (*>> 1. If month is 1, 3, 5, 7, 8, 10, or 12, return 31. <<*)
    | 1 | 3 | 5 | 7 | 8 | 10 | 12 => fun _ => 31
    (*>> 2. If month is 4, 6, 9, or 11, return 30. <<*)
    | 4 | 6 | 9 | 11 => fun _ => 30
    | month => fun h =>
        (*>> 3. Assert: month = 2. <<*)
        assert month = 2 in
        (*>> 4. Return 28 + MathematicalInLeapYear(EpochTimeForYear(year)). <<*)
        28 + MathematicalInLeapYear (EpochTimeForYear year)
    end eq_refl
  ).

  (* Proof of the assert *)
  all: lia.
Defined.

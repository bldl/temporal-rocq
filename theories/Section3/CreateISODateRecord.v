From Stdlib Require Import ZArith.
From Temporal Require Import 
  Basic
  Section3.ISODateRecord
  Section3.IsValidISODate.
Open Scope Z.

(* 3.5.2 CreateISODateRecord *)
(*>> The abstract operation CreateISODateRecord takes arguments
     year (an integer), month (an integer between 1 and 12 inclusive), 
     and day (an integer between 1 and 31 inclusive) and returns an 
     ISO Date Record. <<*)
Program Definition CreateISODateRecord (year month day : Z)
  (month_valid : 1 <= month <= 12) (day_valid : 1 <= day <= 31)
  (is_valid : IsValidISODate year month day = true) : ISODateRecord :=
    (*>> 1. Assert: IsValidISODate(year, month, day) is true. <<*)
    assert IsValidISODate year month day = true in
    (*>> 2. Return ISO Date Record { [[Year]]: year, [[Month]]: month, [[Day]]: day }. <<*)
    mkISODateRecord year month month_valid day day_valid _.

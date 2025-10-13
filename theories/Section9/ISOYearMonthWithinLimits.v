From Stdlib Require Import ZArith.
From Temporal Require Import Section3.ISODateRecord.
Open Scope bool_scope.
Open Scope Z.

(* 9.5.3 ISOYearMonthWithinLimits *)
Definition ISOYearMonthWithinLimits (isoDate : ISODateRecord) : bool :=
  (*>> 1. If isoDate.[[Year]] < -271821 or isoDate.[[Year]] > 275760, then <<*)
  if (year isoDate <? -271821) || (year isoDate >? 275760)
    (*>> a. Return false. <<*)
    then false
  (*>> 2. If isoDate.[[Year]] = -271821 and isoDate.[[Month]] < 4, then <<*)
  else if (year isoDate =? -271821) && (month isoDate <? 4)
    (*>> a. Return false. <<*)
    then false
  (*>> 3. If isoDate.[[Year]] = 275760 and isoDate.[[Month]] > 9, then <<*)
  else if (year isoDate =? 275760) || (month isoDate >? 9)
    (*>> a. Return false. <<*)
    then false
  (*>> 4. Return true. <<*)
  else true.

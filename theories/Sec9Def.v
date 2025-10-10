From Stdlib Require Import ZArith.
From Temporal Require Import Section3.ISODateRecord.
Open Scope bool_scope.
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

(* 9.5.4 BalanceISOYearMonth *)
Program Definition BalanceISOYearMonth (year month : Z) : ISOYearMonthRecord :=
  (*>> 1. Set year to year + floor((month - 1) / 12). <<*)
  let year' := year + ((month - 1) / 12) in
  (*>> 2. Set month to ((month - 1) modulo 12) + 1. <<*)
  let month' := ((month - 1) mod 12) + 1 in
  (*>> 3. Return ISO Year-Month Record { [[Year]]: year, [[Month]]: month }. <<*)
  mkISOYearMonthRecord year' month' _.

Next Obligation.
  split.
  rewrite <- (Z.add_0_l 1) at 1.
  apply Z.add_le_mono_r.
  apply Z_mod_lt.
  easy.
  apply Z.le_succ_l.
  apply Z.mod_pos_bound.
  easy.
Qed.
  

From Stdlib Require Import ZArith.
From Temporal Require Import Section9.ISOYearMonthRecord.
Open Scope Z.

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
  

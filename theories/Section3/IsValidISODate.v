From Stdlib Require Import ZArith.
From Temporal Require Import Section12.ISODaysInMonth.
Open Scope bool_scope.
Open Scope Z.

(* 3.5.7 IsValidISODate *)
Definition IsValidISODate (year month day : Z) : bool.
  refine (
    match month ?= 1 as m_1, month ?= 12 as m_2
    return ((month ?= 1) = m_1 -> (month ?= 12) = m_2 -> bool)
    with
    (*>> 1. If month < 1 or month > 12, then <<*)
    | Lt, _ | _, Gt =>
      (*>> a. Return false. <<*)
      fun _ _ => false
    | _, _ => fun H0 H1 =>
      (*>> 2. Let daysInMonth be ISODaysInMonth(year, month). <<*)
      let daysInMonth := ISODaysInMonth year month _ in
      (*>> 3. If day < 1 or day > daysInMonth, then <<*)
      if (day <? 1) || (day >? daysInMonth) then
        (*>> a. Return false. <<*)
        false
      (*>> 4. Return true. <<*)
      else true
    end eq_refl eq_refl
  ).

  (* month = 1, month = 12 *)
  - rewrite Z.compare_eq_iff in H0.
    rewrite Z.compare_eq_iff in H1.
    rewrite H0 in H1.
    discriminate.
  
  (* month = 1, month < 12 *)
  - rewrite Z.compare_eq_iff in H0.
    rewrite H0.
    easy.
  
  (* month > 1, month = 12 *)
  - rewrite Z.compare_eq_iff in H1.
    rewrite H1.
    easy.
  
  (* month > 1, month < 12 *)
  - rewrite Z.compare_gt_iff in H0.
    rewrite Z.compare_lt_iff in H1.
    split.
    + apply Z.lt_le_incl.
      assumption.
    + apply Z.lt_le_incl.
      assumption.
Defined.

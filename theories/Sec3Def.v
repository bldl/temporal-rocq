From Stdlib Require Import Numbers.BinNums Program.Wf ZArith.
From Temporal Require Import Basic Sec12Def.
Open Scope bool_scope.
Open Scope Z.

(* 3.5.1 ISODateRecord *)
Record ISODateRecord : Type :=
  mkISODateRecord {
    (*>> Field Name | Value                                  | Meaning <<*)
    (*>> [[Year]]  | an integer                             | The year in the ISO 8601 calendar. <<*)
    year : Z;
    (*>> [[Month]] | an integer between 1 and 12, inclusive | The number of the month in the ISO 8601 calendar. <<*)
    month : Z;
    month_valid : 1 <= month <= 12;
    (*>> [[Day]]   | an integer between 1 and 31, inclusive | The number of the day of the month in the ISO 8601 calendar. <<*)
    day : Z;
    day_valid : 1 <= day <= 31;
  }.

(* 3.5.12 CompareISODate *)
Definition CompareISODate (isoDate1 isoDate2 : ISODateRecord) : Z :=
  (*>> 1. If isoDate1.[[Year]] > isoDate2.[[Year]], return 1. <<*)
  if (year isoDate1) >? (year isoDate2) then 1
  (*>> 2. If isoDate1.[[Year]] < isoDate2.[[Year]], return -1. <<*)
  else if (year isoDate1) <? (year isoDate2) then -1
  (*>> 3. If isoDate1.[[Month]] > isoDate2.[[Month]], return 1. <<*)
  else if (month isoDate1) >? (month isoDate2) then 1
  (*>> 4. If isoDate1.[[Month]] < isoDate2.[[Month]], return -1. <<*)
  else if (month isoDate1) <? (month isoDate2) then -1
  (*>> 5. If isoDate1.[[Day]] > isoDate2.[[Day]], return 1. <<*)
  else if (day isoDate1) >? (day isoDate2) then 1
  (*>> 6. If isoDate1.[[Day]] < isoDate2.[[Day]], return -1. <<*)
  else if (day isoDate1) <? (day isoDate2) then -1
  (*>> 7. Return 0. <<*)
  else 0.

(* 3.5.7 IsValidISODate *)
Program Definition IsValidISODate (year month day : Z) : bool :=
  match month ?= 1, month ?= 12 with
  (*>> 1. If month < 1 or month > 12, then <<*)
  | Lt, _ | _, Gt =>
    (*>> a. Return false. <<*)
    false
  | _, _ =>
    (*>> 2. Let daysInMonth be ISODaysInMonth(year, month). <<*)
    let daysInMonth := ISODaysInMonth year month _ in
    (*>> 3. If day < 1 or day > daysInMonth, then <<*)
    if (day <? 1) || (day >? daysInMonth) then
      (*>> a. Return false. <<*)
      false
    (*>> 4. Return true. <<*)
    else true
  end.

Next Obligation.
Proof.
  split.

  (* 1 <= month0 *)
  specialize (H0 Lt).
  rewrite (eq_sym_iff Lt (month0 ?= 1)) in H0.
  rewrite (eq_sym_iff Lt (month0 ?= 12)) in H0.
  rewrite Z.compare_lt_iff in H0.
  rewrite Z.compare_lt_iff in H0.
  specialize (Decidable.not_and _ _ (Z.lt_decidable _ _) H0).
  intro.
  destruct H1.

  (* ~ (month0 < 1) |- 1 <= month0 *)
  rewrite Z.nlt_ge in H1.
  assumption.

  (* ~ (month0 < 12) |- 1 <= month0 *)
  rewrite <- Z.le_ngt in H1.
  refine (Z.le_trans 1 12 month0 _ H1).
  easy.

  (* month0 <= 12 *)
  specialize (H Gt).
  rewrite (eq_sym_iff Gt (month0 ?= 1)) in H.
  rewrite (eq_sym_iff Gt (month0 ?= 12)) in H.
  rewrite Z.compare_gt_iff in H.
  rewrite Z.compare_gt_iff in H.
  specialize (Decidable.not_and _ _ (Z.lt_decidable _ _) H).
  intro.
  destruct H1.

  (* ~ (1 < month0) |- month0 <= 12 *)
  rewrite <- Z.le_ngt in H1.
  refine (Z.le_trans month0 1 12 H1 _).
  easy.

  (* ~ (12 < month0) |- month0 <= 12 *)
  rewrite Z.nlt_ge in H1.
  assumption.
Qed.

Solve Obligations with easy.

(* 3.5.2 CreateISODateRecord *)
Program Definition CreateISODateRecord
  (year month day : Z)
  (month_valid : 1 <= month <= 12) (day_valid : 1 <= day <= 31)
  (is_valid : IsValidISODate year month day = true) : ISODateRecord :=
    (*>> 1. Assert: IsValidISODate(year, month, day) is true. <<*)
    assert IsValidISODate year month day = true in
    (*>> 2. Return ISO Date Record { [[Year]]: year, [[Month]]: month, [[Day]]: day }. <<*)
    mkISODateRecord year month month_valid day day_valid.

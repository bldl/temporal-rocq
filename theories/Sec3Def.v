From Stdlib Require Import Numbers.BinNums Program.Wf ZArith.
From Temporal Require Import Basic Sec12Def Sec12Thm.
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

Inductive Overflow := CONSTRAIN | REJECT.
Definition eq (a b : Overflow) : bool := 
  match a, b with
  | CONSTRAIN, CONSTRAIN => true
  | REJECT, REJECT => true
  | _, _ => false
  end.

(* 3.5.6 RegulateISODate *)
Program Definition RegulateISODate (year month day : Z) (overflow : Overflow) : Completion ISODateRecord :=
  (*>> 1. If overflow is constrain, then <<*)
  if eq overflow CONSTRAIN then
    (*>> a. Set month to the result of clamping month between 1 and 12. <<*)
    let month' := Clamp 1 12 month _ in
    (*>> b. Let daysInMonth be ISODaysInMonth(year, month). <<*)
    let daysInMonth := ISODaysInMonth year month' _ in
    (*>> c. Set day to the result of clamping day between 1 and daysInMonth. <<*)
    let day' := Clamp 1 daysInMonth day _ in
    Normal (CreateISODateRecord year month' day' _ _ _)
  (*>> 2. Else, <<*)
  else
    (*>> a. Assert: overflow is reject. <<*)
    assert overflow = REJECT in
    (*>> b. If IsValidISODate(year, month, day) is false, throw a RangeError exception. <<*)
    if Bool.eqb (IsValidISODate year month day) false
      then Throw RangeError
      (*>> 3. Return CreateISODateRecord(year, month, day). <<*)
      else Normal (CreateISODateRecord year month day _ _ _).

Next Obligation. Proof. apply clamp_between_lower_and_upper. Qed.
Next Obligation. Proof. apply ISODaysInMonth_at_least_1. Qed.
Next Obligation. Proof. apply clamp_between_lower_and_upper. Qed.

Next Obligation.
Proof.
  split.
  - apply clamp_between_lower_and_upper.
  - apply clamp_upper_le.
    apply ISODaysInMonth_range.
Qed.


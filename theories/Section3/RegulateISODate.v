From Stdlib Require Import
  Program.Equality
  ZArith.
From Temporal Require Import
  Basic
  Section3.CreateISODateRecord
  Section3.ISODateRecord
  Section3.IsValidISODate
  Section12.ISODaysInMonth
  Section12.Sec12Thm
  StringUtil.
Open Scope Z.

Inductive Overflow := CONSTRAIN | REJECT.
Definition eq (a b : Overflow) : bool := 
  match a, b with
  | CONSTRAIN, CONSTRAIN => true
  | REJECT, REJECT => true
  | _, _ => false
  end.

(* 3.5.6 RegulateISODate *)
Program Definition RegulateISODate (year month day : Z) (overflow : Overflow) : Completion ISODateRecord :=
  match overflow with
  (*>> 1. If overflow is constrain, then <<*)
  | CONSTRAIN =>
      (*>> a. Set month to the result of clamping month between 1 and 12. <<*)
      let month' := Clamp 1 12 month _ in
      (*>> b. Let daysInMonth be ISODaysInMonth(year, month). <<*)
      let daysInMonth := ISODaysInMonth year month' _ in
      (*>> c. Set day to the result of clamping day between 1 and daysInMonth. <<*)
      let day' := Clamp 1 daysInMonth day _ in
      Normal (CreateISODateRecord year month' day' _ _ _)
  (*>> 2. Else, <<*)
  | _ => 
      (*>> a. Assert: overflow is reject. <<*)
      assert overflow = REJECT in
      match IsValidISODate year month day with
      (*>> b. If IsValidISODate(year, month, day) is false, throw a RangeError exception. <<*)
      | false => Throw RangeError
      (*>> 3. Return CreateISODateRecord(year, month, day). <<*)
      | true => Normal (CreateISODateRecord year month day _ _ _)
      end
  end.

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

Next Obligation.
Proof.
  refine (IsValidISODate_month_day_range year _ _ _ _).
  apply clamp_between_lower_and_upper.
Qed.

Next Obligation.
Proof.
  destruct overflow.
  - contradiction.
  - reflexivity.
Qed.

Next Obligation.
Proof.
  symmetry in Heq_anonymous.
  destruct (IsValidISODate_true year month day Heq_anonymous).
  assumption.
Qed.

Next Obligation.
Proof.
  symmetry in Heq_anonymous.
  destruct (IsValidISODate_true year month day Heq_anonymous).
  destruct H.
  split.
  - assumption.
  - apply Z.le_trans with (m := ISODaysInMonth year month x).
    + assumption.
    + apply ISODaysInMonth_range.
Qed.

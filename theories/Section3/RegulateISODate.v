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


(** States that if we know that a month has a valid range, and the day is valid
    for that month, then `IsValidISODate` returns true. *)
Lemma IsValidISODate_month_day_range :
  forall year month day month_valid,
  1 <= day <= ISODaysInMonth year month month_valid ->
  IsValidISODate year month day = true.
Proof.
  intros.
  unfold IsValidISODate.
  generalize (Z.compare_eq_iff month 1).
  generalize (Z.compare_gt_iff month 1).
  generalize (Z.compare_eq_iff month 12).
  generalize (Z.compare_lt_iff month 12).
  destruct (month ?= 1); destruct (month ?= 12).

  (* contradiction *)
  - intros.
    assert (h : 12 = 1). { rewrite <- (proj1 i0 eq_refl). apply i2. easy. }
    discriminate.

  (* 1 <= day <= ISODaysInMonth year month month_valid *)
  - intros.
    destruct H.
    rewrite Z.gtb_ltb.
    rewrite (proj2 (Z.ltb_ge day 1)).
    + simpl.
      rewrite (proj2 (Z.ltb_ge _ day)).
      * reflexivity.
      * assumption.
    + assumption.

  (* contradiction *)
  - intros.
    assert (h : Gt = Lt). { apply i. rewrite (proj1 i2 eq_refl). easy. }
    discriminate.

  (* contradiction *)
  - intros.
    rewrite (proj1 i0 eq_refl) in i1.
    assert (h : Lt = Gt). { apply i1. easy. }
    discriminate.

  (* contradiction *)
  - intros.
    assert (month_lt_eq : 1 < month \/ 1 = month). {
      apply Z.le_lteq.
      apply month_valid.
    }
    destruct month_lt_eq.
    + assert (h : Lt = Gt). { apply i1. assumption. }
      discriminate.
    + assert (h : Lt = Eq). { apply i2. symmetry. assumption. }
      discriminate.

  (* contradiction *)
  - intros.
    assert (month_lt_eq : month < 12 \/ month = 12). {
      apply Z.le_lteq.
      apply month_valid.
    }
    destruct month_lt_eq.
    + assert (h : Gt = Lt). { apply i. assumption. }
      discriminate.
    + assert (h : Gt = Eq). { apply i0. assumption. }
      discriminate.

  (* 1 <= day <= ISODaysInMonth year month month_valid *)
  - intros.
    destruct H.
    rewrite Z.gtb_ltb.
    rewrite (proj2 (Z.ltb_ge day 1)).
    + simpl.
      rewrite (proj2 (Z.ltb_ge _ day)).
      * reflexivity.
      * assumption.
    + assumption.

  (* 1 <= day <= ISODaysInMonth year month month_valid *)
  - intros.
    destruct H.
    rewrite (proj2 (Z.ltb_ge day 1)).
    + simpl.
      rewrite Z.gtb_ltb.
      rewrite (proj2 (Z.ltb_ge _ day)).
      * reflexivity.
      * assumption.
    + assumption.

  (* contradiction *)
  - intros.
    assert (month_lt_eq : month < 12 \/ month = 12). {
      apply Z.le_lteq.
      apply month_valid.
    }
    destruct month_lt_eq.
    + assert (h : Gt = Lt). { apply i. assumption. }
      discriminate.
    + assert (h : Gt = Eq). { apply i0. assumption. }
      discriminate.
Qed.

(* States that if `IsValidISODate year month day` returns true,
    then `1 <= month 12` and `1 <= day <= ISODaysInMonth year month _` *)
Lemma IsValidISODate_true :
  forall year month day, IsValidISODate year month day = true ->
  exists (month_valid : 1 <= month <= 12),
  1 <= day <= ISODaysInMonth year month month_valid.
Proof.
  intro year.
  intro month.
  intro day.

  unfold IsValidISODate.
  generalize (Z.compare_eq_iff month 1).
  generalize (Z.compare_gt_iff month 1).
  generalize (Z.compare_eq_iff month 12).
  generalize (Z.compare_lt_iff month 12).
  destruct (month ?= 1); destruct (month ?= 12).

  (* contradiction *)
  - intros.
    assert (h : month = 12). { apply i0. reflexivity. }
    assert (h1 : 12 = 1). { rewrite <- h. apply i2. reflexivity. }
    discriminate.

  (* month = 1 *)
  - intros.
    assert (h : month = 1). { apply i2. reflexivity. }
    rewrite h.
    refine (ex_intro _ _ _).
    unfold ISODaysInMonth.
    destruct (day <? 1) eqn: day_lt.
    + simpl in H.
      discriminate.
    + split.
      * rewrite Z.ltb_ge in day_lt.
        assumption.
      * simpl in H.
        destruct (day >? _) eqn: day_gt.
        discriminate.
        rewrite Z.gtb_ltb in day_gt.
        rewrite Z.ltb_ge in day_gt.
        refine (Z.le_trans _ _ 31 _ _).
        exact day_gt.
        apply ISODaysInMonth_range.

  - intros. discriminate. (* contradiction *)
  - intros. discriminate. (* contradiction *)
  - intros. discriminate. (* contradiction *)
  - intros. discriminate. (* contradiction *)

  (* month = 12 *)
  - intros.
    assert (h : month = 12). { apply i0. reflexivity. }
    rewrite h.
    refine (ex_intro _ _ _).
    unfold ISODaysInMonth.
    destruct (day <? 1) eqn: day_lt.
    + simpl in H.
      discriminate.
    + split.
      * rewrite Z.ltb_ge in day_lt.
        assumption.
      * simpl in H.
        destruct (day >? _) eqn: day_gt.
        discriminate.
        rewrite Z.gtb_ltb in day_gt.
        rewrite Z.ltb_ge in day_gt.
        refine (Z.le_trans _ _ 31 _ _).
        exact day_gt.
        apply ISODaysInMonth_range.

  (* 1 < month < 12 *)
  - intros.
    assert (h0 : 1 < month). { apply i1. reflexivity. }
    assert (h1 : month < 12). { apply i. reflexivity. }
    refine (ex_intro _ _ _).
    destruct (day <? 1) eqn: day_lt; destruct (day >? _) eqn: day_gt.
    + discriminate.
    + discriminate.
    + discriminate.
    + rewrite Z.ltb_ge in day_lt.
      rewrite Z.gtb_ltb in day_gt.
      rewrite Z.ltb_ge in day_gt.
      split.
      * assumption.
      * assumption.

  - intros. discriminate. (* contradiction *)

  Unshelve.
  + easy. (* 1 <= 1 <= 12 *)
  + easy. (* 1 <= 12 <= 12 *)
  + split; apply Z.lt_le_incl; assumption. (* 1 < month < 12 -> 1 <= month <= 12 *)
Qed.

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

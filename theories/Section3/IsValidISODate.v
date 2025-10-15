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

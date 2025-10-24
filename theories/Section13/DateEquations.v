From Stdlib Require Import ZArith Program.Wf.
From Temporal Require Import
  Basic
  StringUtil
  Section8.msPerDay.
Open Scope Z.

(* 13.3 Date Equations *)
(* Assumption: 
  EpochDayNumberForYear and msPerDay works on Z and not real numbers *)
(* Note: `/` is floor division with Z. 
  https://rocq-prover.org/doc/V8.21%2Balpha/stdlib/Coq.ZArith.BinIntDef.html#Z.div_eucl *)
(*>> EpochDayNumberForYear(y) = 365 × (y - 1970) + floor((y - 1969) / 4) - floor((y - 1901) / 100) + floor((y - 1601) / 400) <<*)
Definition EpochDayNumberForYear (y : Z) : Z := 365 * (y - 1970) + ((y - 1969) / 4) - ((y - 1901) / 100) + ((y - 1601) / 400).

(*>> EpochTimeForYear(y) = ℝ(msPerDay) × EpochDayNumberForYear(y) <<*)
Definition EpochTimeForYear (y : Z) : Z := msPerDay * EpochDayNumberForYear y.

Lemma EpochDayNumberForYear_monotonic :
  forall y0 y1,
  y0 < y1 -> EpochDayNumberForYear y0 < EpochDayNumberForYear y1.
Proof.
  intros.
  unfold EpochDayNumberForYear.
  rewrite (Z.add_comm).
  rewrite (Z.add_comm _ ((y1 - 1601) / 400)).
  refine (Z.add_le_lt_mono _ _ _ _ _ _).

  (* (y0 - 1601) / 400 <= (y1 - 1601) / 400 *)
  - refine (Z.div_le_mono _ _ 400 ltac:(easy) _).
    rewrite <- Z.sub_le_mono_r.
    apply Z.lt_le_incl.
    assumption.
  
  (* 365 * (y0 - 1970) + (y0 - 1969) / 4 - (y0 - 1901) / 100 <
     365 * (y1 - 1970) + (y1 - 1969) / 4 - (y1 - 1901) / 100 *)
  - rewrite Z.add_sub_swap.
    rewrite Z.add_sub_swap.
    rewrite Z.add_comm.
    rewrite (Z.add_comm _ ((y1 - 1969) / 4)).
    refine (Z.add_le_lt_mono _ _ _ _ _ _).

    (* (y0 - 1969) / 4 <= (y1 - 1969) / 4 *)
    + refine (Z.div_le_mono _ _ 4 ltac:(easy) _).
      rewrite <- Z.sub_le_mono_r.
      exact (Z.lt_le_incl _ _ H).
    
    (* 365 * (y0 - 1970) - (y0 - 1901) / 100 <
       365 * (y0 - 1970) - (y1 - 1901) / 100 *)
    + rewrite <- Z.lt_0_sub.
      rewrite Z.sub_sub_distr.
      rewrite sub_swap.
      rewrite <- Z.mul_sub_distr_l.
      rewrite Z.sub_sub_distr.
      rewrite <- (Z.add_sub_swap _ 1970 _).
      rewrite sub_add_cancel.
      rewrite <- Z.sub_sub_distr.
      rewrite <- (Z.add_opp_l ((y1 - 1901) / 100) _).
      rewrite Z.add_comm.
      rewrite <- Z.div_add.
      rewrite Z.add_comm.
      rewrite Z.mul_opp_l.
      rewrite Z.add_opp_l.
      rewrite div_mul_cancel.
      rewrite Z.sub_sub_distr.
      rewrite sub_swap.
      rewrite Z.sub_sub_distr.
      rewrite Z.add_sub_swap.
      rewrite sub_add_cancel.
      rewrite Z.lt_0_sub.
      rewrite (Z.mul_lt_mono_pos_r 100).
      rewrite (Z.mul_comm (365 * (y1 - y0))).
      rewrite Z.mul_assoc.
      refine (Z.le_lt_trans _ (y1 - y0 + (y0 - 1901) mod 100) _ _ _).
      * apply div_mul_le.
        easy.
      * rewrite <- Z.succ_pred with (n := 100 * 365).
        rewrite Z.mul_succ_l.
        rewrite Z.add_comm.
        rewrite <- Z.add_lt_mono_r.
        refine (Z.lt_trans _ 100 _ _ _).
        apply Z.mod_pos_bound.
        easy.
        refine (Z.lt_le_trans 100 (Z.pred (100 * 365)) _ _ _).
        easy.
        refine (mul_1_le _ _ _ _ _ _).
        easy.
        exact (lt_1_le _ _ H).
        apply Z.le_refl.
      * easy.
      * easy.
      * easy.
Qed.

Lemma EpochTimeForYear_monotonic :
    forall y0 y1,
    y0 < y1 -> EpochTimeForYear y0 < EpochTimeForYear y1.
Proof.
  intros.
  unfold EpochTimeForYear.
  rewrite <- Z.mul_lt_mono_pos_l.
  apply EpochDayNumberForYear_monotonic.
  assumption.
  easy.
Qed.

Program Fixpoint FindYearForwards (t y : Z) (h : EpochTimeForYear y < t)
    {measure (Z.to_nat (t - EpochTimeForYear y))} : Z :=
  let y' := y + 1 in
  match EpochTimeForYear y' ?= t with
  | Lt => FindYearForwards t y' _
  | _ => y
  end.

Next Obligation.
  rewrite <- Z.compare_lt_iff.
  symmetry.
  exact Heq_anonymous.
Qed.

Next Obligation.
  rewrite <- Z2Nat.inj_lt.

  (* t - EpochTimeForYear (y + 1) < t - EpochTimeForYear y *)
  apply Z.sub_lt_mono_l.
  exact (EpochTimeForYear_monotonic y (y + 1) (Z.lt_succ_diag_r y)).
  
  (* 0 <= t - EpochTimeForYear (y + 1) *)
  rewrite Z.le_0_sub.
  rewrite Z.le_lteq.
  left.
  rewrite <- Z.compare_lt_iff.
  symmetry.
  exact Heq_anonymous.

  (* 0 <= t - EpochTimeForYear y *)
  rewrite Z.le_0_sub.
  rewrite Z.le_lteq.
  left.
  exact h.
Qed.

Program Fixpoint FindYearBackwards (t y : Z) (h : t < EpochTimeForYear y)
    {measure (Z.to_nat (EpochTimeForYear y - t))} : Z :=
  let y' := y - 1 in
  match t ?= EpochTimeForYear y' with
  | Lt => FindYearBackwards t y' _
  | _ => y'
  end.

Next Obligation.
  rewrite <- Z.compare_lt_iff.
  symmetry.
  exact Heq_anonymous.
Qed.

Next Obligation.
  rewrite <- Z2Nat.inj_lt.

  (* EpochTimeForYear (y - 1) - t < EpochTimeForYear y - t *)
  apply Z.sub_lt_mono_r.
  exact (EpochTimeForYear_monotonic (y - 1) y (Z.lt_pred_l y)).
  
  (* 0 <= t - EpochTimeForYear (y + 1) *)
  rewrite Z.le_0_sub.
  rewrite Z.le_lteq.
  left.
  rewrite <- Z.compare_lt_iff.
  symmetry.
  exact Heq_anonymous.

  (* 0 <= t - EpochTimeForYear y *)
  rewrite Z.le_0_sub.
  rewrite Z.le_lteq.
  left.
  exact h.
Qed.

(*>> EpochTimeToEpochYear(t) = the largest integral Number y (closest to +∞) such that EpochTimeForYear(y) ≤ t <<*)
Program Definition EpochTimeToEpochYear (t : Z) : Z :=
  match t ?= EpochTimeForYear 1970 with
  | Eq => 1970
  | Gt => FindYearForwards t 1970 _
  | Lt => FindYearBackwards t 1970 _
  end.

Next Obligation.
  apply Z.gt_lt.
  symmetry.
  exact Heq_anonymous.
Qed.

Next Obligation.
  symmetry.
  exact Heq_anonymous.
Qed.

Definition MathematicalDaysInYear (y : Z) : Z :=
  match (y mod 4) =? 0, (y mod 100) =? 0, (y mod 400) =? 0 with
  (*>> = 365 if ((y) modulo 4) ≠ 0 <<*)
  | false, _,     _    => 365
  (*>> = 366 if ((y) modulo 4) = 0 and ((y) modulo 100) ≠ 0 <<*)
  | true,  false, _    => 366
  (*>> = 365 if ((y) modulo 100) = 0 and ((y) modulo 400) ≠ 0 <<*)
  | _,     true, false => 365
  (*>> = 366 if ((y) modulo 400) = 0 <<*)
  | _,     _,    true  => 366
  end.

Lemma MathematicalDaysInYear_365_or_366 :
    forall y,
    MathematicalDaysInYear y = 365 \/ MathematicalDaysInYear y = 366.
Proof.
  intro y.
  unfold MathematicalDaysInYear.
  case (y mod 4 =? 0).
  case (y mod 100 =? 0).
  case (y mod 400 =? 0).
  right. reflexivity.
  left. reflexivity.
  right. reflexivity.
  left. reflexivity.
Qed.

Definition MathematicalInLeapYear (t : Z) : Z.
  refine (
    match MathematicalDaysInYear (EpochTimeToEpochYear t) as d
    return (MathematicalDaysInYear (EpochTimeToEpochYear t) = d -> Z) with
    (*>> = 0 if MathematicalDaysInYear(EpochTimeToEpochYear(t)) = 365 <<*)
    | 365 => fun _ => 0
    (*>> = 1 if MathematicalDaysInYear(EpochTimeToEpochYear(t)) = 366 <<*)
    | 366 => fun _ => 1
    | _ => fun H => impossible
    end eq_refl
  ).

  (* Proof of impossibility of the last case. *)
  all:
    destruct (MathematicalDaysInYear_365_or_366 (EpochTimeToEpochYear t));
    rewrite H in H0;
    discriminate.
Defined.

Lemma MathematicalInLeapYear_0_or_1 :
  forall t, MathematicalInLeapYear t = 0 \/ MathematicalInLeapYear t = 1.
Proof.
  intros.
  unfold MathematicalInLeapYear.
  destruct (MathematicalDaysInYear_365_or_366 (EpochTimeToEpochYear t)).
  - rewrite e.
    left.
    reflexivity.
  - rewrite e.
    right.
    reflexivity.
Qed.

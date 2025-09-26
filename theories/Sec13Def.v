Require Import Coq.Numbers.BinNums Coq.Program.Wf ZArith.
Require Import Lia.
From Temporal Require Import Basic.
Open Scope bool_scope.
Open Scope Z.

(* Assumption: 
  EpochDayNumberForYear and msPerDay works on Z and not real numbers *)
(*>> msPerDay = 86400000𝔽 = msPerHour × 𝔽(HoursPerDay) <<*)
Definition msPerDay : Z := 86400000.

(* 13.3 Date Equations *)
(* Note: `/` is floor division with Z. 
  https://rocq-prover.org/doc/V8.21%2Balpha/stdlib/Coq.ZArith.BinIntDef.html#Z.div_eucl *)
(*>> EpochDayNumberForYear(y) = 365 × (y - 1970) + floor((y - 1969) / 4) - floor((y - 1901) / 100) + floor((y - 1601) / 400) <<*)
Definition EpochDayNumberForYear (y : Z) : Z := 365 * (y - 1970) + ((y - 1969) / 4) - ((y - 1901) / 100) + ((y - 1601) / 400).

(*>> EpochTimeForYear(y) = ℝ(msPerDay) × EpochDayNumberForYear(y) <<*)
Definition EpochTimeForYear (y : Z) : Z := msPerDay * EpochDayNumberForYear y.

Lemma sub_swap : forall x y z, x - y - z = x - z - y.
Proof.
  intros.
  lia.
Qed.

Lemma div_mul_le : forall x y, 0 < y -> (x / y) * y <= x.
Proof.
  intros.
  rewrite Z.mul_comm.
  apply Z.mul_div_le.
  assumption.
Qed.

Lemma lt_1_le : forall x y, x < y -> 1 <= y - x.
Proof.
  intros.
  rewrite <- Z.le_add_le_sub_r.
  rewrite Z.add_1_l.
  rewrite Z.le_succ_l.
  assumption.
Qed.

Lemma mul_1_le : forall x y z, 0 < y -> 1 <= z -> x <= y -> x <= y * z.
Proof.
  intros.
  refine (Z.le_trans _ _ _ H1 _).
  rewrite <-Z.le_mul_diag_r; assumption.
Qed.

Lemma EpochDayNumberForYear_monotonic :
  forall y0 y1,
  y0 < y1 -> EpochDayNumberForYear y0 < EpochDayNumberForYear y1.
Proof.
  intros.
  unfold EpochDayNumberForYear.
  rewrite (Z.add_comm).
  rewrite (Z.add_comm _ ((y1 - 1601) / 400)).
  refine (Z.add_le_lt_mono _ _ _ _ _ _).
  - refine (Z.div_le_mono _ _ 400 ltac:(easy) _).
    rewrite <-Z.sub_le_mono_r.
    exact (Z.lt_le_incl _ _ H).
  - rewrite Z.add_sub_swap.
    rewrite Z.add_sub_swap.
    rewrite Z.add_comm.
    rewrite (Z.add_comm _ ((y1 - 1969) / 4)).
    refine (Z.add_le_lt_mono _ _ _ _ _ _).
    + refine (Z.div_le_mono _ _ 4 ltac:(easy) _).
      rewrite <-Z.sub_le_mono_r.
      exact (Z.lt_le_incl _ _ H).
    + rewrite <-Z.lt_0_sub.
      rewrite Z.sub_sub_distr.
      rewrite sub_swap.
      rewrite <-Z.mul_sub_distr_l.
      rewrite Z.sub_sub_distr.
      rewrite <-(Z.add_sub_swap _ 1970 _).
      rewrite <-(Z.add_sub_swap _ 1970 _).
      rewrite <-Z.add_sub_assoc.
      rewrite Z.sub_diag.
      rewrite Z.add_0_r.
      rewrite <-Z.sub_sub_distr.
      rewrite <-(Z.add_opp_l ((y1 - 1901) / 100) _).
      rewrite Z.add_comm.
      rewrite <-Z.div_add.
      rewrite Z.add_comm.
      rewrite Z.mul_opp_l.
      rewrite Z.add_opp_l.
      rewrite <-(Z.add_0_l ((y0 - 1901) / 100 * 100)).
      rewrite <-Z.sub_diag with (n := (y0 - 1901)).
      rewrite Z.sub_add_distr.
      rewrite Z.sub_sub_distr with (n := y1 - 1901).
      rewrite <-Z.add_sub_assoc.
      rewrite <-Zmod_eq.
      rewrite Z.sub_diag.
      rewrite Z.sub_sub_distr.
      rewrite sub_swap.
      rewrite <-Z.sub_sub_distr.
      rewrite Z.sub_diag.
      rewrite Z.sub_0_r.
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

Theorem EpochTimeForYear_monotonic :
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
Proof.
  rewrite <- Z.compare_lt_iff.
  symmetry.
  exact Heq_anonymous.
Qed.

Next Obligation.
Proof.
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
Proof.
  rewrite <- Z.compare_lt_iff.
  symmetry.
  exact Heq_anonymous.
Qed.

Next Obligation.
Proof.
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
Proof.
  apply Z.gt_lt.
  symmetry.
  exact Heq_anonymous.
Qed.

Next Obligation.
Proof.
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

Program Definition MathematicalInLeapYear (t : Z) : Z :=
  match MathematicalDaysInYear (EpochTimeToEpochYear t) with
  (*>> = 0 if MathematicalDaysInYear(EpochTimeToEpochYear(t)) = 365 <<*)
  | 365 => 0
  (*>> = 1 if MathematicalDaysInYear(EpochTimeToEpochYear(t)) = 366 <<*)
  | 366 => 1
  | _ => impossible
  end.

Next Obligation.
Proof.
  destruct (MathematicalDaysInYear_365_or_366 (EpochTimeToEpochYear t)).
  symmetry in H1.
  contradiction.
  symmetry in H1.
  contradiction.
Qed.

Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.

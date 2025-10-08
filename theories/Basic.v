From Stdlib Require Import ZArith.
Open Scope bool_scope.
Open Scope Z.

Definition assert (P : Prop) (proof : P) : unit := tt.
Notation "'assert' P 'in' A" := (let tt := assert P _ in A) (at level 200).
Notation "'impossible'" := (False_rect _ _).
Notation "a '!=?' b" := (negb (a =? b)) (at level 70).

Inductive Exception := RangeError.

Inductive Completion (result : Type) : Type :=
  | Normal : result -> Completion result 
  | Throw : Exception -> Completion result.

Arguments Normal {result} a.
Arguments Throw {result} e.

Definition Clamp (lower upper x : Z) (h : lower <= upper) : Z :=
  if x <? lower then lower
  else if x >? upper then upper
  else x.

Lemma clamp_between_lower_and_upper :
  forall lower upper x pre, lower <= Clamp lower upper x pre <= upper.
Proof.
  intros.
  unfold Clamp.
  split.
  destruct (x <? lower) eqn:part1.
  easy.
  destruct (x >? upper).
  easy.
  rewrite Z.ltb_ge in part1.
  apply part1.
  destruct (x <? lower).
  easy.
  destruct (x >? upper) eqn:part2.
  easy.
  rewrite Z.gtb_ltb in part2.
  rewrite Z.ltb_ge in part2.
  apply part2.
Qed.

Lemma eq_sym_iff {A} (x y : A) : x = y <-> y = x.
Proof.
  split.
  intro. symmetry. assumption.
  intro. symmetry. assumption.
Qed.

Lemma sub_swap : forall x y z, x - y - z = x - z - y.
Proof.
  intros.
  rewrite <- Z.add_opp_r.
  rewrite <- Z.add_sub_swap.
  rewrite Z.add_opp_r.
  reflexivity.
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
  rewrite <- Z.le_mul_diag_r; assumption.
Qed.

Lemma sub_add_cancel : forall x y, x - y + y = x.
Proof.
  intros.
  rewrite <- Z.add_sub_swap.
  rewrite <- Z.add_sub_assoc.
  rewrite Z.sub_diag.
  rewrite Z.add_0_r.
  reflexivity.
Qed.

Lemma div_mul_cancel : forall x y, 0 < y -> x / y * y = x - x mod y.
Proof.
  intros.
  rewrite <- (Z.add_0_l (x / y * y)).
  rewrite <- (Z.sub_diag x).
  rewrite Zmod_eq.
  rewrite Z.sub_sub_distr.
  reflexivity.
  apply Z.lt_gt.
  assumption.
Qed.

Lemma inside_range_outside_range_impossible {a b c : Z} :
  (a <= b) -> (b <= c) -> ((b <? a) || (b >? c)) = true -> False.
Proof.
  intros a_le_b b_le_c.
  intro H.
  apply Bool.Is_true_eq_left in H.
  apply Bool.orb_prop_elim in H.
  destruct H.
  
  (* b <? a *)
  - apply Bool.Is_true_eq_true in H.
    rewrite Z.ltb_lt in H.
    exact (proj2 (Z.nlt_ge b a) a_le_b H).
  
  (* b >? c *)
  - apply Bool.Is_true_eq_true in H.
    rewrite Z.gtb_gt in H.
    apply Z.gt_lt in H.
    exact (proj2 (Z.nlt_ge c b) b_le_c H).
Qed.

Lemma inside_range_outside_range_impossible' {a b c : Z} :
  (a <= b <= c) -> ((b <? a) || (b >? c)) = true -> False.
Proof.
  intro a_le_b_le_c.
  destruct a_le_b_le_c as [a_le_b b_le_c].
  exact (inside_range_outside_range_impossible a_le_b b_le_c).
Qed.

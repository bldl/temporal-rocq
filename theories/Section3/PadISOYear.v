From Stdlib Require Import
  ZArith
  Strings.String
  Lia.
From Temporal Require Import StringUtil.
Open Scope bool_scope.
Open Scope string_scope.
Open Scope Z.

(* 3.5.9 PadISOYear *)
Program Definition PadISOYear (y : Z) : string :=
  (*>> 1. If y ≥ 0 and y ≤ 9999, then <<*)
  match (y >=? 0) && (y <=? 9999) with
  (*>> a. Return ToZeroPaddedDecimalString(y, 4). <<*)
  | true => ToZeroPaddedDecimalString y 4 _ _
  (*>> 2. If y > 0, let yearSign be "+"; otherwise, let yearSign be "-". <<*)
  | false => let yearSign := if y >? 0 then "+" else "-" in
  (*>> 3. Let year be ToZeroPaddedDecimalString(abs(y), 6). <<*)
  let year := ToZeroPaddedDecimalString (Z.abs y) 6 _ _ in
  (*>> 4. Return the string-concatenation of yearSign and year. <<*)
  yearSign ++ year end.

Next Obligation. 
  apply eq_sym in Heq_anonymous.
  apply Bool.andb_true_iff in Heq_anonymous.
  apply proj1 in Heq_anonymous.
  apply Z.geb_le in Heq_anonymous.
  apply Heq_anonymous.
Defined.

Next Obligation. apply (Z.abs_nonneg). Defined.

Theorem PadISOYear_result_length_at_least_4 :
  forall (y : Z), (4 <= length (PadISOYear y))%nat.
Proof.
  intros.
  unfold PadISOYear.
  unfold PadISOYear_obligation_1.
  generalize (Bool.andb_true_iff (y >=? 0) (y <=? 9999)).
  destruct ((y >=? 0) && (y <=? 9999)).
  - intros.
    simpl.
    now apply ToZeroPaddedDecimalString_length.
  - intros.
    destruct i.
    destruct (y >? 0).
    + simpl.
      rewrite <- Nat.le_pred_le_succ.
      apply ToZeroPaddedDecimalString_length.
      lia.
    + simpl.
      rewrite <- Nat.le_pred_le_succ.
      apply ToZeroPaddedDecimalString_length.
      lia.
Qed.

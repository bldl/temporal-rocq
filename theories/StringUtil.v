From Stdlib Require Import
  ZArith
  Strings.String
  Numbers.DecimalString.
Open Scope bool_scope.
Open Scope string_scope.
Open Scope Z.

Definition Z_to_string (x : Z) : string :=
  NilEmpty.string_of_int (Z.to_int x).

Inductive PadPlacement := START | END.

Definition RotateString (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => s' ++ String c EmptyString
  end.

Fixpoint RepeatString (fillString : string) (fillLen : nat) : string :=
  match fillLen with
  | O => EmptyString
  | S n => 
    match fillString with
    | EmptyString => EmptyString
    | String c _ => String c (RepeatString (RotateString fillString) n)
    end
  end.

Definition StringPad (S : string) (maxLength : Z) (fillString : string) (placement : PadPlacement) (h1 : 0 <= maxLength) : string := 
  let stringLength := Z.of_nat (length S) in
  if maxLength <=? stringLength then S
  else if eqb fillString EmptyString then S
  else let fillLen := maxLength - stringLength in
  let truncatedStringFiller := RepeatString fillString (Z.to_nat fillLen) in
  match placement with
  | START => truncatedStringFiller ++ S
  | END => S ++ truncatedStringFiller
  end.

Definition ToZeroPaddedDecimalString (n minLength : Z) (n_valid : 0 <= n) (minLength_valid : 0 <= minLength) : string :=
  let S := Z_to_string n in
  StringPad S minLength "0" START minLength_valid.

Lemma zero_le_two : 0 <= 2. Proof. easy. Qed.

Close Scope Z.

Lemma append_length :
  forall s0 s1, length (s0 ++ s1) = length s0 + length s1.
Proof.
  intros.
  induction s0.
  - reflexivity.
  - simpl.
    rewrite IHs0.
    reflexivity.
Qed.

Lemma length_char_eq :
  forall a a', length (String a "") = length (String a' "").
Proof.
  reflexivity.
Qed.

Lemma length_append_char : forall s a, length (s ++ String a "") = S (length s).
Proof.
  intros.
  induction s.
  - reflexivity.
  - simpl.
    f_equal.
    assumption.
Qed.

Lemma length_prepend_char : forall s a, length (String a s) = S (length s).
Proof.
  reflexivity.
Qed.

Lemma length_string_eq :
  forall a a' s s',
  length s = length s' <-> length (String a s) = length (String a' s').
Proof.
  split.
  - intros.
    rewrite length_prepend_char, length_prepend_char.
    f_equal.
    assumption.
  - intros.
    rewrite length_prepend_char, length_prepend_char in H.
    now inversion H.
Qed.

Lemma length_nonempty : forall s, s <> "" -> 0 < length s.
Proof.
  intros.
  destruct s.
  + contradiction.
  + simpl.
    apply Nat.lt_0_succ.
Qed.

Lemma RotateString_length : forall s, length (RotateString s) = length s.
Proof.
  intros.
  induction s.
  - reflexivity.
  - unfold RotateString.
    rewrite append_length.
    rewrite Nat.add_comm.
    reflexivity.
Qed.

Lemma RepeatString_zero :
  forall s, length (RepeatString s 0%nat) = 0%nat.
Proof.
  reflexivity.
Qed.

Fixpoint RepeatString_preserves_length :
  forall s0 s1 l, length s0 = length s1 ->
  length (RepeatString s0 l) = length (RepeatString s1 l).
Proof.
  intros.
  destruct l.
  - reflexivity.
  - destruct s0 eqn: s0_def; destruct s1 eqn: s1_def.
    + reflexivity.
    + discriminate.
    + discriminate.
    + simpl.
      f_equal.
      apply RepeatString_preserves_length.
      rewrite append_length, append_length.
      apply f_equal2_plus.
      * rewrite length_string_eq.
        exact H.
      * apply length_char_eq.
Qed.

Lemma RepeatString_length :
  forall s l, 0 < length s -> length (RepeatString s l) = l.
Proof.
  intros.
  induction l.
  - reflexivity.
  - destruct s eqn: s_def.
    + exfalso.
      apply Nat.lt_irrefl with (x := 0).
      assumption.
    + simpl.
      f_equal.
      rewrite <- IHl at 2.
      apply RepeatString_preserves_length.
      rewrite length_append_char.
      rewrite length_prepend_char.
      reflexivity.
Qed.

Lemma StringPad_length :
  forall s l filler placement h, filler <> "" ->
  Z.to_nat l <= length (StringPad s l filler placement h).
Proof.
  intros.
  unfold StringPad.
  destruct (l <=? Z.of_nat (length s))%Z eqn: cmp.
  - rewrite Z.leb_le in cmp.
    apply Nat2Z.inj_le.
    rewrite Z2Nat.id; assumption.
  - rewrite Z.leb_gt in cmp.
    destruct (filler =? "") eqn: filler_eq.
    + rewrite eqb_eq in filler_eq.
      rewrite filler_eq in H.
      contradiction.
    + destruct placement; rewrite append_length, RepeatString_length.
      * rewrite <- Z2Nat.id with (n := l).
        rewrite Z2Nat.inj_sub, Nat2Z.id, Nat2Z.id.
        apply Nat.sub_add_le.
        apply Nat2Z.is_nonneg.
        assumption.
      * apply length_nonempty.
        assumption.
      * rewrite <- Z2Nat.id with (n := l).
        rewrite Z2Nat.inj_sub, Nat2Z.id, Nat2Z.id.
        rewrite Nat.add_sub_assoc, Nat.add_comm, <- Nat.add_sub_assoc.
        now rewrite Nat.sub_diag, Nat.add_0_r.
        easy.
        rewrite <- Z2Nat.id in cmp.
        rewrite <- Nat2Z.inj_lt in cmp.
        now apply Nat.lt_le_incl.
        assumption.
        apply Nat2Z.is_nonneg.
        assumption.
      * apply length_nonempty.
        assumption.
Qed.

Lemma ToZeroPaddedDecimalString_length :
  forall n m m' nv mv, m' <= Z.to_nat m ->
  m' <= length (ToZeroPaddedDecimalString n m nv mv).
Proof.
  intros.
  unfold ToZeroPaddedDecimalString.
  apply Nat.le_trans with (m := Z.to_nat m).
  assumption.
  now apply StringPad_length.
Qed.

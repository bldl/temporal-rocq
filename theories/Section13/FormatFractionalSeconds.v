From Stdlib Require Import
  ZArith
  Strings.String
  Ascii.
From Temporal Require Import
  Grammar
  StringUtil
  Section13.Precision.
From Temporal Require RFC3339.
Open Scope string_scope.
Open Scope Z.

Fixpoint RemoveTrailingZero (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => 
    match RemoveTrailingZero s' with
    | EmptyString => if eqb c "0"%char then EmptyString else String c EmptyString
    | s'' => String c EmptyString ++ s''
    end
  end.

Lemma RemoveTrailingZero_some_digits :
  forall n m nsv mv, 0 < n ->
  generates
    (sequence digit (star digit))
    (RemoveTrailingZero (ToZeroPaddedDecimalString n m nsv mv)).
Admitted.

(* 13.25 FormatFractionalSeconds *)
Program Definition FormatFractionalSeconds (subSecondNanoseconds : Z) (precision : Precision) (subSecondNanoseconds_valid : 0 <= subSecondNanoseconds <= 999999999) : string :=
  match precision with
  (*>> 1. If precision is auto, then <<*)
  | AUTO =>
  (*>> a. If subSecondNanoseconds = 0, return the empty String. <<*)
    if subSecondNanoseconds =? 0 then EmptyString
    (*>> b. Let fractionString be ToZeroPaddedDecimalString(subSecondNanoseconds, 9). <<*)
    else let fractionString := ToZeroPaddedDecimalString subSecondNanoseconds 9 _ _ in
    (*>> c. Set fractionString to the longest prefix of fractionString ending with a code unit other than 0x0030 (DIGIT ZERO). <<*)
    let fractionString' := RemoveTrailingZero fractionString in
    (* NOTE: This is also step 3. *)
    "." ++ fractionString'
  (*>> 2. Else, <<*)
  | PrecisionValue p _ => 
    (*>> a. If precision = 0, return the empty String. <<*)
    if p =? 0 then EmptyString
    (*>> b. Let fractionString be ToZeroPaddedDecimalString(subSecondNanoseconds, 9). <<*)
    else let fractionString := ToZeroPaddedDecimalString subSecondNanoseconds p _ _ in
    (*>> c. Set fractionString to the substring of fractionString from 0 to precision. <<*)
    let fractionString' := fractionString in
  (*>> 3. Return the string-concatenation of the code unit 0x002E (FULL STOP) and fractionString. <<*)
    "." ++ fractionString'
  end.

Lemma FormatFractionalSeconds_rfc3339 :
  forall ns p nsv,
  generates (maybe RFC3339.time_secfrac) (FormatFractionalSeconds ns p nsv).
Proof.
  intros.
  unfold FormatFractionalSeconds.
  destruct p.
  - destruct (ns =? 0) eqn: ns_eq_0.
    + apply gen_alt_l.
      constructor.
    + apply gen_alt_r.
      apply gen_seq.
      * constructor.
      * rewrite Z.eqb_neq in ns_eq_0.
        destruct nsv.
        assert (l' : 0 < ns). {
          apply Z.le_neq.
          split.
          - assumption.
          - symmetry.
            assumption.
        }
        eapply Grammar.equiv_elim.
        apply RemoveTrailingZero_some_digits.
        assumption.
        rewrite <- Grammar.sequence_assoc.
        apply Grammar.sequence_empty_r.
  - destruct (p =? 0) eqn: p_eq_0.
    + apply gen_alt_l.
      constructor.
    + apply gen_alt_r.
      apply gen_seq.
      * constructor.
      * rewrite Z.eqb_neq in p_eq_0.
        destruct a.
        assert (a' : 0 < p). {
          apply Z.le_neq.
          split.
          - assumption.
          - symmetry.
            assumption.
        }
        eapply Grammar.equiv_elim.
        apply ToZeroPaddedDecimalString_gt_0_digits.
        assumption.
        rewrite <- Grammar.sequence_assoc.
        apply Grammar.sequence_empty_r.
Qed.

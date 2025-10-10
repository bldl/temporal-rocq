From Stdlib Require Import ZArith Strings.String.
From Temporal Require Import Basic StringUtil.
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
Qed.
Next Obligation. apply (Z.abs_nonneg). Qed.  

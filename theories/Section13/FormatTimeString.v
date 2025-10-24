From Stdlib Require Import
  ZArith
  Strings.String.
From Temporal Require Import
  Basic
  Grammar
  StringUtil
  Section13.FormatFractionalSeconds
  Section13.PrecisionPrime
  Section13.Style.
From Temporal Require RFC3339.
Open Scope Z.

(* 13.26 FormatTimeString *)
Definition FormatTimeString (hour minute second subSecondNanoseconds : Z) (precision' : Precision') (style : option Style) 
  (hour_valid : 0 <= hour <= 23) (minute_valid : 0 <= minute <= 59) (second_valid : 0 <= second <= 59) (subSecondNanoseconds_valid : 0 <= subSecondNanoseconds <= 999999999) : string :=
  (*>> 1. If style is present and style is unseparated, let separator be the empty String; otherwise, let separator be ":". <<*)
  let separator := match style with
  | Some style' => 
    match style' with
    | SEPARATED => ":"
    | UNSEPARATED => EmptyString
    end
  | None => ":"
  end in
  (*>> 2. Let hh be ToZeroPaddedDecimalString(hour, 2). <<*)
  let hh := ToZeroPaddedDecimalString hour 2 (proj1 hour_valid) zero_le_two in
  (*>> 3. Let mm be ToZeroPaddedDecimalString(minute, 2). <<*)
  let mm := ToZeroPaddedDecimalString minute 2 (proj1 minute_valid) zero_le_two in
  (*>> 4. If precision is minute, return the string-concatenation of hh, separator, and mm. <<*)
  match precision' with
  | MINUTE_PRECISION => hh ++ separator ++ mm
  (*>> 5. Let ss be ToZeroPaddedDecimalString(second, 2). <<*)
  | NormalPrecision precision =>
    let ss := ToZeroPaddedDecimalString second 2 (proj1 second_valid) zero_le_two in
  (*>> 6. Let subSecondsPart be FormatFractionalSeconds(subSecondNanoseconds, precision). <<*)
    let subSecondsPart := FormatFractionalSeconds subSecondNanoseconds precision subSecondNanoseconds_valid in
  (*>> 7. Return the string-concatenation of hh, separator, mm, separator, ss, and subSecondsPart. <<*)
  hh ++ separator ++ mm ++ separator ++ ss ++ subSecondsPart
  end.

Lemma FormatTimeString_rfc3339 :
  forall h min s ns precision h0 h1 h2 h3,
  generates RFC3339.full_time (FormatTimeString h min s ns (NormalPrecision precision) None h0 h1 h2 h3).
Proof.
  intros.
  unfold FormatTimeString.
  repeat (rewrite <- append_assoc).
  apply gen_seq.
  - repeat (rewrite append_assoc).
    repeat (apply gen_seq).
    + apply ToZeroPaddedDecimalString_2_digits.
      destruct h0.
      split.
      * assumption.
      * now (apply Z.le_trans with (m := 23); try assumption).
    + constructor.
    + apply ToZeroPaddedDecimalString_2_digits.
      destruct h1.
      split.
      * assumption.
      * now (apply Z.le_trans with (m := 59); try assumption).
    + constructor.
    + rewrite <- append_empty_r.
      apply gen_seq.
      * apply ToZeroPaddedDecimalString_2_digits.
        auto with *.
      * rewrite <- append_empty_r.
        apply gen_seq; try apply gen_alt_l; constructor.
  - admit.
Admitted.

From Stdlib Require Import
  ZArith
  Strings.String.
From Temporal Require Import
  Section8.msPerDay
  Section13.FormatTimeString
  Section13.Precision
  Section13.PrecisionPrime.
Open Scope bool_scope.
Open Scope string_scope.
Open Scope Z.

(* 11.1.6 FormatUTCOffsetNanoseconds *)
Program Definition FormatUTCOffsetNanoseconds (offsetNanoseconds : Z) : string :=
  (*>> 1. If offsetNanoseconds ≥ 0, let sign be the code unit 0x002B (PLUS SIGN); otherwise, let sign be the code unit 0x002D (HYPHEN-MINUS). <<*)
  let sign := if offsetNanoseconds >=? 0 then "+" else "-" in 
  (*>> 2. Let absoluteNanoseconds be abs(offsetNanoseconds). <<*)
  let absoluteNanoseconds := Z.abs offsetNanoseconds in
  (*>> 3. Let hour be floor(absoluteNanoseconds / (3600 × 10**9)). <<*)
  let hour := absoluteNanoseconds / (3600 * 1000000000) in
  (*>> 4. Let minute be floor(absoluteNanoseconds / (60 × 10**9)) modulo 60. <<*)
  let minute := absoluteNanoseconds / (60 * 1000000000) in
  (*>> 5. Let second be floor(absoluteNanoseconds / 10**9) modulo 60. <<*)
  let second := absoluteNanoseconds / 1000000000 in
  (*>> 6. Let subSecondNanoseconds be absoluteNanoseconds modulo 10**9. <<*)
  let subSecondNanoseconds := absoluteNanoseconds mod 1000000000 in
  (*>> 7. If second = 0 and subSecondNanoseconds = 0, let precision be MINUTE_PRECISION; otherwise, let precision be AUTO. <<*)
  let precision' := if (second =? 0) && (subSecondNanoseconds =? 0) then MINUTE_PRECISION else NormalPrecision AUTO in
  (*>> 8. Let timeString be FormatTimeString(hour, minute, second, subSecondNanoseconds, precision). <<*)
  let timeString := FormatTimeString hour minute second subSecondNanoseconds precision' None _ _ _ _ in
  (*>> 9. Return the string-concatenation of sign and timeString. <<*)
  sign ++ timeString.

Next Obligation. Admitted.

Next Obligation. Admitted.

Next Obligation. Admitted.

Next Obligation.
  split.
  apply Z.mod_pos_bound.
  easy.
  apply Zlt_succ_le.
  simpl.
  apply Z.mod_pos_bound.
  easy.
Qed.


(* Contradictions for 11.1.6 FormatUTCOffsetNanoseconds *)
(* Check FormatUTCOffsetNanoseconds_obligation_1. *)

Definition FormatUTCOffsetNanoseconds_obligation_1_copy (offsetNanoseconds : Z) : Prop :=
  let sign := if offsetNanoseconds >=? 0 then "+" else "-" in
  let absoluteNanoseconds := Z.abs offsetNanoseconds in
  let hour := absoluteNanoseconds / (3600 * 1000000000) in
  let minute := absoluteNanoseconds / (60 * 1000000000) in
  let second := absoluteNanoseconds / 1000000000 in
  let subSecondNanoseconds := absoluteNanoseconds mod 1000000000 in
  let precision' := if (second =? 0) && (subSecondNanoseconds =? 0) then MINUTE_PRECISION else NormalPrecision AUTO in
  0 <= hour <= 23.

Theorem hour_in_FormatUTCOffsetNanoseconds_outside_bounds_of_FormatTimeString :
  exists (offsetNanoseconds : Z),
  ~ FormatUTCOffsetNanoseconds_obligation_1_copy offsetNanoseconds.
Proof.
  exists (3600000000000 * 30).
  unfold FormatUTCOffsetNanoseconds_obligation_1_copy.
  simpl.
  easy.
Qed.

(* Check FormatUTCOffsetNanoseconds_obligation_2. *)

Definition FormatUTCOffsetNanoseconds_obligation_2_copy (offsetNanoseconds : Z) : Prop :=
  let sign := if offsetNanoseconds >=? 0 then "+" else "-" in
  let absoluteNanoseconds := Z.abs offsetNanoseconds in
  let hour := absoluteNanoseconds / (3600 * 1000000000) in
  let minute := absoluteNanoseconds / (60 * 1000000000) in
  let second := absoluteNanoseconds / 1000000000 in
  let subSecondNanoseconds := absoluteNanoseconds mod 1000000000 in
  let precision' := if (second =? 0) && (subSecondNanoseconds =? 0) then MINUTE_PRECISION else NormalPrecision AUTO in
  0 <= minute <= 59.

Theorem minute_in_FormatUTCOffsetNanoseconds_outside_bounds_of_FormatTimeString :
  exists (offsetNanoseconds : Z),
  ~ FormatUTCOffsetNanoseconds_obligation_2_copy offsetNanoseconds.
Proof.
  exists (3600000000000 * 30).
  unfold FormatUTCOffsetNanoseconds_obligation_2_copy.
  simpl.
  easy.
Qed.

(* Check FormatUTCOffsetNanoseconds_obligation_3. *)

Definition FormatUTCOffsetNanoseconds_obligation_3_copy (offsetNanoseconds : Z) : Prop :=
  let sign := if offsetNanoseconds >=? 0 then "+" else "-" in
  let absoluteNanoseconds := Z.abs offsetNanoseconds in
  let hour := absoluteNanoseconds / (3600 * 1000000000) in
  let minute := absoluteNanoseconds / (60 * 1000000000) in
  let second := absoluteNanoseconds / 1000000000 in
  let subSecondNanoseconds := absoluteNanoseconds mod 1000000000 in
  let precision' := if (second =? 0) && (subSecondNanoseconds =? 0) then MINUTE_PRECISION else NormalPrecision AUTO in
  0 <= second <= 59.

Theorem second_in_FormatUTCOffsetNanoseconds_outside_bounds_of_FormatTimeString :
  exists (offsetNanoseconds : Z),
  ~ FormatUTCOffsetNanoseconds_obligation_3_copy offsetNanoseconds.
Proof.
  exists (3600000000000 * 30).
  unfold FormatUTCOffsetNanoseconds_obligation_3_copy.
  simpl.
  easy.
Qed.

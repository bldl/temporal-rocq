From Stdlib Require Import ZArith Strings.String.
From Temporal Require Import Sec11Def Sec13Def.
Open Scope bool_scope.
Open Scope string_scope.
Open Scope Z.

(* Contradiction for 11.1.5 FormatOffsetTimeZoneIdentifier *)
(* Check FormatOffsetTimeZoneIdentifier_obligation_1. *)

Definition FormatOffsetTimeZoneIdentifier_obligation_1_copy (offsetMinutes : Z) (style : option Style) : Prop :=
  let sign := if offsetMinutes >=? 0 then "+" else "-" in
  let absoluteMinutes := Z.abs offsetMinutes in
  let hour := absoluteMinutes / 60 in let minute := absoluteMinutes mod 60 in
  0 <= hour <= 23.

Theorem hour_in_FormatOffsetTimeZoneIdentifier_outside_bounds_of_FormatTimeString :
  exists (offsetMinutes : Z) (style : option Style),
  ~ FormatOffsetTimeZoneIdentifier_obligation_1_copy offsetMinutes style.
Proof.
  exists (2000).
  exists (Some SEPARATED).
  unfold FormatOffsetTimeZoneIdentifier_obligation_1_copy.
  simpl.
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
  let precision' := if (second =? 0) && (subSecondNanoseconds =? 0) then MINUTE_PRECISION' else NormalPrecision AUTO in
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
  let precision' := if (second =? 0) && (subSecondNanoseconds =? 0) then MINUTE_PRECISION' else NormalPrecision AUTO in
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
  let precision' := if (second =? 0) && (subSecondNanoseconds =? 0) then MINUTE_PRECISION' else NormalPrecision AUTO in
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

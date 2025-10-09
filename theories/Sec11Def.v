From Stdlib Require Import ZArith Strings.String.
From Temporal Require Import Sec13Def.
Open Scope bool_scope.
Open Scope string_scope.
Open Scope Z.


(* 11.1.5 FormatOffsetTimeZoneIdentifier *)
Program Definition FormatOffsetTimeZoneIdentifier (offsetMinutes : Z) (style : option Style) : string :=
  (*>> 1. If offsetMinutes ≥ 0, let sign be the code unit 0x002B (PLUS SIGN); otherwise, let sign be the code unit 0x002D (HYPHEN-MINUS). <<*)
  let sign := if offsetMinutes >=? 0 then "+" else "-" in
  (*>> 2. Let absoluteMinutes be abs(offsetMinutes). <<*)
  let absoluteMinutes := Z.abs offsetMinutes in
  (*>> 3. Let hour be floor(absoluteMinutes / 60). <<*)
  let hour := absoluteMinutes / 60 in
  (*>> 4. Let minute be absoluteMinutes modulo 60. <<*)
  let minute := absoluteMinutes mod 60 in
  (*>> 5. Let timeString be FormatTimeString(hour, minute, 0, 0, MINUTE, style). <<*)
  let timeString := FormatTimeString hour minute 0 0 MINUTE style _ _ _ _ in
  (*>> 6. Return the string-concatenation of sign and timeString. <<*)
  sign ++ timeString.

Next Obligation.
Admitted.

Next Obligation.
  split.
  apply Z.mod_pos_bound.
  easy.
  apply Zlt_succ_le.
  simpl.
  apply Z.mod_pos_bound.
  easy.
Qed.

Next Obligation. easy. Qed.

Next Obligation. easy. Qed.

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
  (*>> 7. If second = 0 and subSecondNanoseconds = 0, let precision be MINUTE; otherwise, let precision be AUTO. <<*)
  let precision' := if (second =? 0) && (subSecondNanoseconds =? 0) then MINUTE else NormalPrecision AUTO in
  (*>> 8. Let timeString be FormatTimeString(hour, minute, second, subSecondNanoseconds, precision). <<*)
  let timeString := FormatTimeString hour minute second subSecondNanoseconds precision' None _ _ _ _ in
  (*>> 9. Return the string-concatenation of sign and timeString. <<*)
  sign ++ timeString.

Next Obligation.
Admitted.

Next Obligation.
Admitted.

Next Obligation.
Admitted.

Next Obligation.
  split.
  apply Z.mod_pos_bound.
  easy.
  apply Zlt_succ_le.
  simpl.
  apply Z.mod_pos_bound.
  easy.
Qed.

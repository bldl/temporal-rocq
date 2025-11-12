From Stdlib Require Import
  ZArith
  Strings.String.
From Temporal Require Import
  Section13.FormatTimeString
  Section13.PrecisionPrime
  Section13.Style.
Open Scope string_scope.
Open Scope Z.

(* 11.1.5 FormatOffsetTimeZoneIdentifier *)
Program Definition FormatOffsetTimeZoneIdentifier 
  (offsetMinutes : Z) (offsetMinutes_valid : -1439 <= offsetMinutes <= 1439) (style : option Style) : string :=
  (*>> 1. If offsetMinutes ≥ 0, let sign be the code unit 0x002B (PLUS SIGN); otherwise, let sign be the code unit 0x002D (HYPHEN-MINUS). <<*)
  let sign := if offsetMinutes >=? 0 then "+" else "-" in
  (*>> 2. Let absoluteMinutes be abs(offsetMinutes). <<*)
  let absoluteMinutes := Z.abs offsetMinutes in
  (*>> 3. Let hour be floor(absoluteMinutes / 60). <<*)
  let hour := absoluteMinutes / 60 in
  (*>> 4. Let minute be absoluteMinutes modulo 60. <<*)
  let minute := absoluteMinutes mod 60 in
  (*>> 5. Let timeString be FormatTimeString(hour, minute, 0, 0, MINUTE_PRECISION, style). <<*)
  let timeString := FormatTimeString hour minute 0 0 MINUTE_PRECISION style _ _ _ _ in
  (*>> 6. Return the string-concatenation of sign and timeString. <<*)
  sign ++ timeString.

Next Obligation.
  split.
  apply Z_div_nonneg_nonneg.
  apply Z.abs_nonneg.
  easy.
  apply Zlt_succ_le.
  apply Z.div_lt_upper_bound.
  easy.
  apply Z.abs_lt.
  split.
  apply Z.le_succ_l.
  easy.
  apply Z.le_succ_l.
  apply Z.pred_le_mono.
  rewrite Z.pred_succ.
  easy.
Qed.

Next Obligation.
  split.
  apply Z.mod_pos_bound.
  easy.
  apply Zlt_succ_le.
  apply Z.mod_pos_bound.
  easy.
Qed.

Solve Obligations with easy.

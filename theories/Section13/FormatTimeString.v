From Stdlib Require Import
  ZArith
  Strings.String.
From Temporal Require Import
  Basic
  StringUtil
  Section13.FormatFractionalSeconds
  Section13.PrecisionPrime
  Section13.Style.
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

From Temporal Require Import
  Section13.RoundingMode
  Section13.Sign
  Section13.UnsignedRoundingMode.

(* Table 22 *)
(*>> Rounding Mode | Sign     | Unsigned Rounding Mode <<*)
(*>> ceil          | positive | infinity <<*)
(*>> ceil          | negative | zero <<*)
(*>> floor         | positive | zero <<*)
(*>> floor         | negative | infinity <<*)
(*>> expand        | positive | infinity <<*)
(*>> expand        | negative | infinity <<*)
(*>> trunc         | positive | zero <<*)
(*>> trunc         | negative | zero <<*)
(*>> half-ceil     | positive | half-infinity <<*)
(*>> half-ceil     | negative | half-zero <<*)
(*>> half-floor    | positive | half-zero <<*)
(*>> half-floor    | negative | half-infinity <<*)
(*>> half-expand   | positive | half-infinity <<*)
(*>> half-expand   | negative | half-infinity <<*)
(*>> half-trunc    | positive | half-zero <<*)
(*>> half-trunc    | negative | half-zero <<*)
(*>> half-even     | positive | half-even <<*)
(*>> half-even     | negative | half-even <<*)

(* 13.27 GetUnsignedRoundingMode *)
Definition GetUnsignedRoundingMode (roundingMode : RoundingMode) (sign : Sign) : UnsignedRoundingMode :=
  (*>> 1. Return the specification type in the "Unsigned Rounding Mode" column of Table 22 for the row where the value in the "Rounding Mode" column is roundingMode and the value in the "Sign" column is sign. <<*)
  match roundingMode, sign with
  | CEIL, POSITIVE => INFINITY
  | CEIL, NEGATIVE => ZERO
  | FLOOR, POSITIVE => ZERO
  | FLOOR, NEGATIVE => INFINITY
  | EXPAND, POSITIVE => INFINITY
  | EXPAND, NEGATIVE => INFINITY
  | TRUNC, POSITIVE => ZERO
  | TRUNC, NEGATIVE => ZERO
  | HALF_CEIL, POSITIVE => HALF_INFINITY
  | HALF_CEIL, NEGATIVE => HALF_ZERO
  | HALF_FLOOR, POSITIVE => HALF_ZERO
  | HALF_FLOOR, NEGATIVE => HALF_INFINITY
  | HALF_EXPAND, POSITIVE => HALF_INFINITY
  | HALF_EXPAND, NEGATIVE => HALF_INFINITY
  | HALF_TRUNC, POSITIVE => HALF_ZERO
  | HALF_TRUNC, NEGATIVE => HALF_ZERO
  | HALF_EVEN, POSITIVE => HALF_EVEN_UNSIGNED
  | HALF_EVEN, NEGATIVE => HALF_EVEN_UNSIGNED
  end.

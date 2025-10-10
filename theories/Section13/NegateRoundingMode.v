From Temporal Require Import Section13.RoundingMode.

(* 13.8 NegateRoundingMode *)
Definition NegateRoundingMode (roundingMode : RoundingMode) : RoundingMode :=
  match roundingMode with
  (*>> 1. If roundingMode is ceil, return floor. <<*)
  | CEIL => FLOOR
  (*>> 2. If roundingMode is floor, return ceil. <<*)
  | FLOOR => CEIL
  (*>> 3. If roundingMode is half-ceil, return half-floor. <<*)
  | HALF_CEIL => HALF_FLOOR
  (*>> 4. If roundingMode is half-floor, return half-ceil. <<*)
  | HALF_FLOOR => HALF_CEIL
  (*>> 5. Return roundingMode. <<*)
  | _ => roundingMode
  end.

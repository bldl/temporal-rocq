From Stdlib Require Import ZArith ZArith.Zpow_alt.
Open Scope Z.

Record Float64RepresentableInteger :=
  mkFloat64RepresentableInteger {
    value : Z;
    in_range : -(2 ^^ 53) <= value <= (2 ^^ 53);
  }.

(* 7.5.1 Date Duration Records *)
Record DateDurationRecord :=
  mkDateDurationRecord {
    (*>> Field Name | Value                           | Meaning <<*)
    (*>> [[Years]]  | a float64-representable integer | The number of years in the duration. <<*)
    years : Float64RepresentableInteger;
    (*>> [[Months]] | a float64-representable integer | The number of months in the duration. <<*)
    months : Float64RepresentableInteger;
    (*>> [[Weeks]]  | a float64-representable integer | The number of weeks in the duration. <<*)
    weeks : Float64RepresentableInteger;
    (*>> [[Days]]   | a float64-representable integer | The number of days in the duration. <<*)
    days : Float64RepresentableInteger;
  }.

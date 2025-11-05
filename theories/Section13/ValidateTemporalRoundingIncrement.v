From Stdlib Require Import ZArith.
From Temporal Require Import Basic.
Open Scope Z.

Inductive Unused := UNUSED.

(* 13.14 ValidateTemporalRoundingIncrement *)
Program Definition ValidateTemporalRoundingIncrement (increment dividend : Z) (inclusive : bool)
  (increment_valid : 1 <= increment) (dividend_valid : 1 <= dividend) (relation_valid : (dividend > 1 /\ inclusive = false) \/ (inclusive = true))
  : Completion Unused :=
  (*>> 1. If inclusive is true, then <<*)
  let maximum := match inclusive with
    (*>> a. Let maximum be dividend. <<*)
    | true => dividend
  (*>> 2. Else, <<*)
    (*>> a. Assert: dividend > 1. <<*)
    | false => assert (dividend > 1) in 
    (*>> b. Let maximum be dividend - 1. <<*)
    dividend - 1
    end 
  in
  (*>> 3. If increment > maximum, throw a RangeError exception. <<*)
  if increment >? maximum then Throw RangeError
  (*>> 4. If dividend modulo increment ≠ 0, then <<*)
  else if dividend mod increment =? 0
    (*>> a. Throw a RangeError exception. <<*)
    then Throw RangeError
  (*>> 5. Return unused. <<*)
  else Normal UNUSED.

Next Obligation. apply not_B_if_A_or_B_then_A in relation_valid; easy. Qed.

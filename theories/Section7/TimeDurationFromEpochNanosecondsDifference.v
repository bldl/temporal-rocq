From Stdlib Require Import ZArith.
From Temporal Require Import Basic Section7.MaxTimeDuration.
Open Scope Z.

(* 7.5.26 TimeDurationFromEpochNanosecondsDifference *)
Program Definition TimeDurationFromEpochNanosecondsDifference (one two : Z) : Z :=
  (*>> 1. Let result be ℝ(one) - ℝ(two). <<*)
  let result := one - two in
  (*>> 2. Assert: abs(result) ≤ maxTimeDuration. <<*)
  assert Z.abs result <= MaxTimeDuration in
  (*>> 3. Return result. <<*)
  result.

Next Obligation. Admitted.

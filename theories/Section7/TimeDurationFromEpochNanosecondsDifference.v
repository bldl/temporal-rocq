From Stdlib Require Import ZArith.
From Temporal Require Import
  Basic
  Section7.MaxTimeDuration.
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

(* Contradiction for 7.5.26 TimeDurationFromEpochNanosecondsDifference *)
(* Check TimeDurationFromEpochNanosecondsDifference_obligation_1. *)

Definition TimeDurationFromEpochNanosecondsDifference_obligation_1_copy (one two : Z) :=
let result := one - two in Z.abs result <= MaxTimeDuration.

Theorem result_in_TimeDurationFromEpochNanosecondsDifference_outside_bounds_of_MaxTimeDuration :
  exists (one two : Z),
  ~ TimeDurationFromEpochNanosecondsDifference_obligation_1_copy one two.
Proof.
  exists (MaxTimeDuration).
  exists (MinTimeDuration).
  easy.
Qed.

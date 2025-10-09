From Stdlib Require Import ZArith Strings.String.
From Temporal Require Import Sec4Def Sec7Def.
Open Scope bool_scope.
Open Scope string_scope.
Open Scope Z.

(* Contradiction for 7.5.21 TimeDurationFromComponents *) 
(* Check TimeDurationFromComponents_obligation_1. *)

Definition TimeDurationFromComponents_obligation_1_copy (hours minutes seconds milliseconds microseconds nanoseconds : Z) : Prop :=
  let minutes' := minutes + hours * 60 in
  let seconds' := seconds + minutes * 60 in
  let milliseconds' := milliseconds + seconds * 1000 in
  let microseconds' := microseconds + milliseconds * 1000 in
  let nanoseconds' := nanoseconds + microseconds * 1000 in
  Z.abs nanoseconds' <= MaxTimeDuration.

Theorem nanoseconds'_in_TimeDurationFromComponents_outside_bounds_of_MaxTimeDuration :
  exists (hours minutes seconds milliseconds microseconds nanoseconds : Z),
  ~ TimeDurationFromComponents_obligation_1_copy hours minutes seconds milliseconds microseconds nanoseconds.
Proof.
  exists (0).
  exists (0).
  exists (0).
  exists (0).
  exists (1).
  exists (MaxTimeDuration).
  easy.
Qed.

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

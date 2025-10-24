From Stdlib Require Import ZArith.
From Temporal Require Import
  Basic
  Section7.MaxTimeDuration.
Open Scope Z.

(* 7.5.21 TimeDurationFromComponents *) 
Program Definition TimeDurationFromComponents (hours minutes seconds milliseconds microseconds nanoseconds : Z) : Z :=
  (*>> 1. Set minutes to minutes + hours × 60. <<*)
  let minutes' := minutes + hours * 60 in
  (*>> 2. Set seconds to seconds + minutes × 60. <<*)
  let seconds' := seconds + minutes * 60 in
  (*>> 3. Set milliseconds to milliseconds + seconds × 1000. <<*)
  let milliseconds' := milliseconds + seconds * 1000 in
  (*>> 4. Set microseconds to microseconds + milliseconds × 1000. <<*)
  let microseconds' := microseconds + milliseconds * 1000 in
  (*>> 5. Set nanoseconds to nanoseconds + microseconds × 1000. <<*)
  let nanoseconds' := nanoseconds + microseconds * 1000 in
  (*>> 6. Assert: abs(nanoseconds) ≤ maxTimeDuration. <<*)
  assert Z.abs nanoseconds' <= MaxTimeDuration in
  (*>> 7. Return nanoseconds. <<*)
  nanoseconds'.

Next Obligation. Admitted.

(* Contradiction for 7.5.21 TimeDurationFromComponents *) 
(* Check TimeDurationFromComponents_obligation_1. *)

Definition TimeDurationFromComponents_obligation_1_copy (hours minutes seconds milliseconds microseconds nanoseconds : Z) : Prop :=
  let minutes' := minutes + hours * 60 in
  let seconds' := seconds + minutes * 60 in
  let milliseconds' := milliseconds + seconds * 1000 in
  let microseconds' := microseconds + milliseconds * 1000 in
  let nanoseconds' := nanoseconds + microseconds * 1000 in
  Z.abs nanoseconds' <= MaxTimeDuration.

Theorem TimeDurationFromComponents_nanoseconds'_outside_bounds_of_MaxTimeDuration :
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

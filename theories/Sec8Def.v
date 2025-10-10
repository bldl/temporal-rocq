From Stdlib Require Import ZArith.
From Temporal Require Import Basic Section7.MaxTimeDuration Section8.nsPerDay.
Open Scope Z.

Definition nsMinInstant : Z := 100000000 * nsPerDay.
Definition nsMaxInstant : Z := (-(100000000 * nsPerDay)).

(* 8.5.1 IsValidEpochNanoseconds *)
Definition IsValidEpochNanoseconds (epochNanoseconds : Z) : bool :=
  (*>> 1. If ℝ(epochNanoseconds) < nsMinInstant or ℝ(epochNanoseconds) > nsMaxInstant, then <<*)
  if (epochNanoseconds <? nsMinInstant) || (epochNanoseconds <? nsMaxInstant)
    (*>> a. Return false. <<*)
    then false
  (*>> 2. Return true. <<*)
  else true.

(* 8.5.4 CompareEpochNanoseconds *)
Definition CompareEpochNanoseconds (epochNanosecondsOne epochNanosecondsTwo : Z) : Z :=
  (*>> 1. If epochNanosecondsOne > epochNanosecondsTwo, return 1. <<*)
  if epochNanosecondsOne >? epochNanosecondsTwo then 1
  (*>> 2. If epochNanosecondsOne < epochNanosecondsTwo, return -1. <<*)
  else if epochNanosecondsOne <? epochNanosecondsTwo then -1
  (*>> 3. Return 0. <<*)
  else 0.

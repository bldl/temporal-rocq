From Stdlib Require Import ZArith.
From Temporal Require Import Basic Sec7Def.
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

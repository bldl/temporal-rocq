From Stdlib Require Import ZArith.
From Temporal Require Import
  Section8.nsMaxInstant
  Section8.nsMinInstant.
  Open Scope bool_scope.
Open Scope Z.

(* 8.5.1 IsValidEpochNanoseconds *)
Definition IsValidEpochNanoseconds (epochNanoseconds : Z) : bool :=
  (*>> 1. If ℝ(epochNanoseconds) < nsMinInstant or ℝ(epochNanoseconds) > nsMaxInstant, then <<*)
  if (epochNanoseconds <? nsMinInstant) || (epochNanoseconds >? nsMaxInstant)
    (*>> a. Return false. <<*)
    then false
  (*>> 2. Return true. <<*)
  else true.

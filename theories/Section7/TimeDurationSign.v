From Stdlib Require Import ZArith.
From Temporal Require Import Section7.MaxTimeDuration.
Open Scope Z.

(* 7.5.28 TimeDurationSign *)
Definition TimeDurationSign (d : Z) (d_valid : MinTimeDuration <= d <= MaxTimeDuration) : Z :=
  (*>> 1. If d < 0, return -1. <<*)
  if d <? 0 then -1
  (*>> 2. If d > 0, return 1. <<*)
  else if d >? 0 then 1
  (*>> 3. Return 0. <<*)
  else 0.

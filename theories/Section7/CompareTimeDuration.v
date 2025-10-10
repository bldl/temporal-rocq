From Stdlib Require Import ZArith.
From Temporal Require Import Section7.MaxTimeDuration.
Open Scope Z.

(* 7.5.25 CompareTimeDuration *)
Definition CompareTimeDuration (one two : Z)
(one_valid : MinTimeDuration <= one <= MaxTimeDuration) (two_valid : MinTimeDuration <= two <= MaxTimeDuration) : Z :=
  (*>> 1. If one > two, return 1. <<*)
  if one >? two then 1
  (*>> 2. If one < two, return -1. <<*)
  else if one <? two then -1
  (*>> 3. Return 0. <<*)
  else 0.

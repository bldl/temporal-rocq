From Stdlib Require Import ZArith.
From Temporal Require Import Basic Section7.MaxTimeDuration.
Open Scope Z.

(* 7.5.22 AddTimeDuration *)
Definition AddTimeDuration (one two : Z) 
  (one_valid : MinTimeDuration <= one <= MaxTimeDuration) (two_valid : MinTimeDuration <= two <= MaxTimeDuration) : Completion Z :=
  (*>> 1. Let result be one + two. <<*)
  let result := one + two in
  (*>> 2. If abs(result) > maxTimeDuration, throw a RangeError exception. <<*)
  if Z.abs result >? MaxTimeDuration then Throw RangeError
  (*>> 3. Return result. <<*)
  else Normal result.

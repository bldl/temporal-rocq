From Stdlib Require Import ZArith.
Open Scope Z.

(* 8.5.4 CompareEpochNanoseconds *)
Definition CompareEpochNanoseconds (epochNanosecondsOne epochNanosecondsTwo : Z) : Z :=
  (*>> 1. If epochNanosecondsOne > epochNanosecondsTwo, return 1. <<*)
  if epochNanosecondsOne >? epochNanosecondsTwo then 1
  (*>> 2. If epochNanosecondsOne < epochNanosecondsTwo, return -1. <<*)
  else if epochNanosecondsOne <? epochNanosecondsTwo then -1
  (*>> 3. Return 0. <<*)
  else 0.

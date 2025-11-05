From Stdlib Require Import ZArith.
From Temporal Require Import
  Basic
  Section7.MaxTimeDuration
  Section7.AddTimeDurationToEpochNanoseconds
  Section8.IsValidEpochNanoseconds.

(* 8.5.5 AddInstant *)
Definition AddInstant (epochNanoseconds timeDuration : Z)
  (timeDuration_valid : MinTimeDuration <= timeDuration <= MaxTimeDuration) : Completion Z :=
  (*>> 1. Let result be AddTimeDurationToEpochNanoseconds(timeDuration, epochNanoseconds). <<*)
  let result := AddTimeDurationToEpochNanoseconds timeDuration epochNanoseconds timeDuration_valid in
  (*>> 2. If IsValidEpochNanoseconds(result) is false, throw a RangeError exception. <<*)
  match IsValidEpochNanoseconds result with
  | false => Throw RangeError
  (*>> 3. Return result. <<*)
  | _ => Normal result
  end.

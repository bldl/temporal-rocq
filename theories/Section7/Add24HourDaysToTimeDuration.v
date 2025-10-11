From Stdlib Require Import ZArith.
From Temporal Require Import
  Basic
  Section7.MaxTimeDuration
  Section8.nsPerDay.

(* 7.5.23 Add24HourDaysToTimeDuration *)
Definition Add24HourDaysToTimeDuration (d days : Z)
  (d_valid : MinTimeDuration <= d <= MaxTimeDuration) : Completion Z :=
    (*>> 1. Let result be d + days × nsPerDay. <<*)
    let result := d + days * nsPerDay in
    (*>> 2. If abs(result) > maxTimeDuration, throw a RangeError exception. <<*)
    if Z.abs result >? MaxTimeDuration then Throw RangeError
    (*>> 3. Return result. <<*)
    else Normal result.

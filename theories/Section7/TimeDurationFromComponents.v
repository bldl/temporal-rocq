From Stdlib Require Import ZArith.
From Temporal Require Import Basic Section7.MaxTimeDuration.
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

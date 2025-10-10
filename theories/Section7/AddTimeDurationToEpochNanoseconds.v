From Stdlib Require Import ZArith.
From Temporal Require Import Basic Section7.MaxTimeDuration.

(* 7.5.24 AddTimeDurationToEpochNanoseconds *)
Definition AddTimeDurationToEpochNanoseconds (d epochNs : Z) (d_valid : MinTimeDuration <= d <= MaxTimeDuration) : Z :=
  (*>> 1. Return epochNs + ℤ(d). <<*)
  epochNs + d.

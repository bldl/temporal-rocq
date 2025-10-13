From Stdlib Require Import ZArith.
From Temporal Require Import Section8.msPerDay.
Open Scope Z.

(*>> nsPerDay = 10**6 × ℝ(msPerDay) = 8.64 × 10**13 <<*)
Definition nsPerDay : Z := msPerDay * 1000000.

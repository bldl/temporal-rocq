From Stdlib Require Import ZArith.
From Temporal Require Import Section8.nsPerDay.
Open Scope Z.

Definition nsMinInstant : Z := -(100000000 * nsPerDay).

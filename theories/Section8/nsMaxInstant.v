From Stdlib Require Import ZArith.
From Temporal Require Import Section8.nsPerDay.
Open Scope Z.

Definition nsMaxInstant : Z := -(100000000 * nsPerDay).

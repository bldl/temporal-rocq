From Stdlib Require Import ZArith.
Open Scope Z.

Inductive Precision :=
  | AUTO
  | PrecisionValue : forall (p : Z), 0 <= p <= 9 -> Precision.

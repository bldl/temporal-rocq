From Stdlib Require Import Numbers.BinNums Program.Wf ZArith Lia.
From Temporal Require Import Basic Sec13Def.
Open Scope bool_scope.
Open Scope Z.

Lemma MathematicalInLeapYear_zero_or_one : forall t, MathematicalInLeapYear t = 0 \/ MathematicalInLeapYear t = 1.
Proof.
Admitted.

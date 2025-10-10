From Stdlib Require Import Numbers.BinNums Program.Wf ZArith Lia.
From Temporal Require Import Basic Sec13Def.
Open Scope bool_scope.
Open Scope Z.

Lemma MathematicalInLeapYear_0_or_1 :
  forall t, MathematicalInLeapYear t = 0 \/ MathematicalInLeapYear t = 1.
Proof.
  intros.
  unfold MathematicalInLeapYear.
  destruct (MathematicalDaysInYear_365_or_366 (EpochTimeToEpochYear t)).
  - rewrite e.
    left.
    reflexivity.
  - rewrite e.
    right.
    reflexivity.
Qed.

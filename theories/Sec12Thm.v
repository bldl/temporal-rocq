From Stdlib Require Import Numbers.BinNums Program.Wf ZArith Lia.
From Temporal Require Import Sec12Def Sec13Thm.
Open Scope bool_scope.
Open Scope Z.

Lemma ISODaysInMonth_at_least_1 : forall year month pre, 1 <= ISODaysInMonth year month pre.
Proof.
  intros.
  unfold ISODaysInMonth.
  destruct month.
  rewrite <- Z.le_sub_le_add_l.
  destruct (MathematicalInLeapYear_zero_or_one (Sec13Def.EpochTimeForYear year)).
  rewrite H.
  easy.
  rewrite H.
  easy.
  admit.
  rewrite <- Z.le_sub_le_add_l.
  destruct (MathematicalInLeapYear_zero_or_one (Sec13Def.EpochTimeForYear year)).
  rewrite H.
  easy.
  rewrite H.
  easy.
Admitted.

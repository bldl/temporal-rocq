From Stdlib Require Import ZArith Lia.
From Temporal Require Import Basic Sec4Def.
Open Scope Z.

Theorem TimeRecord_IsValidTime :
  forall (t : TimeRecord),
  IsValidTime (hour t) (minute t) (second t) (millisecond t) (microsecond t) (nanosecond t) = true.
Proof.
  intro t.
  destruct t.
  simpl.
  unfold IsValidTime.

  destruct_with_eqn ((hour <? 0) || (hour >? 23)); try lia.
  destruct_with_eqn ((minute <? 0) || (minute >? 59)); try lia.
  destruct_with_eqn ((second <? 0) || (second >? 59)); try lia.
  destruct_with_eqn ((millisecond <? 0) || (millisecond >? 999)); try lia.
  destruct_with_eqn ((microsecond <? 0) || (microsecond >? 999)); try lia.
  destruct_with_eqn ((nanosecond <? 0) || (nanosecond >? 999)); try lia.
Qed.

(* Proofs that BalanceTime is missing a precondition *)
Theorem delta_days_can_be_negative : exists hour, days (BalanceTime hour 0 0 0 0 0) < 0.
Proof.
  exists (-42).
  unfold BalanceTime.
  simpl.
  easy.
Qed.

Theorem BalanceTime_inconsistent : False.
Proof.
  destruct delta_days_can_be_negative.
  pose (days_valid (BalanceTime x 0 0 0 0 0)) as H1.
  contradiction.
Qed.

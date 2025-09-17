Require Import ZArith.
From Temporal Require Import Sec4Def.
Open Scope Z.

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

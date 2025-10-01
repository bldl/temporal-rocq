From Stdlib Require Import ZArith.
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

  1: destruct_with_eqn ((hour <? 0) || (hour >? 23)).
  2: destruct_with_eqn ((minute <? 0) || (minute >? 59)).
  3: destruct_with_eqn ((second <? 0) || (second >? 59)).
  4: destruct_with_eqn ((millisecond <? 0) || (millisecond >? 999)).
  5: destruct_with_eqn ((microsecond <? 0) || (microsecond >? 999)).
  6: destruct_with_eqn ((nanosecond <? 0) || (nanosecond >? 999)).

  - exfalso.
    exact (inside_range_outside_range_impossible' hour_valid Heqb).
  - exfalso.
    exact (inside_range_outside_range_impossible' minute_valid Heqb0).
  - exfalso.
    exact (inside_range_outside_range_impossible' second_valid Heqb1).
  - exfalso.
    exact (inside_range_outside_range_impossible' millisecond_valid Heqb2).
  - exfalso.
    exact (inside_range_outside_range_impossible' microsecond_valid Heqb3).
  - exfalso.
    exact (inside_range_outside_range_impossible' nanosecond_valid Heqb4).

  - reflexivity.
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

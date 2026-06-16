From Stdlib Require Import ZArith.
From Temporal Require Import
  Basic
  Section4.BalanceTime
  Section4.TimeRecord
  Section7.MaxTimeDuration.

(* 4.5.15 AddTime *)
Definition AddTime (time : TimeRecord) (timeDuration : Z) (timeDuration_valid : MinTimeDuration <= timeDuration <= MaxTimeDuration) : TimeRecord :=
  (*>> 1. Return BalanceTime(time.[[Hour]], time.[[Minute]], time.[[Second]], time.[[Millisecond]], time.[[Microsecond]], time.[[Nanosecond]] + timeDuration). <<*)
  BalanceTime (Hour time) (Minute time) (Second time) (Millisecond time) (Microsecond time) (Nanosecond time + timeDuration).
  (*>> 2. NOTE: If using floating points to implement this operation, add the time components separately before balancing to avoid errors with unsafe integers. <<*)

Lemma zero_timeDuration_valid : MinTimeDuration <= 0 <= MaxTimeDuration.
Proof.
  split; easy.
Qed.

Theorem AddTime_adding_zero_no_change :
  forall time,
  let time' := AddTime time 0 zero_timeDuration_valid in
     Days time' = 0
  /\ Minute time = Minute time'
  /\ Second time = Second time'
  /\ Millisecond time = Millisecond time'
  /\ Microsecond time = Microsecond time'
  /\ Nanosecond time = Nanosecond time'.
Proof.
  intros.
  repeat split.
  - simpl.
    rewrite add_div_small with (a := (Nanosecond time + 0)).
    all: try rewrite Z.add_0_r.
    rewrite add_div_small with (a := Microsecond time).
    rewrite add_div_small with (a := Millisecond time).
    rewrite add_div_small with (a := Second time).
    rewrite add_div_small with (a := Minute time).
    rewrite div_small_pred.
    all: now destruct time.
  - simpl.
    rewrite add_div_small with (a := (Nanosecond time + 0)).
    all: try rewrite Z.add_0_r.
    rewrite add_div_small with (a := Microsecond time).
    rewrite add_div_small with (a := Millisecond time).
    rewrite add_div_small with (a := Second time).
    rewrite mod_small_pred.
    all: now destruct time.
  - simpl.
    rewrite add_div_small with (a := (Nanosecond time + 0)).
    all: try rewrite Z.add_0_r.
    rewrite add_div_small with (a := Microsecond time).
    rewrite add_div_small with (a := Millisecond time).
    rewrite mod_small_pred.
    all: now destruct time.
  - simpl.
    rewrite add_div_small with (a := (Nanosecond time + 0)).
    all: try rewrite Z.add_0_r.
    rewrite add_div_small with (a := Microsecond time).
    rewrite mod_small_pred.
    all: now destruct time.
  - simpl.
    rewrite Z.add_0_r.
    rewrite add_div_small with (a := Nanosecond time).
    rewrite mod_small_pred.
    all: now destruct time.
  - simpl.
    rewrite Z.add_0_r.
    rewrite mod_small_pred.
    all: now destruct time.
Qed.

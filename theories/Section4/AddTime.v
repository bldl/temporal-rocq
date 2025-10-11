From Stdlib Require Import ZArith.
From Temporal Require Import
  Section4.BalanceTime
  Section4.TimeRecord
  Section7.MaxTimeDuration.

(* 4.5.15 AddTime *)
Definition AddTime (time : TimeRecord) (timeDuration : Z) (timeDuration_valid : MinTimeDuration <= timeDuration <= MaxTimeDuration) : TimeRecord :=
  (*>> 1. Return BalanceTime(time.[[Hour]], time.[[Minute]], time.[[Second]], time.[[Millisecond]], time.[[Microsecond]], time.[[Nanosecond]] + timeDuration). <<*)
  BalanceTime (hour time) (minute time) (second time) (millisecond time) (microsecond time) (nanosecond time + timeDuration).
  (*>> 2. NOTE: If using floating points to implement this operation, add the time components separately before balancing to avoid errors with unsafe integers. <<*)

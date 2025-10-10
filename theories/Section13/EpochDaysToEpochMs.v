From Stdlib Require Import ZArith.
From Temporal Require Import Section8.msPerDay.


(* 13.2 EpochDaysToEpochMs *)
Definition EpochDaysToEpochMs (day time : Z) : Z :=
  (*>> 1. Return day × ℝ(msPerDay) + time. <<*)
  day * msPerDay + time.

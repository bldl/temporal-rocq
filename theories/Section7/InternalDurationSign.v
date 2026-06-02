From Stdlib Require Import ZArith.
From Temporal Require Import
  Basic
  Section7.DateDurationSign
  Section7.InternalDurationRecord
  Section7.TimeDurationSign.
Open Scope Z.

(* 7.5.15 InternalDurationSign *)
Program Definition InternalDurationSign (internalDuration : InternalDurationRecord) : Z :=
  (*>> 1. Let dateSign be DateDurationSign(internalDuration.[[Date]]). <<*)
  let dateSign := DateDurationSign (Date internalDuration) in
  (*>> 2. If dateSign ≠ 0, return dateSign. <<*)
  if (dateSign !=? 0) then dateSign
  (*>> 3. Return TimeDurationSign(internalDuration.[[Time]]). <<*)
  else TimeDurationSign (Time internalDuration) _.

Next Obligation. apply Time_valid. Qed.

(* The abstract operation InternalDurationSign takes argument internalDuration (an Internal Duration Record) and returns one of -1, 0, or 1. *)
Lemma InternalDurationSign_inside_correct_range :
  forall internalDuration, 
  InternalDurationSign internalDuration = -1 \/
  InternalDurationSign internalDuration = 0 \/
  InternalDurationSign internalDuration = 1.
Proof. Admitted.

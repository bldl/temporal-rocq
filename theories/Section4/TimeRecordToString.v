From Stdlib Require Import
  ZArith
  Strings.String
  Lia.
From Temporal Require Import 
  Section4.TimeRecord
  Section13.FormatTimeString
  Section13.PrecisionPrime.
Open Scope Z.

(* 4.5.13 TimeRecordToString *)
Program Definition TimeRecordToString (time : TimeRecord) (precision : Precision') : string :=
  (*>> 1. Let subSecondNanoseconds be time.[[Millisecond]] × 10**6 + time.[[Microsecond]] × 10**3 + time.[[Nanosecond]]. <<*)
  let subSecondNanoseconds := (millisecond time) * 1000000 + (microsecond time) * 1000 + (nanosecond time) in 
  (*>> 2. Return FormatTimeString(time.[[Hour]], time.[[Minute]], time.[[Second]], subSecondNanoseconds, precision). <<*)
  FormatTimeString (hour time) (minute time) (second time) subSecondNanoseconds precision None (hour_valid time) (minute_valid time) (second_valid time) _.

Next Obligation.
  split.
  - apply Z.add_nonneg_nonneg.
    apply Z.add_nonneg_nonneg.
    apply Z.mul_nonneg_nonneg.
    apply (proj1 (millisecond_valid time)).
    easy.
    apply Z.mul_nonneg_nonneg.
    apply (proj1 (microsecond_valid time)).
    easy.
    apply (proj1 (nanosecond_valid time)).
  - destruct (millisecond_valid time).
    destruct (microsecond_valid time).
    destruct (nanosecond_valid time).
    lia.
Qed.

From Stdlib Require Import ZArith.
From Temporal Require Import
  Section3.ISODateRecord
  Section4.TimeRecord
  Section5.ISODateTimeRecord.
Open Scope Z.

(* 5.5.3 CombineISODateAndTimeRecord *)
Program Definition CombineISODateAndTimeRecord (isoDate : ISODateRecord) (time : TimeRecord) : ISODateTimeRecord :=
  (*>> 1. NOTE: time.[[Days]] is ignored. <<*)
  (*>> 2. Return ISO Date-Time Record { [[ISODate]]: isoDate, [[Time]]: time }. <<*)
  mkISODateTimeRecord isoDate _ time _.

Next Obligation. Proof. exact (ISODateRecord_IsValidISODate isoDate). Qed.
Next Obligation. Proof. exact (TimeRecord_IsValidTime time). Qed.

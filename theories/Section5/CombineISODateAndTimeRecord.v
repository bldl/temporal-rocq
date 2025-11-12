From Stdlib Require Import ZArith.
From Temporal Require Import
  Section3.ISODateRecord
  Section4.TimeRecord
  Section5.ISODateTimeRecord.
Open Scope Z.

(* 5.5.3 CombineISODateAndTimeRecord *)
Definition CombineISODateAndTimeRecord (isoDate : ISODateRecord) (time : TimeRecord) : ISODateTimeRecord :=
  (*>> 1. NOTE: time.[[Days]] is ignored. <<*)
  (*>> 2. Return ISO Date-Time Record { [[ISODate]]: isoDate, [[Time]]: time }. <<*)
  mkISODateTimeRecord
    isoDate (is_valid_ISO_date isoDate)
    time (TimeRecord_IsValidTime time).

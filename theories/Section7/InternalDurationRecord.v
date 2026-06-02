From Stdlib Require Import ZArith.
From Temporal Require Import
  Section7.DateDurationRecord
  Section7.MaxTimeDuration.

(* 7.5.3 Internal Duration Records *)
Record InternalDurationRecord := 
  mkInternalDurationRecord {
    (*>> Field Name | Value                  | Meaning <<*)
    (*>> [[Date]]   | a Date Duration Record | The date portion of the duration. <<*)
    Date : DateDurationRecord;
    (*>> [[Time]]   | a time duration        | The date portion of the duration. <<*)
    Time : Z;
    Time_valid : MinTimeDuration <= Time <= MaxTimeDuration;
  }.

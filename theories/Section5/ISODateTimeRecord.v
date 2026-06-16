From Stdlib Require Import ZArith.
From Temporal Require Import
  Section3.ISODateRecord
  Section3.IsValidISODate
  Section4.IsValidTime
  Section4.TimeRecord.
Open Scope Z.

(* 5.5.1 ISO Date-Time Records *)
(*>> For any ISO Date-Time Record r,
  IsValidISODate(r.[[ISODate]].[[Year]], r.[[ISODate]][[Month]], r.[[ISODate]].[[Day]]) must return true,
  and IsValidTime(r.[[Time]].[[Hour]], r.[[Time]].[[Minute]], r.[[Time]].[[Second]], r.[[Time]].[[Millisecond]], r.[[Time]].[[Microsecond]], r.[[Time]].[[Nanosecond]]) must return true.
<<*)
Record ISODateTimeRecord := 
mkISODateTimeRecord {
  (*>> Field Name  | Value              | Meaning <<*)
  (*>> [[ISODate]] | an ISO Date Record | The date in the ISO 8601 calendar. <<*)
  ISODate : ISODateRecord;
  (*>> [[Time]]    | a Time Record      | The time. The [[Days]] field is ignored. <<*)
  Time : TimeRecord;

  ISODate_valid : IsValidISODate (Year ISODate) (Month ISODate) (Day ISODate) = true;
  Time_valid : IsValidTime (Hour Time) (Minute Time) (Second Time) (Millisecond Time) (Microsecond Time) (Nanosecond Time) = true;
  }.

From Temporal Require Import Sec4Def Sec3Def.

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
  ISODate_valid : IsValidISODate (year ISODate) (month ISODate) (day ISODate) = true;
  (*>> [[Time]]    | a Time Record      | The time. The [[Days]] field is ignored. <<*)
  Time : TimeRecord;
  Time_valid : IsValidTime (hour Time) (minute Time) (second Time) (millisecond Time) (microsecond Time) (nanosecond Time) = true;
  }.

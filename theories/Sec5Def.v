From Stdlib Require Import ZArith Strings.String Lia.
From Temporal Require Import Basic Sec3Def Sec3Thm Sec4Def Sec4Thm Sec12Def Sec13Def StringUtil.
Open Scope bool_scope.
Open Scope string_scope.
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
  ISODate_valid : IsValidISODate (year ISODate) (month ISODate) (day ISODate) = true;
  (*>> [[Time]]    | a Time Record      | The time. The [[Days]] field is ignored. <<*)
  Time : TimeRecord;
  Time_valid : IsValidTime (hour Time) (minute Time) (second Time) (millisecond Time) (microsecond Time) (nanosecond Time) = true;
  }.

(* 5.5.3 CombineISODateAndTimeRecord *)
Program Definition CombineISODateAndTimeRecord (isoDate : ISODateRecord) (time : TimeRecord) : ISODateTimeRecord :=
  (*>> 1. NOTE: time.[[Days]] is ignored. <<*)
  (*>> 2. Return ISO Date-Time Record { [[ISODate]]: isoDate, [[Time]]: time }. <<*)
  mkISODateTimeRecord isoDate _ time _.

Next Obligation. Proof. exact (ISODateRecord_IsValidISODate isoDate). Qed.
Next Obligation. Proof. exact (TimeRecord_IsValidTime time). Qed.

(* 5.5.10 CompareISODateTime *)
Definition CompareISODateTime (isoDateTime1 isoDateTime2 : ISODateTimeRecord) : Z :=
  (*>> 1. Let dateResult be CompareISODate(isoDateTime1.[[ISODate]], isoDateTime2.[[ISODate]]). <<*)
  let dateResult := CompareISODate (ISODate isoDateTime1) (ISODate isoDateTime2) in
  (*>> 2. If dateResult ≠ 0, return dateResult. <<*)
  if dateResult !=? 0 then dateResult
  (*>> 3. Return CompareTimeRecord(isoDateTime1.[[Time]], isoDateTime2.[[Time]]). <<*)
  else CompareTimeRecord (Time isoDateTime1) (Time isoDateTime2).

(* 5.5.9 ISODateTimeToString *)
Program Definition ISODateTimeToString (isoDateTime : ISODateTimeRecord) (calendar : CalendarType) (precision' : Precision') (showCalendar : ShowCalendar) :=
(*>> 1. Let yearString be PadISOYear(isoDateTime.[[ISODate]].[[Year]]). <<*)
  let yearString := PadISOYear (year (ISODate isoDateTime)) in
  (*>> 2. Let monthString be ToZeroPaddedDecimalString(isoDateTime.[[ISODate]].[[Month]], 2). <<*)
  let monthString := ToZeroPaddedDecimalString (month (ISODate isoDateTime)) 2 _ zero_le_two in
  (*>> 3. Let dayString be ToZeroPaddedDecimalString(isoDateTime.[[ISODate]].[[Day]], 2). <<*)
  let dayString := ToZeroPaddedDecimalString (day (ISODate isoDateTime)) 2 _ zero_le_two in
  (*>> 4. Let subSecondNanoseconds be isoDateTime.[[Time]].[[Millisecond]] × 10**6 + isoDateTime.[[Time]].[[Microsecond]] × 10**3 + isoDateTime.[[Time]].[[Nanosecond]]. <<*)
  let subSecondNanoseconds := (millisecond (Time isoDateTime)) * 1000000 + (microsecond (Time isoDateTime)) * 1000 + (nanosecond (Time isoDateTime)) in 
  (*>> 5. Let timeString be FormatTimeString(isoDateTime.[[Time]].[[Hour]], isoDateTime.[[Time]].[[Minute]], isoDateTime.[[Time]].[[Second]], subSecondNanoseconds, precision). <<*)
  let timeString := FormatTimeString (hour (Time isoDateTime)) (minute (Time isoDateTime)) (second (Time isoDateTime)) subSecondNanoseconds precision' None _ _ _ _ in
  (*>> 6. Let calendarString be FormatCalendarAnnotation(calendar, showCalendar). <<*)
  let calendarString := FormatCalendarAnnotation calendar showCalendar in
  (*>> 7. Return the string-concatenation of yearString, the code unit 0x002D (HYPHEN-MINUS), monthString, the code unit 0x002D (HYPHEN-MINUS), dayString, 0x0054 (LATIN CAPITAL LETTER T), timeString, and calendarString. <<*)
  yearString ++ "-" ++ monthString ++ "-" ++ dayString ++ "T" ++ timeString ++ calendarString.

Next Obligation.
  destruct isoDateTime.
  destruct ISODate0.
  simpl.
  lia.
Qed.
Next Obligation.
  destruct isoDateTime.
  destruct ISODate0.
  simpl.
  lia.
Qed.
Next Obligation.
  destruct isoDateTime.
  destruct Time0.
  simpl.
  lia.
Qed.
Next Obligation.
  destruct isoDateTime.
  destruct Time0.
  simpl.
  lia.
Qed.
Next Obligation.
  destruct isoDateTime.
  destruct Time0.
  simpl.
  lia.
Qed.
Next Obligation.
  destruct isoDateTime.
  destruct Time0.
  simpl.
  lia.
Qed.


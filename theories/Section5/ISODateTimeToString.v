From Stdlib Require Import
  ZArith
  Strings.String
  Lia.
From Temporal Require Import 
  Basic
  StringUtil
  Section3.ISODateRecord
  Section3.PadISOYear
  Section4.TimeRecord
  Section5.ISODateTimeRecord
  Section12.CalendarType
  Section12.FormatCalendarAnnotation
  Section12.ShowCalendar
  Section13.FormatTimeString
  Section13.PrecisionPrime.
Open Scope string_scope.
Open Scope Z.

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

Next Obligation. destruct isoDateTime. destruct ISODate. simpl. lia. Qed.
Next Obligation. destruct isoDateTime. destruct ISODate. simpl. lia. Qed.
Next Obligation. destruct isoDateTime. destruct Time. simpl. lia. Qed.
Next Obligation. destruct isoDateTime. destruct Time. simpl. lia. Qed.
Next Obligation. destruct isoDateTime. destruct Time. simpl. lia. Qed.
Next Obligation. destruct isoDateTime. destruct Time. simpl. lia. Qed.

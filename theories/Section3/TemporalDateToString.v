From Stdlib Require Import ZArith Strings.String.
From Temporal Require Import
  StringUtil
  Grammar
  Section3.ISODateRecord
  Section3.PadISOYear
  Section3.PlainDate
  Section12.FormatCalendarAnnotation
  Section12.ShowCalendar.
From Temporal Require RFC3339.
Open Scope Z.

(* 3.5.10 TemporalDateToString *)
Program Definition TemporalDateToString (temporalDate : PlainDate) (showCalendar : ShowCalendar) : string :=
  (*>> 1. Let year be PadISOYear(temporalDate.[[ISODate]].[[Year]]). <<*)
  let year := PadISOYear (year (isoDate temporalDate)) in
  (*>> 2. Let month be ToZeroPaddedDecimalString(temporalDate.[[ISODate]].[[Month]], 2). <<*)
  let month := ToZeroPaddedDecimalString (month (isoDate temporalDate)) 2 _ _ in
  (*>> 3. Let day be ToZeroPaddedDecimalString(temporalDate.[[ISODate]].[[Day]], 2). <<*)
  let day := ToZeroPaddedDecimalString (day (isoDate temporalDate)) 2 _ _ in
  (*>> 4. Let calendar be FormatCalendarAnnotation(temporalDate.[[Calendar]], showCalendar). <<*)
  let calendar := FormatCalendarAnnotation (calendar temporalDate) showCalendar in
  (*>> 5. Return the string-concatenation of year, the code unit 0x002D (HYPHEN-MINUS), month, the code unit 0x002D (HYPHEN-MINUS), day, and calendar. <<*)
  year ++ "-" ++ month ++ "-" ++ day ++ calendar.

Next Obligation.
  apply Z.le_trans with (m := 1).
  easy.
  destruct (month_valid (isoDate temporalDate)). 
  assumption.
Qed.

Next Obligation.
  apply Z.le_trans with (m := 1).
  easy.
  destruct (day_valid (isoDate temporalDate)).
  assumption.
Qed.

Theorem TemporalDateToString_without_calendar_satisfies_rfc3339 :
  forall temporalDate, 0 <= year (PlainDate.isoDate temporalDate) <= 9999 ->
  generates RFC3339.full_date (TemporalDateToString temporalDate SC_NEVER).
Proof.
  intros.
  unfold TemporalDateToString.
  repeat (apply gen_seq).
  - apply PadISOYear_satisfies_rfc3339.
    assumption.
  - constructor.
  - apply ToZeroPaddedDecimalString_2_digits.
    destruct temporalDate.
    destruct isoDate.
    destruct month_valid.
    split.
    + apply Z.le_trans with (m := 1).
      easy.
      assumption.
    + apply Z.le_trans with (m := 12).
      assumption.
      easy.
  - constructor.
  - apply ToZeroPaddedDecimalString_2_digits.
    destruct temporalDate.
    destruct isoDate.
    destruct day_valid.
    split.
    + apply Z.le_trans with (m := 1).
      easy.
      assumption.
    + apply Z.le_trans with (m := 31).
      assumption.
      easy.
  - apply FormatCalendarAnnotation_never.
Qed.

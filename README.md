# Temporal Mechanization
Our mission is to prove the correctness of a selection of the functions in the ECMAScript [Temporal Proposal](https://tc39.es/proposal-temporal/).
Note: [Based on our findings](https://github.com/tc39/proposal-temporal/pull/3167), the specification text of the proposal will be updated in the nearest future. Our mechanization is based on a previous version of the specification (the most recent snapshot of which was available on October 16th, 2025).

## Developers
- **Aria Bjørnbakken Eide**
- **Vebjørn Søreide Øiestad**

## Supervisor
- **Mikhail Barash**

## Creating Makefile and Building Project
```
$ rocq makefile -f _CoqProject -o Makefile
$ make
```

or just

```
$ ./build.sh
```

## Mechanized Functions
### Section 3
* [3.5.1 ISO Date Records](theories/Section3/ISODateRecord.v)
* [3.5.2 CreateISODateRecord](theories/Section3/CreateISODateRecord.v)
* [3.5.6 RegulateISODate](theories/Section3/RegulateISODate.v)
* [3.5.7 IsValidISODate](theories/Section3/IsValidISODate.v)
* [3.5.9 PadISOYear](theories/Section3/PadISOYear.v)
* [3.5.10 TemporalDateToString](theories/Section3/TemporalDateToString.v)
* [3.5.12 CompareISODate](theories/Section3/CompareISODate.v)
### Section 4
* [4.5.1 Time Records](theories/Section4/TimeRecord.v)
* [4.5.2 CreateTimeRecord](theories/Section4/CreateTimeRecord.v)
* [4.5.3 MidnightTimeRecord](theories/Section4/MidnightTimeRecord.v)
* [4.5.4 NoonTimeRecord](theories/Section4/NoonTimeRecord.v)
* [4.5.5 DifferenceTime](theories/Section4/DifferenceTime.v)
* [4.5.8 RegulateTime](theories/Section4/RegulateTime.v)
* [4.5.9 IsValidTime](theories/Section4/IsValidTime.v)
* [4.5.10 BalanceTime](theories/Section4/BalanceTime.v)
* [4.5.13 TimeRecordToString](theories/Section4/TimeRecordToString.v)
* [4.5.14 CompareTimeRecord](theories/Section4/CompareTimeRecord.v)
* [4.5.15 AddTime](theories/Section4/AddTime.v)
### Section 5
* [5.5.1 ISO Date-Time Records](theories/Section5/ISODateTimeRecord.v)
* [5.5.3 CombineISODateAndTimeRecord](theories/Section5/CombineISODateAndTimeRecord.v)
* [5.5.9 ISODateTimeToString](theories/Section5/ISODateTimeToString.v)
* [5.5.10 CompareISODateTime](theories/Section5/CompareISODateTime.v)
### Section 7
* [7.5.1 Date Duration Records](theories/Section7/DateDurationRecord.v)
* [7.5.14 DateDurationSign](theories/Section7/DateDurationSign.v)
* [7.5.21 TimeDurationFromComponents](theories/Section7/TimeDurationFromComponents.v)
* [7.5.22 AddTimeDuration](theories/Section7/AddTimeDuration.v)
* [7.5.23 Add24HourDaysToTimeDuration](theories/Section7/Add24HourDaysToTimeDuration.v)
* [7.5.24 AddTimeDurationToEpochNanoseconds](theories/Section7/AddTimeDurationToEpochNanoseconds.v)
* [7.5.25 CompareTimeDuration](theories/Section7/CompareTimeDuration.v)
* [7.5.26 TimeDurationFromEpochNanosecondsDifference](theories/Section7/TimeDurationFromEpochNanosecondsDifference.v)
* [7.5.28 TimeDurationSign](theories/Section7/TimeDurationSign.v)
### Section 8
* [8.5.1 IsValidEpochNanoseconds](theories/Section8/IsValidEpochNanoseconds.v)
* [8.5.4 CompareEpochNanoseconds](theories/Section8/CompareEpochNanoseconds.v)
* [8.5.5 AddInstant](/theories/Section8/AddInstant.v)
### Section 9
* [9.5.1 ISO Year-Month Records](theories/Section9/ISOYearMonthRecord.v)
* [9.5.3 ISOYearMonthWithinLimits](theories/Section9/ISOYearMonthWithinLimits.v)
* [9.5.4 BalanceISOYearMonth](theories/Section9/BalanceISOYearMonth.v)
### Section 11
* [11.1.5 FormatOffsetTimeZoneIdentifier](theories/Section11/FormatOffsetTimeZoneIdentifier.v)
* [11.1.6 FormatUTCOffsetNanoseconds](theories/Section11/FormatUTCOffsetNanoseconds.v)
### Section 12
* [12.1 Calendar Types](theories/Section12/CalendarType.v)
* [12.3.15 FormatCalendarAnnotation](theories/Section12/FormatCalendarAnnotation.v)
* [12.3.17 ISODaysInMonth](theories/Section12/ISODaysInMonth.v)
### Section 13
* [13.2 EpochDaysToEpochMs](theories/Section13/EpochDaysToEpochMs.v)
* [13.3 Date Equations](theories/Section13/DateEquations.v)
* [13.8 NegateRoundingMode](theories/Section13/NegateRoundingMode.v)
* [13.14 ValidateTemporalRoundingIncrement](theories/Section13/ValidateTemporalRoundingIncrement.v)
* [13.16 ToSecondsStringPrecisionRecord](theories/Section13/ToSecondsStringPrecisionRecord.v)
* [13.18 ValidateTemporalUnitValue](theories/Section13/ValidateTemporalUnitValue.v)
* [13.20 LargerOfTwoTemporalUnits](theories/Section13/LargerOfTwoTemporalUnits.v)
* [13.21 IsCalendarUnit](theories/Section13/IsCalendarUnit.v)
* [13.22 TemporalUnitCategory](theories/Section13/TemporalUnitCategory.v)
* [13.23 MaximumTemporalDurationRoundingIncrement](theories/Section13/MaximumTemporalDurationRoundingIncrement.v)
* [13.25 FormatFractionalSeconds](theories/Section13/FormatFractionalSeconds.v)
* [13.26 FormatTimeString](theories/Section13/FormatTimeString.v)
* [13.27 GetUnsignedRoundingMode](theories/Section13/GetUnsignedRoundingMode.v)

## Inconsistencies
* [3.5.1 ISODateRecord_IsValidISODate_not_guaranteed](theories/Section3/ISODateRecord.v)
* [4.5.10 BalanceTime_creates_invalid_TimeRecord](theories/Section4/BalanceTime.v)
* [11.1.5 FormatOffsetTimeZoneIdentifier_hour_outside_bounds_of_FormatTimeString](theories/Section11/FormatOffsetTimeZoneIdentifier.v)
* [11.1.6 FormatUTCOffsetNanoseconds_hour_outside_bounds_of_FormatTimeString](theories/Section11/FormatUTCOffsetNanoseconds.v)

## Other Findings
* [7.5.21 TimeDurationFromComponents_nanoseconds'_outside_bounds_of_MaxTimeDuration](theories/Section7/TimeDurationFromComponents.v)
* [7.5.26 TimeDurationFromEpochNanosecondsDifference_result_outside_bounds_of_MaxTimeDuration](theories/Section7/TimeDurationFromEpochNanosecondsDifference.v)

## Notes
* [5.5.3 CombineISODateAndTimeRecord](theories/Section5/Notes/CombineISODateAndTime.v)

## Theorems
### Proven
* [RegulateISODate_never_throws_on_constrain](theories/Section3/RegulateISODate.v)
* [PadISOYear_result_length_at_least_4](theories/Section3/PadISOYear.v)
* [BalanceTime_IsValidTime](theories/Section4/BalanceTime.v)
* [DateDurationSign_year_sign_dominates](theories/Section7/DateDurationSign.v)
* [CompareISODate_eq_zero](theories/Section3/CompareISODate.v)
* [CompareISODate_eq_implies_eq_zero](theories/Section3/CompareISODate.v)
* [CompareTimeRecord_eq_zero](theories/Section4/CompareTimeRecord.v)
* [AddTime_adding_zero_no_change](theories/Section4/AddTime.v)

### Unproven
* [TemporalDateToString_without_calendar_satisfies_rfc3339](theories/Section3/TemporalDateToString.v)
* [ISODateTimeToString_without_calendar_satisfies_rfc3339](theories/Section5/ISODateTimeToString.v)
* [CompareTimeRecord_eq_implies_eq_zero](theories/Section4/CompareTimeRecord.v)

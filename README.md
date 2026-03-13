# Mechanization of the ECMAScipt (JavaScript) Proposal "Temporal" in Rocq
Our mission is to prove the correctness of a selection of the functions in the ECMAScript [Temporal Proposal](https://tc39.es/proposal-temporal/).

## Changes to Specification
[Based on our findings](https://github.com/tc39/proposal-temporal/pull/3167), the specification text of the proposal has been changed. Our mechanization is now updated without the inconsistencies we found, but there are links to the proofs of the inconsistencies in the [Previous Inconsistencies](#previous-inconsistencies) section below.

## Developers
- **Aria Bjørnbakken Eide** (University of Bergen, Norway)
- **Vebjørn Søreide Øiestad** (University of Bergen, Norway)

## Supervisor
- **Mikhail Barash** (Bergen Language Design Laboratory, University of Bergen, Norway)

## Project Presentations
We have presented the preliminary results of this work at RocqPL @ POPL 2026 ([video](https://www.youtube.com/watch?v=sZpVvyoE36E), [abstract](https://popl26.sigplan.org/details/rocqpl-2026-papers/15/Towards-a-Mechanization-of-the-ECMAScript-JavaScript-Proposal-Temporal-)).

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

|section|title|spec text|mechanization|
|-------|-----|---------|-------------|
|3.5.1|ISO Date Records|[spec](https://tc39.es/proposal-temporal/#sec-temporal-iso-date-records)|[ISODateRecord.v](theories/Section3/ISODateRecord.v)|
|3.5.2|`CreateISODateRecord`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-create-iso-date-record)|[CreateISODateRecord.v](theories/Section3/CreateISODateRecord.v)
|~~3.5.6~~ 3.5.7|`RegulateISODate`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-regulateisodate)|[RegulateISODate.v](theories/Section3/RegulateISODate.v)
|~~3.5.7~~ 3.5.8|`IsValidISODate`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-isvalidisodate)|[IsValidISODate.v](theories/Section3/IsValidISODate.v)
|~~3.5.9~~ 3.5.10|`PadISOYear`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-padisoyear)|[PadISOYear.v](theories/Section3/PadISOYear.v)
|~~3.5.10~~ 3.5.11|`TemporalDateToString`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-temporaldatetostring)|[TemporalDateToString.v](theories/Section3/TemporalDateToString.v)
|~~3.5.12~~ 3.5.13|`CompareISODate`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-compareisodate)|[CompareISODate.v](theories/Section3/CompareISODate.v)


### Section 4
|section|title|spec text|mechanization|
|-------|-----|---------|-------------|
|4.5.1|Time Records|[spec](https://tc39.es/proposal-temporal/#sec-temporal-time-records)|[TimeRecord.v](theories/Section4/TimeRecord.v)
|4.5.2|`CreateTimeRecord`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-createtimerecord)|[CreateTimeRecord.v](theories/Section4/CreateTimeRecord.v)
|4.5.3|`MidnightTimeRecord`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-midnighttimerecord)|[MidnightTimeRecord.v](theories/Section4/MidnightTimeRecord.v)
|4.5.4|`NoonTimeRecord`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-noontimerecord)|[NoonTimeRecord.v](theories/Section4/NoonTimeRecord.v)
|4.5.5|`DifferenceTime`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-differencetime)|[DifferenceTime.v](theories/Section4/DifferenceTime.v)
|4.5.8|`RegulateTime`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-regulatetime)|[RegulateTime.v](theories/Section4/RegulateTime.v)
|4.5.9|`IsValidTime`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-isvalidtime)|[IsValidTime.v](theories/Section4/IsValidTime.v)
|4.5.10|`BalanceTime`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-balancetime)|[BalanceTime.v](theories/Section4/BalanceTime.v)
|4.5.13|`TimeRecordToString`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-timerecordtostring)|[TimeRecordToString.v](theories/Section4/TimeRecordToString.v)
|4.5.14|`CompareTimeRecord`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-comparetimerecord)|[CompareTimeRecord.v](theories/Section4/CompareTimeRecord.v)
|4.5.15|`AddTime`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-addtime)|[AddTime.v](theories/Section4/AddTime.v)

  
### Section 5
|section|title|spec text|mechanization|
|-------|-----|---------|-------------|
|5.5.1|ISO Date-Time Records|[spec](https://tc39.es/proposal-temporal/#sec-temporal-iso-date-time-records)|[ISODateTimeRecord.v](theories/Section5/ISODateTimeRecord.v)
|5.5.3|`CombineISODateAndTimeRecord`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-combineisodateandtimerecord)|[CombineISODateAndTimeRecord.v](theories/Section5/CombineISODateAndTimeRecord.v)
|5.5.9|`ISODateTimeToString`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-isodatetimetostring)|[ISODateTimeToString.v](theories/Section5/ISODateTimeToString.v)
|5.5.10|`CompareISODateTime`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-compareisodatetime)|[CompareISODateTime.v](theories/Section5/CompareISODateTime.v)


### Section 7
|section|title|spec text|mechanization|
|-------|-----|---------|-------------|
|7.5.1|Date Duration Records|[spec](https://tc39.es/proposal-temporal/#sec-temporal-date-duration-records)|[DateDurationRecord.v](theories/Section7/DateDurationRecord.v)
|7.5.14|`DateDurationSign`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-datedurationsign)|[DateDurationSign.v](theories/Section7/DateDurationSign.v)
|7.5.21|`TimeDurationFromComponents`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-timedurationfromcomponents)|[TimeDurationFromComponents.v](theories/Section7/TimeDurationFromComponents.v)
|7.5.22|`AddTimeDuration`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-addtimeduration)|[AddTimeDuration.v](theories/Section7/AddTimeDuration.v)
|7.5.23|`Add24HourDaysToTimeDuration`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-add24hourdaystonormalizedtimeduration)|[Add24HourDaysToTimeDuration.v](theories/Section7/Add24HourDaysToTimeDuration.v)
|7.5.24|`AddTimeDurationToEpochNanoseconds`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-addtimedurationtoepochnanoseconds)|[AddTimeDurationToEpochNanoseconds.v](theories/Section7/AddTimeDurationToEpochNanoseconds.v)
|7.5.25|`CompareTimeDuration`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-comparetimeduration)|[CompareTimeDuration.v](theories/Section7/CompareTimeDuration.v)
|7.5.26| `TimeDurationFromEpochNanosecondsDifference`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-timedurationfromepochnanosecondsdifference)|[TimeDurationFromEpochNanosecondsDifference.v](theories/Section7/TimeDurationFromEpochNanosecondsDifference.v)
|7.5.28|`TimeDurationSign`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-timedurationsign)|[TimeDurationSign.v](theories/Section7/TimeDurationSign.v)

### Section 8
|section|title|spec text|mechanization|
|-------|-----|---------|-------------|
|8.5.1|`IsValidEpochNanoseconds`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-isvalidepochnanoseconds)|[IsValidEpochNanoseconds.v](theories/Section8/IsValidEpochNanoseconds.v)
|8.5.4|`CompareEpochNanoseconds`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-compareepochnanoseconds)|[CompareEpochNanoseconds.v](theories/Section8/CompareEpochNanoseconds.v)
|8.5.5|`AddInstant`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-addinstant)|[AddInstant.v](/theories/Section8/AddInstant.v)

### Section 9
|section|title|spec text|mechanization|
|-------|-----|---------|-------------|
|9.5.1|ISO Year-Month Records|[spec](https://tc39.es/proposal-temporal/#sec-temporal-iso-year-month-records)|[ISOYearMonthRecord.v](theories/Section9/ISOYearMonthRecord.v)
|9.5.3|`ISOYearMonthWithinLimits`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-isoyearmonthwithinlimits)|[ISOYearMonthWithinLimits.v](theories/Section9/ISOYearMonthWithinLimits.v)
|9.5.4|`BalanceISOYearMonth`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-balanceisoyearmonth)|[BalanceISOYearMonth.v](theories/Section9/BalanceISOYearMonth.v)

### Section 11
|section|title|spec text|mechanization|
|-------|-----|---------|-------------|
|11.1.5|`FormatOffsetTimeZoneIdentifier`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-formatoffsettimezoneidentifier)|[FormatOffsetTimeZoneIdentifier.v](theories/Section11/FormatOffsetTimeZoneIdentifier.v)
|11.1.6|`FormatUTCOffsetNanoseconds`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-formatutcoffsetnanoseconds)|[FormatUTCOffsetNanoseconds.v](theories/Section11/FormatUTCOffsetNanoseconds.v)

### Section 12
|section|title|spec text|mechanization|
|-------|-----|---------|-------------|
|12.1|Calendar Types|[spec](https://tc39.es/proposal-temporal/#sec-calendar-types)|[CalendarType.v](theories/Section12/CalendarType.v)
|12.3.15|`FormatCalendarAnnotation`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-formatcalendarannotation)|[FormatCalendarAnnotation.v](theories/Section12/FormatCalendarAnnotation.v)
|12.3.17|`ISODaysInMonth`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-isodaysinmonth)|[ISODaysInMonth.v](theories/Section12/ISODaysInMonth.v)

### Section 13
|section|title|spec text|mechanization|
|-------|-----|---------|-------------|
|13.2|`EpochDaysToEpochMs`|[spec](https://tc39.es/proposal-temporal/#sec-epochdaystoepochms)|[EpochDaysToEpochMs.v](theories/Section13/EpochDaysToEpochMs.v)
|13.3|Date Equations|[spec](https://tc39.es/proposal-temporal/#sec-date-equations)|[DateEquations.v](theories/Section13/DateEquations.v)
|13.8|`NegateRoundingMode`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-negateroundingmode)|[NegateRoundingMode.v](theories/Section13/NegateRoundingMode.v)
|13.14|`ValidateTemporalRoundingIncrement`|[spec](https://tc39.es/proposal-temporal/#sec-validatetemporalroundingincrement)|[ValidateTemporalRoundingIncrement.v](theories/Section13/ValidateTemporalRoundingIncrement.v)
|13.16|`ToSecondsStringPrecisionRecord`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-tosecondsstringprecisionrecord)|[ToSecondsStringPrecisionRecord.v](theories/Section13/ToSecondsStringPrecisionRecord.v)
|13.18|`ValidateTemporalUnitValue`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-validatetemporalunitvaluedoption)|[ValidateTemporalUnitValue.v](theories/Section13/ValidateTemporalUnitValue.v)
|13.20|`LargerOfTwoTemporalUnits`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-largeroftwotemporalunits)|[LargerOfTwoTemporalUnits.v](theories/Section13/LargerOfTwoTemporalUnits.v)
|13.21|`IsCalendarUnit`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-iscalendarunit)|[IsCalendarUnit.v](theories/Section13/IsCalendarUnit.v)
|13.22|`TemporalUnitCategory`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-temporalunitcategory)|[TemporalUnitCategory.v](theories/Section13/TemporalUnitCategory.v)
|13.23| `MaximumTemporalDurationRoundingIncrement`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-maximumtemporaldurationroundingincrement)|[MaximumTemporalDurationRoundingIncrement.v](theories/Section13/MaximumTemporalDurationRoundingIncrement.v)
|13.25|`FormatFractionalSeconds`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-formatfractionalseconds)|[FormatFractionalSeconds.v](theories/Section13/FormatFractionalSeconds.v)
|13.26|`FormatTimeString`|[spec](https://tc39.es/proposal-temporal/#sec-temporal-formattimestring)|[FormatTimeString.v](theories/Section13/FormatTimeString.v)
|13.27|`GetUnsignedRoundingMode`|[spec](https://tc39.es/proposal-temporal/#sec-getunsignedroundingmode)|[GetUnsignedRoundingMode.v](theories/Section13/GetUnsignedRoundingMode.v)


## Previous Inconsistencies
* [3.5.1 ISODateRecord_IsValidISODate_not_guaranteed](https://github.com/bldl/temporal-rocq/blob/v0.1.0/theories/Section3/ISODateRecord.v)
* [4.5.10 BalanceTime_creates_invalid_TimeRecord](https://github.com/bldl/temporal-rocq/blob/v0.1.0/theories/Section4/BalanceTime.v)
* [11.1.5 FormatOffsetTimeZoneIdentifier_hour_outside_bounds_of_FormatTimeString](https://github.com/bldl/temporal-rocq/blob/v0.1.0/theories/Section11/FormatOffsetTimeZoneIdentifier.v)
* [11.1.6 FormatUTCOffsetNanoseconds_hour_outside_bounds_of_FormatTimeString](https://github.com/bldl/temporal-rocq/blob/v0.1.0/theories/Section11/FormatUTCOffsetNanoseconds.v)

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

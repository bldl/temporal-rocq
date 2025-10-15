# INF319 Temporal Mechanisation
Our mission is to prove the correctness of a selection of the functions in the Ecmascript Temporal Proposal.

## Developers
- Aria Bjørnbakken Eide
- Vebjørn Søreide Øiestad


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
* [3.5.12 CompareISODate](theories/Section3/CompareISODate.v)
### Section 4
* [4.5.1 Time Records](theories/Section4/TimeRecord.v)
* [4.5.2 CreateTimeRecord](theories/Section4/CreateTimeRecord.v)
* [4.5.3 MidnightTimeRecord](theories/Section4/MidnightTimeRecord.v)
* [4.5.4 NoonTimeRecord](theories/Section4/NoonTimeRecord.v)
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
* [13.20 LargerOfTwoTemporalUnits](theories/Section13/LargerOfTwoTemporalUnits.v)
* [13.21 IsCalendarUnit](theories/Section13/IsCalendarUnit.v)
* [13.22 TemporalUnitCategory](theories/Section13/TemporalUnitCategory.v)
* [13.23 MaximumTemporalDurationRoundingIncrement](theories/Section13/MaximumTemporalDurationRoundingIncrement.v)
* [13.25 FormatFractionalSeconds](theories/Section13/FormatFractionalSeconds.v)
* [13.26 FormatTimeString](theories/Section13/FormatTimeString.v)
* [13.27 GetUnsignedRoundingMode](theories/Section13/GetUnsignedRoundingMode.v)

## Inconsistencies
* [3.5.1 ISO Date Records](theories/Section3/ISODateRecord.v) (Implied consistent, but not explicit)
* [4.5.10 BalanceTime](theories/Section4/BalanceTime.v)
* [7.5.21 TimeDurationFromComponents](theories/Section7/TimeDurationFromComponents.v)
* [7.5.26 TimeDurationFromEpochNanosecondsDifference](theories/Section7/TimeDurationFromEpochNanosecondsDifference.v)
* [11.1.5 FormatOffsetTimeZoneIdentifier](theories/Section11/FormatOffsetTimeZoneIdentifier.v)
* [11.1.6 FormatUTCOffsetNanoseconds](theories/Section11/FormatUTCOffsetNanoseconds.v)

## Notes
* [5.5.3 CombineISODateAndTimeRecord](theories/Section5/Notes/CombineISODateAndTime.v)

## Theorems
### Proven
* [RegulateISODate_never_throws_on_constrain](theories/Section3/RegulateISODate.v)

### Unproven
* [PadISOYear_result_length_at_least_4](theories/Section3/PadISOYear.v)
* [BalanceTime_is_consistent_when_inputs_are_nonnegative](theories/Section4/BalanceTime.v)

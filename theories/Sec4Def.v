Require Import ZArith.
Open Scope bool_scope.
Open Scope Z.

(* 4.5.1 Time Records *)
(*>> For any Time Record t, IsValidTime(t.[[Hour]], t.[[Minute]], t.[[Second]], t.[[Millisecond]], t.[[Microsecond]], t.[[Nanosecond]]) must return true. <<*)
Record TimeRecord := 
  mkTimeRecord {
    (*>> Field Name      | Value                                              | Meaning <<*)
    (*>> [[Days]]        | an integer ≥ 0                                     | A number of overflow days. <<*)
    days : Z;
    days_valid : days >= 0;
    (*>> [[Hour]]        | an integer in the inclusive interval from 0 to 23  | The number of the hour. <<*)
    hour : Z;
    hour_valid : 0 <= hour <= 23;
    (*>> [[Minute]]      | an integer in the inclusive interval from 0 to 59  | The number of the minute. <<*)
    minute : Z;
    minute_valid : 0 <= minute <= 59;
    (*>> [[Second]]      | an integer in the inclusive interval from 0 to 59  | The number of the second. <<*)
    second : Z;
    second_valid : 0 <= second <= 59;
    (*>> [[Millisecond]] | an integer in the inclusive interval from 0 to 999 | The number of the millisecond. <<*)
    millisecond : Z;
    millisecond_valid : 0 <= millisecond <= 999;
    (*>> [[Microsecond]] | an integer in the inclusive interval from 0 to 999 | The number of the microsecond. <<*)
    microsecond : Z;
    microsecond_valid : 0 <= microsecond <= 999;
    (*>> [[Nanosecond]]  | an integer in the inclusive interval from 0 to 999 | The number of the nanosecond. <<*)
    nanosecond : Z;
    nanosecond_valid : 0 <= nanosecond <= 999;
  }.

(* 4.5.3 MidnightTimeRecord *)
Program Definition MidnightTimeRecord : TimeRecord :=
  (*>> 1. Return Time Record { [[Days]]: 0, [[Hour]]: 0, [[Minute]]: 0, [[Second]]: 0, [[Millisecond]]: 0, [[Microsecond]]: 0, [[Nanosecond]]: 0  }. <<*)
  mkTimeRecord 0 _ 0 _ 0 _ 0 _ 0 _ 0 _ 0 _.

(* 4.5.4 NoonTimeRecord *)
Program Definition NoonTimeRecord : TimeRecord :=
  (*>> 1. Return Time Record { [[Days]]: 0, [[Hour]]: 12, [[Minute]]: 0, [[Second]]: 0, [[Millisecond]]: 0, [[Microsecond]]: 0, [[Nanosecond]]: 0  }. <<*)
  mkTimeRecord 0 _ 12 _ 0 _ 0 _ 0 _ 0 _ 0 _.

(* 4.5.9 IsValidTime *)
Definition IsValidTime (hour minute second millisecond microsecond nanosecond : Z) : bool :=
  (*>> 1. If hour < 0 or hour > 23, then <<*)
  if (hour <? 0) || (hour >? 23) then
    (*>> a. Return false. <<*)
    false
  (*>> 2. If minute < 0 or minute > 59, then <<*)
  else if (minute <? 0) || (minute >? 59) then
    (*>> a. Return false. <<*)
    false
  (*>> 3. If second < 0 or second > 59, then <<*)
  else if (second <? 0) || (second >? 59) then
    (*>> a. Return false. <<*)
    false
  (*>> 4. If millisecond < 0 or millisecond > 999, then <<*)
  else if (millisecond <? 0) || (millisecond >? 999) then
    (*>> a. Return false. <<*)
    false
  (*>> 5. If microsecond < 0 or microsecond > 999, then <<*)
  else if (microsecond <? 0) || (microsecond >? 999) then
    (*>> a. Return false. <<*)
    false
  (*>> 6. If nanosecond < 0 or nanosecond > 999, then <<*)
  else if (nanosecond <? 0) || (nanosecond >? 999) then
    (*>> a. Return false. <<*)
    false
  (*>> 7. Return true. <<*)
  else true.

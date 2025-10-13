From Stdlib Require Import 
  ZArith 
  Lia.
From Temporal Require Import Section4.IsValidTime.
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

Theorem TimeRecord_IsValidTime :
  forall (t : TimeRecord),
  IsValidTime (hour t) (minute t) (second t) (millisecond t) (microsecond t) (nanosecond t) = true.
Proof.
  intro t.
  destruct t.
  simpl.
  unfold IsValidTime.

  destruct_with_eqn ((hour0 <? 0) || (hour0 >? 23)); try lia.
  destruct_with_eqn ((minute0 <? 0) || (minute0 >? 59)); try lia.
  destruct_with_eqn ((second0 <? 0) || (second0 >? 59)); try lia.
  destruct_with_eqn ((millisecond0 <? 0) || (millisecond0 >? 999)); try lia.
  destruct_with_eqn ((microsecond0 <? 0) || (microsecond0 >? 999)); try lia.
  destruct_with_eqn ((nanosecond0 <? 0) || (nanosecond0 >? 999)); try lia.
Qed.

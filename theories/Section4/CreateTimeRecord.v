From Stdlib Require Import 
  ZArith
  Lia.
From Temporal Require Import
  Basic
  Section4.IsValidTime
  Section4.TimeRecord.
Open Scope bool_scope.
Open Scope Z.

Definition DeltaDaysValid (deltaDays : option Z) : Prop :=
  match deltaDays with 
  | Some dd => dd >= 0
  | None => True
  end.

(*>> 4.5.2 CreateTimeRecord <<*)
Program Definition CreateTimeRecord (hour minute second millisecond microsecond nanosecond : Z) (deltaDays : option Z) 
  (hour_valid : 0 <= hour <= 23) (minute_valid : 0 <= minute <= 59) (second_valid : 0 <= second <= 59)
  (millisecond_valid : 0 <= millisecond <= 999) (microsecond_valid : 0 <= microsecond <= 999) (nanosecond_valid : 0 <= nanosecond <= 999)
    : TimeRecord := 
  (*>> 1. If deltaDays is not present, set deltaDays to 0. <<*)
  let deltaDays' := 
    match deltaDays with
    | Some value => value
    | None => 0 
    end
  in
  (*>> 2. Assert: IsValidTime(hour, minute, second, millisecond, microsecond, nanosecond). <<*)
  assert IsValidTime hour minute second millisecond microsecond nanosecond = true in
  (*>> 3. Return Time Record { [[Days]]: deltaDays, [[Hour]]: hour, [[Minute]]: minute, [[Second]]: second, [[Millisecond]]: millisecond, [[Microsecond]]: microsecond, [[Nanosecond]]: nanosecond  }. <<*)
  mkTimeRecord deltaDays' hour hour_valid minute minute_valid second second_valid millisecond millisecond_valid microsecond microsecond_valid nanosecond nanosecond_valid.

Next Obligation.
  unfold IsValidTime.
  destruct_with_eqn ((hour <? 0) || (hour >? 23)); try lia.
  destruct_with_eqn ((minute <? 0) || (minute >? 59)); try lia.
  destruct_with_eqn ((second <? 0) || (second >? 59)); try lia.
  destruct_with_eqn ((millisecond <? 0) || (millisecond >? 999)); try lia.
  destruct_with_eqn ((microsecond <? 0) || (microsecond >? 999)); try lia.
  destruct_with_eqn ((nanosecond <? 0) || (nanosecond >? 999)); try lia.
Qed.

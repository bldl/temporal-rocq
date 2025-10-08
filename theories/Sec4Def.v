From Stdlib Require Import Numbers.BinNums Program.Wf ZArith ZArith.Zpow_alt Lia Strings.String Numbers.DecimalString Init.Decimal.
From Temporal Require Import Basic Sec13Def.
Open Scope bool_scope.
Open Scope string_scope.
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

Solve Obligations with easy.

(* 4.5.4 NoonTimeRecord *)
Program Definition NoonTimeRecord : TimeRecord :=
  (*>> 1. Return Time Record { [[Days]]: 0, [[Hour]]: 12, [[Minute]]: 0, [[Second]]: 0, [[Millisecond]]: 0, [[Microsecond]]: 0, [[Nanosecond]]: 0  }. <<*)
  mkTimeRecord 0 _ 12 _ 0 _ 0 _ 0 _ 0 _ 0 _.

Solve Obligations with easy.

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

Definition DeltaDaysValid (deltaDays : option Z) : Prop :=
  match deltaDays with 
  | Some dd => dd >= 0
  | None => True
  end.

(*>> 4.5.2 CreateTimeRecord <<*)
Program Definition CreateTimeRecord (hour minute second millisecond microsecond nanosecond : Z) (deltaDays : option Z) 
  (days_valid : DeltaDaysValid deltaDays)
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
  mkTimeRecord deltaDays' _ hour hour_valid minute minute_valid second second_valid millisecond millisecond_valid microsecond microsecond_valid nanosecond nanosecond_valid.

Next Obligation.
Proof.
  unfold IsValidTime.
  destruct_with_eqn ((hour0 <? 0) || (hour0 >? 23)); try lia.
  destruct_with_eqn ((minute0 <? 0) || (minute0 >? 59)); try lia.
  destruct_with_eqn ((second0 <? 0) || (second0 >? 59)); try lia.
  destruct_with_eqn ((millisecond0 <? 0) || (millisecond0 >? 999)); try lia.
  destruct_with_eqn ((microsecond0 <? 0) || (microsecond0 >? 999)); try lia.
  destruct_with_eqn ((nanosecond0 <? 0) || (nanosecond0 >? 999)); try lia.
Qed.

Next Obligation.
Proof.
  destruct deltaDays.
  unfold DeltaDaysValid in days_valid0.
  assumption.
  easy.
Qed.

Lemma mod_pos_bound (b : Z) (h : 0 < b) : forall a, 0 <= a mod b <= b - 1.
Proof.
  intro a.
  split.
  - exact (proj1 (Z.mod_pos_bound a b h)).
  - apply (Zlt_succ_le (a mod b) (b - 1)).
    rewrite Z.sub_1_r.
    rewrite Z.succ_pred.
    exact (proj2 (Z.mod_pos_bound a b h)).
Qed.

(*>> 4.5.10 BalanceTime <<*)
Program Definition BalanceTime (hour minute second millisecond microsecond nanosecond : Z) : TimeRecord :=
  (*>> 1. Set microsecond to microsecond + floor(nanosecond / 1000). <<*)
  let microsecond' := microsecond + nanosecond / 1000 in
  (*>> 2. Set nanosecond to nanosecond modulo 1000. <<*)
  let nanosecond' := nanosecond mod 1000 in
  (*>> 3. Set millisecond to millisecond + floor(microsecond / 1000). <<*)
  let millisecond' :=  millisecond + microsecond / 1000 in
  (*>> 4. Set microsecond to microsecond modulo 1000. <<*)
  let microsecond'' := microsecond' mod 1000 in
  (*>> 5. Set second to second + floor(millisecond / 1000). <<*)
  let second' := second + millisecond' / 1000 in
  (*>> 6. Set millisecond to millisecond modulo 1000. <<*)
  let millisecond'' := millisecond' mod 1000 in
  (*>> 7. Set minute to minute + floor(second / 60). <<*)
  let minute' := minute + second' / 60 in
  (*>> 8. Set second to second modulo 60. <<*)
  let second'' := second' mod 60 in
  (*>> 9. Set hour to hour + floor(minute / 60). <<*)
  let hour' := hour + minute' / 60 in
  (*>> 10. Set minute to minute modulo 60. <<*)
  let minute'' := minute' mod 60 in
  (*>> 11. Let deltaDays be floor(hour / 24). <<*)
  let deltaDays := hour' / 24 in
  (*>> 12. Set hour to hour modulo 24. <<*)
  let hour'' := hour' mod 24 in
  (*>> 13. Return CreateTimeRecord(hour, minute, second, millisecond, microsecond, nanosecond, deltaDays). <<*)
  CreateTimeRecord hour'' minute'' second'' millisecond'' microsecond'' nanosecond' (Some deltaDays) _ _ _ _ _ _ _.

(* DeltaDaysValid (Some deltaDays) *)
Next Obligation.
Proof.
Admitted.

Next Obligation. Proof. refine (mod_pos_bound 24 _ _). easy. Qed.
Next Obligation. Proof. refine (mod_pos_bound 60 _ _). easy. Qed.
Next Obligation. Proof. refine (mod_pos_bound 60 _ _). easy. Qed.
Next Obligation. Proof. refine (mod_pos_bound 1000 _ _). easy. Qed.
Next Obligation. Proof. refine (mod_pos_bound 1000 _ _). easy. Qed.
Next Obligation. Proof. refine (mod_pos_bound 1000 _ _). easy. Qed.

(* 4.5.14 CompareTimeRecord *)
Definition CompareTimeRecord (time1 time2 : TimeRecord) : Z :=
  (*>> 1. If time1.[[Hour]] > time2.[[Hour]], return 1. <<*)
  if hour time1 >? hour time2 then 1
  (*>> 2. If time1.[[Hour]] < time2.[[Hour]], return -1. <<*)
  else if hour time1 <? hour time2 then -1
  (*>> 3. If time1.[[Minute]] > time2.[[Minute]], return 1. <<*)
  else if minute time1 >? minute time2 then 1
  (*>> 4. If time1.[[Minute]] < time2.[[Minute]], return -1. <<*)
  else if minute time1 <? minute time2 then -1
  (*>> 5. If time1.[[Second]] > time2.[[Second]], return 1. <<*)
  else if second time1 >? second time2 then 1
  (*>> 6. If time1.[[Second]] < time2.[[Second]], return -1. <<*)
  else if second time1 <? second time2 then -1
  (*>> 7. If time1.[[Millisecond]] > time2.[[Millisecond]], return 1. <<*)
  else if millisecond time1 >? millisecond time2 then 1
  (*>> 8. If time1.[[Millisecond]] < time2.[[Millisecond]], return -1. <<*)
  else if millisecond time1 <? millisecond time2 then -1
  (*>> 9. If time1.[[Microsecond]] > time2.[[Microsecond]], return 1. <<*)
  else if microsecond time1 >? microsecond time2 then 1
  (*>> 10. If time1.[[Microsecond]] < time2.[[Microsecond]], return -1. <<*)
  else if microsecond time1 <? microsecond time2 then -1
  (*>> 11. If time1.[[Nanosecond]] > time2.[[Nanosecond]], return 1. <<*)
  else if nanosecond time1 >? nanosecond time2 then 1
  (*>> 12. If time1.[[Nanosecond]] < time2.[[Nanosecond]], return -1. <<*)
  else if nanosecond time1 <? nanosecond time2 then -1
  (*>> 13. Return 0. <<*)
  else 0.

(* 4.5.13 TimeRecordToString *)
Program Definition TimeRecordToString (time : TimeRecord) (precision : Precision') : string :=
  (*>> 1. Let subSecondNanoseconds be time.[[Millisecond]] × 10**6 + time.[[Microsecond]] × 10**3 + time.[[Nanosecond]]. <<*)
  let subSecondNanoseconds := (millisecond time) * 1000000 + (microsecond time) * 1000 + (nanosecond time) in 
  (*>> 2. Return FormatTimeString(time.[[Hour]], time.[[Minute]], time.[[Second]], subSecondNanoseconds, precision). <<*)
  FormatTimeString (hour time) (minute time) (second time) subSecondNanoseconds precision None (hour_valid time) (minute_valid time) (second_valid time) _.

Next Obligation.
  split.
  - apply Z.add_nonneg_nonneg.
    apply Z.add_nonneg_nonneg.
    apply Z.mul_nonneg_nonneg.
    apply (proj1 (millisecond_valid time)).
    easy.
    apply Z.mul_nonneg_nonneg.
    apply (proj1 (microsecond_valid time)).
    easy.
    apply (proj1 (nanosecond_valid time)).
  - destruct (millisecond_valid time).
    destruct (microsecond_valid time).
    destruct (nanosecond_valid time).
    lia.
Qed.

Definition MinTimeDuration : Z := (-9007199254740991999999999).
Definition MaxTimeDuration : Z := 9007199254740991999999999.

(* 4.5.15 AddTime *)
Definition AddTime (time : TimeRecord) (timeDuration : Z) (timeDuration_valid : MinTimeDuration <= timeDuration <= MaxTimeDuration) : TimeRecord :=
  (*>> 1. Return BalanceTime(time.[[Hour]], time.[[Minute]], time.[[Second]], time.[[Millisecond]], time.[[Microsecond]], time.[[Nanosecond]] + timeDuration). <<*)
  BalanceTime (hour time) (minute time) (second time) (millisecond time) (microsecond time) (nanosecond time + timeDuration).
  (*>> 2. NOTE: If using floating points to implement this operation, add the time components separately before balancing to avoid errors with unsafe integers. <<*)

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

Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.

(* 4.5.4 NoonTimeRecord *)
Program Definition NoonTimeRecord : TimeRecord :=
  (*>> 1. Return Time Record { [[Days]]: 0, [[Hour]]: 12, [[Minute]]: 0, [[Second]]: 0, [[Millisecond]]: 0, [[Microsecond]]: 0, [[Nanosecond]]: 0  }. <<*)
  mkTimeRecord 0 _ 12 _ 0 _ 0 _ 0 _ 0 _ 0 _.

Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.

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

Lemma inside_range_outside_range_impossible {a b c : Z} :
  (a <= b <= c) -> ((b <? a) || (b >? c)) = true -> False.
Proof.
  intro a_le_b_le_c.
  destruct a_le_b_le_c as [a_le_b b_le_c].
  intro H.
  apply Bool.Is_true_eq_left in H.
  apply Bool.orb_prop_elim in H.
  destruct H.
  
  (* b <? a *)
  - apply Bool.Is_true_eq_true in H.
    rewrite Z.ltb_lt in H.
    exact (proj2 (Z.nlt_ge b a) a_le_b H).
  
  (* b >? c *)
  - apply Bool.Is_true_eq_true in H.
    rewrite Z.gtb_gt in H.
    apply Z.gt_lt in H.
    exact (proj2 (Z.nlt_ge c b) b_le_c H).
Qed.

Theorem TimeRecord_IsValidTime :
  forall (t : TimeRecord),
  IsValidTime (hour t) (minute t) (second t) (millisecond t) (microsecond t) (nanosecond t) = true.
Proof.
  intro t.
  destruct t.
  simpl.
  unfold IsValidTime.

  1: destruct_with_eqn ((hour0 <? 0) || (hour0 >? 23)).
  2: destruct_with_eqn ((minute0 <? 0) || (minute0 >? 59)).
  3: destruct_with_eqn ((second0 <? 0) || (second0 >? 59)).
  4: destruct_with_eqn ((millisecond0 <? 0) || (millisecond0 >? 999)).
  5: destruct_with_eqn ((microsecond0 <? 0) || (microsecond0 >? 999)).
  6: destruct_with_eqn ((nanosecond0 <? 0) || (nanosecond0 >? 999)).

  - exfalso.
    exact (inside_range_outside_range_impossible hour_valid0 Heqb).
  - exfalso.
    exact (inside_range_outside_range_impossible minute_valid0 Heqb0).
  - exfalso.
    exact (inside_range_outside_range_impossible second_valid0 Heqb1).
  - exfalso.
    exact (inside_range_outside_range_impossible millisecond_valid0 Heqb2).
  - exfalso.
    exact (inside_range_outside_range_impossible microsecond_valid0 Heqb3).
  - exfalso.
    exact (inside_range_outside_range_impossible nanosecond_valid0 Heqb4).

  - reflexivity.
Qed.

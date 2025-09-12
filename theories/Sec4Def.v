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

(* TODO: very tedious proof *)
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

  (* (hour0 <? 0) || (hour0 >? 23) = true -> false = true *)
  - exfalso.
    apply Bool.Is_true_eq_left in Heqb.
    apply Bool.orb_prop_elim in Heqb.
    destruct hour_valid0.
    destruct Heqb.
    + apply Bool.Is_true_eq_true in H1.
      rewrite Z.ltb_lt in H1.
      exact (proj2 (Z.nlt_ge hour0 0) H H1).
    + apply Bool.Is_true_eq_true in H1.
      rewrite Z.gtb_gt in H1.
      apply Z.gt_lt in H1.
      exact (proj2 (Z.nlt_ge 23 hour0) H0 H1).

  (* (minute0 <? 0) || (minute0 >? 59) = true -> false = true *)
  - exfalso.
    apply Bool.Is_true_eq_left in Heqb0.
    apply Bool.orb_prop_elim in Heqb0.
    destruct minute_valid0.
    destruct Heqb0.
    + apply Bool.Is_true_eq_true in H1.
      rewrite Z.ltb_lt in H1.
      exact (proj2 (Z.nlt_ge minute0 0) H H1).
    + apply Bool.Is_true_eq_true in H1.
      rewrite Z.gtb_gt in H1.
      apply Z.gt_lt in H1.
      exact (proj2 (Z.nlt_ge 59 minute0) H0 H1).

  (* (second0 <? 0) || (second0 >? 59) = true -> false = true *)
  - exfalso.
    apply Bool.Is_true_eq_left in Heqb1.
    apply Bool.orb_prop_elim in Heqb1.
    destruct second_valid0.
    destruct Heqb1.
    + apply Bool.Is_true_eq_true in H1.
      rewrite Z.ltb_lt in H1.
      exact (proj2 (Z.nlt_ge second0 0) H H1).
    + apply Bool.Is_true_eq_true in H1.
      rewrite Z.gtb_gt in H1.
      apply Z.gt_lt in H1.
      exact (proj2 (Z.nlt_ge 59 second0) H0 H1).

  (* (millisecond0 <? 0) || (millisecond0 >? 999) = true -> false = true *)
  - exfalso.
    apply Bool.Is_true_eq_left in Heqb2.
    apply Bool.orb_prop_elim in Heqb2.
    destruct millisecond_valid0.
    destruct Heqb2.
    + apply Bool.Is_true_eq_true in H1.
      rewrite Z.ltb_lt in H1.
      exact (proj2 (Z.nlt_ge millisecond0 0) H H1).
    + apply Bool.Is_true_eq_true in H1.
      rewrite Z.gtb_gt in H1.
      apply Z.gt_lt in H1.
      exact (proj2 (Z.nlt_ge 999 millisecond0) H0 H1).

  (* (microsecond0 <? 0) || (microsecond0 >? 999) = true -> false = true *)
  - exfalso.
    apply Bool.Is_true_eq_left in Heqb3.
    apply Bool.orb_prop_elim in Heqb3.
    destruct microsecond_valid0.
    destruct Heqb3.
    + apply Bool.Is_true_eq_true in H1.
      rewrite Z.ltb_lt in H1.
      exact (proj2 (Z.nlt_ge microsecond0 0) H H1).
    + apply Bool.Is_true_eq_true in H1.
      rewrite Z.gtb_gt in H1.
      apply Z.gt_lt in H1.
      exact (proj2 (Z.nlt_ge 999 microsecond0) H0 H1).

  (* (nanosecond0 <? 0) || (nanosecond0 >? 999) = true -> false = true *)
  - exfalso.
    apply Bool.Is_true_eq_left in Heqb4.
    apply Bool.orb_prop_elim in Heqb4.
    destruct nanosecond_valid0.
    destruct Heqb4.
    + apply Bool.Is_true_eq_true in H1.
      rewrite Z.ltb_lt in H1.
      exact (proj2 (Z.nlt_ge nanosecond0 0) H H1).
    + apply Bool.Is_true_eq_true in H1.
      rewrite Z.gtb_gt in H1.
      apply Z.gt_lt in H1.
      exact (proj2 (Z.nlt_ge 999 nanosecond0) H0 H1).
  
  (* true = true *)
  - reflexivity.
Qed.
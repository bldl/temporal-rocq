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
    (*>> [[Days]]        | an integer                                         | A number of overflow days. <<*)
    Days : Z;
    (*>> [[Hour]]        | an integer in the inclusive interval from 0 to 23  | The number of the hour. <<*)
    Hour : Z;
    (*>> [[Minute]]      | an integer in the inclusive interval from 0 to 59  | The number of the minute. <<*)
    Minute : Z;
    (*>> [[Second]]      | an integer in the inclusive interval from 0 to 59  | The number of the second. <<*)
    Second : Z;
    (*>> [[Millisecond]] | an integer in the inclusive interval from 0 to 999 | The number of the millisecond. <<*)
    Millisecond : Z;
    (*>> [[Microsecond]] | an integer in the inclusive interval from 0 to 999 | The number of the microsecond. <<*)
    Microsecond : Z;
    (*>> [[Nanosecond]]  | an integer in the inclusive interval from 0 to 999 | The number of the nanosecond. <<*)
    Nanosecond : Z;

    hour_valid : 0 <= Hour <= 23;
    minute_valid : 0 <= Minute <= 59;
    second_valid : 0 <= Second <= 59;
    millisecond_valid : 0 <= Millisecond <= 999;
    microsecond_valid : 0 <= Microsecond <= 999;
    nanosecond_valid : 0 <= Nanosecond <= 999;
  }.

Lemma TimeRecord_IsValidTime :
  forall (t : TimeRecord),
  IsValidTime (Hour t) (Minute t) (Second t) (Millisecond t) (Microsecond t) (Nanosecond t) = true.
Proof.
  intro t.
  destruct t.
  simpl.
  unfold IsValidTime.

  destruct_with_eqn ((Hour0 <? 0) || (Hour0 >? 23)); try lia.
  destruct_with_eqn ((Minute0 <? 0) || (Minute0 >? 59)); try lia.
  destruct_with_eqn ((Second0 <? 0) || (Second0 >? 59)); try lia.
  destruct_with_eqn ((Millisecond0 <? 0) || (Millisecond0 >? 999)); try lia.
  destruct_with_eqn ((Microsecond0 <? 0) || (Microsecond0 >? 999)); try lia.
  destruct_with_eqn ((Nanosecond0 <? 0) || (Nanosecond0 >? 999)); try lia.
Qed.

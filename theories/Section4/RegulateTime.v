From Stdlib Require Import
  ZArith
  Lia.
From Temporal Require Import 
  Basic
  Section4.CreateTimeRecord
  Section4.IsValidTime
  Section4.TimeRecord.
Open Scope Z.

Inductive Overflow := CONSTRAIN | REJECT.

(* 4.5.8 RegulateTime *)
Program Definition RegulateTime (hour minute second millisecond microsecond nanosecond : Z) 
  (overflow : Overflow) : Completion TimeRecord :=
  (*>> 1. If overflow is constrain, then <<*)
  match overflow with
  | CONSTRAIN =>
    (*>> a. Set hour to the result of clamping hour between 0 and 23. <<*)
    let hour' := Clamp 0 23 hour _ in
    (*>> b. Set minute to the result of clamping minute between 0 and 59. <<*)
    let minute' := Clamp 0 59 minute _ in
    (*>> c. Set second to the result of clamping second between 0 and 59. <<*)
    let second' := Clamp 0 59 second _ in
    (*>> d. Set millisecond to the result of clamping millisecond between 0 and 999. <<*)
    let millisecond' := Clamp 0 999 millisecond _ in
    (*>> e. Set microsecond to the result of clamping microsecond between 0 and 999. <<*)
    let microsecond' := Clamp 0 999 microsecond _ in
    (*>> f. Set nanosecond to the result of clamping nanosecond between 0 and 999. <<*)
    let nanosecond' := Clamp 0 999 nanosecond _ in
    (*>> 3. Return CreateTimeRecord(hour, minute, second, millisecond, microsecond, nanosecond). <<*)
    Normal (CreateTimeRecord hour' minute' second' millisecond' microsecond' nanosecond' None _ _ _ _ _ _ _)
  (*>> 2. Else, <<*)
  | _ =>
    (*>> a. Assert: overflow is reject. <<*)
    assert (overflow = REJECT) in
    (*>> b. If IsValidTime(hour, minute, second, millisecond, microsecond, nanosecond) is false, throw a RangeError exception. <<*)
    match IsValidTime hour minute second millisecond microsecond nanosecond with
    | false => Throw RangeError
    (*>> 3. Return CreateTimeRecord(hour, minute, second, millisecond, microsecond, nanosecond). <<*)
    | true => Normal (CreateTimeRecord hour minute second millisecond microsecond nanosecond None _ _ _ _ _ _ _)
    end
  end.

Next Obligation. apply clamp_between_lower_and_upper. Qed.
Next Obligation. apply clamp_between_lower_and_upper. Qed.
Next Obligation. apply clamp_between_lower_and_upper. Qed.
Next Obligation. apply clamp_between_lower_and_upper. Qed.
Next Obligation. apply clamp_between_lower_and_upper. Qed.
Next Obligation. apply clamp_between_lower_and_upper. Qed.
Next Obligation. destruct overflow. easy. easy. Qed.
Next Obligation.
  unfold IsValidTime in Heq_anonymous.
  destruct ((hour <? 0) || (hour >? 23)) eqn:H in Heq_anonymous; lia.
Qed.
Next Obligation.
  unfold IsValidTime in Heq_anonymous.
  destruct ((hour <? 0) || (hour >? 23)) eqn:H in Heq_anonymous.
  easy.
  destruct ((minute <? 0) || (minute >? 59)) eqn:H1 in Heq_anonymous; lia.
Qed.
Next Obligation.
  unfold IsValidTime in Heq_anonymous.
  destruct ((hour <? 0) || (hour >? 23)) eqn:H in Heq_anonymous.
  easy.
  destruct ((minute <? 0) || (minute >? 59)) eqn:H1 in Heq_anonymous.
  easy.
  destruct ((second <? 0) || (second >? 59)) eqn:H2 in Heq_anonymous; lia.
Qed.
Next Obligation.
  unfold IsValidTime in Heq_anonymous.
  destruct ((hour <? 0) || (hour >? 23)) eqn:H in Heq_anonymous.
  easy.
  destruct ((minute <? 0) || (minute >? 59)) eqn:H1 in Heq_anonymous.
  easy.
  destruct ((second <? 0) || (second >? 59)) eqn:H2 in Heq_anonymous.
  easy.
  destruct ((millisecond <? 0) || (millisecond >? 999)) eqn:H3 in Heq_anonymous; lia.
Qed.
Next Obligation.
  unfold IsValidTime in Heq_anonymous.
  destruct ((hour <? 0) || (hour >? 23)) eqn:H in Heq_anonymous.
  easy.
  destruct ((minute <? 0) || (minute >? 59)) eqn:H1 in Heq_anonymous.
  easy.
  destruct ((second <? 0) || (second >? 59)) eqn:H2 in Heq_anonymous.
  easy.
  destruct ((millisecond <? 0) || (millisecond >? 999)) eqn:H3 in Heq_anonymous.
  easy.
  destruct ((microsecond <? 0) || (microsecond >? 999)) eqn:H4 in Heq_anonymous; lia.
Qed.
Next Obligation.
  unfold IsValidTime in Heq_anonymous.
  destruct ((hour <? 0) || (hour >? 23)) eqn:H in Heq_anonymous.
  easy.
  destruct ((minute <? 0) || (minute >? 59)) eqn:H1 in Heq_anonymous.
  easy.
  destruct ((second <? 0) || (second >? 59)) eqn:H2 in Heq_anonymous.
  easy.
  destruct ((millisecond <? 0) || (millisecond >? 999)) eqn:H3 in Heq_anonymous.
  easy.
  destruct ((microsecond <? 0) || (microsecond >? 999)) eqn:H4 in Heq_anonymous.
  easy.
  destruct ((nanosecond <? 0) || (nanosecond >? 999)) eqn:H5 in Heq_anonymous; lia.
Qed.

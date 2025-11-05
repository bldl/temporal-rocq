From Stdlib Require Import
  Lia
  ZArith
  ZPow.
From Temporal Require Import
  Basic
  Section13.Precision
  Section13.PrecisionPrime.
Open Scope Z.

Inductive SmallestUnit := SU_MINUTE | SU_SECOND | SU_MILLISECOND | SU_MICROSECOND | SU_NANOSECOND | SU_UNSET.
Inductive OutputUnit := OU_MINUTE | OU_SECOND | OU_MILLISECOND | OU_MICROSECOND | OU_NANOSECOND | OU_UNSET.
Inductive Increment := IncrementValue : forall (i : Z), i = 1 \/ i = 10 \/ i = 100 -> Increment.

Record SecondsStringPrecisionRecord :=
  mkSecondsStringPrecisionRecord {
    precision : Precision';
    unit' : OutputUnit;
    increment : Increment;
  }.

(* 13.16 ToSecondsStringPrecisionRecord *)
Program Definition ToSecondsStringPrecisionRecord (smallestUnit : SmallestUnit) (fractionalDigitCount : Precision) : SecondsStringPrecisionRecord :=
  match smallestUnit with
  (*>> 1. If smallestUnit is minute, then <<*)
  | SU_MINUTE =>
    (*>> a. Return the Record { [[Precision]]: minute, [[Unit]]: minute, [[Increment]]: 1  }. <<*)
    mkSecondsStringPrecisionRecord MINUTE_PRECISION OU_MINUTE (IncrementValue 1 _)
  (*>> 2. If smallestUnit is second, then <<*)
  | SU_SECOND =>
    (*>> a. Return the Record { [[Precision]]: 0, [[Unit]]: second, [[Increment]]: 1  }. <<*)
    mkSecondsStringPrecisionRecord (NormalPrecision (PrecisionValue 0 _)) OU_SECOND (IncrementValue 1 _)
  (*>> 3. If smallestUnit is millisecond, then <<*)
  | SU_MILLISECOND =>
    (*>> a. Return the Record { [[Precision]]: 3, [[Unit]]: millisecond, [[Increment]]: 1  }. <<*)
    mkSecondsStringPrecisionRecord (NormalPrecision (PrecisionValue 3 _)) OU_MILLISECOND (IncrementValue 1 _)
  (*>> 4. If smallestUnit is microsecond, then <<*)
  | SU_MICROSECOND =>
    (*>> a. Return the Record { [[Precision]]: 6, [[Unit]]: microsecond, [[Increment]]: 1  }. <<*)
    mkSecondsStringPrecisionRecord (NormalPrecision (PrecisionValue 6 _)) OU_MICROSECOND (IncrementValue 1 _)
  (*>> 5. If smallestUnit is nanosecond, then <<*)
  | SU_NANOSECOND =>
    (*>> a. Return the Record { [[Precision]]: 9, [[Unit]]: nanosecond, [[Increment]]: 1  }. <<*)
    mkSecondsStringPrecisionRecord (NormalPrecision (PrecisionValue 9 _)) OU_NANOSECOND (IncrementValue 1 _)
  (*>> 6. Assert: smallestUnit is unset. <<*)
  | _ => assert smallestUnit = SU_UNSET in
    match fractionalDigitCount with
    (*>> 7. If fractionalDigitCount is auto, then <<*)
    | AUTO =>
      (*>> a. Return the Record { [[Precision]]: auto, [[Unit]]: nanosecond, [[Increment]]: 1  }. <<*)
      mkSecondsStringPrecisionRecord (NormalPrecision (AUTO)) OU_NANOSECOND (IncrementValue 1 _)
    | PrecisionValue p _ =>
      (*>> 8. If fractionalDigitCount = 0, then <<*)
      match p =? 0 with 
        (*>> a. Return the Record { [[Precision]]: 0, [[Unit]]: second, [[Increment]]: 1  }. <<*)
      | true => mkSecondsStringPrecisionRecord (NormalPrecision (PrecisionValue p _)) OU_SECOND (IncrementValue 1 _)
      (*>> 9. If fractionalDigitCount is in the inclusive interval from 1 to 3, then <<*)
      | false => match (1 <=? p) && (p <=? 3) with
        (*>> a. Return the Record { [[Precision]]: fractionalDigitCount, [[Unit]]: millisecond, [[Increment]]: 10**(3 - fractionalDigitCount)  }. <<*)
      | true => mkSecondsStringPrecisionRecord (NormalPrecision (PrecisionValue p _)) OU_MILLISECOND (IncrementValue (10 ^ (3 - p)) _)
      (*>> 10. If fractionalDigitCount is in the inclusive interval from 4 to 6, then <<*)
      | false => match (4 <=? p) && (p <=? 6) with
        (*>> a. Return the Record { [[Precision]]: fractionalDigitCount, [[Unit]]: microsecond, [[Increment]]: 10**(6 - fractionalDigitCount)  }. <<*)
      | true => mkSecondsStringPrecisionRecord (NormalPrecision (PrecisionValue p _)) OU_MICROSECOND (IncrementValue (10 ^ (6 - p)) _)
      (*>> 11. Assert: fractionalDigitCount is in the inclusive interval from 7 to 9. <<*)
      | false => assert (7 <= p <= 9) in
      (*>> 12. Return the Record { [[Precision]]: fractionalDigitCount, [[Unit]]: nanosecond, [[Increment]]: 10**(9 - fractionalDigitCount)  }. <<*)
        mkSecondsStringPrecisionRecord (NormalPrecision (PrecisionValue p _)) OU_NANOSECOND (IncrementValue (10 ^ (9 - p)) _)
      end end end end end.

Next Obligation. easy. Qed.
Next Obligation. easy. Qed.
Next Obligation. easy. Qed.
Next Obligation. easy. Qed.
Next Obligation. destruct smallestUnit; try easy. Qed.
Next Obligation.
  assert (Hp : p = 1 \/ p = 2 \/ p = 3) by lia.
  destruct Hp as [-> | [-> | ->]]; simpl; lia.
Qed.
Next Obligation.
  assert (Hp : p = 4 \/ p = 5 \/ p = 6) by lia.
  destruct Hp as [-> | [-> | ->]]; simpl; lia.
Qed.
Next Obligation. lia. Qed.
Next Obligation.
  assert (Hp : p = 7 \/ p = 8 \/ p = 9) by lia.
  destruct Hp as [-> | [-> | ->]]; simpl; lia.
Qed.
Next Obligation. easy. Qed. 


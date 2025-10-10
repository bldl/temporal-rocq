From Stdlib Require Import List.
From Temporal Require Import Basic Section13.TemporalUnit Section13.TemporalUnitEqb.

Lemma TemporalUnitEqb_neq : forall (u1 u2 : TemporalUnit), TemporalUnitEqb u1 u2 = false -> u1 <> u2.
Proof.
  intros.
  destruct u1.
  destruct u2. all: try easy.
  destruct u2. all: try easy.
  destruct u2. all: try easy.
  destruct u2. all: try easy.
  destruct u2. all: try easy.
  destruct u2. all: try easy.
  destruct u2. all: try easy.
  destruct u2. all: try easy.
  destruct u2. all: try easy.
  destruct u2. all: try easy.
Qed.

Lemma TemporalUnitEqb_sym : forall (u1 u2 : TemporalUnit), TemporalUnitEqb u1 u2 = TemporalUnitEqb u2 u1.
Proof.
  intros.
  destruct u1.
  destruct u2.
  all: easy.
Qed.

Definition TemporalUnits : list TemporalUnit := YEAR :: MONTH :: WEEK :: DAY :: HOUR :: MINUTE :: SECOND :: MILLISECOND :: MICROSECOND :: NANOSECOND :: nil.

Program Fixpoint LargerOfTwoTemporalUnitsHelper (u1 u2 : TemporalUnit) (units : list TemporalUnit)
  (Hin1 : In u1 units) (Hin2 : In u2 units) : TemporalUnit :=
  (*>> 1. For each row of Table 21, except the header row, in table order, do <<*)
  match units with
  (*>> a. Let unit be the value in the "Value" column of the row. <<*)
  | unit' :: units' => 
    (*>> b. If u1 is unit, return unit. <<*)
    match TemporalUnitEqb u1 unit' with
    | true => unit'
    | false =>
    (*>> c. If u2 is unit, return unit. <<*)
    match TemporalUnitEqb u2 unit' with
    | true => unit'
    | false => LargerOfTwoTemporalUnitsHelper u1 u2 units' _ _
    end end
  | nil => impossible
  end.

Next Obligation.
  apply in_inv in Hin1.
  apply not_A_if_A_or_B_then_B in Hin1.
  easy.
  apply TemporalUnitEqb_neq.
  apply eq_sym.
  rewrite TemporalUnitEqb_sym.
  apply Heq_anonymous0.
Qed.

Next Obligation.
  apply in_inv in Hin2.
  apply not_A_if_A_or_B_then_B in Hin2.
  easy.
  apply TemporalUnitEqb_neq.
  apply eq_sym.
  rewrite TemporalUnitEqb_sym.
  apply Heq_anonymous.
Qed.

(* NOTE: Function flow in LargerOfTwoTemporalUnitsHelper *)
(* 13.20 LargerOfTwoTemporalUnits *)
Program Definition LargerOfTwoTemporalUnits (u1 u2 : TemporalUnit) : TemporalUnit :=
  LargerOfTwoTemporalUnitsHelper u1 u2 TemporalUnits _ _.

Next Obligation.
  destruct u1.
  apply or_introl. easy.
  apply or_intror. apply or_introl. easy.
  apply or_intror.
  apply or_intror. apply or_introl. easy.
  apply or_intror. apply or_intror. apply or_intror. apply or_introl. easy.
  apply or_intror. apply or_intror. apply or_intror. apply or_intror. apply or_introl. easy.
  apply or_intror. apply or_intror. apply or_intror. apply or_intror. apply or_intror. 
  apply or_introl. easy.
  apply or_intror. apply or_intror. apply or_intror. apply or_intror. apply or_intror.
  apply or_intror. apply or_introl. easy.
  apply or_intror. apply or_intror. apply or_intror. apply or_intror. apply or_intror.
  apply or_intror. apply or_intror. apply or_introl. easy.
  apply or_intror. apply or_intror. apply or_intror. apply or_intror. apply or_intror.
  apply or_intror. apply or_intror. apply or_intror. apply or_introl. easy.
  apply or_intror. apply or_intror. apply or_intror. apply or_intror. apply or_intror.
  apply or_intror. apply or_intror. apply or_intror. apply or_intror. apply or_introl. easy.
Qed.

Next Obligation.
  destruct u2.
  apply or_introl. easy.
  apply or_intror. apply or_introl. easy.
  apply or_intror. apply or_intror. apply or_introl. easy.
  apply or_intror. apply or_intror. apply or_intror. apply or_introl. easy.
  apply or_intror. apply or_intror. apply or_intror. apply or_intror. apply or_introl. easy.
  apply or_intror. apply or_intror. apply or_intror. apply or_intror. apply or_intror.
  apply or_introl. easy.
  apply or_intror. apply or_intror. apply or_intror. apply or_intror. apply or_intror.
  apply or_intror. apply or_introl. easy.
  apply or_intror. apply or_intror. apply or_intror. apply or_intror. apply or_intror.
  apply or_intror. apply or_intror. apply or_introl. easy.
  apply or_intror. apply or_intror. apply or_intror. apply or_intror. apply or_intror.
  apply or_intror. apply or_intror. apply or_intror. apply or_introl. easy.
  apply or_intror. apply or_intror. apply or_intror. apply or_intror. apply or_intror.
  apply or_intror. apply or_intror. apply or_intror. apply or_intror. apply or_introl. easy.
Qed.

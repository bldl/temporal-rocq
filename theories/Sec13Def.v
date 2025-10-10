From Stdlib Require Import Numbers.BinNums Program.Equality Program.Wf ZArith Lia Strings.String Numbers.DecimalString Init.Decimal List Ascii.
From Temporal Require Import Basic StringUtil Section8.msPerDay.
Open Scope bool_scope.
Open Scope Z.

(* Assumption: 
  EpochDayNumberForYear and msPerDay works on Z and not real numbers *)

(* 13.3 Date Equations *)
(* Note: `/` is floor division with Z. 
  https://rocq-prover.org/doc/V8.21%2Balpha/stdlib/Coq.ZArith.BinIntDef.html#Z.div_eucl *)
(*>> EpochDayNumberForYear(y) = 365 × (y - 1970) + floor((y - 1969) / 4) - floor((y - 1901) / 100) + floor((y - 1601) / 400) <<*)
Definition EpochDayNumberForYear (y : Z) : Z := 365 * (y - 1970) + ((y - 1969) / 4) - ((y - 1901) / 100) + ((y - 1601) / 400).

(*>> EpochTimeForYear(y) = ℝ(msPerDay) × EpochDayNumberForYear(y) <<*)
Definition EpochTimeForYear (y : Z) : Z := msPerDay * EpochDayNumberForYear y.

Lemma EpochDayNumberForYear_monotonic :
  forall y0 y1,
  y0 < y1 -> EpochDayNumberForYear y0 < EpochDayNumberForYear y1.
Proof.
  intros.
  unfold EpochDayNumberForYear.
  rewrite (Z.add_comm).
  rewrite (Z.add_comm _ ((y1 - 1601) / 400)).
  refine (Z.add_le_lt_mono _ _ _ _ _ _).

  (* (y0 - 1601) / 400 <= (y1 - 1601) / 400 *)
  - refine (Z.div_le_mono _ _ 400 ltac:(easy) _).
    rewrite <- Z.sub_le_mono_r.
    apply Z.lt_le_incl.
    assumption.
  
  (* 365 * (y0 - 1970) + (y0 - 1969) / 4 - (y0 - 1901) / 100 <
     365 * (y1 - 1970) + (y1 - 1969) / 4 - (y1 - 1901) / 100 *)
  - rewrite Z.add_sub_swap.
    rewrite Z.add_sub_swap.
    rewrite Z.add_comm.
    rewrite (Z.add_comm _ ((y1 - 1969) / 4)).
    refine (Z.add_le_lt_mono _ _ _ _ _ _).

    (* (y0 - 1969) / 4 <= (y1 - 1969) / 4 *)
    + refine (Z.div_le_mono _ _ 4 ltac:(easy) _).
      rewrite <- Z.sub_le_mono_r.
      exact (Z.lt_le_incl _ _ H).
    
    (* 365 * (y0 - 1970) - (y0 - 1901) / 100 <
       365 * (y0 - 1970) - (y1 - 1901) / 100 *)
    + rewrite <- Z.lt_0_sub.
      rewrite Z.sub_sub_distr.
      rewrite sub_swap.
      rewrite <- Z.mul_sub_distr_l.
      rewrite Z.sub_sub_distr.
      rewrite <- (Z.add_sub_swap _ 1970 _).
      rewrite sub_add_cancel.
      rewrite <- Z.sub_sub_distr.
      rewrite <- (Z.add_opp_l ((y1 - 1901) / 100) _).
      rewrite Z.add_comm.
      rewrite <- Z.div_add.
      rewrite Z.add_comm.
      rewrite Z.mul_opp_l.
      rewrite Z.add_opp_l.
      rewrite div_mul_cancel.
      rewrite Z.sub_sub_distr.
      rewrite sub_swap.
      rewrite Z.sub_sub_distr.
      rewrite Z.add_sub_swap.
      rewrite sub_add_cancel.
      rewrite Z.lt_0_sub.
      rewrite (Z.mul_lt_mono_pos_r 100).
      rewrite (Z.mul_comm (365 * (y1 - y0))).
      rewrite Z.mul_assoc.
      refine (Z.le_lt_trans _ (y1 - y0 + (y0 - 1901) mod 100) _ _ _).
      * apply div_mul_le.
        easy.
      * rewrite <- Z.succ_pred with (n := 100 * 365).
        rewrite Z.mul_succ_l.
        rewrite Z.add_comm.
        rewrite <- Z.add_lt_mono_r.
        refine (Z.lt_trans _ 100 _ _ _).
        apply Z.mod_pos_bound.
        easy.
        refine (Z.lt_le_trans 100 (Z.pred (100 * 365)) _ _ _).
        easy.
        refine (mul_1_le _ _ _ _ _ _).
        easy.
        exact (lt_1_le _ _ H).
        apply Z.le_refl.
      * easy.
      * easy.
      * easy.
Qed.

Theorem EpochTimeForYear_monotonic :
    forall y0 y1,
    y0 < y1 -> EpochTimeForYear y0 < EpochTimeForYear y1.
Proof.
  intros.
  unfold EpochTimeForYear.
  rewrite <- Z.mul_lt_mono_pos_l.
  apply EpochDayNumberForYear_monotonic.
  assumption.
  easy.
Qed.

Program Fixpoint FindYearForwards (t y : Z) (h : EpochTimeForYear y < t)
    {measure (Z.to_nat (t - EpochTimeForYear y))} : Z :=
  let y' := y + 1 in
  match EpochTimeForYear y' ?= t with
  | Lt => FindYearForwards t y' _
  | _ => y
  end.

Next Obligation.
Proof.
  rewrite <- Z.compare_lt_iff.
  symmetry.
  exact Heq_anonymous.
Qed.

Next Obligation.
Proof.
  rewrite <- Z2Nat.inj_lt.

  (* t - EpochTimeForYear (y + 1) < t - EpochTimeForYear y *)
  apply Z.sub_lt_mono_l.
  exact (EpochTimeForYear_monotonic y (y + 1) (Z.lt_succ_diag_r y)).
  
  (* 0 <= t - EpochTimeForYear (y + 1) *)
  rewrite Z.le_0_sub.
  rewrite Z.le_lteq.
  left.
  rewrite <- Z.compare_lt_iff.
  symmetry.
  exact Heq_anonymous.

  (* 0 <= t - EpochTimeForYear y *)
  rewrite Z.le_0_sub.
  rewrite Z.le_lteq.
  left.
  exact h.
Qed.

Program Fixpoint FindYearBackwards (t y : Z) (h : t < EpochTimeForYear y)
    {measure (Z.to_nat (EpochTimeForYear y - t))} : Z :=
  let y' := y - 1 in
  match t ?= EpochTimeForYear y' with
  | Lt => FindYearBackwards t y' _
  | _ => y'
  end.

Next Obligation.
Proof.
  rewrite <- Z.compare_lt_iff.
  symmetry.
  exact Heq_anonymous.
Qed.

Next Obligation.
Proof.
  rewrite <- Z2Nat.inj_lt.

  (* EpochTimeForYear (y - 1) - t < EpochTimeForYear y - t *)
  apply Z.sub_lt_mono_r.
  exact (EpochTimeForYear_monotonic (y - 1) y (Z.lt_pred_l y)).
  
  (* 0 <= t - EpochTimeForYear (y + 1) *)
  rewrite Z.le_0_sub.
  rewrite Z.le_lteq.
  left.
  rewrite <- Z.compare_lt_iff.
  symmetry.
  exact Heq_anonymous.

  (* 0 <= t - EpochTimeForYear y *)
  rewrite Z.le_0_sub.
  rewrite Z.le_lteq.
  left.
  exact h.
Qed.

(*>> EpochTimeToEpochYear(t) = the largest integral Number y (closest to +∞) such that EpochTimeForYear(y) ≤ t <<*)
Program Definition EpochTimeToEpochYear (t : Z) : Z :=
  match t ?= EpochTimeForYear 1970 with
  | Eq => 1970
  | Gt => FindYearForwards t 1970 _
  | Lt => FindYearBackwards t 1970 _
  end.

Next Obligation.
Proof.
  apply Z.gt_lt.
  symmetry.
  exact Heq_anonymous.
Qed.

Next Obligation.
Proof.
  symmetry.
  exact Heq_anonymous.
Qed.

Definition MathematicalDaysInYear (y : Z) : Z :=
  match (y mod 4) =? 0, (y mod 100) =? 0, (y mod 400) =? 0 with
  (*>> = 365 if ((y) modulo 4) ≠ 0 <<*)
  | false, _,     _    => 365
  (*>> = 366 if ((y) modulo 4) = 0 and ((y) modulo 100) ≠ 0 <<*)
  | true,  false, _    => 366
  (*>> = 365 if ((y) modulo 100) = 0 and ((y) modulo 400) ≠ 0 <<*)
  | _,     true, false => 365
  (*>> = 366 if ((y) modulo 400) = 0 <<*)
  | _,     _,    true  => 366
  end.

Lemma MathematicalDaysInYear_365_or_366 :
    forall y,
    MathematicalDaysInYear y = 365 \/ MathematicalDaysInYear y = 366.
Proof.
  intro y.
  unfold MathematicalDaysInYear.
  case (y mod 4 =? 0).
  case (y mod 100 =? 0).
  case (y mod 400 =? 0).
  right. reflexivity.
  left. reflexivity.
  right. reflexivity.
  left. reflexivity.
Qed.

Definition MathematicalInLeapYear (t : Z) : Z.
  refine (
    match MathematicalDaysInYear (EpochTimeToEpochYear t) as d
    return (MathematicalDaysInYear (EpochTimeToEpochYear t) = d -> Z) with
    (*>> = 0 if MathematicalDaysInYear(EpochTimeToEpochYear(t)) = 365 <<*)
    | 365 => fun _ => 0
    (*>> = 1 if MathematicalDaysInYear(EpochTimeToEpochYear(t)) = 366 <<*)
    | 366 => fun _ => 1
    | _ => fun H => impossible
    end eq_refl
  ).

  (* Proof of impossibility of the last case. *)
  all:
    destruct (MathematicalDaysInYear_365_or_366 (EpochTimeToEpochYear t));
    rewrite H in H0;
    discriminate.
Defined.

Fixpoint RemoveTrailingZero (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => 
    match RemoveTrailingZero s' with
    | EmptyString => if eqb c "0"%char then EmptyString else String c EmptyString
    | s'' => String c EmptyString ++ s''
    end
  end. 

Inductive Precision := 
  | AUTO
  | PrecisionValue : forall (p : Z), 0 <= p <= 9 -> Precision.

(* 13.25 FormatFractionalSeconds *)
Program Definition FormatFractionalSeconds (subSecondNanoseconds : Z) (precision : Precision) (subSecondNanoseconds_valid : 0 <= subSecondNanoseconds <= 999999999) : string :=
  match precision with
  (*>> 1. If precision is auto, then <<*)
  | AUTO =>
  (*>> a. If subSecondNanoseconds = 0, return the empty String. <<*)
    if subSecondNanoseconds =? 0 then EmptyString
    (*>> b. Let fractionString be ToZeroPaddedDecimalString(subSecondNanoseconds, 9). <<*)
    else let fractionString := ToZeroPaddedDecimalString subSecondNanoseconds 9 _ _ in
    (*>> c. Set fractionString to the longest prefix of fractionString ending with a code unit other than 0x0030 (DIGIT ZERO). <<*)
    let fractionString' := RemoveTrailingZero fractionString in
    (* NOTE: This is also 3. *)
    "." ++ fractionString'
  (*>> 2. Else, <<*)
  | PrecisionValue p _ => 
    (*>> a. If precision = 0, return the empty String. <<*)
    if p =? 0 then EmptyString
    (*>> b. Let fractionString be ToZeroPaddedDecimalString(subSecondNanoseconds, 9). <<*)
    else let fractionString := ToZeroPaddedDecimalString subSecondNanoseconds p _ _ in
    (*>> c. Set fractionString to the substring of fractionString from 0 to precision. <<*)
    let fractionString' := fractionString in
  (*>> 3. Return the string-concatenation of the code unit 0x002E (FULL STOP) and fractionString. <<*)
    "." ++ fractionString'
  end.

Inductive Precision' :=
| NormalPrecision (p : Precision)
| MINUTE_PRECISION.

Inductive Style := SEPARATED | UNSEPARATED.

(* 13.26 FormatTimeString *)
Definition FormatTimeString (hour minute second subSecondNanoseconds : Z) (precision' : Precision') (style : option Style) 
  (hour_valid : 0 <= hour <= 23) (minute_valid : 0 <= minute <= 59) (second_valid : 0 <= second <= 59) (subSecondNanoseconds_valid : 0 <= subSecondNanoseconds <= 999999999) : string :=
  (*>> 1. If style is present and style is unseparated, let separator be the empty String; otherwise, let separator be ":". <<*)
  let separator := match style with
  | Some style' => 
    match style' with
    | SEPARATED => ":"
    | UNSEPARATED => EmptyString
    end
  | None => ":"
  end in
  (*>> 2. Let hh be ToZeroPaddedDecimalString(hour, 2). <<*)
  let hh := ToZeroPaddedDecimalString hour 2 (proj1 hour_valid) zero_le_two in
  (*>> 3. Let mm be ToZeroPaddedDecimalString(minute, 2). <<*)
  let mm := ToZeroPaddedDecimalString minute 2 (proj1 minute_valid) zero_le_two in
  (*>> 4. If precision is minute, return the string-concatenation of hh, separator, and mm. <<*)
  match precision' with
  | MINUTE_PRECISION => hh ++ separator ++ mm
  (*>> 5. Let ss be ToZeroPaddedDecimalString(second, 2). <<*)
  | NormalPrecision precision =>
    let ss := ToZeroPaddedDecimalString second 2 (proj1 second_valid) zero_le_two in
  (*>> 6. Let subSecondsPart be FormatFractionalSeconds(subSecondNanoseconds, precision). <<*)
    let subSecondsPart := FormatFractionalSeconds subSecondNanoseconds precision subSecondNanoseconds_valid in
  (*>> 7. Return the string-concatenation of hh, separator, mm, separator, ss, and subSecondsPart. <<*)
  hh ++ separator ++ mm ++ separator ++ ss ++ subSecondsPart
  end.

Inductive RoundingMode :=
  | CEIL
  | FLOOR
  | EXPAND
  | TRUNC
  | HALF_CEIL
  | HALF_FLOOR
  | HALF_EXPAND
  | HALF_TRUNC
  | HALF_EVEN.

Inductive Sign := POSITIVE | NEGATIVE.

Inductive UnsignedRoundingMode := 
  | ZERO
  | INFINITY
  | HALF_ZERO
  | HALF_INFINITY
  | HALF_EVEN_UNSIGNED. (* Named unsigned to avoid collision *)


(* Table 22 *)
(*>> Rounding Mode | Sign     | Unsigned Rounding Mode <<*)
(*>> ceil          | positive | infinity <<*)
(*>> ceil          | negative | zero <<*)
(*>> floor         | positive | zero <<*)
(*>> floor         | negative | infinity <<*)
(*>> expand        | positive | infinity <<*)
(*>> expand        | negative | infinity <<*)
(*>> trunc         | positive | zero <<*)
(*>> trunc         | negative | zero <<*)
(*>> half-ceil     | positive | half-infinity <<*)
(*>> half-ceil     | negative | half-zero <<*)
(*>> half-floor    | positive | half-zero <<*)
(*>> half-floor    | negative | half-infinity <<*)
(*>> half-expand   | positive | half-infinity <<*)
(*>> half-expand   | negative | half-infinity <<*)
(*>> half-trunc    | positive | half-zero <<*)
(*>> half-trunc    | negative | half-zero <<*)
(*>> half-even     | positive | half-even <<*)
(*>> half-even     | negative | half-even <<*)

(* 13.27 GetUnsignedRoundingMode *)
Definition GetUnsignedRoundingMode (roundingMode : RoundingMode) (sign : Sign) : UnsignedRoundingMode :=
  (*>> 1. Return the specification type in the "Unsigned Rounding Mode" column of Table 22 for the row where the value in the "Rounding Mode" column is roundingMode and the value in the "Sign" column is sign. <<*)
  match roundingMode, sign with
  | CEIL, POSITIVE => INFINITY
  | CEIL, NEGATIVE => ZERO
  | FLOOR, POSITIVE => ZERO
  | FLOOR, NEGATIVE => INFINITY
  | EXPAND, POSITIVE => INFINITY
  | EXPAND, NEGATIVE => INFINITY
  | TRUNC, POSITIVE => ZERO
  | TRUNC, NEGATIVE => ZERO
  | HALF_CEIL, POSITIVE => HALF_INFINITY
  | HALF_CEIL, NEGATIVE => HALF_ZERO
  | HALF_FLOOR, POSITIVE => HALF_ZERO
  | HALF_FLOOR, NEGATIVE => HALF_INFINITY
  | HALF_EXPAND, POSITIVE => HALF_INFINITY
  | HALF_EXPAND, NEGATIVE => HALF_INFINITY
  | HALF_TRUNC, POSITIVE => HALF_ZERO
  | HALF_TRUNC, NEGATIVE => HALF_ZERO
  | HALF_EVEN, POSITIVE => HALF_EVEN_UNSIGNED
  | HALF_EVEN, NEGATIVE => HALF_EVEN_UNSIGNED
  end.

(* 13.2 EpochDaysToEpochMs *)
Definition EpochDaysToEpochMs (day time : Z) : Z :=
  (*>> 1. Return day × ℝ(msPerDay) + time. <<*)
  day * msPerDay + time.

(* 13.8 NegateRoundingMode *)
Definition NegateRoundingMode (roundingMode : RoundingMode) : RoundingMode :=
  match roundingMode with
  (*>> 1. If roundingMode is ceil, return floor. <<*)
  | CEIL => FLOOR
  (*>> 2. If roundingMode is floor, return ceil. <<*)
  | FLOOR => CEIL
  (*>> 3. If roundingMode is half-ceil, return half-floor. <<*)
  | HALF_CEIL => HALF_FLOOR
  (*>> 4. If roundingMode is half-floor, return half-ceil. <<*)
  | HALF_FLOOR => HALF_CEIL
  (*>> 5. Return roundingMode. <<*)
  | _ => roundingMode
  end.

Inductive Unused := UNUSED.

(* 13.14 ValidateTemporalRoundingIncrement *)
Program Definition ValidateTemporalRoundingIncrement (increment dividend : Z) (inclusive : bool)
  (increment_valid : 1 <= increment) (dividend_valid : 1 <= dividend) (relation_valid : (dividend > 1 /\ inclusive = false) \/ (inclusive = true))
  : Completion Unused :=
  (*>> 1. If inclusive is true, then <<*)
  let maximum := match inclusive with
    (*>> a. Let maximum be dividend. <<*)
    | true => dividend
  (*>> 2. Else, <<*)
    (*>> a. Assert: dividend > 1. <<*)
    | false => assert (dividend > 1) in 
    (*>> b. Let maximum be dividend - 1. <<*)
    dividend - 1
    end 
  in
  (*>> 3. If increment > maximum, throw a RangeError exception. <<*)
  if increment >? maximum then Throw RangeError
  (*>> 4. If dividend modulo increment ≠ 0, then <<*)
  else if dividend mod increment =? 0
    (*>> a. Throw a RangeError exception. <<*)
    then Throw RangeError
  (*>> 5. Return unused. <<*)
  else Normal UNUSED.

Lemma not_B_if_A_or_B_then_A : forall (A B : Prop), ~B -> A \/ B -> A.
Proof.
  intros.
  destruct H0.
  easy.
  easy.
Qed.

Next Obligation.
  apply not_B_if_A_or_B_then_A in relation_valid.
  easy.
  easy.
Qed.

Lemma not_A_if_A_or_B_then_B : forall (A B : Prop), ~A -> A \/ B -> B.
Proof.
  intros.
  destruct H0.
  easy.
  easy.
Qed.

Inductive TemporalUnit := YEAR | MONTH | WEEK | DAY | HOUR | MINUTE | SECOND | MILLISECOND | MICROSECOND | NANOSECOND.

Definition TemporalUnitEqb (u1 u2 : TemporalUnit) : bool :=
  match u1, u2 with
  | YEAR, YEAR => true
  | YEAR, _ => false
  | MONTH, MONTH => true
  | MONTH, _ => false
  | WEEK, WEEK => true
  | WEEK, _ => false
  | DAY, DAY => true
  | DAY, _ => false
  | HOUR, HOUR => true
  | HOUR, _ => false
  | MINUTE, MINUTE => true
  | MINUTE, _ => false
  | SECOND, SECOND => true
  | SECOND, _ => false
  | MILLISECOND, MILLISECOND => true
  | MILLISECOND, _ => false
  | MICROSECOND, MICROSECOND => true
  | MICROSECOND, _ => false
  | NANOSECOND, NANOSECOND => true
  | NANOSECOND, _ => false
  end.

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


(* 13.21 IsCalendarUnit *) 
Definition IsCalendarUnit (unit' : TemporalUnit) : bool :=
  (*>> 1. If unit is year, return true. <<*)
  if TemporalUnitEqb unit' YEAR then true
  (*>> 2. If unit is month, return true. <<*)
  else if TemporalUnitEqb unit' MONTH then true
  (*>> 3. If unit is week, return true. <<*)
  else if TemporalUnitEqb unit' WEEK then true
  (*>> 4. Return false. <<*)
  else false.

Inductive Category := DATE | TIME.

(* Table 21 - Unused rows are not displayed *)
(*>> Value       | Category | Maximum duration rounding increment <<*)
(*>> YEAR        | DATE     | UNSET <<*)
(*>> MONTH       | DATE     | UNSET <<*)
(*>> WEEK        | DATE     | UNSET <<*)
(*>> DAY         | DATE     | UNSET <<*)
(*>> HOUR        | TIME     | 24 <<*)
(*>> MINUTE      | TIME     | 60 <<*)
(*>> SECOND      | TIME     | 60 <<*)
(*>> MILLISECOND | TIME     | 1000 <<*)
(*>> MICROSECOND | TIME     | 1000 <<*)
(*>> NANOSECOND  | TIME     | 1000 <<*)

(* 13.22 TemporalUnitCategory *)
Definition TemporalUnitCategory (unit' : TemporalUnit) : Category :=
  (*>> 1. Return the value from the "Category" column of the row of Table 21 in which unit is in the "Value" column. <<*)
  match unit' with
  | YEAR => DATE
  | MONTH => DATE
  | WEEK => DATE
  | DAY => DATE
  | HOUR => TIME
  | MINUTE => TIME
  | SECOND => TIME
  | MILLISECOND => TIME
  | MICROSECOND => TIME
  | NANOSECOND => TIME
  end.

Inductive RoundingIncrement := UNSET | ValuedRoundingIncrement (roundingIncrement : Z).

(* 13.23 MaximumTemporalDurationRoundingIncrement *)
Definition MaximumTemporalDurationRoundingIncrement (unit' : TemporalUnit) : RoundingIncrement :=
  (*>> 1. Return the value from the "Maximum duration rounding increment" column of the row of Table 21 in which unit is in the "Value" column. <<*)
  match unit' with
  | YEAR => UNSET
  | MONTH => UNSET
  | WEEK => UNSET
  | DAY => UNSET
  | HOUR => ValuedRoundingIncrement 24
  | MINUTE => ValuedRoundingIncrement 60
  | SECOND => ValuedRoundingIncrement 60
  | MILLISECOND => ValuedRoundingIncrement 1000 
  | MICROSECOND => ValuedRoundingIncrement 1000
  | NANOSECOND => ValuedRoundingIncrement 1000
  end.

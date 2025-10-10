From Stdlib Require Import Numbers.BinNums Program.Equality Program.Wf ZArith Strings.String Numbers.DecimalString Init.Decimal.
From Temporal Require Import Basic Sec12Def Sec12Thm StringUtil.
Open Scope bool_scope.
Open Scope string_scope.
Open Scope Z.

(* 3.5.1 ISODateRecord *)
Record ISODateRecord : Type :=
  mkISODateRecord {
    (*>> Field Name | Value                                  | Meaning <<*)
    (*>> [[Year]]  | an integer                             | The year in the ISO 8601 calendar. <<*)
    year : Z;
    (*>> [[Month]] | an integer between 1 and 12, inclusive | The number of the month in the ISO 8601 calendar. <<*)
    month : Z;
    month_valid : 1 <= month <= 12;
    (*>> [[Day]]   | an integer between 1 and 31, inclusive | The number of the day of the month in the ISO 8601 calendar. <<*)
    day : Z;
    day_valid : 1 <= day <= 31;
  }.

(* 3.5.12 CompareISODate *)
Definition CompareISODate (isoDate1 isoDate2 : ISODateRecord) : Z :=
  (*>> 1. If isoDate1.[[Year]] > isoDate2.[[Year]], return 1. <<*)
  if (year isoDate1) >? (year isoDate2) then 1
  (*>> 2. If isoDate1.[[Year]] < isoDate2.[[Year]], return -1. <<*)
  else if (year isoDate1) <? (year isoDate2) then -1
  (*>> 3. If isoDate1.[[Month]] > isoDate2.[[Month]], return 1. <<*)
  else if (month isoDate1) >? (month isoDate2) then 1
  (*>> 4. If isoDate1.[[Month]] < isoDate2.[[Month]], return -1. <<*)
  else if (month isoDate1) <? (month isoDate2) then -1
  (*>> 5. If isoDate1.[[Day]] > isoDate2.[[Day]], return 1. <<*)
  else if (day isoDate1) >? (day isoDate2) then 1
  (*>> 6. If isoDate1.[[Day]] < isoDate2.[[Day]], return -1. <<*)
  else if (day isoDate1) <? (day isoDate2) then -1
  (*>> 7. Return 0. <<*)
  else 0.

(* 3.5.7 IsValidISODate *)
Definition IsValidISODate (year month day : Z) : bool.
  refine (
    match month ?= 1 as m_1, month ?= 12 as m_2
    return ((month ?= 1) = m_1 -> (month ?= 12) = m_2 -> bool)
    with
    (*>> 1. If month < 1 or month > 12, then <<*)
    | Lt, _ | _, Gt =>
      (*>> a. Return false. <<*)
      fun _ _ => false
    | _, _ => fun H0 H1 =>
      (*>> 2. Let daysInMonth be ISODaysInMonth(year, month). <<*)
      let daysInMonth := ISODaysInMonth year month _ in
      (*>> 3. If day < 1 or day > daysInMonth, then <<*)
      if (day <? 1) || (day >? daysInMonth) then
        (*>> a. Return false. <<*)
        false
      (*>> 4. Return true. <<*)
      else true
    end eq_refl eq_refl
  ).

  (* month = 1, month = 12 *)
  - rewrite Z.compare_eq_iff in H0.
    rewrite Z.compare_eq_iff in H1.
    rewrite H0 in H1.
    discriminate.
  
  (* month = 1, month < 12 *)
  - rewrite Z.compare_eq_iff in H0.
    rewrite H0.
    easy.
  
  (* month > 1, month = 12 *)
  - rewrite Z.compare_eq_iff in H1.
    rewrite H1.
    easy.
  
  (* month > 1, month < 12 *)
  - rewrite Z.compare_gt_iff in H0.
    rewrite Z.compare_lt_iff in H1.
    split.
    + apply Z.lt_le_incl.
      assumption.
    + apply Z.lt_le_incl.
      assumption.
Defined.

(** States that if we know that a month has a valid range, and the day is valid
    for that month, then `IsValidISODate` returns true. *)
Lemma IsValidISODate_month_day_range :
  forall year month day month_valid,
  1 <= day <= ISODaysInMonth year month month_valid ->
  IsValidISODate year month day = true.
Proof.
  intros.
  unfold IsValidISODate.
  generalize (Z.compare_eq_iff month0 1).
  generalize (Z.compare_gt_iff month0 1).
  generalize (Z.compare_eq_iff month0 12).
  generalize (Z.compare_lt_iff month0 12).
  destruct (month0 ?= 1); destruct (month0 ?= 12).

  (* contradiction *)
  - intros.
    exfalso.
    rewrite (proj1 i0 eq_refl) in i2.
    specialize (proj1 i2 eq_refl).
    intro.
    discriminate.
  
  (* 1 <= day <= ISODaysInMonth year month month_valid *)
  - intros.
    destruct H.
    rewrite Z.gtb_ltb.
    rewrite (proj2 (Z.ltb_ge day0 1)).
    + simpl.
      rewrite (proj2 (Z.ltb_ge _ day0)).
      * reflexivity.
      * assumption.
    + assumption.
  
  (* contradiction *)
  - intros.
    rewrite (proj1 i2 eq_refl) in i.
    assert (h : Gt = Lt). { apply i. easy. }
    discriminate.
  
  (* contradiction *)
  - intros.
    rewrite (proj1 i0 eq_refl) in i1.
    assert (h : Lt = Gt). { apply i1. easy. }
    discriminate.
  
  (* contradiction *)
  - intros.
    assert (month0_lt_eq : 1 < month0 \/ 1 = month0). {
      apply Z.le_lteq.
      apply month_valid0.
    }
    destruct month0_lt_eq.
    + assert (h : Lt = Gt). { apply i1. assumption. }
      discriminate.
    + assert (h : Lt = Eq). { apply i2. symmetry. assumption. }
      discriminate.
  
  (* contradiction *)
  - intros.
    assert (month0_lt_eq : month0 < 12 \/ month0 = 12). {
      apply Z.le_lteq.
      apply month_valid0.
    }
    destruct month0_lt_eq.
    + assert (h : Gt = Lt). { apply i. assumption. }
      discriminate.
    + assert (h : Gt = Eq). { apply i0. assumption. }
      discriminate.
  
  (* 1 <= day <= ISODaysInMonth year month month_valid *)
  - intros.
    destruct H.
    rewrite Z.gtb_ltb.
    rewrite (proj2 (Z.ltb_ge day0 1)).
    + simpl.
      rewrite (proj2 (Z.ltb_ge _ day0)).
      * reflexivity.
      * assumption.
    + assumption.
  
  (* 1 <= day <= ISODaysInMonth year month month_valid *)
  - intros.
    destruct H.
    rewrite (proj2 (Z.ltb_ge day0 1)).
    + simpl.
      rewrite Z.gtb_ltb.
      rewrite (proj2 (Z.ltb_ge _ day0)).
      * reflexivity.
      * assumption.
    + assumption.
  
  (* contradiction *)
  - intros.
    assert (month0_lt_eq : month0 < 12 \/ month0 = 12). {
      apply Z.le_lteq.
      apply month_valid0.
    }
    destruct month0_lt_eq.
    + assert (h : Gt = Lt). { apply i. assumption. }
      discriminate.
    + assert (h : Gt = Eq). { apply i0. assumption. }
      discriminate.
Qed.

(** States that if `IsValidISODate year month day` returns true,
    then `1 <= month 12` and `1 <= day <= ISODaysInMonth year month _` *)
Lemma IsValidISODate_true :
  forall year month day, IsValidISODate year month day = true ->
  exists (month_valid : 1 <= month <= 12),
  1 <= day <= ISODaysInMonth year month month_valid.
Proof.
  intro year0.
  intro month0.
  intro day0.

  unfold IsValidISODate.
  generalize (Z.compare_eq_iff month0 1).
  generalize (Z.compare_gt_iff month0 1).
  generalize (Z.compare_eq_iff month0 12).
  generalize (Z.compare_lt_iff month0 12).
  destruct (month0 ?= 1); destruct (month0 ?= 12).

  (* contradiction *)
  - intros.
    assert (h : month0 = 12). { apply i0. reflexivity. }
    assert (h1 : 12 = 1). { rewrite <- h. apply i2. reflexivity. }
    discriminate.
  
  (* month = 1 *)
  - intros.
    assert (h : month0 = 1). { apply i2. reflexivity. }
    rewrite h.
    refine (ex_intro _ _ _).
    unfold ISODaysInMonth.
    destruct (day0 <? 1) eqn: day0_lt.
    + simpl in H.
      discriminate.
    + split.
      * rewrite Z.ltb_ge in day0_lt.
        assumption.
      * simpl in H.
        destruct (day0 >? _) eqn: day0_gt.
        discriminate.
        rewrite Z.gtb_ltb in day0_gt.
        rewrite Z.ltb_ge in day0_gt.
        refine (Z.le_trans _ _ 31 _ _).
        exact day0_gt.
        apply ISODaysInMonth_range.
  
  - intros. discriminate. (* contradiction *)
  - intros. discriminate. (* contradiction *)
  - intros. discriminate. (* contradiction *)
  - intros. discriminate. (* contradiction *)
  
  (* month = 12 *)
  - intros.
    assert (h : month0 = 12). { apply i0. reflexivity. }
    rewrite h.
    refine (ex_intro _ _ _).
    unfold ISODaysInMonth.
    destruct (day0 <? 1) eqn: day0_lt.
    + simpl in H.
      discriminate.
    + split.
      * rewrite Z.ltb_ge in day0_lt.
        assumption.
      * simpl in H.
        destruct (day0 >? _) eqn: day0_gt.
        discriminate.
        rewrite Z.gtb_ltb in day0_gt.
        rewrite Z.ltb_ge in day0_gt.
        refine (Z.le_trans _ _ 31 _ _).
        exact day0_gt.
        apply ISODaysInMonth_range.
  
  (* 1 < month < 12 *)
  - intros.
    assert (h0 : 1 < month0). { apply i1. reflexivity. }
    assert (h1 : month0 < 12). { apply i. reflexivity. }
    refine (ex_intro _ _ _).
    destruct (day0 <? 1) eqn: day0_lt; destruct (day0 >? _) eqn: day0_gt.
    + discriminate.
    + discriminate.
    + discriminate.
    + rewrite Z.ltb_ge in day0_lt.
      rewrite Z.gtb_ltb in day0_gt.
      rewrite Z.ltb_ge in day0_gt.
      split.
      * assumption.
      * assumption.
  
  - intros. discriminate. (* contradiction *)

  Unshelve.
  
  (* 1 <= 1 <= 12 *)
  easy.

  (* 1 <= 12 <= 12 *)
  easy.

  (* 1 < month < 12 -> 1 <= month <= 12 *)
  split; apply Z.lt_le_incl; assumption.
Qed.

(* 3.5.2 CreateISODateRecord *)
Program Definition CreateISODateRecord
  (year month day : Z)
  (month_valid : 1 <= month <= 12) (day_valid : 1 <= day <= 31)
  (is_valid : IsValidISODate year month day = true) : ISODateRecord :=
    (*>> 1. Assert: IsValidISODate(year, month, day) is true. <<*)
    assert IsValidISODate year month day = true in
    (*>> 2. Return ISO Date Record { [[Year]]: year, [[Month]]: month, [[Day]]: day }. <<*)
    mkISODateRecord year month month_valid day day_valid.

(* 3.5.9 PadISOYear *)
Program Definition PadISOYear (y : Z) : string :=
  (*>> 1. If y ≥ 0 and y ≤ 9999, then <<*)
  match (y >=? 0) && (y <=? 9999) with
  (*>> a. Return ToZeroPaddedDecimalString(y, 4). <<*)
  | true => ToZeroPaddedDecimalString y 4 _ _
  (*>> 2. If y > 0, let yearSign be "+"; otherwise, let yearSign be "-". <<*)
  | false => let yearSign := if y >? 0 then "+" else "-" in
  (*>> 3. Let year be ToZeroPaddedDecimalString(abs(y), 6). <<*)
  let year := ToZeroPaddedDecimalString (Z.abs y) 6 _ _ in
  (*>> 4. Return the string-concatenation of yearSign and year. <<*)
  yearSign ++ year end.

Next Obligation. 
  apply eq_sym in Heq_anonymous.
  apply Bool.andb_true_iff in Heq_anonymous.
  apply proj1 in Heq_anonymous.
  apply Z.geb_le in Heq_anonymous.
  apply Heq_anonymous.
Qed.
Next Obligation. apply (Z.abs_nonneg). Qed.  

Inductive Overflow := CONSTRAIN | REJECT.
Definition eq (a b : Overflow) : bool := 
  match a, b with
  | CONSTRAIN, CONSTRAIN => true
  | REJECT, REJECT => true
  | _, _ => false
  end.

(* 3.5.6 RegulateISODate *)
Program Definition RegulateISODate (year month day : Z) (overflow : Overflow) : Completion ISODateRecord :=
  match overflow with
  (*>> 1. If overflow is constrain, then <<*)
  | CONSTRAIN =>
      (*>> a. Set month to the result of clamping month between 1 and 12. <<*)
      let month' := Clamp 1 12 month _ in
      (*>> b. Let daysInMonth be ISODaysInMonth(year, month). <<*)
      let daysInMonth := ISODaysInMonth year month' _ in
      (*>> c. Set day to the result of clamping day between 1 and daysInMonth. <<*)
      let day' := Clamp 1 daysInMonth day _ in
      Normal (CreateISODateRecord year month' day' _ _ _)
  (*>> 2. Else, <<*)
  | _ => 
      (*>> a. Assert: overflow is reject. <<*)
      assert overflow = REJECT in
      match IsValidISODate year month day with
      (*>> b. If IsValidISODate(year, month, day) is false, throw a RangeError exception. <<*)
      | false => Throw RangeError
      (*>> 3. Return CreateISODateRecord(year, month, day). <<*)
      | true => Normal (CreateISODateRecord year month day _ _ _)
      end
  end.

Next Obligation. Proof. apply clamp_between_lower_and_upper. Qed.
Next Obligation. Proof. apply ISODaysInMonth_at_least_1. Qed.
Next Obligation. Proof. apply clamp_between_lower_and_upper. Qed.

Next Obligation.
Proof.
  split.
  - apply clamp_between_lower_and_upper.
  - apply clamp_upper_le.
    apply ISODaysInMonth_range.
Qed.

Next Obligation.
Proof.
  refine (IsValidISODate_month_day_range year0 _ _ _ _).
  apply clamp_between_lower_and_upper.
Qed.

Next Obligation.
Proof.
  destruct overflow.
  - contradiction.
  - reflexivity.
Qed.

Next Obligation.
Proof.
  symmetry in Heq_anonymous.
  destruct (IsValidISODate_true year0 month0 day0 Heq_anonymous).
  assumption.
Qed.

Next Obligation.
Proof.
  symmetry in Heq_anonymous.
  destruct (IsValidISODate_true year0 month0 day0 Heq_anonymous).
  destruct H.
  split.
  - assumption.
  - apply Z.le_trans with (m := ISODaysInMonth year0 month0 x).
    + assumption.
    + apply ISODaysInMonth_range.
Qed.

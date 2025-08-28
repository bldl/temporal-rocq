Require Import Coq.Numbers.BinNums ZArith.
Open Scope bool_scope.
Open Scope Z.

(* 3.5.1 ISODateRecord *)
(*>>
Field Name |	Value                                 |  Meaning
[[Year]]   | an integer                             | The year in the ISO 8601 calendar.
[[Month]]  | an integer between 1 and 12, inclusive | The number of the month in the ISO 8601 calendar.
[[Day]]    | an integer between 1 and 31, inclusive | The number of the day of the month in the ISO 8601 calendar. 
<<*)
Record ISODateRecord : Type :=
  mkISODateRecord {
    year : Z;
    month : Z;
    day : Z;
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

Theorem CompareISODate_eq_implies_eq_zero :
  forall (y1 y2 m1 m2 d1 d2 : Z),
  y1 = y2 /\ m1 = m2 /\ d1 = d2 ->
  CompareISODate (mkISODateRecord y1 m1 d1) (mkISODateRecord y2 m2 d2) = 0.
Proof.
  intros y1 y2 m1 m2 d1 d2.
  intro H.
  destruct H.
  destruct H0.
  rewrite H.
  rewrite H0.
  rewrite H1.
  unfold CompareISODate.
  rewrite Z.gtb_ltb.
  rewrite Z.gtb_ltb.
  rewrite Z.gtb_ltb.
  rewrite Z.ltb_irrefl.
  rewrite Z.ltb_irrefl.
  rewrite Z.ltb_irrefl.
  reflexivity.
Qed.

(* Assumption: 
  EpochDayNumberForYear and msPerDay works on Z and not real numbers *)
(*>> msPerDay = 86400000𝔽 = msPerHour × 𝔽(HoursPerDay) <<*)
Definition msPerDay : Z := 86400000.

(* 13.3 Date Equations *)
(* Note: `/` is floor division with Z. 
  https://rocq-prover.org/doc/V8.21%2Balpha/stdlib/Coq.ZArith.BinIntDef.html#Z.div_eucl *)
(*>> EpochDayNumberForYear(y) = 365 × (y - 1970) + floor((y - 1969) / 4) - floor((y - 1901) / 100) + floor((y - 1601) / 400) <<*)
Definition EpochDayNumberForYear (y : Z) : Z := 365 * (y - 1970) + ((y - 1969) / 4) - ((y - 1901) / 100) + ((y - 1601) / 400).

(*>> EpochTimeForYear(y) = ℝ(msPerDay) × EpochDayNumberForYear(y) <<*)
Definition EpochTimeForYear (y : Z) : Z := msPerDay * EpochDayNumberForYear y.

Inductive Direction :=
  Forwards | Backwards.

Fixpoint FindYear (f : nat) (t y : Z) (dir : Direction) : Z := 
  let t' := t - Z.abs (EpochTimeForYear y) in
  match f with
  | O => 0
  | S f' => (
    if t' <? 0
    then match dir with 
    | Forwards => y - 1
    | Backwards => y + 1
    end
    else if t' =? 0 then y
    else match dir with
    | Forwards => FindYear f' t (y + 1) Forwards
    | Backwards => FindYear f' t (y - 1) Backwards
    end)
  end.

(*>> EpochTimeToEpochYear(t) = the largest integral Number y (closest to +∞) such that EpochTimeForYear(y) ≤ t <<*)
Definition EpochTimeToEpochYear (t : Z) : Z :=
  if t >? 0 then FindYear 5000 t 1970 Forwards else FindYear 5000 (Z.abs t) 1969 Backwards.

(* TODO: use numbers instead *)
Inductive DaysInYear :=
  Normal | Leap.

Definition MathematicalDaysInYear (y : Z) : DaysInYear :=
  match (y mod 4) =? 0, (y mod 100) =? 0, (y mod 400) =? 0 with
  (*>> = 365 if ((y) modulo 4) ≠ 0 <<*)
  | false, _,     _    => Normal
  (*>> = 366 if ((y) modulo 4) = 0 and ((y) modulo 100) ≠ 0 <<*)
  | true,  false, _    => Leap
  (*>> = 365 if ((y) modulo 100) = 0 and ((y) modulo 400) ≠ 0 <<*)
  | _,     true, false => Normal
  (*>> = 366 if ((y) modulo 400) = 0 <<*)
  | _,     _,    true  => Leap
  end.

Definition MathematicalInLeapYear (t : Z) : Z :=
  match MathematicalDaysInYear (EpochTimeToEpochYear t) with
  (*>> = 0 if MathematicalDaysInYear(EpochTimeToEpochYear(t)) = 365 <<*)
  | Normal => 0
  (*>> = 1 if MathematicalDaysInYear(EpochTimeToEpochYear(t)) = 366 <<*)
  | Leap => 1
  end.
(* 13.3 end *)

(* 12.3.17 ISODaysInMonth *)
Definition ISODaysInMonth (year month : Z) : Z :=
  match month with
  (*>> 1. If month is 1, 3, 5, 7, 8, 10, or 12, return 31. <<*)
  | 1 | 3 | 5 | 7 | 8 | 10 | 12 => 31
  (*>> 2. If month is 4, 6, 9, or 11, return 30. <<*)
  | 4 | 6 | 9 | 11 => 30
  (*>> 3. Assert: month = 2. <<*)
  (* TODO *)
  (*>> 4. Return 28 + MathematicalInLeapYear(EpochTimeForYear(year)). <<*)
  | _ => 28 + MathematicalInLeapYear (EpochTimeForYear year)
  end.

(* 3.5.7 IsValidISODate *)
Definition IsValidISODate (year month day : Z) : bool :=
  (*>> 1. If month < 1 or month > 12, then <<*)
  if (month <? 1) || (month >? 12) then
    (*>> a. Return false. <<*)
    false
  (*>> 2. Let daysInMonth be ISODaysInMonth(year, month). <<*)
  else let daysInMonth := (ISODaysInMonth year month) in
    (*>> 3. If day < 1 or day > daysInMonth, then <<*)
    if (day <? 1) || (day >? daysInMonth) then
      (*>> a. Return false. <<*)
      false
    (*>> 4. Return true. <<*)
    else true.

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

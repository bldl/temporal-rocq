Require Import Coq.Numbers.BinNums ZArith.
Open Scope bool_scope.
Open Scope Z.

(* 3.5.1 ISODateRecord *)
Record ISODateRecord : Type :=
  mkISODateRecord {
    year : Z;
    month : Z;
    day : Z;
  }.

(* 3.5.12 CompareISODate *)
Definition CompareISODate (isoDate1 isoDate2 : ISODateRecord) : Z :=
  if Z.gtb (year isoDate1) (year isoDate2) then 1
  else if Z.ltb (year isoDate1) (year isoDate2) then -1
  else if Z.gtb (month isoDate1) (month isoDate2) then 1
  else if Z.ltb (month isoDate1) (month isoDate2) then -1
  else if Z.gtb (day isoDate1) (day isoDate2) then 1
  else if Z.ltb (day isoDate1) (day isoDate2) then -1
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

(* TODO assumptions assummptions *)
Definition msPerDay : Z := 86400000.

Definition EpochDayNumberForYear (y : Z) : Z :=
  365 * (y - 1970) + ((y - 1969) / 4) - ((y - 1901) / 100) + ((y - 1601) / 400).

Definition EpochTimeForYear (y : Z) : Z :=
  msPerDay * EpochDayNumberForYear y.

Definition EpochTimeToEpochYear (t : Z) : Z := 0.

Definition MathematicalDaysInYear (y : Z) : Z :=
  match (y mod 4) =? 0, (y mod 100) =? 0, (y mod 400) =? 0 with
  | false, _,     _    => 365
  | true,  false, _    => 366
  | _,     true, false => 365
  | _,     _,    true  => 366
  end.

Lemma MathematicalDaysInYear_365_or_366 :
  forall (y : Z),
  MathematicalDaysInYear y = 365 \/ MathematicalDaysInYear y = 366.
Proof.
  intro y.
  unfold MathematicalDaysInYear.
  destruct (y mod 4 =? 0).
  destruct (y mod 100 =? 0).
  destruct (y mod 400 =? 0).
  right.
  reflexivity.
  left.
  reflexivity.
  right.
  reflexivity.
  left.
  reflexivity.
Qed.

Lemma MathematicalDaysInYear_help :
  forall (y : Z)
  (ne_365 : MathematicalDaysInYear y <> 365)
  (ne_366 : MathematicalDaysInYear y <> 366),
  False.
Proof.
  intros y ne_365 ne_366.
  destruct (MathematicalDaysInYear_365_or_366 y).
  contradiction.
  contradiction.
Qed.

Definition MathematicalInLeapYear (t : Z) : Z :=
  match MathematicalDaysInYear (EpochTimeToEpochYear t) with
  | 365 => 0
  | 366 => 1
  | _ => False_rect Z (MathematicalDaysInYear_help (EpochTimeToEpochYear t))
  end.

(* TODO: Assert month is 2 and add leap day *)
(* 12.3.17 ISODaysInMonth *)
Definition ISODaysInMonth (year month : Z) : Z :=
  match month with
  | 1 | 3 | 5 | 7 | 8 | 10 | 12 => 31
  | 4 | 6 | 9 | 11 => 30
  | _ => 28
  end.

(* 3.5.7 IsValidISODate *)
Definition IsValidISODate (year month day : Z) : bool :=
  if orb (Z.ltb month 1) (Z.gtb month 12) then false
  else let daysInMonth := (ISODaysInMonth year month) in
    if orb (Z.ltb day 1) (Z.gtb day daysInMonth) then false
    else true.

(* 4.5.9 IsValidTime *)
Definition IsValidTime (hour minute second millisecond microsecond nanosecond : Z) : bool :=
  if orb (Z.ltb hour 0) (Z.gtb hour 23) then false
  else if orb (Z.ltb minute 0) (Z.gtb minute 59) then false
  else if orb (Z.ltb second 0) (Z.gtb second 59) then false
  else if orb (Z.ltb millisecond 0) (Z.gtb millisecond 999) then false
  else if orb (Z.ltb microsecond 0) (Z.gtb microsecond 999) then false
  else if orb (Z.ltb nanosecond 0) (Z.gtb nanosecond 999) then false
  else true.

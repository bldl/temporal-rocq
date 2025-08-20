Require Import Coq.Numbers.BinNums ZArith.

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
  CompareISODate (mkISODateRecord y1 m1 d1) (mkISODateRecord y2 m2 d2) = 0%Z.
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

(* TODO: Assert month is 2 and add leap day *)
(* 12.3.17 ISODaysInMonth *)
Definition ISODaysInMonth (year month : Z) : Z :=
  match month with
  | 1%Z | 3%Z | 5%Z | 7%Z | 8%Z | 10%Z | 12%Z => 31%Z
  | 4%Z | 6%Z | 9%Z | 11%Z => 30%Z
  | _ => 28%Z
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

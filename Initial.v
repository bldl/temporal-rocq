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

(* 12.3.17 ISODaysInMonth *)
Definition ISODaysInMonth (year month : Z) : Z := 31%Z.

(* 3.5.7 IsValidISODate *)
Definition IsValidISODate (year month day : Z) : bool :=
  if orb (Z.ltb month 1) (Z.gtb month 12) then false
  else let daysInMonth := (ISODaysInMonth year month) in
    if orb (Z.ltb day 1) (Z.gtb day daysInMonth) then false
    else true.

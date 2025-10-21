From Stdlib Require Import ZArith.
From Temporal Require Import Section3.ISODateRecord.
Open Scope Z.

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

Theorem CompareISODate_eq_zero : forall isoDate, CompareISODate isoDate isoDate = 0.
Proof.
  intros.
  unfold CompareISODate.
  repeat (rewrite Z.gtb_ltb, Z.ltb_irrefl).
  reflexivity.
Qed.

Theorem CompareISODate_eq_implies_eq_zero :
  forall (y1 y2 m1 m2 d1 d2 : Z),
  y1 = y2 /\ m1 = m2 /\ d1 = d2 ->
  forall (m1_valid : 1 <= m1 <= 12) (m2_valid : 1 <= m2 <= 12)
  (d1_valid : 1 <= d1 <= 31) (d2_valid : 1 <= d2 <= 31),
  CompareISODate (mkISODateRecord y1 m1 m1_valid d1 d1_valid) (mkISODateRecord y2 m2 m2_valid d2 d2_valid) = 0.
Proof.
  intros y1 y2 m1 m2 d1 d2.
  intro H.
  intros m1_valid m2_valid d1_valid d2_valid.
  destruct H, H0.
  unfold CompareISODate.
  simpl.
  rewrite H.
  rewrite H0.
  rewrite H1.
  repeat (rewrite Z.gtb_ltb, Z.ltb_irrefl).
  reflexivity.
Qed.

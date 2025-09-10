Require Import Coq.Numbers.BinNums Coq.Program.Wf ZArith.
From Temporal Require Export Sec3Def.
Open Scope bool_scope.
Open Scope Z.

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
  destruct H.
  destruct H0.
  unfold CompareISODate.
  simpl.
  rewrite H.
  rewrite H0.
  rewrite H1.
  rewrite Z.gtb_ltb.
  rewrite Z.gtb_ltb.
  rewrite Z.gtb_ltb.
  rewrite Z.ltb_irrefl.
  rewrite Z.ltb_irrefl.
  rewrite Z.ltb_irrefl.
  reflexivity.
Qed.

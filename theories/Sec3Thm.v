Require Import Coq.Numbers.BinNums Coq.Program.Wf ZArith Sec3Def.
Open Scope bool_scope.
Open Scope Z.


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

From Ltac2 Require Import Ltac2.
From Stdlib Require Import Numbers.BinNums Program.Wf ZArith Lia.
From Temporal Require Import Sec12Def Sec13Def Sec13Thm.
Open Scope bool_scope.
Open Scope Z.

Ltac2 easy0 () := ltac1:(easy).
Ltac2 Notation easy := easy0 ().

Ltac2 lia0 () := ltac1:(lia).
Ltac2 Notation lia := lia0 ().

Ltac2 rec expand_match () :=
  Control.enter (fun () =>
    lazy_match! goal with
    | [ p : positive |- _ <= match _ with _ => _ end _ ] => 
        let p := Control.hyp p in
        destruct $p;
        expand_match ()
    | [ p : positive |- match _ with _ => _ end _ <= _ ] =>
        let p := Control.hyp p in
        destruct $p;
        expand_match ()
    | [ |- _ ] => ()
    end
  ).

Ltac2 solve_lower () :=
  Control.enter (fun () =>
    lazy_match! goal with
    | [ year : Z |- _ <= 28 + _ ] =>
        let year := Control.hyp year in
        destruct (MathematicalInLeapYear_0_or_1 (EpochTimeForYear $year)) as [H | H];
        rewrite &H;
        easy
    | [ |- _ <= 30 ] => easy
    | [ |- _ <= 31 ] => easy
    end
  ).

Ltac2 solve_upper () :=
  Control.enter (fun () =>
    lazy_match! goal with
    | [ year : Z |- 28 + _ <= _ ] =>
        let year := Control.hyp year in
        destruct (MathematicalInLeapYear_0_or_1 (EpochTimeForYear $year)) as [H | H];
        rewrite &H;
        easy
    | [ |- _ <= _ ] => easy 
    end
  ).

Lemma ISODaysInMonth_range : forall year month pre, 28 <= ISODaysInMonth year month pre <= 31.
Proof.
  intros.
  split; unfold ISODaysInMonth; destruct month.
  - solve_lower ().
  - expand_match ().
    all: solve_lower ().
  - solve_lower ().
  - solve_upper ().
  - expand_match ().
    all: solve_upper ().
  - solve_upper ().
Qed.

Lemma ISODaysInMonth_at_least_1 : forall year month pre, 1 <= ISODaysInMonth year month pre.
Proof.
  intros.
  destruct (ISODaysInMonth_range year month pre).
  apply Z.le_trans with (m := 28).
  - easy.
  - assumption.
Qed.
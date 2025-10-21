From Ltac2 Require Import Ltac2.
From Stdlib Require Import ZArith Lia.
From Temporal Require Import Basic Section13.DateEquations.
Open Scope Z.

(* Notations to use the `easy` and `lia` tactics *)
Ltac2 easy0 () := ltac1:(easy).
Ltac2 Notation easy := easy0 ().

Ltac2 lia0 () := ltac1:(lia).
Ltac2 Notation lia := lia0 ().

(* 12.3.17 ISODaysInMonth *)
(*>> The abstract operation ISODaysInMonth takes arguments year (an integer) and
     month (an integer in the inclusive interval from 1 to 12) and returns a
     positive integer. <<*)
Definition ISODaysInMonth (year month : Z) (h : 1 <= month <= 12) : Z.
  ltac1:(refine (
    match month as m return (month = m -> Z) with
    (*>> 1. If month is 1, 3, 5, 7, 8, 10, or 12, return 31. <<*)
    | 1 | 3 | 5 | 7 | 8 | 10 | 12 => fun _ => 31
    (*>> 2. If month is 4, 6, 9, or 11, return 30. <<*)
    | 4 | 6 | 9 | 11 => fun _ => 30
    | month => fun h =>
        (*>> 3. Assert: month = 2. <<*)
        assert month = 2 in
        (*>> 4. Return 28 + MathematicalInLeapYear(EpochTimeForYear(year)). <<*)
        28 + MathematicalInLeapYear (EpochTimeForYear year)
    end eq_refl
  )).

  (* Proof of the assert *)
  all: lia.
Defined.

(* Tactic to expand a `match p with ... end` to the individual cases.  Used
   because `repeat (destruct p)` takes too long :-) *)
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

(* Solves the goals that look like `30 <= 31`, `28 <= 28 + ...` *)
Ltac2 discharge_bound name :=
  let name := Control.hyp name in
  destruct (MathematicalInLeapYear_0_or_1 (EpochTimeForYear $name)) as [H | H];
  rewrite &H;
  easy.

Ltac2 solve_bound () :=
  Control.enter (fun () =>
    lazy_match! goal with
    | [ year : Z |- _ <= 28 + _ ] => discharge_bound year
    | [ year : Z |- 28 + _ <= _ ] => discharge_bound year
    | [ |- _ <= _ ] => easy
    | [ |- _ <= _ ] => easy
    end
  ).

Lemma ISODaysInMonth_range : forall year month pre, 28 <= ISODaysInMonth year month pre <= 31.
Proof.
  intros.
  split; unfold ISODaysInMonth; destruct month.
  - solve_bound ().
  - expand_match ().
    all: solve_bound ().
  - solve_bound ().
  - solve_bound ().
  - expand_match ().
    all: solve_bound ().
  - solve_bound ().
Qed.

Lemma ISODaysInMonth_at_least_1 : forall year month pre, 1 <= ISODaysInMonth year month pre.
Proof.
  intros.
  destruct (ISODaysInMonth_range year month pre).
  apply Z.le_trans with (m := 28).
  - easy.
  - assumption.
Qed.

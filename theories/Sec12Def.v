Require Import Coq.Numbers.BinNums Coq.Program.Wf ZArith.
From Temporal Require Import Basic Sec13Def.
Open Scope bool_scope.
Open Scope Z.

(* 12.3.17 ISODaysInMonth *)
Program Definition ISODaysInMonth (year month : Z) (h : 1 <= month <= 12) : Z :=
  match month with
  (*>> 1. If month is 1, 3, 5, 7, 8, 10, or 12, return 31. <<*)
  | 1 | 3 | 5 | 7 | 8 | 10 | 12 => 31
  (*>> 2. If month is 4, 6, 9, or 11, return 30. <<*)
  | 4 | 6 | 9 | 11 => 30
  | month =>
      (*>> 3. Assert: month = 2. <<*)
      assert month = 2 in
      (*>> 4. Return 28 + MathematicalInLeapYear(EpochTimeForYear(year)). <<*)
      28 + MathematicalInLeapYear (EpochTimeForYear year)
  end.

(* assert month = 2 *)
Next Obligation.
Proof.
  lia.
Qed.

Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.
Next Obligation. Proof. easy. Qed.

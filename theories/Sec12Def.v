Require Import Coq.Numbers.BinNums Coq.Program.Wf ZArith.
From Temporal Require Export Sec13Def.
Open Scope bool_scope.
Open Scope Z.

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

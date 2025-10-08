From Stdlib Require Import Numbers.BinNums Program.Wf ZArith Strings.String Numbers.DecimalString Init.Decimal.
Open Scope bool_scope.
Open Scope string_scope.
Open Scope Z.

Definition Z_to_string (x : Z) : string :=
  NilEmpty.string_of_int (Z.to_int x).

Inductive PadPlacement := START | END.

Definition RotateString (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => s' ++ String c EmptyString
  end.

Fixpoint RepeatString (fillString : string) (fillLen : nat) : string :=
  match fillLen with
  | O => EmptyString
  | S n => 
    match fillString with
    | EmptyString => EmptyString
    | String c _ => String c (RepeatString (RotateString fillString) n)
    end
  end.

Definition StringPad (S : string) (maxLength : Z) (fillString : string) (placement : PadPlacement) (h1 : 0 <= maxLength) : string := 
  let stringLength := Z.of_nat (length S) in
  if maxLength <=? stringLength then S
  else if eqb fillString EmptyString then S
  else let fillLen := maxLength - stringLength in
  let truncatedStringFiller := RepeatString fillString (Z.to_nat fillLen) in
  match placement with
  | START => truncatedStringFiller ++ S
  | END => S ++ truncatedStringFiller
  end.

Definition ToZeroPaddedDecimalString (n minLength : Z) (h1 : 0 <= n) (h2 : 0 <= minLength) : string :=
  let S := Z_to_string n in
  StringPad S minLength "0" START h2.

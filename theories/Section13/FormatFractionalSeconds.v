From Stdlib Require Import ZArith Strings.String Ascii.
From Temporal Require Import Section13.Precision StringUtil.
Open Scope string_scope.
Open Scope Z.

Fixpoint RemoveTrailingZero (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => 
    match RemoveTrailingZero s' with
    | EmptyString => if eqb c "0"%char then EmptyString else String c EmptyString
    | s'' => String c EmptyString ++ s''
    end
  end. 

(* 13.25 FormatFractionalSeconds *)
Program Definition FormatFractionalSeconds (subSecondNanoseconds : Z) (precision : Precision) (subSecondNanoseconds_valid : 0 <= subSecondNanoseconds <= 999999999) : string :=
  match precision with
  (*>> 1. If precision is auto, then <<*)
  | AUTO =>
  (*>> a. If subSecondNanoseconds = 0, return the empty String. <<*)
    if subSecondNanoseconds =? 0 then EmptyString
    (*>> b. Let fractionString be ToZeroPaddedDecimalString(subSecondNanoseconds, 9). <<*)
    else let fractionString := ToZeroPaddedDecimalString subSecondNanoseconds 9 _ _ in
    (*>> c. Set fractionString to the longest prefix of fractionString ending with a code unit other than 0x0030 (DIGIT ZERO). <<*)
    let fractionString' := RemoveTrailingZero fractionString in
    (* NOTE: This is also step 3. *)
    "." ++ fractionString'
  (*>> 2. Else, <<*)
  | PrecisionValue p _ => 
    (*>> a. If precision = 0, return the empty String. <<*)
    if p =? 0 then EmptyString
    (*>> b. Let fractionString be ToZeroPaddedDecimalString(subSecondNanoseconds, 9). <<*)
    else let fractionString := ToZeroPaddedDecimalString subSecondNanoseconds p _ _ in
    (*>> c. Set fractionString to the substring of fractionString from 0 to precision. <<*)
    let fractionString' := fractionString in
  (*>> 3. Return the string-concatenation of the code unit 0x002E (FULL STOP) and fractionString. <<*)
    "." ++ fractionString'
  end.

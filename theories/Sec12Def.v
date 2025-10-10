From Stdlib Require Import Numbers.BinNums Program.Wf ZArith Lia Strings.String Ascii.
From Temporal Require Import Basic Sec13Def.
Open Scope bool_scope.
Open Scope string_scope.
Open Scope Z.

(* 12.3.17 ISODaysInMonth *)
(*>> The abstract operation ISODaysInMonth takes arguments year (an integer) and
     month (an integer in the inclusive interval from 1 to 12) and returns a
     positive integer. It returns the number of days in the given year and month
     in the ISO 8601 calendar. It performs the following steps when called: <<*)
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
Next Obligation. Proof. lia. Qed.
Solve Obligations with easy.

Inductive ShowCalendar := SC_AUTO | SC_ALWAYS | SC_NEVER | SC_CRITICAL.

Definition ValidCalendarTypeChars : string := "abcdefghijklmnopqrstuvwxyz0123456789".

Fixpoint IsInString (c : ascii) (s : string) : bool :=
  match s with
  | String c' s' => if eqb c c' then true else IsInString c s'
  | EmptyString => false
  end.

Fixpoint IsValidCalendarType (calendarType : string) : bool :=
  match calendarType with
  | String c s => 
    if IsInString c ValidCalendarTypeChars 
    then IsValidCalendarType s
    else match c, s with
    | "-"%char, String "-" _  => false
    | "-"%char, EmptyString => false
    | "-"%char, _ =>  IsValidCalendarType s
    | _, _ => false
    end
  | EmptyString => true
  end.
(* 12.1 Calendar Types *)
Inductive CalendarType := mkCalendarType (calendarTypeId : string) (calendarType_valid : IsValidCalendarType calendarTypeId = true).

(* 12.3.15 FormatCalendarAnnotation *)
Definition FormatCalendarAnnotation (id' : CalendarType) (showCalendar : ShowCalendar) : string :=
  match showCalendar, id' with
  (*>> 1. If showCalendar is never, return the empty String. <<*)
  | SC_NEVER, _ => EmptyString
  (*>> 2. If showCalendar is auto and id is "iso8601", return the empty String. <<*)
  | SC_AUTO, mkCalendarType "iso8601" _ => EmptyString
  (*>> 3. If showCalendar is critical, let flag be "!"; else, let flag be the empty String. <<*)
  | _, _ => 
    let flag := match showCalendar with
    | SC_CRITICAL => "!"
    | _ => EmptyString
    end in
  (*>> 4. Return the string-concatenation of "[", flag, "u-ca=", id, and "]". <<*)
    let idStringValue := match id' with
    | mkCalendarType s _ => s
    end in
    "[" ++ flag ++ "u-ca=" ++ idStringValue ++ "]"
  end.

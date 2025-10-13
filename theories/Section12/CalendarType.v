From Stdlib Require Import
  Strings.String
  Ascii.
Open Scope char_scope.

Definition ValidCalendarTypeChars : string := "abcdefghijklmnopqrstuvwxyz0123456789"%string.

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
    | "-", String "-" _  => false
    | "-", EmptyString => false
    | "-", _ =>  IsValidCalendarType s
    | _, _ => false
    end
  | EmptyString => true
  end.

(* 12.1 Calendar Types *)
Inductive CalendarType := mkCalendarType (calendarTypeId : string) (calendarType_valid : IsValidCalendarType calendarTypeId = true).

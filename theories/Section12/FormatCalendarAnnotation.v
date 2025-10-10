From Stdlib Require Import Strings.String.
From Temporal Require Import Section12.CalendarType Section12.ShowCalendar.
Open Scope string_scope.

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

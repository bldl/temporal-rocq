Require Import Coq.Numbers.BinNums Coq.Program.Wf ZArith Sec12Def.
Open Scope bool_scope.
Open Scope Z.

(* 3.5.1 ISODateRecord *)
(*>>
Field Name |	Value                                 |  Meaning
[[Year]]   | an integer                             | The year in the ISO 8601 calendar.
[[Month]]  | an integer between 1 and 12, inclusive | The number of the month in the ISO 8601 calendar.
[[Day]]    | an integer between 1 and 31, inclusive | The number of the day of the month in the ISO 8601 calendar. 
<<*)
Record ISODateRecord : Type :=
  mkISODateRecord {
    year : Z;
    month : Z;
    day : Z;
  }.

(* 3.5.12 CompareISODate *)
Definition CompareISODate (isoDate1 isoDate2 : ISODateRecord) : Z :=
  (*>> 1. If isoDate1.[[Year]] > isoDate2.[[Year]], return 1. <<*)
  if (year isoDate1) >? (year isoDate2) then 1
  (*>> 2. If isoDate1.[[Year]] < isoDate2.[[Year]], return -1. <<*)
  else if (year isoDate1) <? (year isoDate2) then -1
  (*>> 3. If isoDate1.[[Month]] > isoDate2.[[Month]], return 1. <<*)
  else if (month isoDate1) >? (month isoDate2) then 1
  (*>> 4. If isoDate1.[[Month]] < isoDate2.[[Month]], return -1. <<*)
  else if (month isoDate1) <? (month isoDate2) then -1
  (*>> 5. If isoDate1.[[Day]] > isoDate2.[[Day]], return 1. <<*)
  else if (day isoDate1) >? (day isoDate2) then 1
  (*>> 6. If isoDate1.[[Day]] < isoDate2.[[Day]], return -1. <<*)
  else if (day isoDate1) <? (day isoDate2) then -1
  (*>> 7. Return 0. <<*)
  else 0.


(* 3.5.7 IsValidISODate *)
Definition IsValidISODate (year month day : Z) : bool :=
  (*>> 1. If month < 1 or month > 12, then <<*)
  if (month <? 1) || (month >? 12) then
    (*>> a. Return false. <<*)
    false
  (*>> 2. Let daysInMonth be ISODaysInMonth(year, month). <<*)
  else let daysInMonth := (ISODaysInMonth year month) in
    (*>> 3. If day < 1 or day > daysInMonth, then <<*)
    if (day <? 1) || (day >? daysInMonth) then
      (*>> a. Return false. <<*)
      false
    (*>> 4. Return true. <<*)
    else true.


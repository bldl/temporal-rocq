Require Import Coq.Numbers.BinNums ZArith.

(* 3.5.1 ISODateRecord *)
Record ISODateRecord : Type :=
  mkISODateRecord {
    year : Z;
    month : Z;
    day : Z;
  }.

(* 3.5.12 CompareISODate *)
Definition CompareISODate (isoDate1 isoDate2 : ISODateRecord) : Z :=
  if Z.gtb (year isoDate1) (year isoDate2) then 1
  else if Z.ltb (year isoDate1) (year isoDate2) then -1
  else if Z.gtb (month isoDate1) (month isoDate2) then 1
  else if Z.ltb (month isoDate1) (month isoDate2) then -1
  else if Z.gtb (day isoDate1) (day isoDate2) then 1
  else if Z.ltb (day isoDate1) (day isoDate2) then -1
  else 0.

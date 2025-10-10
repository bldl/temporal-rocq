From Stdlib Require Import ZArith.
From Temporal Require Import Basic Section3.CompareISODate Section4.CompareTimeRecord Section5.ISODateTimeRecord.
Open Scope Z.

(* 5.5.10 CompareISODateTime *)
Definition CompareISODateTime (isoDateTime1 isoDateTime2 : ISODateTimeRecord) : Z :=
  (*>> 1. Let dateResult be CompareISODate(isoDateTime1.[[ISODate]], isoDateTime2.[[ISODate]]). <<*)
  let dateResult := CompareISODate (ISODate isoDateTime1) (ISODate isoDateTime2) in
  (*>> 2. If dateResult ≠ 0, return dateResult. <<*)
  if dateResult !=? 0 then dateResult
  (*>> 3. Return CompareTimeRecord(isoDateTime1.[[Time]], isoDateTime2.[[Time]]). <<*)
  else CompareTimeRecord (Time isoDateTime1) (Time isoDateTime2).

From Stdlib Require Import ZArith.
From Temporal Require Import
  Section3.CompareISODate
  Section4.CompareTimeRecord
  Section4.TimeRecord
  Section5.CombineISODateAndTimeRecord
  Section5.CompareISODateTime
  Section5.ISODateTimeRecord
  Section5.ISODateTimeToString.
Open Scope Z.

(* 5.5.3 CombineISODateAndTimeRecord *)
(*>> 1. NOTE: time.[[Days]] is ignored. <<*)
Definition With (f : ISODateTimeRecord -> ISODateTimeRecord -> Prop) : Prop :=
  forall i iv d0 d0v d1 d1v h hv m mv s sv ms msv us usv ns nsv,
  let t0 := mkTimeRecord d0 d0v h hv m mv s sv ms msv us usv ns nsv in
  let t1 := mkTimeRecord d1 d1v h hv m mv s sv ms msv us usv ns nsv in
  let t0v := TimeRecord_IsValidTime t0 in
  let t1v := TimeRecord_IsValidTime t1 in
  f (mkISODateTimeRecord i iv t0 t0v) (mkISODateTimeRecord i iv t1 t1v).

Theorem CompareISODate_holds :
  With (fun i0 i1 => CompareISODateTime i0 i1 = 0).
Proof.
  unfold With.
  unfold CompareISODateTime.
  intros.
  rewrite CompareISODate_eq_zero.
  apply CompareTimeRecord_ignores_days.
Qed.
Theorem ISODateTimeToString_holds :
  With (fun i0 i1 => ISODateTimeToString i0 = ISODateTimeToString i1).
Proof.
  unfold With.
  unfold ISODateTimeToString.
  reflexivity.
Qed.

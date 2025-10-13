From Stdlib Require Import ZArith.
From Temporal Require Import Section4.TimeRecord.
Open Scope Z.

(* 4.5.14 CompareTimeRecord *)
Definition CompareTimeRecord (time1 time2 : TimeRecord) : Z :=
  (*>> 1. If time1.[[Hour]] > time2.[[Hour]], return 1. <<*)
  if hour time1 >? hour time2 then 1
  (*>> 2. If time1.[[Hour]] < time2.[[Hour]], return -1. <<*)
  else if hour time1 <? hour time2 then -1
  (*>> 3. If time1.[[Minute]] > time2.[[Minute]], return 1. <<*)
  else if minute time1 >? minute time2 then 1
  (*>> 4. If time1.[[Minute]] < time2.[[Minute]], return -1. <<*)
  else if minute time1 <? minute time2 then -1
  (*>> 5. If time1.[[Second]] > time2.[[Second]], return 1. <<*)
  else if second time1 >? second time2 then 1
  (*>> 6. If time1.[[Second]] < time2.[[Second]], return -1. <<*)
  else if second time1 <? second time2 then -1
  (*>> 7. If time1.[[Millisecond]] > time2.[[Millisecond]], return 1. <<*)
  else if millisecond time1 >? millisecond time2 then 1
  (*>> 8. If time1.[[Millisecond]] < time2.[[Millisecond]], return -1. <<*)
  else if millisecond time1 <? millisecond time2 then -1
  (*>> 9. If time1.[[Microsecond]] > time2.[[Microsecond]], return 1. <<*)
  else if microsecond time1 >? microsecond time2 then 1
  (*>> 10. If time1.[[Microsecond]] < time2.[[Microsecond]], return -1. <<*)
  else if microsecond time1 <? microsecond time2 then -1
  (*>> 11. If time1.[[Nanosecond]] > time2.[[Nanosecond]], return 1. <<*)
  else if nanosecond time1 >? nanosecond time2 then 1
  (*>> 12. If time1.[[Nanosecond]] < time2.[[Nanosecond]], return -1. <<*)
  else if nanosecond time1 <? nanosecond time2 then -1
  (*>> 13. Return 0. <<*)
  else 0.

(** States that `CompareTimeRecord` ignores the `deltaDays` component. *)
Lemma CompareTimeRecord_ignores_days :
  forall d0 d0v d1 d1v,
  forall h hv m mv s sv ms msv us usv ns nsv,
  let t0 := mkTimeRecord d0 d0v h hv m mv s sv ms msv us usv ns nsv in
  let t1 := mkTimeRecord d1 d1v h hv m mv s sv ms msv us usv ns nsv in
  CompareTimeRecord t0 t1 = 0.
Proof.
  intros.
  unfold CompareTimeRecord.
  simpl.
  repeat (rewrite Z.gtb_ltb, Z.ltb_irrefl).
  reflexivity.
Qed.

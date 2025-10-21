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

Theorem CompareTimeRecord_eq_zero : forall time, CompareTimeRecord time time = 0.
Admitted.

Theorem CompareTimeRecord_eq_implies_eq_zero :
  forall (d1 d2 h1 h2 m1 m2 s1 s2 ms1 ms2 us1 us2 ns1 ns2 : Z),
  h1 = h2 /\ m1 = m2 /\ s1 = s2 /\ ms1 = ms2 /\ us1 = us2 /\ ns1 = ns2 ->
  forall (d1_valid : d1 >= 0) (h1_valid : 0 <= h1 <= 23) (m1_valid : 0 <= m1 <= 59) (s1_valid : 0 <= s1 <= 59)
  (ms1_valid : 0 <= ms1 <= 999) (us1_valid : 0 <= us1 <= 999) (ns1_valid : 0 <= ns1 <= 999)
  (d2_valid : d2 >= 0) (h2_valid : 0 <= h2 <= 23) (m2_valid : 0 <= m2 <= 59) (s2_valid : 0 <= s2 <= 59)
  (ms2_valid : 0 <= ms2 <= 999) (us2_valid : 0 <= us2 <= 999) (ns2_valid : 0 <= ns2 <= 999),
  CompareTimeRecord (mkTimeRecord d1 d1_valid h1 h1_valid m1 m1_valid s1 s1_valid ms1 ms1_valid us1 us1_valid ns1 ns1_valid)
                    (mkTimeRecord d2 d2_valid h2 h2_valid m2 m2_valid s2 s2_valid ms2 ms2_valid us2 us2_valid ns2 ns2_valid) = 0.
Admitted.

From Stdlib Require Import
  ZArith
  Lia.
From Temporal Require Import
  Basic
  Section4.TimeRecord
  Section7.TimeDurationFromComponents
  Section8.nsPerDay.
Open Scope Z.

(* 4.5.5 DifferenceTime *)
Program Definition DifferenceTime (time1 time2 : TimeRecord) : Z :=
  (*>> 1. Let hours be time2.[[Hour]] - time1.[[Hour]]. <<*)
  let hours := (hour time2) - (hour time1) in
  (*>> 2. Let minutes be time2.[[Minute]] - time1.[[Minute]]. <<*)
  let minutes := (minute time2) - (minute time1) in
  (*>> 3. Let seconds be time2.[[Second]] - time1.[[Second]]. <<*)
  let seconds := (second time2) - (second time1) in
  (*>> 4. Let milliseconds be time2.[[Millisecond]] - time1.[[Millisecond]]. <<*)
  let milliseconds := (millisecond time2) - (millisecond time1) in
  (*>> 5. Let microseconds be time2.[[Microsecond]] - time1.[[Microsecond]]. <<*)
  let microseconds := (microsecond time2) - (microsecond time1) in
  (*>> 6. Let nanoseconds be time2.[[Nanosecond]] - time1.[[Nanosecond]]. <<*)
  let nanoseconds := (nanosecond time2) - (nanosecond time1) in
  (*>> 7. Let timeDuration be TimeDurationFromComponents(hours, minutes, seconds, milliseconds, microseconds, nanoseconds). <<*)
  let timeDuration := TimeDurationFromComponents hours minutes seconds milliseconds microseconds nanoseconds in
  (*>> 8. Assert: abs(timeDuration) < nsPerDay. <<*)
  assert (Z.abs timeDuration) < nsPerDay in
  (*>> 9. Return timeDuration. <<*)
  timeDuration.

Next Obligation.
  unfold nsPerDay.
  unfold msPerDay.msPerDay.
  simpl.
  unfold TimeDurationFromComponents.
  destruct (nanosecond_valid time1).
  destruct (nanosecond_valid time2).
  destruct (microsecond_valid time1).
  destruct (microsecond_valid time2).
  destruct (millisecond_valid time1).
  destruct (millisecond_valid time2).
  destruct (second_valid time1).
  destruct (second_valid time2).
  destruct (minute_valid time1).
  destruct (minute_valid time2).
  destruct (hour_valid time1).
  destruct (hour_valid time2).
  lia.
Qed.

From Stdlib Require Import ZArith.
From Temporal Require Import 
  Section4.CreateTimeRecord
  Section4.IsValidTime
  Section4.TimeRecord.
Open Scope Z.

Lemma mod_pos_bound (b : Z) (h : 0 < b) : forall a, 0 <= a mod b <= b - 1.
Proof.
  intro a.
  split.
  - exact (proj1 (Z.mod_pos_bound a b h)).
  - apply (Zlt_succ_le (a mod b) (b - 1)).
    rewrite Z.sub_1_r.
    rewrite Z.succ_pred.
    exact (proj2 (Z.mod_pos_bound a b h)).
Qed.

(*>> 4.5.10 BalanceTime <<*)
Program Definition BalanceTime (hour minute second millisecond microsecond nanosecond : Z) : TimeRecord :=
  (*>> 1. Set microsecond to microsecond + floor(nanosecond / 1000). <<*)
  let microsecond' := microsecond + nanosecond / 1000 in
  (*>> 2. Set nanosecond to nanosecond modulo 1000. <<*)
  let nanosecond' := nanosecond mod 1000 in
  (*>> 3. Set millisecond to millisecond + floor(microsecond / 1000). <<*)
  let millisecond' :=  millisecond + microsecond / 1000 in
  (*>> 4. Set microsecond to microsecond modulo 1000. <<*)
  let microsecond'' := microsecond' mod 1000 in
  (*>> 5. Set second to second + floor(millisecond / 1000). <<*)
  let second' := second + millisecond' / 1000 in
  (*>> 6. Set millisecond to millisecond modulo 1000. <<*)
  let millisecond'' := millisecond' mod 1000 in
  (*>> 7. Set minute to minute + floor(second / 60). <<*)
  let minute' := minute + second' / 60 in
  (*>> 8. Set second to second modulo 60. <<*)
  let second'' := second' mod 60 in
  (*>> 9. Set hour to hour + floor(minute / 60). <<*)
  let hour' := hour + minute' / 60 in
  (*>> 10. Set minute to minute modulo 60. <<*)
  let minute'' := minute' mod 60 in
  (*>> 11. Let deltaDays be floor(hour / 24). <<*)
  let deltaDays := hour' / 24 in
  (*>> 12. Set hour to hour modulo 24. <<*)
  let hour'' := hour' mod 24 in
  (*>> 13. Return CreateTimeRecord(hour, minute, second, millisecond, microsecond, nanosecond, deltaDays). <<*)
  CreateTimeRecord hour'' minute'' second'' millisecond'' microsecond'' nanosecond' (Some deltaDays) _ _ _ _ _ _ _.

(* DeltaDaysValid (Some deltaDays) *)
Next Obligation. Admitted.

Next Obligation. refine (mod_pos_bound 24 _ _). easy. Qed.
Next Obligation. refine (mod_pos_bound 60 _ _). easy. Qed.
Next Obligation. refine (mod_pos_bound 60 _ _). easy. Qed.
Next Obligation. refine (mod_pos_bound 1000 _ _). easy. Qed.
Next Obligation. refine (mod_pos_bound 1000 _ _). easy. Qed.
Next Obligation. refine (mod_pos_bound 1000 _ _). easy. Qed.

Lemma mod_if_range :
  forall e u otherwise, 0 < u -> otherwise = true ->
  (if ((e mod u) <? 0) || ((e mod u) >? Z.pred u) then false else otherwise) = true.
Proof.
  intros.
  destruct (((e mod u) <? 0) || ((e mod u) >? Z.pred u)) eqn: range.
  - exfalso.
    destruct (Bool.orb_true_elim _ _ range).
    + rewrite Z.ltb_lt in e0.
      apply Z.lt_irrefl with (x := 0).
      apply Z.le_lt_trans with (m := (e mod u)).
      apply Z.mod_pos_bound.
      assumption.
      assumption.
    + rewrite Z.gtb_ltb in e0.
      rewrite Z.ltb_lt in e0.
      apply Z.lt_irrefl with (x := Z.pred u).
      apply Z.lt_le_trans with (m := e mod u).
      assumption.
      rewrite <- Z.lt_succ_r.
      rewrite Z.succ_pred.
      now apply Z.mod_pos_bound.
  - assumption.
Qed.

Theorem BalanceTime_IsValidTime :
  forall h min s ms us ns,
  let t := BalanceTime h min s ms us ns in
  IsValidTime (hour t) (minute t) (second t) (millisecond t) (microsecond t) (nanosecond t) = true.
Proof.
  intros.
  unfold IsValidTime.
  repeat (apply mod_if_range; try easy).
Qed.

Theorem BalanceTime_days_valid_when_nonnegative_inputs :
  forall h min s ms us ns,
  0 <= h -> 0 <= min -> 0 <= s -> 0 <= ms -> 0 <= us -> 0 <= ns ->
  0 <= days (BalanceTime h min s ms us ns).
Proof.
  intros.
  unfold BalanceTime.
  repeat (apply Z.div_pos; try (apply Z.add_nonneg_nonneg); try assumption); easy.
Qed.

(* Proves that BalanceTime can create invalid Time Records *)
Theorem BalanceTime_creates_invalid_TimeRecord :
  exists hour, days (BalanceTime hour 0 0 0 0 0) < 0.
Proof.
  exists (-42).
  easy.
Qed.

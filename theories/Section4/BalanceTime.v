From Stdlib Require Import ZArith.
From Temporal Require Import 
  Section4.CreateTimeRecord
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
Next Obligation.
Proof.
Admitted.

Next Obligation. Proof. refine (mod_pos_bound 24 _ _). easy. Qed.
Next Obligation. Proof. refine (mod_pos_bound 60 _ _). easy. Qed.
Next Obligation. Proof. refine (mod_pos_bound 60 _ _). easy. Qed.
Next Obligation. Proof. refine (mod_pos_bound 1000 _ _). easy. Qed.
Next Obligation. Proof. refine (mod_pos_bound 1000 _ _). easy. Qed.
Next Obligation. Proof. refine (mod_pos_bound 1000 _ _). easy. Qed.

(* Proofs that BalanceTime is missing a precondition *)
Theorem delta_days_can_be_negative : exists hour, days (BalanceTime hour 0 0 0 0 0) < 0.
Proof.
  exists (-42).
  unfold BalanceTime.
  simpl.
  easy.
Qed.

Theorem BalanceTime_inconsistent : False.
Proof.
  destruct delta_days_can_be_negative.
  pose (days_valid (BalanceTime x 0 0 0 0 0)) as H1.
  contradiction.
Qed.

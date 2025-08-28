Require Import Coq.Numbers.BinNums ZArith.
Open Scope bool_scope.
Open Scope Z.

(* 3.5.1 ISODateRecord *)
Record ISODateRecord : Type :=
  mkISODateRecord {
    year : Z;
    month : Z;
    day : Z;
  }.

(* 3.5.12 CompareISODate *)
Definition CompareISODate (isoDate1 isoDate2 : ISODateRecord) : Z :=
  if (year isoDate1) >? (year isoDate2) then 1
  else if (year isoDate1) <? (year isoDate2) then -1
  else if (month isoDate1) >? (month isoDate2) then 1
  else if (month isoDate1) <? (month isoDate2) then -1
  else if (day isoDate1) >? (day isoDate2) then 1
  else if (day isoDate1) <? (day isoDate2) then -1
  else 0.

Theorem CompareISODate_eq_implies_eq_zero :
  forall (y1 y2 m1 m2 d1 d2 : Z),
  y1 = y2 /\ m1 = m2 /\ d1 = d2 ->
  CompareISODate (mkISODateRecord y1 m1 d1) (mkISODateRecord y2 m2 d2) = 0.
Proof.
  intros y1 y2 m1 m2 d1 d2.
  intro H.
  destruct H.
  destruct H0.
  rewrite H.
  rewrite H0.
  rewrite H1.
  unfold CompareISODate.
  rewrite Z.gtb_ltb.
  rewrite Z.gtb_ltb.
  rewrite Z.gtb_ltb.
  rewrite Z.ltb_irrefl.
  rewrite Z.ltb_irrefl.
  rewrite Z.ltb_irrefl.
  reflexivity.
Qed.

(* Assumption: 
  EpochDayNumberForYear and msPerDay works on Z and not real numbers *)
Definition msPerDay : Z := 86400000.

(* 13.3 Date Equations *)
(* Note: `/` is floor division with Z. 
  https://rocq-prover.org/doc/V8.21%2Balpha/stdlib/Coq.ZArith.BinIntDef.html#Z.div_eucl *)
Definition EpochDayNumberForYear (y : Z) : Z :=
  365 * (y - 1970) + ((y - 1969) / 4) - ((y - 1901) / 100) + ((y - 1601) / 400).

Definition EpochTimeForYear (y : Z) : Z :=
  msPerDay * EpochDayNumberForYear y.

Inductive Direction :=
  Forwards | Backwards.

Fixpoint FindYear (f : nat) (t y : Z) (dir : Direction) : Z := 
  let t' := t - Z.abs (EpochTimeForYear y) in
  match f with
  | O => 0
  | S f' => (
    if t' <? 0
    then match dir with 
    | Forwards => y - 1
    | Backwards => y + 1
    end
    else if t' =? 0 then y
    else match dir with
    | Forwards => FindYear f' t (y + 1) Forwards
    | Backwards => FindYear f' t (y - 1) Backwards
    end)
  end.

Definition EpochTimeToEpochYear (t : Z) : Z :=
  if t >? 0 then FindYear 5000 t 1970 Forwards else FindYear 5000 (Z.abs t) 1969 Backwards.

Inductive DaysInYear :=
  Normal | Leap.

Definition MathematicalDaysInYear (y : Z) : DaysInYear :=
  match (y mod 4) =? 0, (y mod 100) =? 0, (y mod 400) =? 0 with
  | false, _,     _    => Normal
  | true,  false, _    => Leap
  | _,     true, false => Normal
  | _,     _,    true  => Leap
  end.

Definition MathematicalInLeapYear (t : Z) : Z :=
  match MathematicalDaysInYear (EpochTimeToEpochYear t) with
  | Normal => 0
  | Leap => 1
  end.
(* 13.3 end *)

(* TODO: Assert month is 2 *)
(* 12.3.17 ISODaysInMonth *)
Definition ISODaysInMonth (year month : Z) : Z :=
  match month with
  | 1 | 3 | 5 | 7 | 8 | 10 | 12 => 31
  | 4 | 6 | 9 | 11 => 30
  | _ => 28 + MathematicalInLeapYear (EpochTimeForYear year)
  end.

(* 3.5.7 IsValidISODate *)
Definition IsValidISODate (year month day : Z) : bool :=
  if (month <? 1) || (month >? 12) then false
  else let daysInMonth := (ISODaysInMonth year month) in
    if (day <? 1) || (day >? daysInMonth) then false
    else true.

(* 4.5.9 IsValidTime *)
Definition IsValidTime (hour minute second millisecond microsecond nanosecond : Z) : bool :=
  if (hour <? 0) || (hour >? 23) then false
  else if (minute <? 0) || (minute >? 59) then false
  else if (second <? 0) || (second >? 59) then false
  else if (millisecond <? 0) || (millisecond >? 999) then false
  else if (microsecond <? 0) || (microsecond >? 999) then false
  else if (nanosecond <? 0) || (nanosecond >? 999) then false
  else true.

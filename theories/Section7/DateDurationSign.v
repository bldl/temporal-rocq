From Stdlib Require Import
  ZArith
  Lia
  List.
From Temporal Require Import
  Basic
  Section7.DateDurationRecord
  Section7.MaxTimeDuration.
Open Scope Z.

(* 7.5.14 DateDurationSign *)
Definition DateDurationSign (dateDuration : DateDurationRecord) : Z :=
  let ValueSign := fix ValueSign (vs : list (DateDurationRecord -> Float64RepresentableInteger)) (dateDuration : DateDurationRecord) : option Z :=
    match vs with
    | nil => None
    | f :: vs' => let v := value (f dateDuration) in
      (*>> a. If v < 0, return -1. <<*)
      if v <? 0 then Some (-1)
      (*>> b. If v > 0, return 1. <<*)
      else if v >? 0 then Some 1
      else ValueSign vs' dateDuration
    end 
  in
  (*>> 1. For each value v of « dateDuration.[[Years]], dateDuration.[[Months]], dateDuration.[[Weeks]], dateDuration.[[Days]] », do <<*)
  match ValueSign (years :: months :: weeks :: days :: nil) dateDuration with
  | Some x => x
  (*>> 2. Return 0. <<*)
  | None => 0
  end.

Lemma DateDurationSign_zero_year :
  forall years months weeks days,
  DateDurationSign (mkDateDurationRecord years months weeks days) = 0 -> value years = 0.
Proof.
  intros.
  unfold DateDurationSign in H.
  simpl in H.
  destruct (value years <? 0) eqn:H0. easy.
  destruct (value years >? 0) eqn:H1. easy.
  destruct (value months <? 0). easy.
  destruct (value months >? 0). easy.
  destruct (value weeks <? 0). easy.
  destruct (value weeks >? 0). easy.
  destruct (value days <? 0). easy.
  destruct (value days >? 0). easy.
  rewrite Z.ltb_ge in H0.
  rewrite Z.gtb_ltb in H1.
  rewrite Z.ltb_ge in H1.
  apply Z.le_antisymm; assumption.
Qed.

Lemma DateDurationSign_positive_year :
  forall years months weeks days,
  0 < value years -> DateDurationSign (mkDateDurationRecord years months weeks days) = 1.
Proof.
  intros.
  unfold DateDurationSign.
  simpl.
  assert (H' : (value years >? 0) = true). {
    rewrite Z.gtb_ltb.
    rewrite Z.ltb_lt.
    assumption.
  }
  rewrite H'.
  destruct (value years <? 0) eqn: H0.
  - exfalso.
    rewrite Z.ltb_lt in H0.
    apply Z.lt_irrefl with (x := 0).
    apply Z.lt_trans with (m := value years); assumption.
  - reflexivity.
Qed.

Lemma DateDurationSign_negative_year :
  forall years months weeks days,
  value years < 0 -> DateDurationSign (mkDateDurationRecord years months weeks days) = -1.
Proof.
  intros.
  unfold DateDurationSign.
  simpl.
  rewrite <-Z.ltb_lt in H.
  rewrite H.
  reflexivity.
Qed.

Theorem DateDurationSign_year_sign_dominates :
  forall years months weeks days,
  (DateDurationSign (mkDateDurationRecord years months weeks days) = 0 -> value years = 0) /\
  (0 < value years -> DateDurationSign (mkDateDurationRecord years months weeks days) = 1) /\
  (value years < 0 -> DateDurationSign (mkDateDurationRecord years months weeks days) = (-1)).
Proof.
  intros.
  split; try split.
  apply DateDurationSign_zero_year.
  apply DateDurationSign_positive_year.
  apply DateDurationSign_negative_year.
Qed.

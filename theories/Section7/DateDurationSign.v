From Stdlib Require Import
  ZArith
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

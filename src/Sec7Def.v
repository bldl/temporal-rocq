From Stdlib Require Import ZArith ZArith.Zpow_alt List.
From Temporal Require Import Basic Section7.MaxTimeDuration Sec13Def.
Open Scope Z.

Record Float64RepresentableInteger :=
  mkFloat64RepresentableInteger {
    value : Z;
    in_range : -(2 ^^ 53) <= value <= (2 ^^ 53);
  }.

(* 7.5.1 Date Duration Records *)
Record DateDurationRecord :=
  mkDateDurationRecord {
    (*>> Field Name | Value                           | Meaning <<*)
    (*>> [[Years]]  | a float64-representable integer | The number of years in the duration. <<*)
    years : Float64RepresentableInteger;
    (*>> [[Months]] | a float64-representable integer | The number of months in the duration. <<*)
    months : Float64RepresentableInteger;
    (*>> [[Weeks]]  | a float64-representable integer | The number of weeks in the duration. <<*)
    weeks : Float64RepresentableInteger;
    (*>> [[Days]]   | a float64-representable integer | The number of days in the duration. <<*)
    days : Float64RepresentableInteger;
  }.

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

(* 7.5.21 TimeDurationFromComponents *) 
Program Definition TimeDurationFromComponents (hours minutes seconds milliseconds microseconds nanoseconds : Z) : Z :=
  (*>> 1. Set minutes to minutes + hours × 60. <<*)
  let minutes' := minutes + hours * 60 in
  (*>> 2. Set seconds to seconds + minutes × 60. <<*)
  let seconds' := seconds + minutes * 60 in
  (*>> 3. Set milliseconds to milliseconds + seconds × 1000. <<*)
  let milliseconds' := milliseconds + seconds * 1000 in
  (*>> 4. Set microseconds to microseconds + milliseconds × 1000. <<*)
  let microseconds' := microseconds + milliseconds * 1000 in
  (*>> 5. Set nanoseconds to nanoseconds + microseconds × 1000. <<*)
  let nanoseconds' := nanoseconds + microseconds * 1000 in
  (*>> 6. Assert: abs(nanoseconds) ≤ maxTimeDuration. <<*)
  assert Z.abs nanoseconds' <= MaxTimeDuration in
  (*>> 7. Return nanoseconds. <<*)
  nanoseconds'.

Next Obligation. Admitted.

(* 7.5.22 AddTimeDuration *)
Definition AddTimeDuration (one two : Z) 
  (one_valid : MinTimeDuration <= one <= MaxTimeDuration) (two_valid : MinTimeDuration <= two <= MaxTimeDuration) : Completion Z :=
  (*>> 1. Let result be one + two. <<*)
  let result := one + two in
  (*>> 2. If abs(result) > maxTimeDuration, throw a RangeError exception. <<*)
  if Z.abs result >? MaxTimeDuration then Throw RangeError
  (*>> 3. Return result. <<*)
  else Normal result.

Definition nsPerDay : Z := msPerDay * 1000000.

(* 7.5.23 Add24HourDaysToTimeDuration *)
Definition Add24HourDaysToTimeDuration (d days : Z) (d_valid : MinTimeDuration <= d <= MaxTimeDuration) : Completion Z :=
  (*>> 1. Let result be d + days × nsPerDay. <<*)
  let result := d + days * nsPerDay in
  (*>> 2. If abs(result) > maxTimeDuration, throw a RangeError exception. <<*)
  if Z.abs result >? MaxTimeDuration then Throw RangeError
  (*>> 3. Return result. <<*)
  else Normal result.

(* 7.5.24 AddTimeDurationToEpochNanoseconds *)
Definition AddTimeDurationToEpochNanoseconds (d epochNs : Z) (d_valid : MinTimeDuration <= d <= MaxTimeDuration) : Z :=
  (*>> 1. Return epochNs + ℤ(d). <<*)
  epochNs + d.

(* 7.5.25 CompareTimeDuration *)
Definition CompareTimeDuration (one two : Z)
(one_valid : MinTimeDuration <= one <= MaxTimeDuration) (two_valid : MinTimeDuration <= two <= MaxTimeDuration) : Z :=
  (*>> 1. If one > two, return 1. <<*)
  if one >? two then 1
  (*>> 2. If one < two, return -1. <<*)
  else if one <? two then -1
  (*>> 3. Return 0. <<*)
  else 0.

(* 7.5.26 TimeDurationFromEpochNanosecondsDifference *)
Program Definition TimeDurationFromEpochNanosecondsDifference (one two : Z) : Z :=
  (*>> 1. Let result be ℝ(one) - ℝ(two). <<*)
  let result := one - two in
  (*>> 2. Assert: abs(result) ≤ maxTimeDuration. <<*)
  assert Z.abs result <= MaxTimeDuration in
  (*>> 3. Return result. <<*)
  result.

Next Obligation. Admitted.

(* 7.5.28 TimeDurationSign *)
Definition TimeDurationSign (d : Z) (d_valid : MinTimeDuration <= d <= MaxTimeDuration) : Z :=
  (*>> 1. If d < 0, return -1. <<*)
  if d <? 0 then -1
  (*>> 2. If d > 0, return 1. <<*)
  else if d >? 0 then 1
  (*>> 3. Return 0. <<*)
  else 0.

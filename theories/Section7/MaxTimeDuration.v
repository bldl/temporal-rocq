From Stdlib Require Import ZArith.
Open Scope Z.

(*>> A time duration is an integer in the inclusive interval from -maxTimeDuration to maxTimeDuration,
  where maxTimeDuration = 2**53 × 10**9 - 1 = 9,007,199,254,740,991,999,999,999 <<*)
Definition MaxTimeDuration : Z := 9007199254740991999999999.
Definition MinTimeDuration : Z := (-9007199254740991999999999).

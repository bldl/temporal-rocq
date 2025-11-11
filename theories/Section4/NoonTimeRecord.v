From Stdlib Require Import ZArith.
From Temporal Require Import Section4.TimeRecord.
Open Scope Z.

(* 4.5.4 NoonTimeRecord *)
Program Definition NoonTimeRecord : TimeRecord :=
  (*>> 1. Return Time Record { [[Days]]: 0, [[Hour]]: 12, [[Minute]]: 0, [[Second]]: 0, [[Millisecond]]: 0, [[Microsecond]]: 0, [[Nanosecond]]: 0  }. <<*)
  mkTimeRecord 0 12 _ 0 _ 0 _ 0 _ 0 _ 0 _.

Solve Obligations with easy.

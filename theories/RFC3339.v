From Stdlib Require Import Ascii List Strings.String.
From Temporal Require Import Grammar.
Open Scope char_scope.

(* Defines the grammar from RFC 33339 *)
(* https://www.rfc-editor.org/rfc/rfc3339#section-5.6 *)

Definition date_fullyear := ntimes 4 digit.
Definition date_month    := ntimes 2 digit.
Definition date_mday     := ntimes 2 digit.

Definition time_hour    := ntimes 2 digit.
Definition time_minute  := ntimes 2 digit.
Definition time_second  := ntimes 2 digit.
Definition time_secfrac := seq (char "." :: digit :: star digit :: nil).
Definition time_numoffset :=
  seq (
    alternative (char "+") (char "-") :: time_hour :: char ":" :: time_minute :: nil
  ).
Definition time_offset :=
  alternative (alternative (char "Z") (char "z")) time_numoffset.

Definition partial_time :=
  seq (
    time_hour :: char ":" :: time_minute :: char ":" :: time_second ::
    maybe time_secfrac :: nil
  ).

Definition full_date :=
  seq (date_fullyear :: char "-" :: date_month :: char "-" :: date_mday :: nil).

Definition full_time := sequence partial_time time_offset.

Definition date_time :=
  seq (full_date :: alternative (char "T") (char "t") :: full_time :: nil).

Definition date_time_without_offset :=
  seq (full_date :: alternative (char "T") (char "t") :: partial_time :: nil).

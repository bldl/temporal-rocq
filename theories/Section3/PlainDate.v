From Temporal Require Import
  Section3.ISODateRecord
  Section12.CalendarType.

(* TODO: This should _really_ be an JS object *)
Record PlainDate := mkPlainDate {
  isoDate : ISODateRecord;
  calendar : CalendarType;
}.

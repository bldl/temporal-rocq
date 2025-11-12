From Stdlib Require Import List.
From Temporal Require Import
  Basic
  Section13.TemporalUnit
  Section13.TemporalUnitCategory
  Section13.TemporalUnitEqb.

Inductive TemporalUnit' :=
| NormalTemporalUnit (tu : TemporalUnit)
| TUP_AUTO.

Inductive TemporalUnit'' :=
| NormalTemporalUnit' (tu' : TemporalUnit')
| TUP_UNSET.

Inductive UnitGroup := UG_DATE | UG_TIME | UG_DATETIME.

Definition ContainsTemporalUnit' (l : option (list TemporalUnit')) (unit' : TemporalUnit') : bool :=
  match l with
  | Some l' =>
    match l' with
    | unit'' :: rest => 
      match unit', unit'' with
      | TUP_AUTO, TUP_AUTO => true
      | TUP_AUTO, _ => false
      | _, TUP_AUTO => false
      | NormalTemporalUnit nu, NormalTemporalUnit nu' => TemporalUnitEqb nu nu'
      end
    | nil => false
    end
  | None => false
  end.

(* 13.18 ValidateTemporalUnitValue *)
Definition ValidateTemporalUnitValue (value : TemporalUnit'') (unitGroup : UnitGroup)
  (extraValues : option (list TemporalUnit')) : Completion Unused :=
  (*>> 1. If value is unset, return unused. <<*)
  match value with
  | TUP_UNSET => Normal UNUSED
  | NormalTemporalUnit' unit' => 
    (*>> 2. If extraValues is present and extraValues contains value, return unused. <<*)
    match ContainsTemporalUnit' extraValues unit' with
    | true => Normal UNUSED
    | false =>
      (*>> 3. Let category be the value in the “Category” column of the row of Table 21 whose “Value” column contains value. If there is no such row, throw a RangeError exception. <<*)
      match unit' with
      | TUP_AUTO => Throw RangeError
      | NormalTemporalUnit unit'' =>
        let category := TemporalUnitCategory unit'' in
        match category, unitGroup with
        (*>> 4. If category is date and unitGroup is date or datetime, return unused. <<*)
        | DATE, UG_DATE => Normal UNUSED
        | DATE, UG_DATETIME => Normal UNUSED
        (*>> 5. If category is time and unitGroup is time or datetime, return unused. <<*)
        | TIME, UG_TIME => Normal UNUSED
        | TIME, UG_DATETIME => Normal UNUSED
        (*>> 6. Throw a RangeError exception. <<*)
        | _, _ => Throw RangeError
      end end end end.

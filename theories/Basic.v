Definition assert (P : Prop) (proof : P) : unit := tt.
Notation "'assert' P 'in' A" := (let tt := assert P _ in A) (at level 200).
Notation "'impossible'" := (False_rect _ _).

Lemma eq_sym_iff {A} (x y : A) : x = y <-> y = x.
Proof.
  split.
  intro. symmetry. assumption.
  intro. symmetry. assumption.
Qed.
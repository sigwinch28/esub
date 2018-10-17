Inductive lit :=
| atom
| boolean
| integer
| tupleNil
| tupleCons : lit -> lit -> lit.

Lemma lit_eq_dec : forall (x y : lit), {x = y} + {x <> y}.
Proof.
  decide equality.
Qed.


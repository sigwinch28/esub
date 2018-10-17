Require Import Esub.Literal.

Section patterns.
  Variables V : Type.
  Hypothesis Veq_dec : forall (x y : V), {x = y} + {x <> y}.

  Inductive pat :=
  | PVar : V -> pat
  | PLit : lit -> pat
  | PTupleNil : pat
  | PTupleCons : pat -> pat -> pat.

  Inductive tuple_pat : pat -> Prop :=
  | tpTupleNil : tuple_pat PTupleNil
  | tpTupleCons : forall x y, tuple_pat (PTupleCons x y).

  Inductive wf_pat : pat -> Prop :=
  | wfpVar : forall v, wf_pat (PVar v)
  | wfpLit : forall l, wf_pat (PLit l)
  | wfpTupleNil : wf_pat PTupleNil
  | wfpTupleCons : forall x y,
      wf_pat x ->
      wf_pat y ->
      tuple_pat y ->
      wf_pat (PTupleCons x y).

  Fixpoint pat_den (p : pat) (l : lit) : bool :=
    match p with
    | PVar v => true
    | PLit l' => if lit_eq_dec l l' then true else false
    | PTupleNil =>
      match l with
      | TupleNil => true
      | _ => false
      end
    | PTupleCons p1 p2 =>
      match l with
      | TupleCons l1 l2 => andb (pat_den p1 l1) (pat_den p2 l2)
      | _ => false
      end
    end.
End patterns.
             

  
  
        
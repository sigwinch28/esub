Section types.
  Variable l : Type.
  Hypothesis leq_dec : forall (x y : l), {x = y} + {x <> y}.
  
  Inductive ty : Type :=
  | Any
  | Atom
  | Boolean
  | Number
  | Integer
  | Tuple
  | TupleNil
  | TupleCons : ty -> ty -> ty
  | Singleton : ty -> l -> ty
  | Not : ty -> ty
  | And : ty -> ty -> ty
  | Or : ty -> ty -> ty.

  Lemma tyeq_dec : forall (x y : ty), {x = y} + {x <> y}.
  Proof.
    decide equality.
  Defined.

  Notation "'TNone'" := (Not Any) (only parsing) : ty_scope.
  Bind Scope ty_scope with ty.
  Delimit Scope ty_scope with ty.

  Inductive tuple_ty : ty -> Prop :=
  | ttNil : tuple_ty TupleNil
  | ttCons : forall x y, tuple_ty (TupleCons x y).

  Inductive wf_ty : ty -> Prop :=
  | wfAny : wf_ty Any
  | wfAtom : wf_ty Atom
  | wfBoolean : wf_ty Boolean
  | wfNumber : wf_ty Number
  | wfInteger : wf_ty Integer
  | wfTuple : wf_ty Tuple
  | wfTupleNil : wf_ty TupleNil
  | wfTupleCons : forall x y,
      wf_ty x ->
      wf_ty y ->
      tuple_ty y ->
      wf_ty (TupleCons x y)
  | wfSingleton : forall x l,
      wf_ty x ->
      wf_ty (Singleton x l).

  Inductive simple_ty : ty -> Prop :=
  | sAny : simple_ty Any
  | sAtom : simple_ty Atom
  | sBoolean : simple_ty Boolean
  | sNumber : simple_ty Number
  | sInteger : simple_ty Integer.

  Inductive compound_ty : ty -> Prop :=
  | cTuple : compound_ty Tuple
  | cTupleNil : compound_ty TupleNil
  | cTupleCons : forall x y,
      pos_ty x ->
      pos_ty y ->
      tuple_ty y ->
      compound_ty (TupleCons x y)
  | cSingleton : forall x l, 
      simple_ty x ->
      compound_ty (Singleton x l)
  with pos_ty : ty -> Prop :=
       | pSimple : forall x, simple_ty x -> pos_ty x
       | pCompound : forall x, compound_ty x -> pos_ty x.

  Inductive neg_ty : ty -> Prop :=
  | nNot : forall x, pos_ty x -> neg_ty (Not x).

  Inductive atom_ty : ty -> Prop :=
  | aPos : forall x, pos_ty x -> atom_ty x
  | aNeg : forall x, neg_ty x -> atom_ty x.

  Hint Constructors simple_ty compound_ty pos_ty neg_ty atom_ty.

  Definition map {A B : Type} (f : A -> B) (xs : list A) : list B.
    refine ((fix m f xs :=
              match xs with
              | cons x xs => cons (f x) (m f xs)
              | _ => nil
              end) f xs) .
  Defined.

  Fixpoint pos_sub (s t : ty) : option ty :=
    match (s,t) with
    | (s, Any) => Some s
    | (Boolean, Atom) => Some Atom
    | (Integer, Number) => Some Integer
    | (Singleton s v, Singleton t w) =>
      match pos_sub s t with
      | Some u => if leq_dec v w then Some (Singleton u v) else None
      | None => None
      end
    | (Singleton s v, t) =>
      match pos_sub s t with
      | Some u => Some (Singleton s v)
      | None => None
      end
    | (TupleNil, Tuple) => Some TupleNil
    | (TupleCons x y, Tuple) => Some (TupleCons x y)
    | (TupleCons x1 y1, TupleCons x2 y2) =>
      match (pos_sub x1 x2, pos_sub y1 y2) with
      | (Some x', Some y') => Some (TupleCons x' y')
      | _ => None
      end
    | (s, t) => if tyeq_dec s t then Some s else None
    end.

  Fixpoint pos_inter1 (s t : ty) : option ty :=
    match (s, t) with
    | (s, Any) => Some Any
    | (Boolean, Atom) => Some Boolean
    | (Integer, Number) => Some Integer
    | (Singleton s v, Singleton t w) =>
      match pos_inter1 s t with
      | Some u => if leq_dec v w then Some (Singleton u v) else None
      | None => None
      end
    | (Singleton s v, t) =>
      match pos_inter1 s  t with
      | Some u => Some (Singleton s v)
      | None => None
      end
    | (TupleNil, Tuple) => Some TupleNil
    | (TupleCons x y, Tuple) => Some (TupleCons x y)
    | (TupleCons x1 y1, TupleCons x2 y2) =>
      match (pos_inter1 x1 x2, pos_inter1 y1 y2) with
      | (Some x', Some y') => Some (TupleCons x' y')
      | _ => None
      end
    | (s, t) => if tyeq_dec s t then Some s else None
    end.

  Definition pos_inter (s t : ty) : option ty :=
    match pos_inter1 s t with
    | Some u => Some u
    | None => pos_inter1 t s
    end.
End types.

  
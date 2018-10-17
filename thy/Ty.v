Require Import Esub.Literal.
Require Import Coq.Lists.List.

Import ListNotations.

Inductive ty : Type :=
| Any
| Atom
| Boolean
| Number
| Integer
| Tuple
| TupleNil
| TupleCons : ty -> ty -> ty
| Singleton : ty -> lit -> ty
| Not : ty -> ty
| And : ty -> ty -> ty
| Or : ty -> ty -> ty.

Lemma tyeq_dec : forall (x y : ty), {x = y} + {x <> y}.
Proof.
  decide equality.
  apply lit_eq_dec.
Defined.

Fixpoint ty_of_lit (l : lit) : ty :=
  match l with
  | atom => Singleton Atom atom
  | boolean => Singleton Boolean boolean
  | integer => Singleton Integer integer
  | tupleNil => TupleNil
  | tupleCons x y => TupleCons (ty_of_lit x) (ty_of_lit y)
  end.

Fixpoint pos_sub (s t : ty) : option ty :=
  match (s,t) with
  | (s, Any) => Some s
  | (Boolean, Atom) => Some Atom
  | (Integer, Number) => Some Integer
  | (Singleton s v, Singleton t w) =>
    match pos_sub s t with
    | Some u => if lit_eq_dec v w then Some (Singleton u v) else None
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

Definition pos_subb (s t : ty) :=
  match pos_sub s t with
  | Some _ => true
  | None => false
  end.

Fixpoint ty_den (t : ty) (l : lit) : bool :=
  match t with
  | Any => true
  | Atom => pos_subb (ty_of_lit l) Atom
  | Boolean => pos_subb (ty_of_lit l) Boolean
  | Number => pos_subb (ty_of_lit l) Number
  | Integer => pos_subb (ty_of_lit l) Integer
  | Tuple => pos_subb (ty_of_lit l) Tuple
  | TupleNil => pos_subb (ty_of_lit l) TupleNil
  | TupleCons tx ty =>
    match l with
    | tupleCons lx ly => andb (ty_den tx lx) (ty_den ty ly)
    | _ => false
    end
  | Singleton t v =>
    if lit_eq_dec v l then pos_subb (ty_of_lit l) t else false
  | Not t => negb (ty_den t l)
  | And x y => andb (ty_den x l) (ty_den y l)
  | Or x y => orb (ty_den x l) (ty_den y l)
  end.

           
    



Check fold_left.

Fixpoint pairwise {A B C : Type} (f : A -> B -> C) (xs : list A) (ys : list B) : list C :=
  flat_map (fun x => map (fun y => f x y) ys) xs.

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


Lemma ty_of_lit_pos : forall l, pos_ty (ty_of_lit l).
Proof.
  induction l; simpl; auto; reflexivity.
Qed.



Fixpoint lit_of_ty (t : ty) : option (list lit) :=
  match t with
  | Any => None
  | Atom => None
  | Boolean => None
  | Number => None
  | Integer => None
  | Tuple => None
  | TupleNil => Some [tupleNil]
  | TupleCons x y =>
    match (lit_of_ty x, lit_of_ty y) with
    | (Some xs, Some ys) => Some (pairwise (fun x y => tupleCons x y) xs ys)
    | _ => None
    end
  | Singleton t l => Some [l]
  | Not t => None
  | _ => None
  end.

Lemma lit_of_ty_of_lit : forall l, lit_of_ty (ty_of_lit l) = Some [l].
Proof.
  intros.
  induction l.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite -> IHl1. rewrite -> IHl2. reflexivity.
Qed.

 

Ltac kill t := repeat (destruct t; simpl).
Ltac decidable := reflexivity || contradiction.

Lemma pos_sub_refl: forall t, pos_sub t t = Some t.
Proof with decidable.
  intros.
  induction t; simpl.
  all: try ((try kill tyeq_dec); decidable).
  - rewrite -> IHt1. rewrite -> IHt2. decidable.
  - rewrite -> IHt. kill lit_eq_dec; decidable.
Qed.

Fixpoint pos_inter1 (s t : ty) : option ty :=
  match (s, t) with
  | (s, Any) => Some Any
  | (Boolean, Atom) => Some Boolean
  | (Integer, Number) => Some Integer
  | (Singleton s v, Singleton t w) =>
    match pos_inter1 s t with
    | Some u => if lit_eq_dec v w then Some (Singleton u v) else None
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

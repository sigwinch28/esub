Require Import Esub.Literal Esub.Ty.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.Sumbool.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

Section maps.
  Variables K V : Type.
  Hypothesis Keq_dec : forall (x y : K), {x = y} + {x <> y}.

  Definition map := list (K * V).

  Check fold_left.
  Check fold_right.

  Fixpoint keys (m : map) : list K :=
    match m with
    | nil => nil
    | (k, v) :: ms => k :: (keys ms)
    end.
  
  Fixpoint mem (k : K) (m : map) : bool :=
    match m with
    | nil => false
    | (k', v) :: ms => if Keq_dec k k' then true else mem k ms
    end.

  Fixpoint find (k : K) (m : map) : option V :=
    match m with
    | nil => None
    | (k', v) :: ms => if Keq_dec k k' then Some v else find k ms
    end.

  Fixpoint remove (k : K) (m : map) : map :=
    match m with
    | nil => nil
    | (k', v) :: ms =>
      if Keq_dec k k' then (k', v) :: (remove k ms) else remove k ms
    end.
  
  Fixpoint add (k : K) (v : V) (m : map) : map :=
    match m with
    | nil => [(k, v)]
    | (k', v') :: ms =>
      if Keq_dec k k' then (k, v) :: ms else (k', v') :: (add k v ms)
    end.


  Definition map_equiv (m n : map) := forall k, find k m = find k n.

  Lemma map_equiv_refl : forall m, map_equiv m m.
  Proof.
    unfold map_equiv. auto.
  Qed.
  
  Lemma map_equiv_sym : forall m n, map_equiv m n -> map_equiv n m.
  Proof.
    unfold map_equiv. auto.
  Qed.

  Lemma map_equiv_trans : forall m n o,
      map_equiv m n -> map_equiv n o -> map_equiv m o.
  Proof.
    unfold map_equiv.
    congruence.
  Qed.
End maps.


Fixpoint map_values {K A B : Type} (f : A -> B) (xs : map K A) : map K B :=
  match xs with
  | [] => []
  | (k, v) :: xs => (k, f v) :: (map_values f xs)
  end.

Check find.

Lemma find_map_Some {K A B : Type} :
  forall f k Keq_dec v m, find K A Keq_dec k m = Some v -> find K B Keq_dec k (map_values f m) = Some (f v).
  Proof.
    intros. generalize dependent k. induction m; intros.
    - inversion H.
    - destruct a.
      simpl in H. simpl.
      destruct Keq_dec.
      + inversion H. reflexivity.
      + apply IHm. assumption.
  Qed.

  Lemma find_map_None {K A B : Type} :
    forall f k Keq_dec m, find K A Keq_dec k m = None -> find K B Keq_dec k (map_values f m) = None.
  Proof.
    intros. generalize dependent k. induction m; intros.
    - reflexivity.
    - destruct a.
      simpl in H. simpl.
      destruct Keq_dec.
      + inversion H.
      + apply IHm in H. assumption.
  Qed.

Section sets.
  Variable A : Type.

  Definition set := list A.
  Definition union := app.
End sets.


Section guards.
  Variable V : Type.
  Hypothesis Veq_dec : forall (x y : V), {x = y} + {x <> y}.

  Inductive guard :=
  | GTrue
  | GFalse
  | GNot : guard -> guard
  | GIf : guard -> guard -> guard -> guard
  | GTest : V -> ty -> guard
  | GEq : V -> lit -> guard.

  Definition Rho := map V lit.
  Definition Rfind := find V lit Veq_dec.
  Check Rfind.

  Fixpoint guard_denb (g : guard) (R : Rho) : bool :=
    match g with
    | GTrue => true
    | GFalse => false
    | GNot g => negb (guard_denb g R)
    | GIf x t f => if (guard_denb x R) then guard_denb t R else guard_denb f R
    | GTest v t =>
      match Rfind v R with
      | Some l =>
        match pos_sub (ty_of_lit l) t with
        | Some _ => true
        | None => false
        end
      | None => false
      end
    | GEq v l =>
      match Rfind v R with
      | Some l' => (if lit_eq_dec l l' then true else false)
      | None => false
      end
    end.

                  
                                                         

  Lemma if_idem : forall (b : bool), (if b then true else false) = b.
  Proof.
    intros b. destruct b; reflexivity.
  Qed.
  
  Lemma guard_if_idempotent : forall g r, guard_denb g r = guard_denb (GIf g GTrue GFalse) r.
  Proof.
    intros g r. simpl. symmetry. apply if_idem.
  Qed.

  Lemma guard_neg_involutive : forall g r, guard_denb g r = guard_denb (GNot (GNot g)) r.
  Proof.
    intros g r. simpl.
    symmetry. apply negb_involutive.
  Qed.

  Definition Gamma := map V ty.
  Definition Gfind := find V ty Veq_dec.
  Definition Gkeys := keys V ty.
  Definition Gammas := set Gamma.
  Definition Gunion := union Gamma.

  Fixpoint any {A : Type} (f : A -> bool) (xs : list A) : bool :=
    match xs with
    | [] => false
    | x :: xs => if f x then true else any f xs
    end.

  Variables x y : lit.
  Compute bool_of_sumbool (lit_eq_dec x y).

  
  Fixpoint guard_denb_gamma (g : guard) (G : Gamma) : bool :=
    match g with
    | GTrue => true
    | GFalse => false
    | GNot g => negb (guard_denb_gamma g G)
    | GIf x t f =>
      if (guard_denb_gamma x G) then guard_denb_gamma t G else guard_denb_gamma f G
    | GTest v t =>
      match Gfind v G with
      | Some s =>
        match pos_sub s t with
        | Some _ => true
        | None => false
        end
      | None => false
      end
    | GEq v l =>
      match Gfind v G with
      | Some t =>
        match lit_of_ty t with
        | Some ls =>
          if any (fun l' => if lit_eq_dec l l' then true else false) ls
          then true else false
        | None => false
        end
      | None => false
      end
    end.

  Lemma guard_denb_denb_gamma : forall g R, guard_denb g R = guard_denb_gamma g (map_values ty_of_lit R).
    intros g. induction g; intros r.
    - reflexivity.
    - reflexivity.
    - simpl. f_equal. apply IHg.
    - simpl. rewrite -> IHg1. rewrite -> IHg2. rewrite -> IHg3. reflexivity.
    - simpl.
      destruct Rfind eqn:Hr.
      + unfold Gfind. unfold Rfind in Hr.
        pose proof (@find_map_Some V lit ty ty_of_lit v Veq_dec l r).
        apply H in Hr. rewrite -> Hr. reflexivity.
      + unfold Gfind. unfold Rfind in Hr.
        pose proof (@find_map_None V lit ty ty_of_lit v Veq_dec r).
        apply H in Hr. rewrite -> Hr. reflexivity.
    - simpl.
      destruct Rfind eqn:Hr.
      + unfold Gfind. unfold Rfind in Hr.
        pose proof (@find_map_Some V lit ty ty_of_lit v Veq_dec l0 r).
        apply H in Hr. rewrite -> Hr.
        pose proof (lit_of_ty_of_lit l0). rewrite -> H0.
        simpl.
        repeat rewrite -> if_idem. reflexivity.
      + unfold Gfind. unfold Rfind in Hr.
        pose proof (@find_map_None V lit ty ty_of_lit v Veq_dec r).
        apply H in Hr. rewrite -> Hr. reflexivity.
  Qed.
  

  Fixpoint join_keys (ks : list V) (x y : Gamma) :=
    match ks with
    | [] => []
    | k :: ks =>
      match (Gfind k x, Gfind k y) with
      | (Some v1, Some v2) => (k, And v1 v2) :: join_keys ks x y
      | (Some v1, None) => (k, v1) :: join_keys ks x y
      | (None, Some v2) => (k, v2) :: join_keys ks x y
      | (None, None) => join_keys ks x y
      end
    end.

  Check List.map.

  
  Fixpoint In (x : V) (xs : list V) : bool :=
    match xs with
    | [] => false
    | x' :: xs => if Veq_dec x x' then true else In x xs
    end.

  Fixpoint nub (xs : list V) : list V :=
    match xs with
    | [] => []
    | x :: xs => if In x xs then nub xs else x :: (nub xs)
    end.
  

  Fixpoint join1 (x : Gamma) (ys : Gammas) : Gammas :=
    match ys with
    | [] => []
    | y :: ys =>
      let keys := nub ((Gkeys x) ++ (Gkeys y)) in
      (join_keys keys x y) :: (join1 x ys)
    end.

  Fixpoint join (xs : Gammas) (ys : Gammas) : Gammas :=
    match xs with
    | [] => []
    | x :: xs => (join1 x ys) ++ (join xs ys)
    end.

  Definition empty : Gamma := [].
  
  Definition singleton (x : V) (t : ty) : Gamma :=
    add V ty Veq_dec x t empty.

  Fixpoint guard_type (g : guard) : Gammas * Gammas :=
    match g with
    | GTrue => ([empty], [])
    | GFalse => ([], [empty])
    | GNot g => (snd (guard_type g), fst (guard_type g))
    | GIf g t f =>
      let g_type := guard_type g in
      let t_type := guard_type t in
      let f_type := guard_type f in
      (Gunion (join (fst(g_type)) (fst(t_type))) (join (snd(g_type)) (fst(f_type))),
       Gunion (join (fst(g_type)) (snd(t_type))) (join (snd(g_type)) (snd(f_type))))
    | GTest v t => ([singleton v t],[singleton v (Not t)])
    | GEq v l => let t := Singleton (ty_of_lit l) l in ([singleton v t], [singleton v (Not t)])
    end.

  Lemma foo : forall v l t, ty_of_lit l = t -> guard_denb (GTest v t) [(v, l)] = true.
  Proof.
    intros. simpl.
    destruct Veq_dec eqn:Veq.
    - rewrite -> H. rewrite -> pos_sub_refl. reflexivity.
    - contradiction.
  Qed.
    
End guards.

Definition x := 0.
Definition y := 1.
Variable s : ty.
Variable t : ty.

Check GTest.
  Definition g1 := (GIf nat (GTest nat x s) (GTrue nat) (GTest nat y t)).

  Definition gt1 := fst (guard_type nat Nat.eq_dec g1).
  Compute gt1.
  
  Compute List.map (fun y => y x) gt1.
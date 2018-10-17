
Section total.
  Variables A B : Type.
  Hypothesis Aeq_dec : forall (x y : A), {x = y} + {x <> y}.
  
  Definition tmap := A -> B.

  Definition update_tmap (v : A) (x : B) (m : tmap) : tmap :=
    fun w => if Aeq_dec v w then x else m w.

  Lemma update_tmap_apply: forall v x m, (update_tmap v x m) v = x.
  Proof.
    intros.
    unfold update_tmap. destruct Aeq_dec; reflexivity || contradiction.
  Qed.
End total.

Section partial.
  Variables A B : Type.
  Hypothesis Aeq_dec : forall (x y : A), {x = y} + {x <> y}.

  Definition pmap  := tmap A (option B).

  Local Definition update_map' := update_tmap A (option B) Aeq_dec.

  Definition update_pmap (v : A) (x : B) (m : pmap) : pmap :=
    update_map' v (Some x) m.

  Lemma update_pmap_apply: forall v x m, (update_pmap v x m) v = Some x.
  Proof.
    intros.
    unfold update_pmap.
    apply update_tmap_apply.
  Qed.
  
  Definition remove_pmap (v : A) (m : pmap) : pmap :=
    update_map' v None m.

  Lemma remove_pmap_apply: forall v m, (remove_pmap v m) v = None.
  Proof.
    intros.
    unfold remove_pmap.
    apply update_tmap_apply.
  Qed.
End partial.

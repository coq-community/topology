From Coq Require Import
  ClassicalChoice
  Description
  FunctionalExtensionality
  ProofIrrelevance.
From ZornsLemma Require Import
  Cardinals.CSB
  FunctionProperties
  FunctionPropertiesEns
  ZornsLemma.
From Coq Require Import RelationClasses.

Definition le_cardinal (A B : Type) : Prop :=
  exists f : A -> B, injective f.
Definition eq_cardinal (X Y : Type) : Prop :=
  exists (f : X -> Y) (g : Y -> X), inverse_map f g.

Definition lt_cardinal (kappa lambda:Type) : Prop :=
  le_cardinal kappa lambda /\ ~ eq_cardinal kappa lambda.
Definition ge_cardinal (kappa lambda:Type) : Prop :=
  le_cardinal lambda kappa.
Definition gt_cardinal (kappa lambda:Type) : Prop :=
  lt_cardinal lambda kappa.

#[export]
Instance le_cardinal_preorder : PreOrder le_cardinal.
Proof.
split.
- red; intro; exists id; apply id_bijective.
- intros ? ? ? [f Hf] [g Hg].
  exists (compose g f).
  apply injective_compose; auto.
Qed.

#[export]
Instance eq_cardinal_equiv : Equivalence eq_cardinal.
Proof.
split.
- red; intro. exists id, id. apply id_inverse_map.
- red; intros ? ? [f [g Hfg]].
  exists g, f. apply inverse_map_sym. assumption.
- intros ? ? ? [f Hf] [g Hg].
  exists (compose g f).
  apply invertible_compose; assumption.
Qed.

#[export]
Instance le_cardinal_PartialOrder :
  PartialOrder eq_cardinal le_cardinal.
Proof.
split.
- intros [f Hf]; split.
  + exists f. apply invertible_impl_bijective; assumption.
  + destruct Hf as [g Hfg].
    exists g. apply invertible_impl_bijective.
    exists f. apply inverse_map_sym.
    assumption.
- intros [[f Hf] [g Hg]].
  apply CSB_inverse_map with (f := f) (g := g); auto.
Qed.

Lemma eq_cardinal_impl_le_cardinal: forall kappa lambda: Type,
  eq_cardinal kappa lambda -> le_cardinal kappa lambda.
Proof.
intros ? ? [f Hf].
exists f. apply invertible_impl_bijective; auto.
Qed.

(** This lemma is helpful, if one wants
    to avoid using an axiom of choice. *)
Lemma le_cardinal_img_inj_ens {X Y : Type} (Z : Type) (f : X -> Y) (U : Ensemble X) :
  injective_ens f U ->
  le_cardinal X Z ->
  le_cardinal (sig (Im U f)) Z.
Proof.
  intros Hf [g Hg].
  assert (forall p : { y : Y | In (Im U f) y },
             { x : X | In U x /\ (proj1_sig p) = f x}) as H.
  { intros [y Hy].
    simpl.
    apply constructive_definite_description.
    inversion Hy; subst; clear Hy.
    exists x; split; auto.
    intros x' []; auto.
  }
  exists (compose g (fun p => proj1_sig (H p))).
  apply injective_compose; auto.
  clear g Hg.
  intros p0 p1 Hp.
  pose proof (proj2_sig (H p0)) as [Hp00 Hp01].
  pose proof (proj2_sig (H p1)) as [Hp10 Hp11].
  destruct p0 as [y0 Hy0], p1 as [y1 Hy1].
  simpl in *. rewrite <- Hp in Hp11.
  cut (y0 = y1); try congruence.
  intros. destruct H0.
  destruct (proof_irrelevance _ Hy0 Hy1).
  reflexivity.
Qed.

(* The results below require Axiom of Choice *)

Lemma surj_le_cardinal: forall {X Y:Type} (f:X->Y),
  surjective f -> le_cardinal Y X.
Proof.
intros.
pose proof (choice (fun (y:Y) (x:X) => f x = y) H).
simpl in H0.
destruct H0 as [g].
exists g.
red; intros.
congruence.
Qed.

Section le_cardinal_total.

Variable X Y:Type.

Record partial_injection : Type := {
  pi_dom: Ensemble X;
  pi_func: forall x:X, In pi_dom x -> Y;
  pi_inj: forall (x1 x2:X) (i1:In pi_dom x1) (i2:In pi_dom x2),
    pi_func x1 i1 = pi_func x2 i2 -> x1 = x2
}.
Record partial_injection_ord (pi1 pi2:partial_injection) : Prop := {
  pi_dom_inc: Included (pi_dom pi1) (pi_dom pi2);
  pi_func_ext: forall (x:X) (i1:In (pi_dom pi1) x)
   (i2:In (pi_dom pi2) x),
    pi_func pi1 x i1 = pi_func pi2 x i2
}.

Lemma partial_injection_preord: preorder partial_injection_ord.
Proof.
constructor.
- red; intros.
  destruct x.
  constructor.
  + auto with sets.
  + intros. simpl in *.
    assert (i1 = i2).
    { apply proof_irrelevance. }
    rewrite H.
    reflexivity.
- red; intros.
  destruct H.
  destruct H0.
  constructor.
  + auto with sets.
  + intros.
    assert (In (pi_dom y) x0).
    { auto with sets. }
    transitivity (pi_func y x0 H); trivial.
Qed.

Lemma partial_injection_chain_ub: forall S:Ensemble partial_injection,
  chain partial_injection_ord S -> exists x:partial_injection,
  forall y:partial_injection, In S y -> partial_injection_ord y x.
Proof.
intros.
pose (ub_dom := [x:X | exists y:partial_injection,
  In S y /\ In (pi_dom y) x]).
assert (forall x:X, In ub_dom x -> { y:Y | exists z:partial_injection,
  In S z /\ exists i:In (pi_dom z) x, pi_func z x i = y }).
{ intros.
  apply constructive_definite_description.
  destruct H0.
  destruct H0.
  destruct H0.
  exists (pi_func x0 x H1).
  red; split.
  - exists x0.
    split.
    + assumption.
    + exists H1.
      reflexivity.
  - intros.
    destruct H2.
    destruct H2.
    destruct H3.
    pose proof (H x0 x1 H0 H2).
    case H4.
    + intro.
      rewrite <- H3.
      apply pi_func_ext.
      assumption.
    + intro.
      rewrite <- H3.
      symmetry.
      apply pi_func_ext.
      assumption.
}
assert (forall (x1 x2:X) (i1:In ub_dom x1) (i2:In ub_dom x2),
  proj1_sig (X0 x1 i1) = proj1_sig (X0 x2 i2) -> x1 = x2).
{ intros.
  destruct X0 in H0.
  destruct X0 in H0.
  simpl in H0.
  destruct H0.
  destruct e.
  destruct H0.
  destruct H1.
  destruct e0.
  destruct H2.
  destruct H3.
  destruct H1.
  case (H x0 x4 H0 H2).
  - intro.
    assert (In (pi_dom x4) x1).
    { apply (pi_dom_inc _ _ H1).
      assumption.
    }
    assert (pi_func x4 x1 H4 = pi_func x4 x2 x5).
    { rewrite H3.
      symmetry.
      apply pi_func_ext.
      assumption.
    }
    apply pi_inj in H5.
    assumption.
  - intro.
    assert (In (pi_dom x0) x2).
    { apply (pi_dom_inc _ _ H1).
      assumption.
    }
    assert (pi_func x0 x1 x3 = pi_func x0 x2 H4).
    { rewrite <- H3.
      apply pi_func_ext.
      assumption.
    }
    apply pi_inj in H5.
    assumption.
}
exists (Build_partial_injection ub_dom
  (fun (x:X) (i:In ub_dom x) => proj1_sig (X0 x i)) H0).
intros.
constructor.
- simpl.
  red; intros.
  constructor.
  exists y.
  tauto.
- simpl.
  intros.
  destruct (X0 x i2).
  simpl.
  destruct e.
  destruct H2.
  destruct H3.
  destruct H3.
  case (H y x1 H1 H2).
  + intro.
    apply pi_func_ext.
    assumption.
  + intro.
    symmetry.
    apply pi_func_ext.
    assumption.
Qed.

Lemma premaximal_partial_injection:
  exists x:partial_injection, premaximal partial_injection_ord x.
Proof.
apply ZornsLemmaForPreorders.
- exact partial_injection_preord.
- exact partial_injection_chain_ub.
Qed.

Lemma premaximal_pi_is_full_or_surj:
  forall x:partial_injection, premaximal partial_injection_ord x ->
    pi_dom x = Full_set \/
    forall y:Y, exists x0:X, exists i:(In (pi_dom x) x0),
      pi_func x x0 i = y.
Proof.
intros.
case (classic (pi_dom x = Full_set)).
{ left.
  trivial.
}
intro.
assert (exists x0:X, ~ In (pi_dom x) x0).
{ apply NNPP.
  intuition.
  apply H0.
  apply Extensionality_Ensembles.
  red; split.
  - red; intros.
    constructor.
  - red; intros.
    apply NNPP.
    intuition.
    apply H1.
    exists x0.
    assumption.
}
right.
destruct H1.
intros.
apply NNPP.
intuition.

pose (pi_dom_ext := Add (pi_dom x) x0).
assert (forall (x':X), In pi_dom_ext x' ->
  { y':Y | (exists i2:In (pi_dom x) x', y' = pi_func x x' i2) \/
          (x' = x0 /\ y' = y) }).
{ intros.
  apply constructive_definite_description.
  case H3.
  - intros.
    exists (pi_func x x1 H4).
    red; split.
    + left.
      exists H4.
      reflexivity.
    + intros.
      case H5.
      * intro.
        destruct H6.
        subst.
        replace H4 with x2.
        -- reflexivity.
        -- apply proof_irrelevance.
      * intros.
        destruct H6.
        subst.
        contradict H1.
        assumption.
  - intros.
    destruct H4.
    exists y.
    red; split.
    + right.
      tauto.
    + intros.
      case H4.
      * intro.
        destruct H5.
        subst.
        contradiction H1.
      * intros.
        symmetry.
        tauto.
}

pose (pi_func_ext0 := fun (x:X) (i:In pi_dom_ext x) =>
  proj1_sig (X0 x i)).

assert (forall (x1:X) (i:In (pi_dom x) x1) (i2:In pi_dom_ext x1),
  pi_func_ext0 x1 i2 = pi_func x x1 i).
{ intros.
  unfold pi_func_ext0.
  destruct (X0 x1 i2).
  simpl.
  case o.
  - intros.
    destruct H3.
    subst.
    replace i with x3.
    + reflexivity.
    + apply proof_irrelevance.
  - intros.
    destruct H3.
    contradiction H1.
    rewrite <- H3.
    assumption.
}

assert (forall (i:In pi_dom_ext x0), pi_func_ext0 x0 i = y).
{ intros.
  unfold pi_func_ext0.
  destruct (X0 x0 i); simpl.
  case o.
  - intro.
    destruct H4.
    contradiction H1.
  - tauto.
}

assert (forall (x1 x2:X) (i1:In pi_dom_ext x1) (i2:In pi_dom_ext x2),
  pi_func_ext0 x1 i1 = pi_func_ext0 x2 i2 -> x1 = x2).
{ intros.
  inversion i1; subst.
  - inversion i2; subst.
    + rewrite (H3 x1 H6 i1) in H5.
      rewrite (H3 x2 H7 i2) in H5.
      apply pi_inj in H5.
      assumption.
    + destruct H7.
      rewrite (H3 x1 H6 i1) in H5.
      rewrite H4 in H5.
      contradiction H2.
      exists x1, H6.
      assumption.
  - destruct H6.
    rewrite H4 in H5.
    inversion i2.
    + rewrite (H3 x2 H6 i2) in H5.
      contradiction H2.
      exists x2, H6.
      symmetry; assumption.
    + destruct H6.
      reflexivity.
}

pose (pi_ext := Build_partial_injection pi_dom_ext pi_func_ext0 H5).
assert (partial_injection_ord x pi_ext).
{ constructor.
  - unfold pi_ext; simpl.
    unfold pi_dom_ext.
    red; intros.
    left.
    assumption.
  - intros.
    symmetry.
    apply H3.
}

apply H in H6.
contradiction H1.
apply (pi_dom_inc _ _ H6).
simpl.
right.
constructor.
Qed.

Lemma types_comparable: (exists f:X->Y, injective f) \/
                        (exists f:Y->X, injective f).
Proof.
pose proof premaximal_partial_injection.
destruct H.
apply premaximal_pi_is_full_or_surj in H.
case H.
- left.
  assert (forall x0:X, In (pi_dom x) x0).
  { rewrite H0.
    constructor.
  }
  exists (fun x0:X => pi_func x x0 (H1 x0)).
  red; intros.
  apply pi_inj in H2.
  assumption.
- right.
  assert (forall y:Y, { x0:X | exists i:In (pi_dom x) x0, pi_func x x0 i = y }).
  { intro.
    apply constructive_definite_description.
    pose proof (H0 y).
    destruct H1.
    exists x0.
    red; split.
    - assumption.
    - intros.
      destruct H1.
      destruct H2.
      destruct H2.
      apply pi_inj in H1.
      assumption.
  }
  exists (fun y:Y => proj1_sig (X0 y)).
  red; intros.
  destruct X0 in H1; destruct X0 in H1; simpl in H1.
  destruct e; destruct e0.
  subst.
  replace x3 with x4.
  + reflexivity.
  + apply proof_irrelevance.
Qed.

End le_cardinal_total.

Corollary le_cardinal_total: forall kappa lambda:Type,
  le_cardinal kappa lambda \/ le_cardinal lambda kappa.
Proof.
intros T0 T1.
destruct (types_comparable T0 T1) as [[f]|[f]];
  [left|right];
  exists f; assumption.
Qed.

Lemma cardinal_no_inj_equiv_lt_cardinal (A B : Type) :
  (forall f : A -> B, ~ injective f) <->
  lt_cardinal B A.
Proof.
split.
- intros.
  split.
  + (* |B| ≤ |A| *)
    destruct (le_cardinal_total B A).
    { assumption. }
    destruct H0 as [f Hf].
    specialize (H f Hf).
    contradiction.
  + (* |B| ≠ |A| *)
    intro.
    destruct H0 as [f [g [Hgf Hfg]]].
    pose proof (invertible_impl_bijective g).
    destruct H0 as [Hg0 Hg1].
    { exists f; split; assumption. }
    apply (H g Hg0).
- intros [[f Hf]] g Hg.
  contradict H.
  apply CSB_inverse_map with (f := f) (g := g);
    assumption.
Qed.

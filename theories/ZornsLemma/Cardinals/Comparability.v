(** Proves the cardinal comparability theorem [types_comparable] using
  Zorns Lemma for preorders. It states that between any two types [A]
  and [B] there is an injection [A -> B] or an injection [B -> A].

  Alternate proofs can be done using the well-ordering principle,
  using the fact that well-orders are totally ordered.
 *)

From Coq Require Import
  Description.
From ZornsLemma Require Import
  Cardinals.Cardinals
  Cardinals.CardinalsEns
  Cardinals.CSB
  Families
  FunctionProperties
  Image
  ZornsLemma.

Section le_cardinal_total.

Variable X Y:Type.

(** We define the type of "partial injections" from [X] to [Y]
    consisting of injective maps [pi_func] which are only defined on
    an Ensemble of [X].

    We define a preorder on them, by defining [pi1 ≤ pi2] if
    the same inequality holds for their domains and [pi2] agrees with
    [pi1] wherever the latter is defined.

    We go on to show that this order satisfies Zorns Lemma
    (see [partial_injection_chain_ub]) and thus contains a maximal
    element (see [premaximal_partial_injection]).

    Next we show that such a maximal element is either surjective or
    its domain is the whole of [X] (see
    [premaximal_pi_is_full_or_surj]).

    In [types_comparable] we show that in one case, we can transform
    the partial injection to an injection [X -> Y], while in the other
    case we can construct an injection [Y -> X] because the maximal element
    is surjective.
 *)
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
- intros x.
  destruct x.
  constructor.
  + auto with sets.
  + intros. simpl in *.
    f_equal.
    apply proof_irrelevance.
- intros x y z ? ?.
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
intros S HS.
(* whenever two elements of [S] are applied to the same element,
   they agree *)
assert (forall (pi1 pi2 : partial_injection)
          (Hpi1 : In S pi1) (Hpi2 : In S pi2)
          (x : X) (Hx1 : In (pi_dom pi1) x)
          (Hx2 : In (pi_dom pi2) x),
           pi_func pi1 x Hx1 = pi_func pi2 x Hx2) as HSeq.
{ intros pi1 pi2 Hpi1 Hpi2 x Hx1 Hx2.
  specialize (HS pi1 pi2 Hpi1 Hpi2) as [Hpi|Hpi].
  - apply pi_func_ext, Hpi.
  - symmetry. apply pi_func_ext, Hpi.
}
(* [ub_dom] is the union of all [pi_dom] that occur in [S] *)
pose (ub_dom := FamilyUnion (Im S pi_dom)).
(* define the map from [ub_dom] to [Y] *)
assert (forall x:X, In ub_dom x -> { y:Y | exists z:partial_injection,
  In S z /\ exists i:In (pi_dom z) x, pi_func z x i = y })
  as ub_func.
{ intros x Hx.
  apply constructive_definite_description.
  destruct Hx as [dom x Hdom Hx].
  destruct Hdom as [pi Hpi dom Hdom].
  subst.
  exists (pi_func pi x Hx).
  split.
  { exists pi. split; eauto. }
  (* uniqueness *)
  intros y [pi0 [Hpi0 [Hx0 Hy]]].
  subst y.
  apply HSeq; assumption.
}
(* show that [ub_func] is injective *)
assert (forall (x1 x2:X) (i1:In ub_dom x1) (i2:In ub_dom x2),
  proj1_sig (ub_func x1 i1) = proj1_sig (ub_func x2 i2) -> x1 = x2)
  as ub_inj.
{ intros x1 x2 i1 i2 Hx.
  (* destruct [ub_func] *)
  destruct (ub_func x1 i1) as [y1 [piy1 [Hpiy1S [Hpiy1x Hpiy1]]]] in Hx.
  destruct (ub_func x2 i2) as [y2 [piy2 [Hpiy2S [Hpiy2x Hpiy2]]]] in Hx.
  simpl in Hx. subst y1 y2.
  (* destruct [i1] and [i2], i.e. the fact that [x1, x2] lie in the domain of
     [ub_func] *)
  destruct i1 as [S1 x1 i1 Hx1].
  destruct i2 as [S2 x2 i2 Hx2].
  destruct i1 as [pi1 Hpi1 S1 HS1].
  destruct i2 as [pi2 Hpi2 S2 HS2].
  subst S1 S2.
  (* use the fact that we're dealing with a chain.
     Here it is essential, that the domains are included in eachother.
    *)
  specialize (HS piy1 piy2 Hpiy1S Hpiy2S) as [HpiyS|HpiyS].
  - assert (In (pi_dom piy2) x1) as Hpiy2x1.
    { apply (pi_dom_inc _ _ HpiyS).
      assumption.
    }
    apply (pi_inj piy2 x1 x2 Hpiy2x1 Hpiy2x).
    rewrite <- Hx.
    symmetry.
    apply pi_func_ext.
    assumption.
  - assert (In (pi_dom piy1) x2) as Hpiy1x2.
    { apply (pi_dom_inc _ _ HpiyS).
      assumption.
    }
    apply (pi_inj piy1 x1 x2 Hpiy1x Hpiy1x2).
    rewrite Hx.
    apply pi_func_ext.
    assumption.
}
exists (Build_partial_injection ub_dom
  (fun (x:X) (i:In ub_dom x) => proj1_sig (ub_func x i)) ub_inj).
(* show maximality *)
intros pi Hpi.
constructor; simpl.
{ apply FamilyUnion_In_Included.
  apply Im_def.
  assumption.
}
intros x Hpix Hubx.
destruct (ub_func x Hubx) as [y [pi0 [Hpi0 [Hpi0x Hy]]]].
subst y. simpl.
apply HSeq; assumption.
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
intros pi Hpi.
destruct (classic (exists x0:X, ~ In (pi_dom pi) x0)) as [Hnsurj|Hnsurj].
2: {
  left.
  apply Extensionality_Ensembles; split.
  { intros ? ?; constructor. }
  intros x _.
  apply NNPP.
  intros Hx.
  contradict Hnsurj.
  exists x; assumption.
}
right.
destruct Hnsurj as [x Hx].
intros y.
(* assume for a contradiction, that [y] has no preimage *)
apply NNPP.
intros Hy.

(* we construct another partial injection which is strictly larger
   than [pi] *)
pose (pi_dom_ext := Add (pi_dom pi) x).
(* the function maps like [pi], except it maps [x] to [y] *)
assert (forall (x':X), In pi_dom_ext x' ->
  { y':Y | (exists i2:In (pi_dom pi) x', y' = pi_func pi x' i2) \/
          (x' = x /\ y' = y) }) as pi_func_ext.
{ intros x0 Hx0.
  apply constructive_definite_description.
  destruct Hx0 as [x0 Hx0|x0 Hx0].
  - exists (pi_func pi x0 Hx0).
    split.
    + left. exists Hx0. reflexivity.
    + intros y0 [[Hy0 Hy1]|[]]; subst.
      * f_equal. apply proof_irrelevance.
      * contradiction.
  - destruct Hx0.
    exists y. split.
    + right; tauto.
    + intros y0 [[Hy0 Hy1]|[]]; subst; auto.
      contradiction.
}

pose (pi_func_ext0 := fun (x:X) (i:In pi_dom_ext x) =>
  proj1_sig (pi_func_ext x i)).

(* prove that [pi_func_ext0] agrees with [pi] *)
assert (forall (x1:X) (i:In (pi_dom pi) x1) (i2:In pi_dom_ext x1),
  pi_func_ext0 x1 i2 = pi_func pi x1 i) as pi_func_ext_ext.
{ intros x0 Hx0 Hx0_ext.
  unfold pi_func_ext0.
  destruct (pi_func_ext x0 Hx0_ext)
    as [y0 Hy0].
  simpl.
  destruct Hy0 as [[? ?]|[]]; subst.
  2: contradiction.
  f_equal. apply proof_irrelevance.
}

(* prove that [pi_func_ext0] maps [x] to [y] *)
assert (forall (i:In pi_dom_ext x), pi_func_ext0 x i = y) as
  pi_func_ext_x.
{ intros Hx0.
  unfold pi_func_ext0.
  destruct (pi_func_ext x Hx0) as [y0 Hy0].
  simpl. destruct Hy0 as [[? ?]|[]]; subst; tauto.
}

(* prove that [pi_func_ext0] is injective *)
assert (forall (x1 x2:X) (i1:In pi_dom_ext x1) (i2:In pi_dom_ext x2),
  pi_func_ext0 x1 i1 = pi_func_ext0 x2 i2 -> x1 = x2)
  as pi_inj_ext.
{ intros x1 x2 Hx1 Hx2 Hxx.
  destruct Hx1 as [x1 Hx1|x1 Hx1],
      Hx2 as [x2 Hx2|x2 Hx2].
  - rewrite (pi_func_ext_ext x1 Hx1) in Hxx.
    rewrite (pi_func_ext_ext x2 Hx2) in Hxx.
    apply pi_inj in Hxx.
    assumption.
  - rewrite (pi_func_ext_ext x1 Hx1) in Hxx.
    destruct Hx2.
    rewrite pi_func_ext_x in Hxx.
    contradict Hy.
    eauto.
  - destruct Hx1.
    rewrite (pi_func_ext_ext x2 Hx2) in Hxx.
    rewrite pi_func_ext_x in Hxx.
    contradict Hy.
    eauto.
  - destruct Hx1, Hx2.
    reflexivity.
}

pose (pi_ext := Build_partial_injection pi_dom_ext pi_func_ext0 pi_inj_ext).
assert (partial_injection_ord pi pi_ext) as Hord.
{ constructor.
  - apply Union_increases_l.
  - intros. symmetry. apply pi_func_ext_ext.
}

apply Hpi in Hord.
contradict Hx.
apply (pi_dom_inc _ _ Hord).
simpl.
right.
constructor.
Qed.

Theorem le_cardinal_total :
  le_cardinal X Y \/ le_cardinal Y X.
Proof.
pose proof premaximal_partial_injection
  as [pi Hpi].
apply premaximal_pi_is_full_or_surj in Hpi.
destruct Hpi as [Hpi|Hpi].
- left.
  assert (forall x0:X, In (pi_dom pi) x0) as Hpi0.
  { rewrite Hpi. constructor. }
  exists (fun x0:X => pi_func pi x0 (Hpi0 x0)).
  red; intros.
  apply pi_inj in H.
  assumption.
- right.
  (* similar to [bijective_impl_invertible] *)
  assert (forall y:Y, { x0:X | exists i:In (pi_dom pi) x0, pi_func pi x0 i = y })
    as F.
  { intros y.
    apply constructive_definite_description.
    pose proof (Hpi y) as [x Hx].
    exists x. split; auto.
    destruct Hx as [Hx Hy].
    subst.
    intros x0 [Hx0 Hxx].
    apply pi_inj in Hxx.
    symmetry. assumption.
  }
  exists (fun y:Y => proj1_sig (F y)).
  intros y0 y1 Hy.
  destruct (F y0) as [x0 [Hx0 Hxy0]] in Hy.
  destruct (F y1) as [x1 [Hx1 Hxy1]] in Hy.
  simpl in Hy. subst.
  f_equal. apply proof_irrelevance.
Qed.

End le_cardinal_total.

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

Theorem le_cardinal_ens_total {X Y : Type} (U : Ensemble X) (V : Ensemble Y) :
  le_cardinal_ens U V \/ le_cardinal_ens V U.
Proof.
  destruct (le_cardinal_total (sig U) (sig V)) as [[f Hf]|[f Hf]];
    [left|right].
  - eapply le_cardinal_ens_sig_injective; eauto.
  - eapply le_cardinal_ens_sig_injective; eauto.
Qed.

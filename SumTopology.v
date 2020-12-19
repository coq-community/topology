Require Export TopologicalSpaces.
Require Import StrongTopology Compactness.
From ZornsLemma Require Import DependentTypeChoice EnsemblesTactics.

Section SumTopology.

Variable A:Type.
Variable X:forall a:A, TopologicalSpace.

Inductive sum_space_point_set : Type :=
  sum_space_point_set_intro (a : A) : point_set (X a) -> sum_space_point_set.

Definition SumTopology : TopologicalSpace :=
  StrongTopology sum_space_point_set_intro.

End SumTopology.

Arguments sum_space_point_set {A}.
Arguments sum_space_point_set_intro {A}.

Lemma sum_topology_open_full_set_component {A : Type} (X : forall a, TopologicalSpace) :
  forall a, @open (SumTopology A X) (Im Full_set (sum_space_point_set_intro X a)).
Proof.
intros a1 a2.
destruct (classic (a1 = a2)).
- subst.
  replace (inverse_image (sum_space_point_set_intro X a2) (Im Full_set (sum_space_point_set_intro X a2))) with
          (@Full_set (point_set (X a2))).
  + apply open_full.
  + extensionality_ensembles;
      repeat econstructor.
- replace (inverse_image (sum_space_point_set_intro X a2) (Im Full_set (sum_space_point_set_intro X a1))) with
          (@Empty_set (point_set (X a2))).
  + apply open_empty.
  + extensionality_ensembles_inv.
    subst.
    injection H2 as H2.
    now subst.
Qed.

Lemma sum_topology_closed_full_set_component {A : Type} (X : forall a, TopologicalSpace) :
  forall a, @closed (SumTopology A X) (Im Full_set (sum_space_point_set_intro X a)).
Proof.
intros a1 a2.
destruct (classic (a1 = a2)).
- subst.
  replace (inverse_image (sum_space_point_set_intro X a2)
     (@Complement (point_set (SumTopology A X))
        (Im Full_set (sum_space_point_set_intro X a2)))) with
          (@Empty_set (point_set (X a2))).
  + apply open_empty.
  + extensionality_ensembles_inv.
    destruct H0.
    repeat econstructor.
- replace (inverse_image (sum_space_point_set_intro X a2)
     (@Complement (point_set (SumTopology A X))
        (Im Full_set (sum_space_point_set_intro X a1)))) with
          (@Full_set (point_set (X a2))).
  + apply open_full.
  + extensionality_ensembles_inv;
      repeat econstructor.
    intro.
    inversion H0.
    injection H3 as H3.
    now subst.
Qed.

Lemma sum_topology_inj_image_open {A : Type} (X : forall a, TopologicalSpace) (a : A) (S : Ensemble (point_set (X a))) :
  open S <-> @open (SumTopology A X) (Im S (sum_space_point_set_intro X a)).
Proof.
split; intros.
- intro a'.
  destruct (classic (a = a')).
  + subst.
    replace (inverse_image (sum_space_point_set_intro X a') (Im S (sum_space_point_set_intro X a'))) with S;
      trivial.
    extensionality_ensembles_inv.
    * now repeat econstructor.
    * injection H2 as H2.
      apply inj_pair2 in H2.
      now subst.
  + replace (inverse_image (sum_space_point_set_intro X a') (Im S (sum_space_point_set_intro X a))) with
            (@Empty_set (point_set (X a'))).
    * apply open_empty.
    * extensionality_ensembles_inv.
      injection H3 as H3.
      now subst.
- replace S with (inverse_image (sum_space_point_set_intro X a) (Im S (sum_space_point_set_intro X a))).
  + apply H.
  + extensionality_ensembles_inv.
    * injection H2 as H2.
      apply inj_pair2 in H2.
      now subst.
    * now repeat econstructor.
Qed.

Lemma sum_topology_compact {A : Type} (X : forall a, TopologicalSpace) :
  FiniteT A ->
  (forall a, compact (X a)) ->
  compact (SumTopology A X).
Proof.
intros HA HC F HF eq.

assert (forall a U, In (Im F (inverse_image (sum_space_point_set_intro X a))) U -> open U).
intros.
inversion H.
subst.
now apply strong_topology_makes_continuous_funcs, HF.

assert (forall a, FamilyUnion (Im F (inverse_image (sum_space_point_set_intro X a))) = Full_set).
intro.
extensionality_ensembles_inv;
  [constructor |].
subst.
assert (In (@Full_set (point_set (SumTopology A X))) (sum_space_point_set_intro X a x)) by constructor.
rewrite <- eq in H0.
inversion H0.
subst.
repeat econstructor;
  eassumption.

destruct (choice_on_dependent_type _ (fun a => (HC a _ (H a) (H0 a)))) as [fa Hfa].

assert (forall a (U : {U : _ | In (fa a) U}), exists S, In F S /\ inverse_image (sum_space_point_set_intro X a) S = proj1_sig U).
intros a [U HU].
destruct (Hfa a) as [H1 [H2 H3]].
pose proof (H2 _ HU).
inversion H4.
subst.
exists x.
now repeat constructor.

destruct (choice_on_dependent_type _ (fun a => (choice_on_dependent_type _ (H1 a)))) as [f Hf].

exists (IndexedUnion (fun a => Im Full_set (f a))).
repeat split.
- apply finite_indexed_union; trivial.
  intro.
  apply FiniteT_img.
  + apply Finite_ens_type.
    now destruct (Hfa a).
  + intros.
    now apply classic.
- intros S HS.
  inversion HS;
    inversion H2;
    subst;
    now destruct (Hf a x0).
- extensionality_ensembles_inv;
    [ constructor |].
  subst.
  destruct x.
  assert (In Full_set p) by constructor.
  destruct (Hfa a) as [H3 [H4 H5]].
  rewrite <- H5 in H2.
  destruct H2, (Hf a (exist _ S H2)).
  assert (In (Im Full_set (f a)) (f a (exist _ S H2))) by now econstructor.
  econstructor.
  econstructor.
  * eassumption.
  * apply in_inverse_image.
    now rewrite (H8 : (@inverse_image _ (point_set (SumTopology A X)) _ _) = _).
Qed.

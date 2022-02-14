From Coq Require Import ProofIrrelevance.
From ZornsLemma Require Import Families Quotients EnsemblesTactics.
Require Export TopologicalSpaces.
Require Import Connectedness Compactness CountabilityAxioms StrongTopology.

Definition QuotientTopology {X : TopologicalSpace} (R : Relation (point_set X)) :
  TopologicalSpace := StrongTopology (True_rect (quotient_projection R)).

Lemma quotient_projection_continuous {X : TopologicalSpace} (R : Relation (point_set X)) :
  @continuous X (QuotientTopology R) (quotient_projection R).
Proof.
intros U HU.
now apply strong_topology_makes_continuous_funcs with (a:=I) in HU.
Qed.

Lemma quotient_projection_open_iff {X : TopologicalSpace} (R : Relation (point_set X))
  (U : Ensemble (point_set (QuotientTopology R))) :
  open (inverse_image (quotient_projection R) U) <-> open U.
Proof.
split.
- now intros H [].
- apply quotient_projection_continuous.
Qed.

Lemma quotient_projection_surjective' {A : Type} (R : relation A):
  surjective (quotient_projection R).
Proof.
intro.
destruct (quotient_projection_surjective y).
now exists x.
Qed.

Lemma quotient_connected {X : TopologicalSpace} (R : Relation (point_set X)) :
  connected X -> connected (QuotientTopology R).
Proof.
intros H U [H1 H2].
destruct (H (inverse_image (quotient_projection R) U)).
- split;
  [ | red;
      rewrite <- inverse_image_complement ];
    now apply quotient_projection_continuous.
- left.
  eapply inverse_image_surjective_injective.
  + apply quotient_projection_surjective'.
  + now rewrite inverse_image_empty.
- right.
  eapply inverse_image_surjective_injective.
  + apply quotient_projection_surjective'.
  + now rewrite inverse_image_full.
Qed.

Lemma quotient_compact {X : TopologicalSpace} (R : Relation (point_set X)) :
  compact X -> compact (QuotientTopology R).
Proof.
intros H F HF eqF.
apply (f_equal (inverse_image (quotient_projection R))) in eqF.
rewrite inverse_image_full,
        inverse_image_family_union_image in eqF.
apply H in eqF.
- destruct eqF as [F' [H1 [H2 H3]]].
  exists (inverse_image (inverse_image (quotient_projection R)) F').
  repeat split.
  + apply inverse_image_finite; trivial.
    apply quotient_projection_surjective'.
  + intros U [H4].
    apply H2 in H4.
    inversion H4.
    subst.
    apply inverse_image_surjective_injective in H5.
    * now subst.
    * apply quotient_projection_surjective'.
  + extensionality_ensembles_inv.
    * constructor.
    * destruct (quotient_projection_surjective' _ x).
      assert (In (FamilyUnion F') x1) as H6
        by now rewrite H3.
      destruct H6, (H2 _ H5).
      subst.
      destruct H6.
      repeat econstructor;
        eassumption.
- intros U [? ? ? ?].
  subst.
  now apply quotient_projection_open_iff, HF.
Qed.

Lemma quotient_separable {X : TopologicalSpace} (R : Relation (point_set X)) :
  separable X -> separable (QuotientTopology R).
Proof.
intros [S [HC HD]].
exists (Im S (quotient_projection R)). split.
- unshelve refine (surj_countable (fun x => exist _ (quotient_projection R (proj1_sig x)) _) HC _).
  + destruct x.
    now econstructor; trivial.
  + intros [? [x H ? ?]].
    exists (exist _ x H).
    now apply subset_eq_compat.
- now apply (dense_image_surjective S
    (quotient_projection_continuous R)
    (quotient_projection_surjective' R)).
Qed.

Lemma saturated_subset_quotient_projection_open {X : TopologicalSpace} (R : relation X) (S : Ensemble X) :
  equivalence R ->
  (forall x, In S x -> Included (equiv_class R x) S) ->
  open S -> @open (QuotientTopology R) (Im S (quotient_projection R)).
Proof.
intros.
apply quotient_projection_open_iff.
replace (inverse_image (quotient_projection R) (Im S (quotient_projection R))) with S; trivial.
extensionality_ensembles_inv.
- repeat econstructor + eassumption.
- apply quotient_projection_minimally_collapses_R in H4; trivial.
  apply H0 in H2.
  apply H2.
  constructor.
  now apply equiv_sym.
Qed.

Lemma induced_function_continuous {X : TopologicalSpace} (R : relation X)
      (Y : TopologicalSpace) (f : X -> Y)
      (Hf : forall x0 x1, R x0 x1 -> f x0 = f x1)
      (HR : equivalence R) :
  continuous f ->
  @continuous (QuotientTopology R) Y (induced_function _ HR Hf).
Proof.
  intros.
  apply StrongTopology.strong_topology_continuous_char.
  intros [].
  simpl.
  unfold compose.
  apply (continuous_funext f); auto.
  intros. symmetry.
  apply induced_function_correct.
Qed.

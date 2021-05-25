From Topology Require Import Homeomorphisms.
From Topology Require Import SubspaceTopology.
From Topology Require Import EuclideanSpaces.
From Topology Require Import CountabilityAxioms.
From Topology Require Import SeparatednessAxioms.
From Coq Require Import Image.

Definition restriction {X Y: Type} (f : X -> Y) (U : Ensemble X): {x | U x} -> {y | Im U f y}.
intro x.
exists (f (proj1_sig x)).
now apply (Im_intro _ _ _ _ _ (proj2_sig x)).
Defined.

Inductive locally_homeomorphic (X Y : TopologicalSpace) : Prop :=
| intro_locally_homeomorphic:
  (forall (x: point_set X),
    exists (f : point_set X -> point_set Y) (U:Ensemble (point_set X)),
      open_neighborhood U x /\
      open (Im U f) /\
      @homeomorphism (SubspaceTopology U) (SubspaceTopology (Im U f)) (restriction f U)) ->
  locally_homeomorphic X Y.

Lemma homeomorphism_refl (X : TopologicalSpace) : @homeomorphism X X id.
Proof.
econstructor;
  (apply continuous_identity || now intros).
Qed.

Lemma restriction_continuous {X Y: TopologicalSpace} (f : point_set X -> point_set Y) (U : Ensemble X):
  continuous f -> @continuous (SubspaceTopology U) (SubspaceTopology (Im U f)) (restriction f U).
Proof.
  intros Hcont V [F H].
  rewrite inverse_image_family_union_image.
  apply open_family_union.
  intros.
  destruct H0.
  subst.
  apply H in H0.
  clear H F V.
  induction H0.
  - match goal with
     | [ |- open ?S ] => replace S with (@Full_set (SubspaceTopology U))
    end.
    + apply open_full.
    + extensionality_ensembles;
        repeat constructor.
  - destruct H, a.
    match goal with
     | [ |- open ?S ] => replace S with (inverse_image (subspace_inc U) (inverse_image f V))
    end.
    + now apply subspace_inc_continuous, Hcont.
    + extensionality_ensembles;
        now repeat constructor.
  - rewrite inverse_image_intersection.
    now apply open_intersection2.
Qed.

Definition full_set_unrestriction (X : TopologicalSpace):
  @SubspaceTopology X (@Im X X (@Full_set X) (@id X)) -> @SubspaceTopology X (@Full_set X).
intro x.
now exists (proj1_sig x).
Defined.

Lemma full_set_unrestriction_continuous (X : TopologicalSpace): continuous (full_set_unrestriction X).
Proof.
  intros V [F H].
  rewrite inverse_image_family_union_image.
  apply open_family_union.
  intros.
  destruct H0.
  subst.
  apply H in H0.
  induction H0.
  - rewrite inverse_image_full.
    apply open_full.
  - destruct H0, a.
    unfold full_set_unrestriction.
    match goal with
     | [ |- open ?S ] => replace S with (inverse_image (subspace_inc (Im (@Full_set X) id)) V0)
    end.
    + now apply subspace_inc_continuous.
    + extensionality_ensembles;
        now repeat constructor.
  - rewrite inverse_image_intersection.
    now apply open_intersection2.
Qed.

Lemma locally_homeomorphic_refl (X : TopologicalSpace) : locally_homeomorphic X X.
Proof.
  apply intro_locally_homeomorphic.
  intros x.
  exists id.
  exists Full_set.
  repeat split.
  - apply X.
  - replace (Im Full_set id) with (@Full_set X).
    + apply X.
    + extensionality_ensembles;
        repeat econstructor.
  - econstructor.
    + apply restriction_continuous, continuous_identity.
    + apply full_set_unrestriction_continuous.
    + now intros [x0 []].
    + intros [x0 [x1 [] ?]].
      now subst.
Qed.

(* Definition of n-dimensional manifold *)
Definition Manifold (X:TopologicalSpace) (n : nat) : Prop :=
  second_countable X /\ Hausdorff X /\ locally_homeomorphic X (EuclideanSpace n).

From Topology Require Import RTopology.
Theorem RManifold : Manifold RTop 1.
Proof.
  constructor.
  - apply RTop_second_countable.
  - split.
    + apply metrizable_Hausdorff.
      apply RTop_metrizable.
    + (* locally_homeomorphic RTop (EuclideanSpace 1) *)
      admit.
Admitted.

(* R^n is a manifold *)
Theorem EuclideanManifold (n : nat) : Manifold (EuclideanSpace n) n.
Proof.
  constructor.
  - (* need proof that second_countable (EuclideanSpace n) *)
    admit.
  - split.
    + (* need proof that R^n is Hausdorff *)
      admit.
    + apply locally_homeomorphic_refl.
Admitted.

Theorem SphereManifold (n : nat) : Manifold (Sphere (S n)) n.
Proof.
  constructor.
  - (* provide an atlas for the sphere *)
    admit.
  - split.
    + (* sphere is Hausdorff *)
      admit.
    + (* sphere is locally homeomorphic to R^n *)
      admit.
Admitted.

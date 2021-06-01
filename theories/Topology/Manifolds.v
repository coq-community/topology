From Coq Require Import Image.
From Topology Require Import Homeomorphisms.
From Topology Require Import SubspaceTopology.
From Topology Require Import CountabilityAxioms.
From Topology Require Import SeparatednessAxioms.
From Topology Require Import EuclideanSpaces.

Definition restriction {X Y: Type} (f : X -> Y) (U : Ensemble X): {x | U x} -> {y | Im U f y}.
intro x.
exists (f (proj1_sig x)).
now apply (Im_intro _ _ _ _ _ (proj2_sig x)).
Defined.

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

(* No matter onto which subset [U] some homeomorphism [f] is
   restricted, it stays a homeomorphism. *)
Lemma homeomorphism_restriction (X Y : TopologicalSpace) (f : X -> Y) (U : Ensemble X) :
  homeomorphism f ->
  @homeomorphism (SubspaceTopology U) (SubspaceTopology (Im U f)) (restriction f U).
Proof.
  intros.
  destruct H.
  unshelve eexists.
  - (* define [g] *)
    intros.
    destruct X0 as [y].
    eexists (g y).
    destruct i.
    subst.
    rewrite H1.
    assumption.
  - apply restriction_continuous.
    assumption.
  - simpl. red. intros ?.
    rewrite ?subspace_open_char.
    intros [V' []].
    exists (Im V' f).
    split.
    + apply homeomorphism_is_open_map.
      * exists g; assumption.
      * assumption.
    + subst.
      apply Extensionality_Ensembles; split; red; intros.
      * red; red.
        destruct H4.
        destruct x.
        red in H4. red in H4.
        simpl in *.
        exists (g x); auto.
      * destruct x.
        constructor.
        red in H4. red in H4.
        simpl in H4.
        red. red. simpl.
        inversion H4; subst; clear H4.
        rewrite H1. assumption.
  - intros.
    destruct x.
    simpl.
    apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
    auto.
  - intros.
    destruct y.
    unfold restriction.
    simpl.
    apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
    auto.
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

Inductive locally_homeomorphic (X Y : TopologicalSpace) : Prop :=
| intro_locally_homeomorphic:
  (forall (x: point_set X),
    exists (f : point_set X -> point_set Y) (U:Ensemble (point_set X)),
      open_neighborhood U x /\
      open (Im U f) /\
      @homeomorphism (SubspaceTopology U) (SubspaceTopology (Im U f)) (restriction f U)) ->
  locally_homeomorphic X Y.

Lemma homeomorphic_locally_homeomorphic (X Y : TopologicalSpace) :
  homeomorphic X Y -> locally_homeomorphic X Y.
Proof.
  intros.
  destruct H.
  constructor.
  intros.
  exists f, Full_set.
  repeat split; auto using open_full, homeomorphism_restriction.
  apply homeomorphism_is_open_map; auto using open_full.
Qed.

Corollary locally_homeomorphic_refl (X : TopologicalSpace) : locally_homeomorphic X X.
Proof.
  apply homeomorphic_locally_homeomorphic.
  apply homeomorphic_equiv.
Qed.

(* Definition of n-dimensional manifold *)
Definition Manifold (X:TopologicalSpace) (n : nat) : Prop :=
  second_countable X /\ Hausdorff X /\ locally_homeomorphic X (EuclideanSpace n).

From Topology Require Import RTopology.

Lemma RTop_lhom_R1 : locally_homeomorphic RTop (EuclideanSpace 1).
Proof. Admitted.

Lemma RManifold : Manifold RTop 1.
Proof.
  constructor.
  - apply RTop_second_countable.
  - split.
    + apply metrizable_Hausdorff.
      apply RTop_metrizable.
    + apply RTop_lhom_R1.
Qed.

Lemma Euclidean_second_countable (n : nat) : second_countable (EuclideanSpace n).
Proof. Admitted.


Lemma EuclideanHausdorff (n : nat) : Hausdorff (EuclideanSpace n).
Proof. Admitted.


(* R^n is a manifold *)
Lemma EuclideanManifold (n : nat) : Manifold (EuclideanSpace n) n.
Proof.
  constructor.
  - apply Euclidean_second_countable.
  - split.
    + apply EuclideanHausdorff.
    + apply locally_homeomorphic_refl.
Qed.

Lemma Sphere_second_countable (n : nat) : second_countable (Sphere n).
Proof. Admitted.

Lemma Sphere_hausdorff (n : nat) : Hausdorff (Sphere n).
Proof. Admitted.

Lemma Sphere_lhom_Rn (n : nat) : locally_homeomorphic (Sphere (S n)) (EuclideanSpace n).
Proof. Admitted.

Lemma SphereManifold (n : nat) : Manifold (Sphere (S n)) n.
Proof.
  constructor.
  - apply Sphere_second_countable.
  - split.
    + apply Sphere_hausdorff.
    + apply Sphere_lhom_Rn.
Qed.

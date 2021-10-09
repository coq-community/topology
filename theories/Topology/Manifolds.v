From Coq Require Import Image.
From Topology Require Import Homeomorphisms.
From Topology Require Import SubspaceTopology.
From Topology Require Import CountabilityAxioms.
From Topology Require Import SeparatednessAxioms.
From Topology Require Import EuclideanSpaces.

Definition restriction {X Y: Type} (f : X -> Y) (U : Ensemble X): {x | U x} -> {y | Im U f y} :=
  fun x =>
    exist _
          (f (proj1_sig x))
          (Im_intro _ _ U f _ (proj2_sig x) _ eq_refl).

Lemma restriction_continuous {X Y: TopologicalSpace} (f : point_set X -> point_set Y) (U : Ensemble X):
  continuous f -> @continuous (SubspaceTopology U) (SubspaceTopology (Im U f)) (restriction f U).
Proof.
  intros.
  rewrite subspace_continuous_char.
  unfold compose.
  simpl.
  apply (continuous_composition f); try assumption.
  apply subspace_inc_continuous.
Qed.

(* No matter onto which subset [U] some homeomorphism [f] is
   restricted, it stays a homeomorphism. *)
Lemma homeomorphism_restriction (X Y : TopologicalSpace) (f : X -> Y) (U : Ensemble X) :
  homeomorphism f ->
  @homeomorphism (SubspaceTopology U) (SubspaceTopology (Im U f)) (restriction f U).
Proof.
Admitted.

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

Definition locally_homeomorphic (X Y : TopologicalSpace) : Prop :=
  forall (x : X),
    exists (f : X -> Y) (U : Ensemble X),
      open_neighborhood U x /\
      open (Im U f) /\
      @homeomorphism (SubspaceTopology U) (SubspaceTopology (Im U f)) (restriction f U).

Lemma homeomorphic_locally_homeomorphic (X Y : TopologicalSpace) :
  homeomorphic X Y -> locally_homeomorphic X Y.
Proof.
  intros.
  destruct H.
  red.
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

Require Import List.
Import ListNotations.
Import Ensembles.

Definition Rinfty_from_list (l : list R) : Rinfty :=
  fun n => nth n l 0.

Program Definition Rn_from_list (l : list R) : EuclideanSpace (length l) :=
  Rinfty_from_list l.
Next Obligation.
  intros ? ?.
  apply nth_overflow.
  assumption.
Qed.

(* TODO: We need to establish a Coercion between [EuclideanSpace] and
   [Rinfty] via [proj1_sig]. *)
Lemma RTop_homeo_R1 : homeomorphic RTop (EuclideanSpace 1).
Proof.
  exists (fun x => Rn_from_list [x]).
  exists (fun p : EuclideanSpace 1 => (proj1_sig p) 0%nat).
  - (* continuity of [f] *)
    admit.
  - (* continuity of [g] *)
    admit.
  - intros. simpl. reflexivity.
  - intros. simpl. unfold Rn_from_list.
    Require Import FunctionalExtensionality.
    Require Import Program.Subset.
    apply subset_eq.
    apply functional_extensionality_dep.
    simpl.
    admit.
Admitted.

Corollary RTop_lhom_R1 : locally_homeomorphic RTop (EuclideanSpace 1).
Proof.
  apply homeomorphic_locally_homeomorphic.
  apply RTop_homeo_R1.
Qed.

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

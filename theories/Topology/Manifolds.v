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
    exists (U : Ensemble X) (V : Ensemble Y),
      open_neighborhood U x /\
      open V /\
      homeomorphic (SubspaceTopology U) (SubspaceTopology V).

Lemma Subspace_Full_set_homeomorphic X :
  homeomorphic X (SubspaceTopology (@Full_set X)).
Proof.
  unshelve eexists (fun x => exist _ x _); try constructor.
  exists (subspace_inc Full_set); admit.
Admitted.

Instance homeomorphic_Equiv : RelationClasses.Equivalence homeomorphic.
Proof.
Admitted.

Lemma homeomorphic_locally_homeomorphic (X Y : TopologicalSpace) :
  homeomorphic X Y -> locally_homeomorphic X Y.
Proof.
  intros.
  red.
  intros.
  exists Full_set, Full_set.
  repeat split; auto using open_full.
  transitivity X.
  { symmetry.
    apply Subspace_Full_set_homeomorphic.
  }
  transitivity Y.
  2: {
    apply Subspace_Full_set_homeomorphic.
  }
  assumption.
Qed.

Corollary locally_homeomorphic_refl (X : TopologicalSpace) : locally_homeomorphic X X.
Proof.
  apply homeomorphic_locally_homeomorphic.
  reflexivity.
Qed.

Lemma proj1_sig_Im_Full_set {X : Type} (U : Ensemble X) :
  Im Full_set (@proj1_sig _ U) = U.
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - inversion H; subst; clear H.
    apply (proj2_sig x0).
  - exists (exist _ x H); auto with sets.
Qed.

Lemma subspace_inc_open_map (X : TopologicalSpace) (U : Ensemble X) :
  open U <-> open_map (subspace_inc U).
Proof.
  split.
  - intros. red.
    intros.
    rewrite subspace_open_char in H0.
    destruct H0 as [V []].
    subst.
    replace (Im _ _) with (Intersection U V).
    { apply open_intersection2; assumption. }
    apply Extensionality_Ensembles; split; red; intros.
    + destruct H1.
      exists (exist _ x H1); try reflexivity.
      constructor.
      assumption.
    + inversion H1; subst; clear H1.
      destruct H2.
      split; try assumption.
      apply (proj2_sig x0).
  - intros.
    specialize (H Full_set).
    unfold subspace_inc in H.
    replace (Im Full_set _) with U in H.
    { apply H.
      apply open_full.
    }
    symmetry.
    apply proj1_sig_Im_Full_set.
Qed.

Require Import SumTopology.

Definition SumTopology2 (X Y : TopologicalSpace) : TopologicalSpace :=
  SumTopology bool (fun b : bool => if b then X else Y).

Definition SumTopology_inclusion {A : Type} {X : A -> TopologicalSpace} (a : A) :
  X a -> SumTopology A X :=
  fun q => sum_space_point_set_intro _ _ q.

Lemma SumTopology_inclusion_open {A X} a :
  open_map (@SumTopology_inclusion A X a).
Proof.
  red. intros.
  rewrite <- sum_topology_inj_image_open.
  assumption.
Qed.

Definition SumTopology2_inl {X Y : TopologicalSpace} : X -> SumTopology2 X Y :=
  SumTopology_inclusion true.

Lemma SumTopology2_inl_open {X Y} :
  open_map (@SumTopology2_inl X Y).
Proof.
  unfold SumTopology2_inl.
  apply (@SumTopology_inclusion_open bool (fun b : bool => if b then X else Y) true).
Qed.

Lemma locally_homeomorphic_sum (X Y Z : TopologicalSpace) :
  locally_homeomorphic X Y ->
  locally_homeomorphic X (SumTopology2 Y Z).
Proof.
  intros.
  red; intros.
  specialize (H x) as [U [V]].
  exists U.
  exists (Im V SumTopology2_inl).
  intuition.
  - apply SumTopology2_inl_open.
    assumption.
  - transitivity (SubspaceTopology V);
      try assumption.
    admit.
Admitted.

(* Under what condition is [locally_homeomorphic] symmetric?
  If [X] is locally homeomorphic to [Y], then not all points of [Y]
  might be necessary, so [Y] could have arbitrary structure. See for
  example the above lemma [locally_homeomorphic_sum].
*)

Lemma locally_homeomorphic_trans (X Y Z : TopologicalSpace) :
  locally_homeomorphic X Y ->
  locally_homeomorphic Y Z ->
  locally_homeomorphic X Z.
Proof.
  intros.
  red.
  intros.
  specialize (H x) as [U0 [V0 [? [? [f0]]]]].
  specialize (H0 (proj1_sig (f0 (exist _ x (proj2 H))))) as [U1 [V1 [? [? [f1]]]]].
  pose (W := Intersection V0 U1).
  exists (Im (inverse_image f0 (inverse_image (subspace_inc V0) W)) (subspace_inc U0)).
  exists (Im (Im (inverse_image (subspace_inc U1) W) f1) (subspace_inc V1)).
  repeat split.
  - apply (subspace_inc_open_map _ U0).
    + apply H.
    + apply H2.
      apply subspace_inc_continuous.
      unfold W.
      apply open_intersection2;
        try assumption.
      apply H0.
  - exists (exist _ x (proj2 H)).
    2: reflexivity.
    constructor.
    constructor.
    split.
    + apply (proj2_sig _).
    + apply H0.
  - apply (subspace_inc_open_map _ V1).
    1: assumption.
    apply homeomorphism_is_open_map;
      try assumption.
    apply subspace_inc_continuous.
    apply open_intersection2;
      try assumption.
    apply H0.
  - (* Very difficult. *)
    admit.
Admitted.

Require Import Connectedness.

(* Needs homology theory or similar to prove. *)
Theorem euclidean_dimension_invariance n m :
  homeomorphic (EuclideanSpace n) (EuclideanSpace m) ->
  n = m.
Proof.
Admitted.

Definition locally_euclidean_at {X : TopologicalSpace} (p : X) (n : nat) :=
  exists U,
    open_neighborhood U p /\
      homeomorphic (SubspaceTopology U) (EuclideanSpace n).

Lemma manifold_dimension_invariance_point (X : TopologicalSpace) (p : X) n m :
  locally_euclidean_at p n ->
  locally_euclidean_at p m ->
  n = m.
Proof.
  intros.
  destruct H as [U []].
  destruct H0 as [V []].
  apply euclidean_dimension_invariance.
  (* Consider the intersection of [U] and [V].
     Show that it contains a set homeomorphic to both an n- and an m- ball. *)
  admit.
Admitted.

Definition locally_euclidean_same_dimension {X : TopologicalSpace} (p q : X) :=
  exists n,
    locally_euclidean_at p n /\
      locally_euclidean_at q n.

Import RelationClasses.

Instance locally_euclidean_same_dimension_Symm {X} :
  Symmetric (@locally_euclidean_same_dimension X).
Proof.
  red; intros.
  destruct H as [n].
  exists n.
  tauto.
Qed.

Instance locally_euclidean_same_dimension_Trans {X} :
  Transitive (@locally_euclidean_same_dimension X).
Proof.
  red; intros.
  destruct H as [n [Hx Hy0]], H0 as [m [Hy1 Hz]].
  assert (n = m).
  { eapply manifold_dimension_invariance_point; eassumption.
  }
  subst. exists m. tauto.
Qed.

Import ZornsLemma.Quotients.

Lemma locally_euclidean_same_dimension_open {X : TopologicalSpace} (p : X) :
  open (equiv_class locally_euclidean_same_dimension p).
Proof.
  apply open_char_neighborhood.
  intros.
  inversion H; subst; clear H.
  red.
  destruct H0 as [n []].
  destruct H0 as [U []].
  exists U; split; try assumption.
  intros ? ?.
  constructor.
  red. exists n; split; try assumption.
  exists U; split; try assumption.
  split; try assumption.
  apply H0.
Qed.

Import RelationClasses.
Import ZornsLemma.DecidableDec.

Lemma equiv_classes_open_clopen (X : TopologicalSpace) (R : X -> X -> Prop) {HR: Equivalence R} :
  (forall p, open (equiv_class R p)) ->
  forall p, clopen (equiv_class R p).
Proof.
  intros.
  split; auto.
  red.
  replace (Complement (equiv_class R p)) with
    (IndexedUnion
       (fun p0 : X =>
          if classic_dec (R p p0) then
            Empty_set
          else
            (equiv_class R p0))).
  { apply open_indexed_union.
    intros. destruct (classic_dec _).
    + apply open_empty.
    + auto.
  }
  apply Extensionality_Ensembles; split; red; intros.
  - inversion H0; subst; clear H0.
    destruct (classic_dec _).
    { contradiction. }
    repeat red. intros.
    destruct H1, H0.
    apply n.
    transitivity x; try assumption.
    symmetry; assumption.
  - exists x.
    repeat red in H0.
    destruct (classic_dec _).
    + exfalso. apply H0.
      constructor. assumption.
    + constructor.
      reflexivity.
Qed.

Lemma equiv_classes_open_connected_total (X : TopologicalSpace) (R : X -> X -> Prop)
      {HR: Equivalence R} :
  connected X ->
  (forall p, open (equiv_class R p)) ->
  forall p0 p1, R p0 p1.
Proof.
  intros.
  specialize (H (equiv_class R p0)).
  destruct H.
  { apply equiv_classes_open_clopen; try assumption.
  }
  { cut (In Empty_set p0).
    { contradiction. }
    rewrite <- H.
    constructor.
    reflexivity.
  }
  cut (In Full_set p1).
  2: { constructor. }
  rewrite <- H.
  intros.
  destruct H1.
  assumption.
Qed.

(* Consider a topological space [X] which is connected and in each
   point is locally homeomorphic to *some* ℝ^n. Then the choice of [n]
   is globally uniform. I.e. for all points the same. *)
Theorem manifold_dimension_invariance (X : TopologicalSpace) :
  connected X ->
  inhabited X ->
  (forall p : X,
    exists n,
      locally_euclidean_at p n) ->
  exists! n,
  forall p : X,
    locally_euclidean_at p n.
Proof.
  intros.
  (* Strategy: Split the points of [X] into equivalence classes,
     according to their local dimension.
     Then show that each equivalence class is open.
     Since [X] is connected, there can be at most one equiv-class,
     and because [X] is inhabited there is at least one eqiuv-class.
   *)
  assert (Equivalence (@locally_euclidean_same_dimension X)).
  { split; try typeclasses eauto.
    red. intros p.
    destruct (H1 p) as [n].
    exists n; tauto.
  }
  assert (forall p0 p1 : X,
             locally_euclidean_same_dimension p0 p1).
  { apply equiv_classes_open_connected_total;
      try assumption.
    apply locally_euclidean_same_dimension_open.
  }
  destruct H0 as [p0].
  destruct (H1 p0) as [n0].
  exists n0. split.
  - intros.
    specialize (H3 p0 p) as [m []].
    assert (m = n0).
    { eauto using manifold_dimension_invariance_point. }
    subst.
    assumption.
  - intros.
    specialize (H4 p0).
    eauto using manifold_dimension_invariance_point.
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

Require Import Homeomorphisms.
Require Import SubspaceTopology.
Require Import EuclideanSpaces.
Require Import CountabilityAxioms.
Require Import SeparatednessAxioms.
Require Export Ensembles.

Definition restriction {X Y: Type} (f : X -> Y) (U : Ensemble X): {x | U x} -> {y | Im U f y}.
intro x.
apply (exist _ (f (proj1_sig x))).
apply (Im_intro _ _ _ _ _ (proj2_sig x)).
reflexivity.
Defined.

Inductive local_homeomorphism {X Y : TopologicalSpace}
                              (f : point_set X -> point_set Y) : Prop :=
| intro_local_homeomorphism:
  (forall (x: point_set X),
    exists U:Ensemble (point_set X),
      open_neighborhood U x /\
      open (Im U f) /\
      @homeomorphism (SubspaceTopology U) (SubspaceTopology (Im U f)) (restriction f U)) ->
    local_homeomorphism f.

Inductive locally_homeomorphic (X Y:TopologicalSpace) : Prop :=
| intro_locally_homeomorphic: forall f:point_set X -> point_set Y,
    local_homeomorphism f -> locally_homeomorphic X Y.


Lemma locally_homeomorphic_refl (X : TopologicalSpace) : locally_homeomorphic X X.
Proof.
  apply intro_locally_homeomorphic with (f := (fun x => x)).
  constructor.
  intros x.
  exists Full_set.
  split.
  - repeat constructor. apply open_full.
  - split.
    + assert (surjective (fun x : X => x)).
      {
        econstructor.
        reflexivity.
      }
      rewrite <- Im_Full_set_surj.
      * apply open_full.
      * assumption.
    + econstructor.
      * admit.
      * admit.
      * admit.
      * admit.
Admitted.

Definition Manifold (X:TopologicalSpace) (n : nat) : Prop :=
  second_countable X /\ Hausdorff X
  /\ locally_homeomorphic X (EuclideanSpace n).

(* R^n is a manifold *)

Require Import MetricSpaces.

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

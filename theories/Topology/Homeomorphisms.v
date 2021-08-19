From ZornsLemma Require Import EnsemblesTactics.
Require Export TopologicalSpaces.
Require Export Continuity.

Inductive homeomorphism {X Y:TopologicalSpace}
  (f:X -> Y) : Prop :=
| intro_homeomorphism: forall g:Y -> point_set X,
  continuous f -> continuous g ->
  (forall x:point_set X, g (f x) = x) ->
  (forall y:point_set Y, f (g y) = y) -> homeomorphism f.

Lemma homeomorphism_is_invertible: forall {X Y:TopologicalSpace}
  (f:X -> Y),
  homeomorphism f -> invertible f.
Proof.
intros.
destruct H as [g].
exists g; trivial.
Qed.

Definition open_map {X Y:TopologicalSpace}
  (f:X -> Y) : Prop :=
forall U:Ensemble X, open U -> open (Im U f).

Lemma homeomorphism_is_open_map: forall {X Y:TopologicalSpace}
  (f:X -> Y),
  homeomorphism f -> open_map f.
Proof.
intros.
destruct H as [g].
red; intros.
assert (Im U f = inverse_image g U).
{ extensionality_ensembles.
  - subst.
    constructor.
    now rewrite H1.
  - exists (g x); auto. }
rewrite H4.
auto.
Qed.

Lemma invertible_open_map_is_homeomorphism: forall {X Y:TopologicalSpace}
  (f:X -> Y),
  invertible f -> continuous f -> open_map f -> homeomorphism f.
Proof.
intros.
destruct H as [g].
exists g; trivial.
red.
intros.
assert (inverse_image g V = Im V f).
{ extensionality_ensembles.
  - exists (g x); auto.
  - constructor.
    now rewrite H5, H. }
rewrite H4.
auto.
Qed.

Lemma homeomorphism_id (X : TopologicalSpace) : homeomorphism (@id X).
Proof.
  exists id; auto using continuous_identity.
Qed.

Inductive homeomorphic (X Y:TopologicalSpace) : Prop :=
| intro_homeomorphic: forall f:X -> point_set Y,
    homeomorphism f -> homeomorphic X Y.

Require Export Relation_Definitions.
From ZornsLemma Require Import Relation_Definitions_Implicit.

Lemma homeomorphic_equiv: equivalence homeomorphic.
Proof.
constructor.
- eexists; eapply homeomorphism_id.
- intros X Y Z ? ?.
  destruct H as [f [finv]].
  destruct H0 as [g [ginv]].
  exists (fun x => g (f x)), (fun z => finv (ginv z));
    congruence || now apply continuous_composition.
- intros X Y ?.
  destruct H as [f [finv]].
  now exists finv, f.
Qed.

Definition topological_property (P : TopologicalSpace -> Prop) :=
  forall (X Y : TopologicalSpace) (f : X -> Y),
    homeomorphism f -> P X -> P Y.

Global Hint Unfold topological_property : homeo.

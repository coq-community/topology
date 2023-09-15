From Coq Require Export
  Relation_Definitions.
From ZornsLemma Require Import
  EnsemblesTactics
  Relation_Definitions_Implicit.
From Topology Require Export
  TopologicalSpaces
  Continuity.

Inductive homeomorphism {X Y:TopologicalSpace}
  (f:X -> Y) : Prop :=
| intro_homeomorphism: forall g:Y -> X,
  continuous f -> continuous g ->
  (forall x:X, g (f x) = x) ->
  (forall y:Y, f (g y) = y) -> homeomorphism f.

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
rewrite inverse_map_image_inverse_image with f g U.
{ apply H0, H3. }
split; assumption.
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
rewrite <- inverse_map_image_inverse_image with f g V.
{ apply H1, H3. }
split; assumption.
Qed.

Lemma homeomorphism_id (X : TopologicalSpace) : homeomorphism (@id X).
Proof.
  exists id; auto using continuous_identity.
Qed.

Inductive homeomorphic (X Y:TopologicalSpace) : Prop :=
| intro_homeomorphic: forall f:X -> point_set Y,
    homeomorphism f -> homeomorphic X Y.

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

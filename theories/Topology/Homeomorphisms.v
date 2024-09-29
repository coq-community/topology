From Coq Require Import
  Morphisms.
From Topology Require Export
  TopologicalSpaces
  Continuity.
From Coq Require Import
  RelationClasses.

Definition homeomorphism {X Y : TopologicalSpace}
  (f : X -> Y) : Prop :=
  continuous f /\
  exists g : Y -> X,
    continuous g /\
      inverse_map f g.

Lemma homeomorphism_is_invertible: forall {X Y:TopologicalSpace}
  (f:X -> Y),
  homeomorphism f -> invertible f.
Proof.
intros.
destruct H as [_ [g []]].
exists g; assumption.
Qed.

Definition open_map {X Y:TopologicalSpace} (f:X -> Y) : Prop :=
forall U:Ensemble X, open U -> open (Im U f).

(** it suffices to check [open_map] on an [open_basis] *)
Lemma open_map_via_open_basis {X Y : TopologicalSpace} (f : X -> Y)
  (B : Family X) (HB : open_basis B) :
  (forall U, In B U -> open (Im U f)) -> open_map f.
Proof.
  intros Hf U HU.
  rewrite (open_basis_replace_with_FamilyUnion B U HB HU).
  rewrite image_family_union. apply open_family_union.
  intros S HS. destruct HS as [V [HVU HBV] S HS].
  subst S. apply Hf, HBV.
Qed.

Lemma homeomorphism_is_open_map: forall {X Y:TopologicalSpace}
  (f:X -> Y),
  homeomorphism f -> open_map f.
Proof.
intros.
destruct H as [Hf [g [Hg]]].
red; intros.
erewrite inverse_map_image_inverse_image;
  eauto.
Qed.

Lemma inverse_open_map_continuous
  {X Y : TopologicalSpace} (f : X -> Y) (g : Y -> X) :
  inverse_map f g ->
  open_map f <-> continuous g.
Proof.
  intros Hfg.
  split.
  - (* -> *)
    intros Hf U HU.
    erewrite <- inverse_map_image_inverse_image;
      eauto.
  - (* <- *)
    intros Hg U HU.
    erewrite inverse_map_image_inverse_image;
      eauto.
Qed.

Lemma invertible_open_map_is_homeomorphism: forall {X Y:TopologicalSpace}
  (f:X -> Y),
  invertible f -> continuous f -> open_map f -> homeomorphism f.
Proof.
intros X Y f [g Hfg] Hfcont Hfopen.
split; auto.
exists g; split; auto.
eapply inverse_open_map_continuous; eassumption.
Qed.

(** every continuous self-inverse map is a homeomorphism *)
Lemma homeomorphism_cont_involution (X : TopologicalSpace)
  (f : X -> X) :
  continuous f -> (forall x, f (f x) = x) -> homeomorphism f.
Proof.
  intros Hf Hff.
  split; auto.
  exists f; split; auto.
  split; auto.
Qed.

Lemma homeomorphism_id (X : TopologicalSpace) : homeomorphism (@id X).
Proof.
  apply homeomorphism_cont_involution; auto.
  apply continuous_identity.
Qed.

Lemma homeomorphism_compose {X Y Z : TopologicalSpace}
  (f : X -> Y) (g : Y -> Z) :
  homeomorphism f -> homeomorphism g ->
  homeomorphism (compose g f).
Proof.
  intros [Hf [f0 [Hf0 Hff]]] [Hg [g0 [Hg0 Hgg]]].
  split.
  { unfold compose. apply continuous_composition; auto. }
  exists (compose f0 g0). split.
  { unfold compose. apply continuous_composition; auto. }
  apply inverse_map_compose; auto.
Qed.

Definition homeomorphic (X Y : TopologicalSpace) : Prop :=
  exists f : X -> Y, homeomorphism f.

Instance homeomorphic_Equivalence : Equivalence homeomorphic.
Proof.
constructor.
- eexists; eapply homeomorphism_id.
- intros X Y [f Hf].
  destruct Hf as [Hf [g [Hg Hfg]]].
  exists g. split; auto.
  exists f; split; auto.
  apply inverse_map_sym; auto.
- intros X Y Z [f Hf] [g Hg].
  exists (compose g f).
  apply homeomorphism_compose; assumption.
Qed.

(** To prove `topological_property` it is helpful to use
  `Coq.Classes.Morphisms.proper_sym_impl_iff` *)
Definition topological_property (P : TopologicalSpace -> Prop) :=
  Proper (homeomorphic ==> iff) P.

(** a lemma to prove [topological_property] more easily, with less
  boilerplate *)
Lemma Build_topological_property (P : TopologicalSpace -> Prop) :
  (forall (X Y : TopologicalSpace)
     (f : X -> Y) (Hf : continuous f)
     (g : Y -> X) (Hg : continuous g)
     (Hfg : inverse_map f g) (HX : P X), P Y) ->
  topological_property P.
Proof.
  intros H.
  apply proper_sym_impl_iff.
  { typeclasses eauto. }
  intros X Y [f [Hf [g [Hg Hfg]]]].
  exact (H X Y f Hf g Hg Hfg).
Qed.

Lemma topological_property_Proper (P Q : TopologicalSpace -> Prop) :
  (forall X : TopologicalSpace, P X <-> Q X) ->
  topological_property P -> topological_property Q.
Proof.
  intros HPQ HP X Y HXY.
  rewrite <- !HPQ.
  exact (HP X Y HXY).
Qed.

Lemma topological_property_and (P Q : TopologicalSpace -> Prop) :
  topological_property P -> topological_property Q ->
  topological_property (fun X => P X /\ Q X).
Proof.
  intros HP HQ X Y HXY.
  specialize (HP X Y HXY).
  specialize (HQ X Y HXY).
  tauto.
Qed.

Lemma topological_property_or (P Q : TopologicalSpace -> Prop) :
  topological_property P -> topological_property Q ->
  topological_property (fun X => P X \/ Q X).
Proof.
  intros HP HQ X Y HXY.
  specialize (HP X Y HXY).
  specialize (HQ X Y HXY).
  tauto.
Qed.

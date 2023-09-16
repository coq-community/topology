From Coq Require Import
  ClassicalChoice.
From ZornsLemma Require Import
  CardinalsEns.
From Topology Require Export
  TopologicalSpaces.

Section OpenBasis.

Context {X : TopologicalSpace}.
Variable B : Family X.

Record open_basis : Prop :=
  { open_basis_elements :
     forall V:Ensemble X, In B V -> open V;
    open_basis_cover :
     forall (x:X) (U:Ensemble X),
        open U -> In U x -> exists V:Ensemble X,
        In B V /\ Included V U /\ In V x
  }.

Hypothesis Hbasis: open_basis.

Lemma coverable_by_open_basis_impl_open:
  forall U:Ensemble X,
    (forall x:X, In U x -> exists V:Ensemble X,
     In B V /\ Included V U /\ In V x) -> open U.
Proof.
intros.
replace U with (FamilyUnion [ V:Ensemble X |
                          In B V /\ Included V U ]).
- apply open_family_union.
  intros.
  destruct H0.
  destruct H0.
  now apply open_basis_elements.
- extensionality_ensembles.
  + destruct H0.
    auto with sets.
  + destruct (H x H0) as [V].
    destruct H1 as [? [? ?]].
    exists V; auto.
    constructor; auto.
Qed.

End OpenBasis.

Section BuildFromOpenBasis.

Context {X : Type}.
Variable B : Family X.

Definition open_basis_cond :=
  forall U V:Ensemble X, In B U -> In B V ->
    forall x:X, In (Intersection U V) x ->
      exists W:Ensemble X, In B W /\ In W x /\
                           Included W (Intersection U V).
Definition open_basis_cover_cond :=
  forall x:X, exists U:Ensemble X, In B U /\ In U x.

Hypothesis Hbasis : open_basis_cond.
Hypothesis Hbasis_cover: open_basis_cover_cond.

Inductive B_open : Ensemble X -> Prop :=
  | B_open_intro: forall F:Family X, Included F B ->
    B_open (FamilyUnion F).

Lemma B_open_alt (U : Ensemble X) :
  U = FamilyUnion
        (fun V : Ensemble X =>
           In B V /\ Included V U) ->
  B_open U.
Proof.
  intros. rewrite H.
  constructor.
  firstorder.
Qed.

Program Definition Build_TopologicalSpace_from_open_basis : TopologicalSpace :=
  {| point_set := X;
     open := B_open;
  |}.
Next Obligation.
  apply B_open_alt.
  extensionality_ensembles; auto.
  specialize (H S H0).
  inversion H; subst; clear H.
  inversion H1; subst; clear H1.
  exists S; auto.
  split; auto.
  clear x H3.
  intros x Hx.
  exists (FamilyUnion F0); auto.
  exists S; auto.
Qed.
Next Obligation.
  apply B_open_alt.
  extensionality_ensembles; auto.
  destruct H, H0, H1, H2.
  pose proof (H _ H1).
  pose proof (H0 _ H2).
  pose proof (Hbasis _ _ H5 H6).
  assert (In (Intersection S S0) x) by
    now constructor.
  apply H7 in H8.
  clear H7.
  destruct H8, H7 as [? [? ?]].
  exists x0; trivial.
  split; trivial.
  red. intros.
  constructor.
  - exists S; trivial.
    now destruct (H9 x1 H10).
  - destruct (H9 x1 H10).
    econstructor; eassumption.
Qed.
Next Obligation.
  apply B_open_alt.
  extensionality_ensembles.
  - destruct (Hbasis_cover x), H.
    now exists x0.
  - constructor.
Qed.

Lemma Build_TopologicalSpace_from_open_basis_point_set:
  point_set Build_TopologicalSpace_from_open_basis = X.
Proof.
reflexivity.
Qed.

Lemma Build_TopologicalSpace_from_open_basis_basis:
  @open_basis Build_TopologicalSpace_from_open_basis B.
Proof.
constructor.
- intros.
  simpl.
  rewrite <- family_union_singleton.
  constructor.
  red. intros.
  now destruct H0.
- simpl.
  intros.
  destruct H, H0.
  exists S.
  repeat split; auto with sets.
  red. intros.
  now exists S.
Qed.

End BuildFromOpenBasis.

(* The [weight] of a topological space is the least cardinality for
   which there exists a basis on the space.
   See for example:
   https://encyclopediaofmath.org/wiki/Weight_of_a_topological_space
   Some books, for example the “Encyclopedia of general topology”,
   lets the weight be at least aleph0 to ensure that it is infinite. *)
Definition weight (X : TopologicalSpace) {Y : Type} (kappa : Ensemble Y) :=
  least_cardinal_ext (@open_basis X) kappa.

Lemma weight_unique (X : TopologicalSpace) :
  forall {Y0 Y1 : Type} (kappa : Ensemble Y0) (lambda : Ensemble Y1),
    weight X kappa -> weight X lambda ->
    eq_cardinal_ens kappa lambda.
Proof.
  intros.
  eapply least_cardinal_unique; eauto.
Qed.

Lemma weight_exists (X : TopologicalSpace) :
  exists (kappa : Family X), weight X kappa.
Proof.
  apply least_cardinal_ext_exists.
  (* The family of open sets of [X] is a basis of [X]. *)
  exists open. firstorder.
Qed.

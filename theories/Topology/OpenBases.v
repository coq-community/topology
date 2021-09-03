Require Export TopologicalSpaces.
Require Import ClassicalChoice.
From ZornsLemma Require Import EnsemblesSpec EnsemblesTactics.

Section OpenBasis.

Variable X : TopologicalSpace.
Variable B : Family (point_set X).

Record open_basis : Prop :=
  { open_basis_elements :
     forall V:Ensemble (point_set X), In B V -> open V;
    open_basis_cover :
     forall (x:point_set X) (U:Ensemble (point_set X)),
        open U -> In U x -> exists V:Ensemble (point_set X),
        In B V /\ Included V U /\ In V x
  }.

Hypothesis Hbasis: open_basis.

Lemma coverable_by_open_basis_impl_open:
  forall U:Ensemble (point_set X),
    (forall x:point_set X, In U x -> exists V:Ensemble (point_set X),
     In B V /\ Included V U /\ In V x) -> open U.
Proof.
intros.
replace U with (FamilyUnion [ V:Ensemble (point_set X) |
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

Arguments open_basis {X}.
Arguments coverable_by_open_basis_impl_open {X}.
Arguments open_basis_elements {X}.
Arguments open_basis_cover {X}.

Section BuildFromOpenBasis.

Variable X : Type.
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

Definition Build_TopologicalSpace_from_open_basis : TopologicalSpace.
refine (Build_TopologicalSpace X B_open _ _ _).
- intros.
  pose proof (choice (fun (x:{S:Ensemble X | In F S}) (F:Family X) =>
    Included F B /\ proj1_sig x = FamilyUnion F)).
  unshelve refine (let H1:=(H0 _) in _); [ | clearbody H1 ].
  + intros.
    destruct x.
    pose proof (H x i).
    destruct H1.
    exists F0.
    now split.
  + clear H0.
    destruct H1.
    replace (FamilyUnion F) with (FamilyUnion (IndexedUnion x)).
    * constructor.
      red. intros.
      destruct H1.
      pose proof (H0 a).
      destruct H2.
      auto with sets.
    * extensionality_ensembles.
      ** destruct (H0 a), a.
         simpl in H4.
         exists x2; trivial.
         rewrite H4.
         now exists x1.
      ** destruct (H0 (exist _ _ H1)).
         simpl in H4.
         rewrite H4 in H2.
         destruct H2.
         constructor 1 with S0; trivial.
         now exists (exist _ _ H1).
- intros.
  replace (Intersection U V) with (FamilyUnion
    [ S:Ensemble X | In B S /\ Included S (Intersection U V) ]).
  + constructor.
    red. intros.
    destruct H1.
    destruct H1.
    auto.
  + extensionality_ensembles.
    * destruct H1.
      auto.
    * destruct H.
      destruct H0.
      destruct H1.
      destruct H2.
      pose proof (H _ H1).
      pose proof (H0 _ H2).
      pose proof (Hbasis _ _ H5 H6).
      assert (In (Intersection S S0) x) by
        now constructor.
      apply H7 in H8.
      clear H7.
      destruct H8, H7 as [? [? ?]].
      exists x0; trivial.
      constructor.
      split; trivial.
      red. intros.
      constructor.
      ** exists S; trivial.
         now destruct (H9 x1 H10).
      ** destruct (H9 x1 H10).
         econstructor; eassumption.
- replace Full_set with (FamilyUnion B).
  + constructor.
    auto with sets.
  + extensionality_ensembles.
    * constructor.
    * destruct (Hbasis_cover x), H.
      now exists x0.
Defined.

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

Arguments open_basis_cond {X}.
Arguments open_basis_cover_cond {X}.
Arguments Build_TopologicalSpace_from_open_basis {X}.
Arguments Build_TopologicalSpace_from_open_basis_point_set {X}.
Arguments Build_TopologicalSpace_from_open_basis_basis {X}.

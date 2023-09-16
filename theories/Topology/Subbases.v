From ZornsLemma Require Export
  FiniteTypes.
From ZornsLemma Require Import
  FiniteIntersections.
From Topology Require Export
  OpenBases.

Section Subbasis.

Variable X:TopologicalSpace.
Variable SB:Family X.

Record subbasis : Prop := {
  subbasis_elements: forall U:Ensemble X,
    In SB U -> open U;
  subbasis_cover: forall (U:Ensemble X) (x:X),
    In U x -> open U ->
    exists V,
      In V x /\
        In (finite_intersections SB) V /\
        Included V U;
}.

Lemma open_basis_is_subbasis: open_basis SB -> subbasis.
Proof.
intros.
destruct H.
constructor.
{ exact open_basis_elements. }
intros.
destruct (open_basis_cover x U); trivial.
destruct H1 as [? [? ?]].
exists x0. split; auto.
split; auto.
constructor. assumption.
Qed.

Lemma finite_intersections_of_subbasis_form_open_basis:
  subbasis ->
  open_basis (finite_intersections SB).
Proof.
constructor.
- intros.
  induction H0; auto with topology.
  apply H. assumption.
- intros.
  pose proof (subbasis_cover H U x H1 H0) as [V [? []]].
  exists V. repeat split; auto.
Qed.

End Subbasis.

Arguments subbasis {X}.

From ZornsLemma Require Import FiniteIntersections.

Section build_from_subbasis.

Variable X:Type.
Variable S:Family X.

Definition Build_TopologicalSpace_from_subbasis : TopologicalSpace.
refine (Build_TopologicalSpace_from_open_basis
          (finite_intersections S) _ _).
- red; intros.
  exists (Intersection U V); repeat split; trivial.
  + apply intro_intersection; trivial.
  + destruct H1; assumption.
  + destruct H1; assumption.
  + destruct H2; assumption.
  + destruct H2; assumption.
- red; intro.
  exists Full_set.
  split; constructor.
Defined.

Lemma Build_TopologicalSpace_from_subbasis_subbasis:
  @subbasis Build_TopologicalSpace_from_subbasis S.
Proof.
assert (@open_basis Build_TopologicalSpace_from_subbasis
  (finite_intersections S)).
{ apply Build_TopologicalSpace_from_open_basis_basis. }
constructor.
- intros.
  simpl in U.
  apply open_basis_elements with (finite_intersections S); trivial.
  constructor; trivial.
- intros.
  destruct (@open_basis_cover _ _ H x U) as [V]; trivial.
  destruct H2 as [? [? ?]].
  simpl.
  exists V. repeat split; auto.
Qed.

End build_from_subbasis.

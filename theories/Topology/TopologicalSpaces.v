From Coq Require Export Ensembles.
From ZornsLemma Require Import EnsemblesImplicit.
From ZornsLemma Require Export Families.
From ZornsLemma Require Export IndexedFamilies.
From ZornsLemma Require Export FiniteTypes.
From ZornsLemma Require Import EnsemblesSpec.
From ZornsLemma Require Import Powerset_facts.

Record TopologicalSpace : Type := {
  point_set :> Type;
  open : Ensemble point_set -> Prop;
  open_family_union : forall F : Family point_set,
    (forall S : Ensemble point_set, In F S -> open S) ->
    open (FamilyUnion F);
  open_intersection2: forall U V:Ensemble point_set,
    open U -> open V -> open (Intersection U V);
  open_full : open Full_set
}.

Arguments open {t}.
Arguments open_family_union {t}.
Arguments open_intersection2 {t}.

Lemma open_empty: forall X:TopologicalSpace,
  open (@Empty_set X).
Proof.
intros.
rewrite <- empty_family_union.
apply open_family_union.
intros.
destruct H.
Qed.

Lemma open_union2: forall {X:TopologicalSpace}
  (U V:Ensemble X), open U -> open V -> open (Union U V).
Proof.
intros.
rewrite union_as_family_union.
apply open_family_union.
intros.
destruct H1; trivial.
Qed.

Lemma open_indexed_union: forall {X:TopologicalSpace} {A:Type}
  (F:IndexedFamily A X),
  (forall a:A, open (F a)) -> open (IndexedUnion F).
Proof.
intros.
rewrite indexed_to_family_union.
apply open_family_union.
intros.
destruct H0.
rewrite H1; apply H.
Qed.

Lemma open_finite_indexed_intersection:
  forall {X:TopologicalSpace} {A:Type}
    (F:IndexedFamily A X),
    FiniteT A -> (forall a:A, open (F a)) ->
    open (IndexedIntersection F).
Proof.
intros.
induction H.
- rewrite empty_indexed_intersection.
  apply open_full.
- assert (IndexedIntersection F = Intersection
    (IndexedIntersection (fun x:T => F (Some x)))
    (F None)).
  { apply Extensionality_Ensembles; split; red; intros.
    - destruct H1.
      constructor.
      + constructor.
        intros; apply H1.
      + apply H1.
    - destruct H1.
      destruct H1.
      constructor.
      destruct a.
      + apply H1.
      + apply H2.
  }
  rewrite H1.
  apply open_intersection2.
  + apply IHFiniteT.
    intros; apply H0.
  + apply H0.
- destruct H1.
  assert (IndexedIntersection F =
    IndexedIntersection (fun x:X0 => F (f x))).
  { apply Extensionality_Ensembles; split; red; intros.
    - constructor.
      destruct H3.
      intro; apply H3.
    - constructor.
      destruct H3.
      intro; rewrite <- H2 with a.
      apply H3.
  }
  rewrite H3.
  apply IHFiniteT.
  intro; apply H0.
Qed.

Definition closed {X:TopologicalSpace} (F:Ensemble X) :=
  open (Ensembles.Complement F).

Lemma closed_complement_open: forall {X:TopologicalSpace}
  (U:Ensemble X), closed (Ensembles.Complement U) ->
  open U.
Proof.
intros.
red in H.
rewrite Complement_Complement in H.
assumption.
Qed.

Lemma closed_empty : forall {X : TopologicalSpace},
    closed (@Empty_set X).
Proof.
  intros. red.
  rewrite Complement_Empty_set.
  apply open_full.
Qed.

Lemma closed_full : forall {X : TopologicalSpace},
    closed (@Full_set X).
Proof.
  intros. red.
  rewrite Complement_Full_set.
  apply open_empty.
Qed.

Lemma closed_union2: forall {X:TopologicalSpace}
  (F G:Ensemble X),
  closed F -> closed G -> closed (Union F G).
Proof.
intros.
red in H, H0.
red.
rewrite Complement_Union.
apply open_intersection2; assumption.
Qed.

Lemma closed_intersection2: forall {X:TopologicalSpace}
  (F G:Ensemble X),
  closed F -> closed G -> closed (Intersection F G).
Proof.
intros.
red in H, H0.
red.
rewrite Complement_Intersection.
apply open_union2; trivial.
Qed.

Lemma closed_family_intersection: forall {X:TopologicalSpace}
  (F:Family X),
  (forall S:Ensemble X, In F S -> closed S) ->
  closed (FamilyIntersection F).
Proof.
intros.
unfold closed in H.
red.
rewrite Complement_FamilyIntersection.
apply open_family_union.
intros.
destruct H0.
pose proof (H _ H0).
rewrite Complement_Complement in H1; assumption.
Qed.

Lemma closed_indexed_intersection: forall {X:TopologicalSpace}
  {A:Type} (F:IndexedFamily A X),
  (forall a:A, closed (F a)) -> closed (IndexedIntersection F).
Proof.
intros.
rewrite indexed_to_family_intersection.
apply closed_family_intersection.
intros.
destruct H0.
rewrite H1; trivial.
Qed.

Lemma closed_finite_indexed_union: forall {X:TopologicalSpace}
  {A:Type} (F:IndexedFamily A X),
  FiniteT A -> (forall a:A, closed (F a)) ->
  closed (IndexedUnion F).
Proof.
intros.
red.
rewrite Complement_IndexedUnion.
apply open_finite_indexed_intersection; trivial.
Qed.

Global Hint Unfold closed : topology.
Global Hint Resolve open_family_union open_intersection2 open_full
  open_empty open_union2 open_indexed_union
  open_finite_indexed_intersection closed_complement_open
  closed_union2 closed_intersection2 closed_family_intersection
  closed_indexed_intersection closed_finite_indexed_union
  : topology.

Section Build_from_closed_sets.

Variable X:Type.
Variable closedP : Ensemble X -> Prop.
Hypothesis closedP_empty: closedP Empty_set.
Hypothesis closedP_union2: forall F G:Ensemble X,
  closedP F -> closedP G -> closedP (Union F G).
Hypothesis closedP_family_intersection: forall F:Family X,
  (forall G:Ensemble X, In F G -> closedP G) ->
  closedP (FamilyIntersection F).

Definition Build_TopologicalSpace_from_closed_sets : TopologicalSpace.
refine (Build_TopologicalSpace X
  (fun U:Ensemble X => closedP (Ensembles.Complement U)) _ _ _).
- intros.
  rewrite Complement_FamilyUnion.
  apply closedP_family_intersection.
  destruct 1.
  rewrite <- Complement_Complement.
  apply H; trivial.
- intros.
  rewrite Complement_Intersection.
  apply closedP_union2; trivial.
- apply eq_ind with (1 := closedP_empty).
  rewrite Complement_Full_set.
  reflexivity.
Defined.

Lemma Build_TopologicalSpace_from_closed_sets_closed:
  forall (F:Ensemble (point_set Build_TopologicalSpace_from_closed_sets)),
  closed F <-> closedP F.
Proof.
intros.
unfold closed.
simpl.
rewrite Complement_Complement.
split; trivial.
Qed.

End Build_from_closed_sets.

Arguments Build_TopologicalSpace_from_closed_sets {X}.

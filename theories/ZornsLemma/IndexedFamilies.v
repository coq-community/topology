From ZornsLemma Require Export Families.
From ZornsLemma Require Import
  EnsemblesImplicit
  FunctionProperties
  ImageImplicit.

Set Implicit Arguments.

Section IndexedFamilies.

Variable A T:Type.
Definition IndexedFamily := A -> Ensemble T.
Variable F:IndexedFamily.

Inductive IndexedUnion : Ensemble T :=
  | indexed_union_intro: forall (a:A) (x:T),
    In (F a) x -> In IndexedUnion x.

Inductive IndexedIntersection : Ensemble T :=
  | indexed_intersection_intro: forall (x:T),
    (forall a:A, In (F a) x) -> In IndexedIntersection x.

End IndexedFamilies.

(* unions and intersections over subsets of the index set *)
Lemma sub_indexed_union: forall {A B T:Type} (f:A->B)
  (F:IndexedFamily B T),
  let subF := (fun a:A => F (f a)) in
    Included (IndexedUnion subF) (IndexedUnion F).
Proof.
unfold Included.
intros.
destruct H.
apply indexed_union_intro with (f a).
assumption.
Qed.

Lemma sub_indexed_intersection: forall {A B T:Type} (f:A->B)
  (F:IndexedFamily B T),
  let subF := (fun a:A => F (f a)) in
    Included (IndexedIntersection F) (IndexedIntersection subF).
Proof.
unfold Included.
intros.
constructor.
destruct H.
intro.
apply H.
Qed.

Lemma empty_indexed_intersection: forall {T:Type}
  (F:IndexedFamily False T),
  IndexedIntersection F = Full_set.
Proof.
intros.
apply Extensionality_Ensembles; red; split; red; intros;
  auto with sets.
constructor.
destruct a.
Qed.

Lemma empty_indexed_union: forall {T:Type}
  (F:IndexedFamily False T),
  IndexedUnion F = Empty_set.
Proof.
intros.
apply Extensionality_Ensembles; red; split; red; intros.
- destruct H.
  destruct a.
- destruct H.
Qed.

Lemma Complement_IndexedUnion {A T : Type} {F : IndexedFamily A T} :
  Ensembles.Complement (IndexedUnion F) =
  IndexedIntersection (fun a:A => Ensembles.Complement (F a)).
Proof.
apply Extensionality_Ensembles; split; red; intros.
- constructor. intros.
  red; red; intro.
  contradiction H.
  exists a. assumption.
- destruct H.
  red; red; intro.
  destruct H0.
  contradiction (H a).
Qed.

Lemma Complement_IndexedIntersection {A T : Type} {F : IndexedFamily A T} :
  Ensembles.Complement (IndexedIntersection F) =
  IndexedUnion (fun a:A => Ensembles.Complement (F a)).
Proof.
apply Extensionality_Ensembles; split; red; intros.
- red in H; red in H.
  apply NNPP. intro.
  contradict H.
  constructor. intros.
  apply NNPP. intro.
  contradict H0.
  exists a.
  assumption.
- destruct H.
  red; red; intro.
  apply H.
  destruct H0.
  apply H0.
Qed.

Lemma IndexedIntersection_option_Intersection
      {X A : Type} (V : IndexedFamily (option X) A) :
  IndexedIntersection V =
  Intersection (IndexedIntersection (fun a => V (Some a))) (V None).
Proof.
apply Extensionality_Ensembles; split; red; intros.
- destruct H.
  constructor.
  + constructor. intros. apply H.
  + apply H.
- destruct H. destruct H.
  constructor. intros.
  destruct a; auto.
Qed.

Lemma IndexedIntersection_surj_fn
      {X A B : Type} (V : IndexedFamily A X) (f : B -> A) :
  surjective f ->
  IndexedIntersection V = IndexedIntersection (fun x => V (f x)).
Proof.
intros Hf.
apply Extensionality_Ensembles; split.
- intros x Hx. destruct Hx as [x Hx].
  constructor. intros b. apply Hx.
- intros x Hx. destruct Hx as [x Hx].
  constructor. intros a.
  specialize (Hf a) as [b Hb]. subst. apply Hx.
Qed.

Lemma image_indexed_union (X Y I : Type) (F : IndexedFamily I X) (f : X -> Y) :
  Im (IndexedUnion F) f = IndexedUnion (fun i => Im (F i) f).
Proof.
apply Extensionality_Ensembles; split; red; intros.
- inversion H; subst; clear H.
  inversion H0; subst; clear H0.
  exists a.
  exists x0.
  all: auto.
- inversion H; subst; clear H.
  inversion H0; subst; clear H0.
  exists x0; [|reflexivity].
  exists a. assumption.
Qed.

Section IndexedFamilyToFamily.

(* relation to families of subsets of T *)
Variable T:Type.
Variable A:Type.
Variable F:IndexedFamily A T.

Definition ImageFamily : Family T :=
  Im Full_set F.

Lemma indexed_to_family_union: IndexedUnion F = FamilyUnion ImageFamily.
Proof.
apply Extensionality_Ensembles.
unfold Same_set.
unfold Included.
intuition.
- destruct H.
  apply family_union_intro with (F a).
  + apply Im_intro with a; auto with sets.
  + assumption.
- destruct H.
  destruct H.
  apply indexed_union_intro with x0.
  rewrite <- H1.
  assumption.
Qed.

Lemma indexed_to_family_intersection:
  IndexedIntersection F = FamilyIntersection ImageFamily.
Proof.
apply Extensionality_Ensembles.
unfold Same_set.
unfold Included.
intuition.
- constructor.
  intros.
  destruct H.
  destruct H0.
  rewrite H1.
  apply H.
- constructor.
  intro.
  destruct H.
  apply H.
  apply Im_intro with a;
    auto with sets.
Qed.

End IndexedFamilyToFamily.

From ZornsLemma Require Export Families.
From ZornsLemma Require Export Image.
From ZornsLemma Require Import ImageImplicit.
From ZornsLemma Require Import FiniteTypes.
From ZornsLemma Require Export EnsemblesTactics.

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

Section IndexedFamilyFacts.

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

Lemma finite_indexed_union {A T : Type} {F : IndexedFamily A T} :
  FiniteT A ->
  (forall a, Finite (F a)) ->
  Finite (IndexedUnion F).
Proof.
intro H.
induction H;
  intros.
- replace (IndexedUnion F) with (@Empty_set T).
  + constructor.
  + extensionality_ensembles.
    destruct a.
- replace (IndexedUnion F) with (Union (IndexedUnion (fun t => In (F (Some t)))) (F None)).
  + apply Union_preserves_Finite.
    * apply IHFiniteT.
      intro.
      apply H0.
    * apply H0.
  + extensionality_ensembles.
    * econstructor.
      eassumption.
    * econstructor.
      eassumption.
    * destruct a.
      ** left.
         econstructor.
         eassumption.
      ** now right.
- replace (IndexedUnion F) with (IndexedUnion (fun x => F (f x))).
  + apply IHFiniteT.
    intro.
    apply H1.
  + extensionality_ensembles.
    * econstructor.
      eassumption.
    * destruct H0.
      rewrite <- (H3 a) in H2.
      econstructor.
      eassumption.
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
intros.
apply Extensionality_Ensembles; split; red; intros.
- destruct H0. constructor. intros. apply H0.
- destruct H0. constructor. intros. destruct (H a).
  subst. apply H0.
Qed.

End IndexedFamilyFacts.

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

(* Collect lemmas that are missing from the Coq stdlib and describe the
   Ensemble-operations as boolean algebra.
   Associativity, idempotence, commutativity, complements, distributivity, …
*)

From Coq.Sets Require Export Powerset_facts.
From ZornsLemma Require Export EnsemblesImplicit EnsemblesTactics.
From ZornsLemma Require Import FunctionProperties.
From Coq Require Import Classical_Prop RelationClasses.

Global Instance Included_PreOrder {X : Type} :
  PreOrder (@Included X).
Proof.
firstorder.
Qed.

Global Instance Same_set_Equivalence {X : Type} :
  Equivalence (@Same_set X).
Proof.
firstorder.
Qed.

Global Instance Included_PartialOrder {X : Type} :
  PartialOrder (@Same_set X) (@Included X).
Proof.
  firstorder.
Qed.

Lemma Intersection_Full_set
  {X : Type}
  {U : Ensemble X} :
  Intersection Full_set U = U.
Proof.
now extensionality_ensembles.
Qed.

Lemma Intersection_associative
  {X : Type}
  (U V W: Ensemble X) :
  Intersection (Intersection U V) W = Intersection U (Intersection V W).
Proof.
now extensionality_ensembles.
Qed.

Lemma Complement_Union {X : Type} (U V : Ensemble X) :
  Complement (Union U V) = Intersection (Complement U) (Complement V).
Proof.
unfold Complement.
apply Extensionality_Ensembles; split; red; intros.
- constructor; auto with sets.
- subst. red; red; intro. destruct H. destruct H0; auto.
Qed.

Lemma Complement_Intersection {X : Type} (U V : Ensemble X) :
  Complement (Intersection U V) = Union (Complement U) (Complement V).
Proof.
apply Extensionality_Ensembles; split; red; intros.
- apply NNPP. red; intro.
  unfold Complement, In in H.
  contradict H.
  constructor.
  + apply NNPP. red; intro.
    auto with sets.
  + apply NNPP. red; intro.
    auto with sets.
- red; intro.
  destruct H0.
  destruct H; contradiction.
Qed.

Lemma Complement_Full_set {X : Type} :
  Complement (@Full_set X) = Empty_set.
Proof.
apply Extensionality_Ensembles; split; red; intros.
- exfalso. apply H. constructor.
- destruct H.
Qed.

Lemma Complement_Empty_set {X : Type} :
  Complement (@Empty_set X) = Full_set.
Proof.
apply Extensionality_Ensembles; split; red; intros.
- constructor.
- intro. destruct H0.
Qed.

Lemma False_Ensembles_eq (U V : Ensemble False) : U = V.
Proof.
apply Extensionality_Ensembles; split; red;
  intros; contradiction.
Qed.

Lemma not_inhabited_empty {X : Type} (U : Ensemble X) :
  ~ Inhabited U -> U = Empty_set.
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
- contradict H. exists x. assumption.
- destruct H0.
Qed.

Lemma Setminus_Intersection {X : Type} (U V : Ensemble X) :
  Setminus U V = Intersection U (Complement V).
Proof.
apply Extensionality_Ensembles; split; red; intros.
- destruct H. split; assumption.
- destruct H. split; assumption.
Qed.

Instance Disjoint_Symmetric (A : Type) :
  Symmetric (@Disjoint A).
Proof.
  intros ? ? ?.
  destruct H.
  constructor.
  rewrite Intersection_commutative.
  assumption.
Qed.

Lemma Disjoint_Intersection:
  forall (A : Type) (s1 s2 : Ensemble A),
  Disjoint s1 s2 <-> Intersection s1 s2 = Empty_set.
Proof.
intros. split.
- apply Coq.Sets.Powerset_facts.Disjoint_Intersection.
- intros. constructor. intros.
  intros ?. rewrite H in H0. destruct H0.
Qed.

Lemma Disjoint_Included_Complement :
  forall (A : Type) (s1 s2 : Ensemble A),
    Disjoint s1 s2 <-> Included s1 (Complement s2).
Proof.
intros.
split.
- intros. intros ? ? ?. destruct H.
  apply (H x). split; assumption.
- intros. constructor. intros ? ?.
  destruct H0.
  apply (H x); assumption.
Qed.

Lemma Disjoint_Complement_r {X} (U : Ensemble X) :
  Disjoint U (Complement U).
Proof.
  constructor. intros.
  intros ?. destruct H. intuition.
Qed.

Lemma Disjoint_Complement_l {X} (U : Ensemble X) :
  Disjoint (Complement U) U.
Proof.
  constructor. intros.
  intros ?. destruct H. intuition.
Qed.

Lemma Union_Complement_r {X} (U : Ensemble X) :
  Union U (Complement U) = Full_set.
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - constructor.
  - destruct (classic (In U x)); [left|right]; assumption.
Qed.

Lemma Union_Complement_l {X} (U : Ensemble X) :
  Union (Complement U) U = Full_set.
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  { constructor. }
  destruct (classic (In U x)); [right|left]; assumption.
Qed.

Lemma Couple_swap {X} (x y : X) :
  Couple x y = Couple y x.
Proof.
  extensionality_ensembles_inv; constructor.
Qed.

Lemma union_complement_included_l {X : Type} (U V : Ensemble X) :
  Included V U ->
  Union U (Complement V) = Full_set.
Proof.
  intros.
  apply Extensionality_Ensembles; split; red; intros.
  { constructor. }
  destruct (classic (In V x));
    [left|right]; auto.
Qed.

Lemma not_SIncl_full {X : Type} (U : Ensemble X) :
  ~ Strict_Included Full_set U.
Proof.
  intros ?.
  destruct H.
  apply H0.
  extensionality_ensembles; try constructor.
  apply H. constructor.
Qed.

Lemma Strict_Included_char {X : Type} (U V : Ensemble X) :
  Strict_Included U V <->
    (Included U V /\ exists x, In V x /\ ~ In U x).
Proof.
  split.
  - intros [H0 H1].
    split; auto.
    apply NNPP.
    intros Hn. contradict H1.
    apply Extensionality_Ensembles; split; auto; clear H0.
    intros x HVx. apply NNPP.
    intros HUx. contradict Hn.
    exists x; split; auto.
  - intros [H0 H1].
    split; auto.
    intros ?; subst.
    destruct H1 as [? []]; auto.
Qed.

Corollary Strict_Included_Union_l {X : Type} (U V : Ensemble X) :
  Strict_Included U (Union U V) ->
  exists x : X, In V x /\ ~ In U x.
Proof.
  rewrite Strict_Included_char.
  intros [H0 [x [Hx0 Hx1]]].
  destruct Hx0 as [x Hx0|x Hx0]; try contradiction.
  exists x; split; auto.
Qed.

Corollary Strict_Included_Union_r {X : Type} (U V : Ensemble X) :
  Strict_Included V (Union U V) ->
  exists x : X, In U x /\ ~ In V x.
Proof.
  rewrite Union_commutative.
  apply Strict_Included_Union_l.
Qed.

Lemma Singleton_injective {T : Type} :
  forall x y : T, Singleton x = Singleton y -> x = y.
Proof.
intros.
assert (In (Singleton x) x) by constructor.
rewrite H in H0.
now destruct H0.
Qed.

Definition Union_add_r := Union_add.

Corollary Union_add_l {X : Type} (A B : Ensemble X) (x : X) :
  Add (Union A B) x = Union (Add A x) B.
Proof.
  rewrite (Union_commutative _ (Add _ _)).
  rewrite <- (Union_add_r _ _ A).
  rewrite (Union_commutative _ B).
  reflexivity.
Qed.

Lemma Complement_injective (X : Type) :
  injective (@Complement X).
Proof.
  red; intros.
  rewrite <- (Complement_Complement _ x).
  rewrite <- (Complement_Complement _ y).
  rewrite H.
  reflexivity.
Qed.

Lemma Subtract_not_in {X : Type} (U : Ensemble X) (x : X) :
  ~ In (Subtract U x) x.
Proof.
  intros H.
  destruct H.
  contradict H0.
  constructor.
Qed.

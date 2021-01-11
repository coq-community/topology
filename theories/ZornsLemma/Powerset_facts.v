(* Collect lemmas that are missing from the Coq stdlib and describe the
   Ensemble-operations as boolean algebra.
   Associativity, idempotence, commutativity, complements, distributivity, …
*)

From Coq.Sets Require Export Powerset_facts.
Require Export EnsemblesImplicit EnsemblesTactics.
Require Import Classical_Prop.

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

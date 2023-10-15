From Coq Require Import
  ClassicalChoice
  Description
  FunctionalExtensionality
  ProofIrrelevance.
From ZornsLemma Require Import
  FunctionProperties
  FunctionPropertiesEns
  ZornsLemma.
From Coq Require Import RelationClasses.

Definition le_cardinal (A B : Type) : Prop :=
  exists f : A -> B, injective f.
Definition eq_cardinal (X Y : Type) : Prop :=
  exists (f : X -> Y) (g : Y -> X), inverse_map f g.

Definition lt_cardinal (kappa lambda:Type) : Prop :=
  le_cardinal kappa lambda /\ ~ eq_cardinal kappa lambda.

#[export]
Instance le_cardinal_preorder : PreOrder le_cardinal.
Proof.
split.
- red; intro; exists id; apply id_bijective.
- intros ? ? ? [f Hf] [g Hg].
  exists (compose g f).
  apply injective_compose; auto.
Qed.

#[export]
Instance eq_cardinal_equiv : Equivalence eq_cardinal.
Proof.
split.
- red; intro. exists id, id. apply id_inverse_map.
- red; intros ? ? [f [g Hfg]].
  exists g, f. apply inverse_map_sym. assumption.
- intros ? ? ? [f Hf] [g Hg].
  exists (compose g f).
  apply invertible_compose; assumption.
Qed.

Lemma eq_cardinal_impl_le_cardinal: forall kappa lambda: Type,
  eq_cardinal kappa lambda -> le_cardinal kappa lambda.
Proof.
intros ? ? [f Hf].
exists f. apply invertible_impl_bijective; auto.
Qed.

(** This lemma is helpful, if one wants
    to avoid using an axiom of choice. *)
Lemma le_cardinal_img_inj_ens {X Y : Type} (Z : Type) (f : X -> Y) (U : Ensemble X) :
  injective_ens f U ->
  le_cardinal X Z ->
  le_cardinal (sig (Im U f)) Z.
Proof.
  intros Hf [g Hg].
  assert (forall p : { y : Y | In (Im U f) y },
             { x : X | In U x /\ (proj1_sig p) = f x}) as H.
  { intros [y Hy].
    simpl.
    apply constructive_definite_description.
    inversion Hy; subst; clear Hy.
    exists x; split; auto.
    intros x' []; auto.
  }
  exists (compose g (fun p => proj1_sig (H p))).
  apply injective_compose; auto.
  clear g Hg.
  intros p0 p1 Hp.
  pose proof (proj2_sig (H p0)) as [Hp00 Hp01].
  pose proof (proj2_sig (H p1)) as [Hp10 Hp11].
  destruct p0 as [y0 Hy0], p1 as [y1 Hy1].
  simpl in *. rewrite <- Hp in Hp11.
  cut (y0 = y1); try congruence.
  intros. destruct H0.
  destruct (proof_irrelevance _ Hy0 Hy1).
  reflexivity.
Qed.

(* The results below require Axiom of Choice *)

Lemma surj_le_cardinal: forall {X Y:Type} (f:X->Y),
  surjective f -> le_cardinal Y X.
Proof.
intros.
pose proof (choice (fun (y:Y) (x:X) => f x = y) H).
simpl in H0.
destruct H0 as [g].
exists g.
red; intros.
congruence.
Qed.

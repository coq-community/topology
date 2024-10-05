From Coq Require Export
  Image
  Program.Basics.
From Coq Require Import
  Description
  FunctionalExtensionality.
From ZornsLemma Require Import
  EnsemblesImplicit
  ImageImplicit.

Arguments injective {U} {V}.
Definition surjective {X Y:Type} (f:X->Y) :=
  forall y:Y, exists x:X, f x = y.
Definition bijective {X Y:Type} (f:X->Y) :=
  injective f /\ surjective f.

Definition inverse_map {X Y : Type}
  (f : X -> Y) (g : Y -> X) :=
  (forall x, g (f x) = x) /\
    (forall y, f (g y) = y).

Definition invertible {X Y:Type} (f:X->Y) : Prop :=
  exists g : Y -> X, inverse_map f g.

Lemma inverse_map_sym {X Y : Type}
  (f : X -> Y) (g : Y -> X) :
  inverse_map f g -> inverse_map g f.
Proof.
unfold inverse_map. tauto.
Qed.

Lemma inverse_map_unique {X Y : Type}
  (f : X -> Y) (g0 g1 : Y -> X) :
  inverse_map f g0 -> inverse_map f g1 ->
  forall y : Y, g0 y = g1 y.
Proof.
intros Hg0 Hg1 y.
transitivity (g0 (f (g1 y))).
- rewrite (proj2 Hg1). reflexivity.
- rewrite (proj1 Hg0). reflexivity.
Qed.

Lemma unique_inverse: forall {X Y:Type} (f:X->Y), invertible f ->
  exists! g:Y->X, inverse_map f g. 
Proof.
intros X Y f [g Hfg].
exists g.
split.
{ assumption. }
intros h Hfh.
extensionality y.
eapply inverse_map_unique; eassumption.
Qed.

Definition function_inverse {X Y:Type} (f:X->Y)
  (i:invertible f) : { g:Y->X | inverse_map f g } :=
     (constructive_definite_description _
      (unique_inverse f i)).

Lemma bijective_impl_invertible: forall {X Y:Type} (f:X->Y),
  bijective f -> invertible f.
Proof.
intros.
destruct H.
assert (forall y:Y, {x:X | f x = y}).
{ intro.
  apply constructive_definite_description.
  pose proof (H0 y).
  destruct H1.
  exists x.
  red; split.
  - assumption.
  - intros.
    apply H.
    transitivity y;
      auto with *.
}
pose (g := fun y:Y => proj1_sig (X0 y)).
pose proof (fun y:Y => proj2_sig (X0 y)).
simpl in H1.
exists g. split.
- intro.
  apply H.
  unfold g; rewrite H1.
  reflexivity.
- intro.
  unfold g; apply H1.
Qed.

Lemma invertible_impl_bijective: forall {X Y:Type} (f:X->Y),
  invertible f -> bijective f.
Proof.
intros.
destruct H as [g []].
split.
- red; intros.
  congruence.
- red; intro.
  exists (g y).
  apply H0.
Qed.

Lemma id_bijective: forall {X:Type},
  bijective (@id X).
Proof.
intros.
red; split; red; intros.
- assumption.
- exists y. reflexivity.
Qed.

Lemma id_inverse_map (X : Type) :
  inverse_map (@id X) (@id X).
Proof.
  split; reflexivity.
Qed.

Lemma injective_compose {X Y Z : Type} (f : X -> Y) (g : Y -> Z) :
  injective f -> injective g -> injective (compose g f).
Proof.
intros.
red; intros.
apply H0 in H1.
apply H in H1.
assumption.
Qed.

Lemma surjective_compose {X Y Z : Type} (f : X -> Y) (g : Y -> Z) :
  surjective f -> surjective g -> surjective (compose g f).
Proof.
intros.
red; intros z.
specialize (H0 z) as [y].
specialize (H y) as [x].
exists x. subst. reflexivity.
Qed.

Lemma bijective_compose {X Y Z : Type} (f : X -> Y) (g : Y -> Z) :
  bijective f -> bijective g -> bijective (compose g f).
Proof.
intros.
destruct H, H0.
split.
- apply injective_compose; assumption.
- apply surjective_compose; assumption.
Qed.

Lemma inverse_map_compose {X Y Z : Type}
  (f0 : X -> Y) (f1 : Y -> X) (g0 : Y -> Z) (g1 : Z -> Y) :
  inverse_map f0 f1 -> inverse_map g0 g1 ->
  inverse_map (compose g0 f0) (compose f1 g1).
Proof.
unfold inverse_map, compose; intuition; congruence.
Qed.

Lemma invertible_compose {X Y Z : Type} (f : X -> Y) (g : Y -> Z) :
  invertible f -> invertible g -> invertible (compose g f).
Proof.
intros [f0 Hf] [g0 Hg].
exists (compose f0 g0).
apply inverse_map_compose; assumption.
Qed.

Lemma surjective_compose_conv {X Y Z : Type} (f : X -> Y) (g : Y -> Z) :
  surjective (compose g f) -> surjective g.
Proof.
  intros.
  red; intros.
  specialize (H y).
  destruct H as [x].
  exists (f x).
  assumption.
Qed.

Lemma injective_compose_conv {X Y Z : Type} (f : X -> Y) (g : Y -> Z) :
  injective (compose g f) -> injective f.
Proof.
  intros ? ? ? ?.
  apply (f_equal g) in H0.
  apply H in H0.
  assumption.
Qed.

Lemma surjective_Im_char {X Y : Type} (f : X -> Y) :
  surjective f <-> Im Full_set f = Full_set.
Proof.
  split.
  - intros Hf. apply Extensionality_Ensembles; split.
    { constructor. }
    intros y _. specialize (Hf y) as [x Hx].
    exists x; auto with sets.
  - intros Hf y.
    pose proof (Full_intro Y y) as Hy.
    rewrite <- Hf in Hy. destruct Hy.
    eexists; eauto.
Qed.

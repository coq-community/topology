From ZornsLemma Require Export ImageImplicit.
From ZornsLemma Require Import EnsemblesImplicit.
From ZornsLemma Require Import FunctionProperties.

Lemma option_Full_set_Im (X : Type) :
  Full_set = Add (Im Full_set (@Some X)) None.
Proof.
apply Extensionality_Ensembles; split; red; intros.
2: { constructor. }
destruct x.
- left. exists x; constructor.
- right. constructor.
Qed.

Lemma Im_Full_set_surj {X Y : Type} (f : X -> Y) :
  surjective f <->
  Full_set = Im Full_set f.
Proof.
  split.
  - intros H.
    apply Extensionality_Ensembles; split; red; intros x ?.
    2: { constructor. }
    destruct (H x) as [y].
    subst. apply Im_def.
    constructor.
  - intros H y.
    assert (In (Im Full_set f) y) as Hy.
    { rewrite <- H. constructor. }
    inversion Hy; subst; clear Hy.
    eexists; reflexivity.
Qed.

Lemma Im_monotonous {X Y : Type} (f : X -> Y) (U V : Ensemble X) :
  Included U V ->
  Included (Im U f) (Im V f).
Proof.
  intros.
  red. intros.
  inversion H0; subst; clear H0.
  apply H in H1.
  exists x0; auto.
Qed.

Lemma Im_Included_injective {X Y : Type} (f : X -> Y) :
  injective f <->
  forall U V : Ensemble X,
    Included U V <->
    Included (Im U f) (Im V f).
Proof.
  split.
  - intros. split.
    { apply Im_monotonous. }
    intros.
    red; intros.
    specialize (H0 (f x)).
    unshelve epose proof (H0 _); [|clear H0].
    { exists x; auto. }
    inversion H2; subst; clear H2.
    apply H in H3.
    subst. assumption.
  - intros.
    red; intros.
    specialize (H (Singleton x) (Singleton y)) as [_].
    unshelve epose proof (H _); [|clear H].
    { red; intros.
      inversion H1; subst; clear H1.
      inversion H2; subst; clear H2.
      exists y; auto with sets.
    }
    unshelve epose proof (H1 x _); [|clear H1].
    { constructor. }
    inversion H; subst; clear H.
    reflexivity.
Qed.

Lemma Union_Im {X Y : Type} (f : X -> Y) (U V : Ensemble X) :
  Union (Im U f) (Im V f) = Im (Union U V) f.
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - destruct H.
    all: inversion H; subst; clear H.
    all: apply Im_def.
    1: left.
    2: right.
    all: assumption.
  - inversion H; subst; clear H.
    destruct H0; [left|right].
    all: apply Im_def.
    all: assumption.
Qed.

(* The inclusion [Intersection_Im] holds always.
   The other inclusion is eqiuvalent to injectivity. *)
Lemma Intersection_Im {X Y : Type} (f : X -> Y) (U V : Ensemble X) :
  Included
    (Im (Intersection U V) f)
    (Intersection (Im U f) (Im V f)).
Proof.
  intros y Hy.
  destruct Hy as [x Hx y Hy].
  subst.
  destruct Hx as [x HU HV].
  split; exists x; auto.
Qed.

Lemma Im_id {X : Type} (U : Ensemble X) :
  Im U id = U.
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - inversion H; subst; clear H. assumption.
  - exists x; auto.
Qed.

Lemma Im_singleton {X Y : Type} (f : X -> Y) (x : X) :
  Im (Singleton x) f = Singleton (f x).
Proof.
  apply Extensionality_Ensembles; split.
  - intros y Hy.
    destruct Hy as [x0 Hx0]; subst.
    destruct Hx0; constructor.
  - intros y Hy.
    destruct Hy.
    apply Im_def.
    constructor.
Qed.

Lemma Im_compose {X Y Z : Type} (f : X -> Y) (g : Y -> Z)
  (U : Ensemble X) :
  Im U (compose g f) =
    Im (Im U f) g.
Proof.
  apply Extensionality_Ensembles; split.
  - intros z Hz.
    destruct Hz as [x Hx z Hz].
    subst. unfold compose.
    do 2 apply Im_def.
    assumption.
  - intros z Hz.
    destruct Hz as [y Hy z Hz].
    subst.
    destruct Hy as [x Hx y Hy].
    subst.
    unfold compose.
    exists x; auto.
Qed.

Lemma Im_injective {X Y : Type} (f : X -> Y) (U V : Ensemble X) :
  injective f ->
  Im U f = Im V f -> U = V.
Proof.
  intros Hf HUV.
  apply Extensionality_Ensembles; split;
    intros x Hx.
  - assert (In (Im V f) (f x)).
    { rewrite <- HUV.
      apply Im_def.
      assumption.
    }
    inversion H; subst; clear H.
    apply Hf in H1; subst.
    assumption.
  - assert (In (Im U f) (f x)).
    { rewrite HUV.
      apply Im_def.
      assumption.
    }
    inversion H; subst; clear H.
    apply Hf in H1; subst.
    assumption.
Qed.

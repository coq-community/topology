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
  surjective f ->
  Full_set = Im Full_set f.
Proof.
intros. apply Extensionality_Ensembles; split; red; intros.
2: { constructor. }
destruct (H x) as [y].
subst. apply Im_def.
constructor.
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

Lemma Im_id {X : Type} (U : Ensemble X) :
  Im U id = U.
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - inversion H; subst; clear H. assumption.
  - exists x; auto.
Qed.

Lemma Im_compose_inj_surj {X Y Z : Type} (f : X -> Y) (g : Y -> Z) :
  injective g -> Im Full_set (compose g f) = Im Full_set g ->
  surjective f.
Proof.
  intros ? ? ?.
  assert (In (Im Full_set g) (g y)).
  { apply Im_def. constructor. }
  rewrite <- H0 in H1.
  inversion H1; subst; clear H1.
  unfold compose in H3.
  exists x. apply H in H3.
  congruence.
Qed.

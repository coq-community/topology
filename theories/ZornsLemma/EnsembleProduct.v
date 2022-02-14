From ZornsLemma Require Import EnsemblesImplicit InverseImage.

Definition EnsembleProduct {X Y : Type} (SX : Ensemble X) (SY : Ensemble Y) : Ensemble (X * Y) :=
  fun p => In SX (fst p) /\ In SY (snd p).

Lemma EnsembleProduct_Full {X Y : Type} :
  @EnsembleProduct X Y Full_set Full_set = Full_set.
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - constructor.
  - destruct x.
    split.
    all: constructor.
Qed.

Lemma EnsembleProduct_Empty_l {X Y : Type} V :
  @EnsembleProduct X Y Empty_set V = Empty_set.
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - destruct x. destruct H. destruct H.
  - destruct H.
Qed.

Lemma EnsembleProduct_Empty_r {X Y : Type} U :
  @EnsembleProduct X Y U Empty_set = Empty_set.
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - destruct x. destruct H. destruct H0.
  - destruct H.
Qed.

Lemma EnsembleProduct_Union {X Y : Type} (U0 U1 : Ensemble X) (V0 V1 : Ensemble Y) :
  Included (Union (EnsembleProduct U0 V0) (EnsembleProduct U1 V1))
           (EnsembleProduct (Union U0 U1) (Union V0 V1)).
Proof.
  intros x H.
  destruct H as [|]; destruct x; destruct H.
  - split; left; assumption.
  - split; right; assumption.
Qed.

Lemma EnsembleProduct_Intersection {X Y : Type} (U0 U1 : Ensemble X) (V0 V1 : Ensemble Y) :
  Intersection (EnsembleProduct U0 V0) (EnsembleProduct U1 V1) =
  EnsembleProduct (Intersection U0 U1) (Intersection V0 V1).
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - destruct H. destruct x. destruct H, H0.
    split; split; assumption.
  - destruct H.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    split; constructor; assumption.
Qed.

Lemma inverse_image_fst {X Y : Type} (U : Ensemble X) :
  inverse_image fst U = EnsembleProduct U (@Full_set Y).
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - do 2 red. destruct H. auto with sets.
  - destruct H. constructor. auto.
Qed.

Lemma inverse_image_snd {X Y : Type} (V : Ensemble Y) :
  inverse_image snd V = EnsembleProduct (@Full_set X) V.
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - do 2 red. destruct H. auto with sets.
  - destruct H. constructor. auto.
Qed.

Lemma EnsembleProduct_proj {X Y : Type} (U : Ensemble X) (V : Ensemble Y) :
  EnsembleProduct U V = Intersection (inverse_image fst U)
                                     (inverse_image snd V).
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - destruct x. destruct H.
    split; constructor; assumption.
  - destruct H. inversion H. inversion H0.
    destruct x. split; assumption.
Qed.

Lemma EnsembleProduct_Included {X Y : Type} (U0 U1 : Ensemble X) (V0 V1 : Ensemble Y) :
  Included U0 U1 -> Included V0 V1 ->
  Included (EnsembleProduct U0 V0) (EnsembleProduct U1 V1).
Proof.
  intros. red; intros.
  destruct x; destruct H1.
  split; auto.
Qed.

Lemma EnsembleProduct_Complement {X Y : Type} (U : Ensemble X) (V : Ensemble Y) :
  Complement (EnsembleProduct U V) =
  Union (EnsembleProduct Full_set (Complement V))
        (EnsembleProduct (Complement U) Full_set).
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - red in H. red in H.
    apply not_and_or in H.
    destruct x as [x y].
    destruct H.
    + right. split; [assumption|constructor].
    + left. split; [constructor|assumption].
  - destruct H.
    + destruct x, H.
      cbv. intros. intuition.
    + destruct x, H. cbv. intuition.
Qed.

Lemma EnsembleProduct_Union_dist {X Y : Type} (U : Ensemble X) (V0 V1 : Ensemble Y) :
  Union (EnsembleProduct U V0) (EnsembleProduct U V1) =
  EnsembleProduct U (Union V0 V1).
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - destruct H.
    + destruct H. split; try assumption.
      left. assumption.
    + destruct H. split; try assumption.
      right. assumption.
  - destruct H.
    inversion H0; subst; clear H0.
    + left. split; assumption.
    + right. split; assumption.
Qed.

Lemma EnsembleProduct_Intersection_dist {X Y : Type} (U : Ensemble X) (V0 V1 : Ensemble Y) :
  Intersection (EnsembleProduct U V0) (EnsembleProduct U V1) =
  EnsembleProduct U (Intersection V0 V1).
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - destruct H. destruct H, H0.
    split; try assumption; split; assumption.
  - destruct H. inversion H0; subst; clear H0.
    split; split; assumption.
Qed.

From ZornsLemma Require Import InverseImage.
From ZornsLemma Require Import Families.
From Coq Require Import Sets.Finite_sets_facts.

Lemma inverse_image_fun
  {X Y : Type}
  (f : X -> Y)
  (T : Ensemble Y) :
  inverse_image f T = fun x => T (f x).
Proof.
  apply Extensionality_Ensembles.
  split;
    red;
    intros;
    constructor + destruct H;
    assumption.
Qed.

Lemma in_inverse_image
  {X Y : Type}
  (f : X -> Y)
  (T : Ensemble Y)
  (x : X) :
  In T (f x) <-> In (inverse_image f T) x.
Proof.
  rewrite inverse_image_fun.
  split; auto.
Qed.

Lemma inverse_image_id
  {X Y : Type}
  {f : X -> Y}
  {g : Y -> X} :
  (forall y, f (g y) = y) ->
  forall S,
    inverse_image g (inverse_image f S) = S.
Proof.
  intros Hfg S.
  rewrite <- inverse_image_composition.
  apply Extensionality_Ensembles.
  split; red; intros.
  - destruct H.
    rewrite <- Hfg.
    assumption.
  - constructor.
    rewrite Hfg.
    assumption.
Qed.

Lemma inverse_image_family_union
  {X Y : Type}
  {f : X -> Y}
  {g : Y -> X}
  (F : Family Y) :
  (forall x, g (f x) = x) ->
  (forall y, f (g y) = y) ->
  inverse_image f (FamilyUnion F) = FamilyUnion (inverse_image (inverse_image g) F).
Proof.
  intros Hgf Hfg.
  apply Extensionality_Ensembles.
  split; red; intros.
  - apply in_inverse_image in H.
    inversion H.
    subst.
    rewrite <- Hgf.
    econstructor.
    + constructor.
      erewrite inverse_image_id.
      * exact H0.
      * exact Hfg.
    + rewrite Hgf.
      constructor.
      assumption.
  - destruct H.
    apply in_inverse_image in H.
    constructor.
    econstructor.
    + exact H.
    + constructor.
      rewrite Hgf.
      assumption.
Qed.

Lemma inverse_image_singleton
  {X Y : Type}
  (f : X -> Y)
  (g : Y -> X)
  (T : Ensemble Y) :
  (forall x, g (f x) = x) ->
  (forall y, f (g y) = y) ->
  inverse_image (inverse_image g) (Singleton T) = Singleton (inverse_image f T).
Proof.
  intros Hgf Hfg.
  rewrite inverse_image_fun.
  apply Extensionality_Ensembles.
  split;
    red;
    intros;
    inversion H;
    subst;
    red;
    rewrite inverse_image_id;
    constructor + assumption.
Qed.

Lemma inverse_image_add
  {X Y : Type}
  (f : X -> Y)
  (g : Y -> X)
  (F : Family Y)
  (T : Ensemble Y) :
  (forall x, g (f x) = x) ->
  (forall y, f (g y) = y) ->
  inverse_image (inverse_image g) (Add F T) = Add (inverse_image (inverse_image g) F) (inverse_image f T).
Proof.
  intros Hgf Hfg.
  apply Extensionality_Ensembles.
  rewrite inverse_image_fun, inverse_image_fun.
  split;
    red;
    intros;
    inversion H;
    subst;
    (left; 
     assumption) +
    (right;
     inversion H0;
     rewrite inverse_image_id;
     constructor + assumption).
Qed.

Lemma inverse_image_finite
  {X Y : Type}
  (f : X -> Y)
  (g : Y -> X)
  (F : Family Y) :
  (forall x, g (f x) = x) ->
  (forall y, f (g y) = y) ->
  Finite _ F -> Finite _ (inverse_image (inverse_image g) F).
Proof.
  intros Hgf Hfg Hfin.
  induction Hfin;
    subst.
  - unfold Add.
    rewrite inverse_image_empty.
    constructor.
  - rewrite (inverse_image_add f g);
      [apply Add_preserves_Finite | |];
      assumption.
Qed.

Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Export EnsemblesSpec.
Require Export FunctionProperties.

Definition inverse_image {X Y:Type} (f:X->Y) (T:Ensemble Y) : Ensemble X :=
  [ x:X | In T (f x) ].
Hint Unfold inverse_image : sets.

Lemma inverse_image_increasing: forall {X Y:Type} (f:X->Y)
  (T1 T2:Ensemble Y), Included T1 T2 ->
  Included (inverse_image f T1) (inverse_image f T2).
Proof.
intros.
red; intros.
destruct H0.
constructor.
auto.
Qed.

Lemma inverse_image_empty: forall {X Y:Type} (f:X->Y),
  inverse_image f Empty_set = Empty_set.
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
destruct H as [[]].
destruct H.
Qed.

Lemma inverse_image_full: forall {X Y:Type} (f:X->Y),
  inverse_image f Full_set = Full_set.
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros;
  constructor; constructor.
Qed.

Lemma inverse_image_intersection: forall {X Y:Type} (f:X->Y)
  (T1 T2:Ensemble Y), inverse_image f (Intersection T1 T2) =
  Intersection (inverse_image f T1) (inverse_image f T2).
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
destruct H.
inversion H.
constructor; constructor; trivial.

destruct H as [? [] []].
constructor; constructor; trivial.
Qed.

Lemma inverse_image_union: forall {X Y:Type} (f:X->Y)
  (T1 T2:Ensemble Y), inverse_image f (Union T1 T2) =
  Union (inverse_image f T1) (inverse_image f T2).
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
destruct H.
inversion H.
left; constructor; trivial.
right; constructor; trivial.

constructor.
destruct H as [? []|? []].
left; trivial.
right; trivial.
Qed.

Lemma inverse_image_complement: forall {X Y:Type} (f:X->Y)
  (T:Ensemble Y), inverse_image f (Complement T) =
  Complement (inverse_image f T).
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
red; intro.
destruct H.
destruct H0.
contradiction H.

constructor.
intro.
contradiction H.
constructor; trivial.
Qed.

Lemma inverse_image_composition: forall {X Y Z:Type} (f:Y->Z) (g:X->Y)
  (U:Ensemble Z), inverse_image (fun x:X => f (g x)) U =
  inverse_image g (inverse_image f U).
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
constructor; constructor.
destruct H.
assumption.

destruct H; inversion H.
constructor; trivial.
Qed.

Hint Resolve @inverse_image_increasing : sets.
Hint Rewrite @inverse_image_empty @inverse_image_full
  @inverse_image_intersection @inverse_image_union
  @inverse_image_complement @inverse_image_composition : sets.

Require Import IndexedFamilies.

Lemma inverse_image_indexed_intersection :
  forall {A X Y:Type} (f:X->Y) (F:IndexedFamily A Y),
    inverse_image f (IndexedIntersection F) =
    IndexedIntersection (fun a:A => inverse_image f (F a)).
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
- destruct H.
  inversion_clear H.
  constructor. intros.
  constructor.
  apply H0.
- destruct H.
  constructor.
  constructor. intros.
  destruct (H a).
  exact H0.
Qed.

Lemma inverse_image_indexed_union :
  forall {A X Y:Type} (f:X->Y) (F:IndexedFamily A Y),
    inverse_image f (IndexedUnion F) =
    IndexedUnion (fun a:A => inverse_image f (F a)).
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
- destruct H.
  inversion_clear H.
  exists a.
  constructor.
  exact H0.
- destruct H.
  inversion_clear H.
  constructor.
  exists a.
  exact H0.
Qed.

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

Lemma inverse_image_empty_set {X Y : Type} (f : X -> Y) :
  inverse_image f Empty_set = Empty_set.
Proof.
apply Extensionality_Ensembles.
split; red; intros;
  repeat destruct H.
Qed.

Lemma inverse_image_full_set {X Y : Type} (f : X -> Y) :
  inverse_image f Full_set = Full_set.
Proof.
apply Extensionality_Ensembles.
split; red; intros;
  repeat constructor.
Qed.

Lemma inverse_image_union2 {X Y : Type} (f : X -> Y) (U V : Ensemble Y) :
  inverse_image f (Union U V) = Union (inverse_image f U) (inverse_image f V).
Proof.
apply Extensionality_Ensembles.
split; red; intros.
- destruct H.
  inversion H;
    subst;
  [ left | right ];
    now constructor.
- now inversion H;
    destruct H0;
    subst;
    constructor;
  [ left | right ].
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

Lemma inverse_image_family_union_image
  {X Y : Type}
  (f : X -> Y)
  (F : Family Y) :
  inverse_image f (FamilyUnion F) = FamilyUnion (Im F (inverse_image f)).
Proof.
apply Extensionality_Ensembles.
split; red; intros;
  inversion H;
  inversion H0;
  subst;
  repeat econstructor;
  eassumption + now destruct H1.
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

Lemma inverse_image_image_surjective
  {X Y : Type}
  (f : X -> Y)
  (T : Ensemble Y) :
  surjective f ->
  Im (inverse_image f T) f = T.
Proof.
intro.
apply Extensionality_Ensembles.
split;
  red;
  intros.
- inversion H0.
  subst.
  now destruct H1.
- destruct (H x).
  subst.
  now repeat econstructor.
Qed.

Lemma inverse_image_surjective_singleton
  {X Y : Type}
  (f : X -> Y)
  (T : Ensemble X) :
  surjective f ->
  Included (inverse_image (inverse_image f) (Singleton T)) (Singleton (Im T f)).
Proof.
intros H U HU.
destruct HU.
inversion H0.
subst.
now rewrite inverse_image_image_surjective.
Qed.

Lemma inverse_image_finite {X Y : Type} (f : X -> Y) (F : Family X) :
  surjective f ->
  Finite _ F ->
  Finite _ (inverse_image (inverse_image f) F).
Proof.
intros Hf H.
induction H.
- rewrite inverse_image_empty_set.
  constructor.
- unfold Add.
  rewrite inverse_image_union2.
  pose proof (Singleton_is_finite _ (Im x f)).
  now eapply Union_preserves_Finite,
             Finite_downward_closed,
             inverse_image_surjective_singleton.
Qed.

Lemma inverse_image_surjective_injective
  {X Y : Type}
  (f : X -> Y) :
  surjective f ->
  injective (inverse_image f).
Proof.
intros H U V eq.
apply Extensionality_Ensembles.
split; red; intros;
  destruct (H x);
  subst;
  apply (in_inverse_image f);
[ rewrite <- eq | rewrite eq ];
  now constructor.
Qed.

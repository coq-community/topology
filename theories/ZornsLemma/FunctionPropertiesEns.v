(** Similar to [ZornsLemma.FunctionProperties] but focused on properties
    restricted to ensembles. *)

From Coq Require Import
  ClassicalChoice
  Description
  Program.Subset.
From ZornsLemma Require Import
  DecidableDec
  EnsemblesImplicit
  Families
  FunctionProperties
  Image
  InverseImage
  Powerset_facts
  Proj1SigInjective.
From Coq Require Import
  RelationClasses.

Section FunctionPropertiesEns.
  Context {A B : Type}
    (f : A -> B) (U : Ensemble A) (V : Ensemble B).

  Definition range :=
    forall x : A, In U x -> In V (f x).

  Lemma range_char_inverse_image :
    range <-> Included U (inverse_image f V).
  Proof.
    firstorder.
  Qed.

  Lemma range_char_Im :
    range <-> Included (Im U f) V.
  Proof.
    rewrite range_char_inverse_image.
    symmetry.
    apply inverse_image_Im_adjoint.
  Qed.

  Definition range_restr (H : range) :
    { x : A | In U x } -> { y : B | In V y } :=
    fun p : { x : A | In U x } =>
      exist (fun y : B => In V y)
        (f (proj1_sig p))
        (H (proj1_sig p) (proj2_sig p)).

  Definition injective_ens : Prop :=
    forall x0 x1 : A,
      In U x0 -> In U x1 ->
      f x0 = f x1 ->
      x0 = x1.

  Definition surjective_ens : Prop :=
    forall y : B,
      In V y ->
      exists x : A,
        In U x /\ y = f x.

  Definition bijective_ens : Prop :=
    injective_ens /\ surjective_ens.

  Lemma injective_ens_char
    (H : range) :
    injective_ens <->
      injective (range_restr H).
  Proof.
    split.
    - intros H0 [x0 Hx0] [x1 Hx1] Hx.
      simpl in *.
      specialize (H0 x0 x1 Hx0 Hx1).
      inversion Hx; subst; clear Hx.
      apply subset_eq_compat.
      auto.
    - intros H0 x0 x1 Hx0 Hx1 Heq.
      specialize (H0 (exist _ x0 Hx0)
                     (exist _ x1 Hx1)).
      simpl in H0.
      unshelve epose proof
        (H0 _) as H0.
      { apply subset_eq_compat.
        assumption.
      }
      inversion H0; subst; clear H0.
      reflexivity.
  Qed.

  Lemma injective_injective_ens :
    injective f -> injective_ens.
  Proof.
    intros Hf x0 x1 _ _; apply Hf; auto.
  Qed.

  Lemma surjective_ens_char
    (H : range) :
    surjective_ens <->
      surjective (range_restr H).
  Proof.
    split.
    - intros H0 [y Hy].
      specialize (H0 y Hy) as [x [Hx Hxy]].
      subst.
      exists (exist _ x Hx).
      apply subset_eq_compat.
      reflexivity.
    - intros H0 y Hy.
      specialize (H0 (exist _ y Hy)) as [[x Hx] Hxy].
      exists x; split; auto.
      cbv in Hxy.
      apply eq_sig_fst in Hxy.
      auto.
  Qed.
End FunctionPropertiesEns.

Lemma range_id {A : Type} (U V : Ensemble A) :
  range id U V <-> Included U V.
Proof.
  rewrite range_char_Im.
  rewrite Im_id.
  reflexivity.
Qed.

#[export]
Instance range_id_refl {A : Type} :
  Reflexive (@range A A id).
Proof.
  intros U. apply range_id. reflexivity.
Qed.

Lemma range_full {A B : Type} (f : A -> B) (U : Ensemble A) :
  range f U Full_set.
Proof.
  intros ?; constructor.
Qed.

Lemma injective_ens_empty
  {X Y : Type} (f : X -> Y) :
  injective_ens f Empty_set.
Proof.
  intros ? ? ?. contradiction.
Qed.

Lemma bijective_ens_id {A : Type} (U : Ensemble A) :
  bijective_ens id U U.
Proof.
  split.
  - intros ? ? ?. auto.
  - intros ? ?. exists y. auto.
Qed.

Lemma surjective_ens_Im {X Y : Type} (f : X -> Y)
  (U : Ensemble X) :
  surjective_ens f U (Im U f).
Proof.
  intros y Hy.
  inversion Hy; subst; clear Hy.
  exists x; split; auto.
Qed.

(** ** Locally inverse functions *)
Definition inverse_map_ens {A B : Type}
  (f : A -> B) (g : B -> A)
  (U : Ensemble A) (V : Ensemble B) : Prop :=
  (forall a : A, In U a -> g (f a) = a) /\
    (forall b : B, In V b -> f (g b) = b).

Lemma inverse_map_ens_sym
  {A B : Type} (f : A -> B) (g : B -> A) U V :
  inverse_map_ens f g U V ->
  inverse_map_ens g f V U.
Proof.
  firstorder.
Qed.

Lemma inverse_map_ens_surjective_ens_range {A B : Type}
  (f : A -> B) (g : B -> A) U V :
  surjective_ens f U V ->
  inverse_map_ens f g U V ->
  range g V U.
Proof.
  intros Hf_surj [Hgf Hfg] b Hb.
  specialize (Hf_surj b Hb) as [a [Ha Hab]].
  subst. rewrite Hgf; auto.
Qed.

Lemma bijective_impl_invertible_ens_dec
  {A B : Type} (f : A -> B) (U : Ensemble A) (V : Ensemble B)
  (a0 : A) (HV : forall b : B, In V b \/ ~ In V b) :
  range f U V ->
  bijective_ens f U V ->
  exists g : B -> A, inverse_map_ens f g U V.
Proof.
  intros Hf [Hf0 Hf1].
  assert (forall b : B,
             { a : A | (In V b -> In U a /\ f a = b) /\
                         (~ In V b -> a = a0) }).
  { intros b.
    apply constructive_definite_description.
    specialize (HV b) as [Hb|Hb].
    - specialize (Hf1 b Hb) as [a [Ha0 Ha1]].
      subst. exists a. split; firstorder.
    - exists a0. split; firstorder.
  }
  exists (fun b => proj1_sig (X b)).
  split.
  - intros a Ha.
    pose proof (proj2_sig (X (f a))) as [Ha0 _].
    specialize (Ha0 (Hf a Ha)) as [Ha0 Ha1].
    apply Hf0 in Ha1; auto.
  - intros b Hb.
    pose proof (proj2_sig (X b)) as [Hb0 _].
    specialize (Hb0 Hb) as [_ Hb1].
    assumption.
Qed.

Lemma bijective_ens_impl_invertible_ens
  {A B : Type} (f : A -> B) (U : Ensemble A) (V : Ensemble B)
  (a0 : A) :
  range f U V ->
  bijective_ens f U V ->
  exists g : B -> A, inverse_map_ens f g U V.
Proof.
  apply bijective_impl_invertible_ens_dec; auto.
  intros ?. apply classic.
Qed.

Lemma inverse_map_ens_range_bijective_ens
  {A B : Type} (f : A -> B) (g : B -> A) (U : Ensemble A) (V : Ensemble B) :
  range f U V ->
  inverse_map_ens f g U V ->
  bijective_ens g V U.
Proof.
  intros Hf_range Hfg.
  destruct Hfg as [Hgf Hfg].
  split.
  - intros b0 b1 Hb0 Hb1 Hb.
    rewrite <- (Hfg b0 Hb0), <- (Hfg b1 Hb1).
    congruence.
  - intros a Ha.
    exists (f a). split; auto.
    symmetry; auto.
Qed.

(** ** Function composition *)
Section compose.
  Context {A B C : Type}
    (U : Ensemble A) (V : Ensemble B) (W : Ensemble C).

  Lemma range_compose (f : A -> B) (g : B -> C) :
    range f U V -> range g V W ->
    range (compose g f) U W.
  Proof.
    intros Hf Hg x Hx.
    apply Hg, Hf, Hx.
  Qed.

  Lemma injective_ens_compose (f : A -> B) (g : B -> C) :
    range f U V ->
    injective_ens f U ->
    injective_ens g V ->
    injective_ens (compose g f) U.
  Proof.
    firstorder.
  Qed.

  Lemma surjective_ens_compose (f : A -> B) (g : B -> C) :
    surjective_ens f U V ->
    surjective_ens g V W ->
    surjective_ens (compose g f) U W.
  Proof.
    intros Hf Hg z Hz.
    specialize (Hg z Hz) as [y [Hy Hyz]].
    subst.
    specialize (Hf y Hy) as [x [Hx Hxy]].
    subst.
    exists x; split; auto.
  Qed.

  Lemma bijective_ens_compose (f : A -> B) (g : B -> C) :
    range f U V ->
    bijective_ens f U V -> bijective_ens g V W ->
    bijective_ens (compose g f) U W.
  Proof.
    intros Hf [Hf0 Hf1] [Hg0 Hg1].
    split.
    - eapply injective_ens_compose; eauto.
    - eapply surjective_ens_compose; eauto.
  Qed.
End compose.

(** ** Extending a function from a sigma type *)
Definition sig_fn_extend_dec {X Y : Type} {P : X -> Prop}
  (HP : forall x : X, {P x} + {~ P x})
  (f : sig P -> Y) (y : Y) : X -> Y :=
  fun x : X =>
    match HP x with
    | left Hx => f (exist P x Hx)
    | right _ => y
    end.

Definition sig_fn_extend {X Y : Type} {P : X -> Prop}
  (f : sig P -> Y) (y : Y) : X -> Y :=
  sig_fn_extend_dec
    (fun x => classic_dec (P x)) f y.

Lemma sig_fn_extend_range {X Y : Type} {P : X -> Prop}
  (f : sig P -> Y) (y : Y) (V : Ensemble Y) :
  range f Full_set V ->
  range (sig_fn_extend f y) P V.
Proof.
  intros Hf x Hx.
  cbv. destruct (classic_dec (P x)); try contradiction.
  apply Hf. constructor.
Qed.

Lemma sig_fn_extend_injective_ens {X Y : Type} {P : X -> Prop}
  (f : sig P -> Y) (y : Y) :
  injective_ens (sig_fn_extend f y) P <->
    injective f.
Proof.
  split.
  - intros Hf [x0 Hx0] [x1 Hx1] Hx.
    specialize (Hf x0 x1 Hx0 Hx1).
    apply subset_eq_compat.
    apply Hf. clear Hf.
    cbv. destruct (classic_dec _), (classic_dec _);
      try contradiction.
    destruct (proof_irrelevance _ Hx0 p).
    destruct (proof_irrelevance _ Hx1 p0).
    assumption.
  - intros Hf x0 x1 Hx0 Hx1 Hx.
    specialize (Hf (exist P x0 Hx0) (exist P x1 Hx1)).
    cbv in Hx.
    destruct (classic_dec _), (classic_dec _);
      try contradiction.
    destruct (proof_irrelevance _ Hx0 p).
    destruct (proof_irrelevance _ Hx1 p0).
    specialize (Hf Hx).
    inversion Hf; subst; clear Hf.
    reflexivity.
Qed.

Lemma sig_fn_extend_surjective_ens {X Y : Type} {P : X -> Prop}
  (f : sig P -> Y) (y0 : Y) (V : Ensemble Y) :
  surjective_ens (sig_fn_extend f y0) P V <->
    surjective_ens f Full_set V.
Proof.
  split.
  - intros Hf y Hy.
    specialize (Hf y Hy) as [x [Hx Hxy]].
    subst.
    exists (exist P x Hx).
    split; [constructor|].
    cbv. destruct (classic_dec _); try contradiction.
    destruct (proof_irrelevance _ Hx p); reflexivity.
  - intros Hf y Hy.
    specialize (Hf y Hy) as [[x Hx] [_ Hxy]].
    subst.
    exists x. split; auto.
    cbv. destruct (classic_dec _); try contradiction.
    destruct (proof_irrelevance _ Hx p); reflexivity.
Qed.

(** ** Left and right inverses *)
Lemma injective_ens_left_inverse {X Y : Type}
  (U : Ensemble X) (V : Ensemble Y) (f : X -> Y) (x0 : X) :
  In U x0 ->
  range f U V ->
  injective_ens f U ->
  exists g : Y -> X,
    range g V U /\
      forall x : X, In U x -> g (f x) = x.
Proof.
  intros Hx0 **.
  assert
    (forall y : Y,
        { x : X | (In (Im U f) y -> f x = y /\ In U x) /\
                    (~ In (Im U f) y -> x = x0) }) as ?H.
  { intros y.
    apply constructive_definite_description.
    destruct (classic (In (Im U f) y)).
    - apply Im_inv in H1.
      destruct H1 as [x [Hx Hxy]].
      exists x. split.
      + split; auto. intros ?H.
        subst. contradict H1. exists x; auto.
      + intros x' []. subst.
        specialize (H1 (Im_def _ _ _ Hx)) as [].
        apply H0; auto.
    - exists x0. split; [split|]; auto.
      + intros; contradiction.
      + intros ? [].
        firstorder.
  }
  exists (fun y => proj1_sig (H1 y)).
  split.
  - intros y Hy.
    pose proof (proj2_sig (H1 y)) as [? ?].
    destruct (classic (In (Im U f) y));
      intuition.
    rewrite H5. assumption.
  - intros.
    pose proof (proj2_sig (H1 (f x))) as [? _].
    specialize (H3 (Im_def _ _ _ H2)) as [].
    apply H0 in H3; auto.
Qed.

Lemma surjective_ens_right_inverse {X Y : Type}
  (U : Ensemble X) (V : Ensemble Y) (f : X -> Y) (x0 : X) :
  In U x0 ->
  range f U V ->
  surjective_ens f U V ->
  exists g : Y -> X,
    range g V U /\
      forall y : Y, In V y -> f (g y) = y.
Proof.
  intros Hx0 Hf0 Hf1.
  destruct
    (choice (fun (y : Y) (x : X) =>
               (In V y -> y = f x /\ In U x) /\
                 (~ In V y -> x = x0)))
    as [g Hg].
  { intros y.
    destruct (classic (In V y)) as [Hy|Hy].
    - destruct (Hf1 y Hy) as [x [Hx Hxy]].
      subst. exists x. split; auto.
      intros ?. contradiction.
    - exists x0; split; intros; auto. contradiction.
  }
  exists g; split.
  - intros y Hy.
    specialize (Hf1 y Hy) as [x [Hx Hxy]].
    subst.
    specialize (Hg (f x)) as [? _].
    specialize (H Hy) as [_ ?].
    assumption.
  - intros y Hy.
    specialize (Hg y) as [? _].
    specialize (H Hy) as [? _].
    congruence.
Qed.

Lemma image_surjective_ens_range {X Y : Type}
  (f : X -> Y) (U : Ensemble X) (V : Ensemble Y) :
  range f U V ->
  surjective_ens f U V ->
  V = Im U f.
Proof.
  intros Hf0 Hf1.
  apply Extensionality_Ensembles; split.
  - intros y Hy.
    specialize (Hf1 y Hy) as [x [Hx Hxy]]; subst.
    apply Im_def. assumption.
  - intros y Hy.
    destruct Hy as [x Hx y Hy].
    subst. apply Hf0. assumption.
Qed.

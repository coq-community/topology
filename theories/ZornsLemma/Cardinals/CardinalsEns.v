(** Instead of comparing cardinalities of elements of [Type],
    compare cardinalities of ensembles.
    With this technique, we can avoid problems w.r.t. type universes
    that occur with the approach of [ZornsLemma.Cardinals].

    On the other hand, we need classical logic more often, because a
    statement like [eq_cardinal_ens] decides whether the ensemble and
    a type are inhabited or not.

    Similarly, we can not define [eq_cardinal_ens] via
    [inverse_map_ens], because that leads to a notion incompatible
    with [le_cardinal_ens].  Namely it would reqiure classical logic
    to prove [eq_cardinal_ens -> le_cardinal_ens].
*)
From Coq Require Import
  ClassicalChoice
  Description
  Lia
  PeanoNat
  Program.Subset.
From ZornsLemma Require Import
  Cardinals.Cardinals
  DecidableDec
  Families
  FunctionProperties
  FunctionPropertiesEns
  InverseImage
  Powerset_facts
  Proj1SigInjective
  ReverseMath.AddSubtract.
From Coq Require Import
  RelationClasses.

Definition eq_cardinal_ens {A B : Type}
  (U : Ensemble A) (V : Ensemble B) : Prop :=
  ((B -> False) /\ forall a : A, ~ In U a) \/
  exists f : A -> B,
    range f U V /\ bijective_ens f U V.
Definition le_cardinal_ens {A B : Type}
  (U : Ensemble A) (V : Ensemble B) : Prop :=
  ((B -> False) /\ forall a : A, ~ In U a) \/
    exists f : A -> B,
      range f U V /\ injective_ens f U.
Definition lt_cardinal_ens {A B : Type}
  (U : Ensemble A) (V : Ensemble B) : Prop :=
  le_cardinal_ens U V /\
    ~ eq_cardinal_ens V U.
Definition ge_cardinal_ens {A B : Type}
  (U : Ensemble A) (V : Ensemble B) : Prop :=
  (forall b : B, ~ In V b) \/
    exists f : A -> B,
      range f U V /\ surjective_ens f U V.

#[export]
Instance eq_cardinal_ens_Reflexive (A : Type) :
  Reflexive (@eq_cardinal_ens A A).
Proof.
  right.
  exists id. split; auto.
  - reflexivity.
  - apply bijective_ens_id.
Qed.

Lemma eq_cardinal_ens_sym_dec {A B : Type}
  (HA : inhabited A \/ ~ inhabited A)
  (U : Ensemble A) (V : Ensemble B)
  (HVdec : forall b : B, In V b \/ ~ In V b) :
  eq_cardinal_ens U V ->
  eq_cardinal_ens V U.
Proof.
  intros [[H0 H1]|[f [Hf0 Hf1]]].
  - right.
    exists (fun b : B =>
         False_rect A (H0 b)).
    split; [|split]; intros ? ?; try contradiction.
    firstorder.
  - destruct HA.
    2: {
      left. split.
      { intros a; apply H; constructor; auto. }
      intros b Hb.
      destruct Hf1 as [_ Hf1].
      specialize (Hf1 b Hb) as [a [Ha0 Ha1]].
      apply H. constructor; auto.
    }
    right.
    destruct H as [a0].
    pose proof (bijective_impl_invertible_ens_dec
                  f U V a0 HVdec Hf0 Hf1) as [g Hfg].
    exists g. split.
    + apply (inverse_map_ens_surjective_ens_range f); auto.
      apply Hf1.
    + apply (inverse_map_ens_range_bijective_ens f); auto.
Qed.

Lemma eq_cardinal_ens_sym {A B : Type}
  (U : Ensemble A) (V : Ensemble B) :
  eq_cardinal_ens U V ->
  eq_cardinal_ens V U.
Proof.
  apply eq_cardinal_ens_sym_dec.
  - apply classic.
  - intros ?. apply classic.
Qed.

Lemma eq_cardinal_ens_trans {A B C : Type}
  (U : Ensemble A) (V : Ensemble B) (W : Ensemble C) :
  eq_cardinal_ens U V -> eq_cardinal_ens V W ->
  eq_cardinal_ens U W.
Proof.
  intros [[H0 H1]|[f [Hf0 Hf1]]].
  { intros [[H2 H3]|[g [Hg0 Hg1]]].
    { left. split; auto. }
    destruct (classic (inhabited C)).
    2: now left; split; auto.
    right.
    destruct H as [c].
    exists (fun _ => c); split; [|split].
    - intros x Hx. specialize (H1 x Hx); contradiction.
    - intros ? ? Hx. specialize (H1 _ Hx); contradiction.
    - intros z Hz.
      destruct Hg1 as [Hg1 Hg2].
      specialize (Hg2 z Hz) as [b Hb].
      contradiction.
  }
  intros [[H0 H1]|[g [Hg0 Hg1]]].
  { left. split; auto.
    intros a Ha.
    apply (H1 (f a)).
    apply Hf0. assumption.
  }
  right. exists (compose g f).
  split.
  - eapply range_compose; eauto.
  - eapply bijective_ens_compose; eauto.
Qed.

Lemma eq_cardinal_ens_le {A B : Type}
  (U : Ensemble A) (V : Ensemble B) :
  eq_cardinal_ens U V ->
  le_cardinal_ens U V.
Proof.
  intros [H|[f [Hf0 [Hf1 _]]]].
  { left; auto. }
  right. exists f; split; auto.
Qed.

Section compose.
  Context {A B C : Type}
    (U : Ensemble A) (V : Ensemble B) (W : Ensemble C).

  Lemma le_cardinal_ens_transitive :
    le_cardinal_ens U V ->
    le_cardinal_ens V W ->
    le_cardinal_ens U W.
  Proof.
    intros HUV [[H0 H1]|[g [Hg0 Hg1]]].
    { left. split; auto.
      destruct HUV as [[H2 H3]|[f [Hf0 Hf1]]].
      { assumption. }
      intros a Ha.
      apply (H1 (f a)).
      apply (Hf0 a Ha).
    }
    destruct HUV as [[H0 H1]|[f [Hf0 Hf1]]].
    { destruct (classic (inhabited C)).
      - right.
        destruct H as [c0].
        exists (fun _ => c0). split.
        + intros a Ha. firstorder.
        + intros a0 a1 Ha0 Ha1; firstorder.
      - left. split; auto.
    }
    right. exists (compose g f).
    split.
    - eapply range_compose; eauto.
    - eapply injective_ens_compose; eauto.
  Qed.
End compose.

Lemma le_cardinal_ens_Proper_r {X Y Z : Type}
  (U : Ensemble X) (V : Ensemble Y) (W : Ensemble Z) :
  eq_cardinal_ens V W ->
  le_cardinal_ens U V -> le_cardinal_ens U W.
Proof.
  intros H0 H1.
  apply eq_cardinal_ens_le in H0.
  eapply le_cardinal_ens_transitive; eauto.
Qed.

Lemma le_cardinal_ens_Proper_l {X Y Z : Type}
  (U : Ensemble X) (V : Ensemble Y) (W : Ensemble Z) :
  eq_cardinal_ens U V ->
  le_cardinal_ens U W -> le_cardinal_ens V W.
Proof.
  intros H0 H1.
  apply eq_cardinal_ens_sym in H0.
  apply eq_cardinal_ens_le in H0.
  eapply le_cardinal_ens_transitive; eauto.
Qed.

Lemma le_cardinal_ens_Empty_set (X : Type) {Y : Type}
  (U : Ensemble Y) :
  le_cardinal_ens (@Empty_set X) U.
Proof.
  destruct (classic (inhabited Y)).
  - destruct H as [y].
    right. exists (fun _ => y).
    firstorder.
  - left. firstorder.
Qed.

Lemma eq_cardinal_ens_empty {X Y : Type} (U : Ensemble Y) :
  eq_cardinal_ens (@Empty_set X) U <->
    (forall y : Y, ~ In U y).
Proof.
  split.
  - intros [|[f [Hf0 [Hf1 Hf2]]]] y Hy.
    + tauto.
    + specialize (Hf2 y Hy) as [x [Hx Hxy]].
      contradiction.
  - intros HU.
    destruct (classic (inhabited Y)).
    2: {
      left; auto with sets.
    }
    right.
    destruct H as [y0].
    exists (fun _ => y0). split; firstorder.
Qed.

Lemma eq_cardinal_ens_Im_injective
  {X Y : Type} (U : Ensemble X) (f : X -> Y) :
  injective_ens f U ->
  eq_cardinal_ens U (Im U f).
Proof.
  intros Hf.
  right. exists f.
  split.
  - apply range_char_Im.
    reflexivity.
  - split.
    + assumption.
    + apply surjective_ens_Im.
Qed.

Lemma le_cardinal_ens_Im {X Y : Type} (f : X -> Y)
  (U : Ensemble X) :
  le_cardinal_ens (Im U f) U.
Proof.
  destruct (classic (Inhabited U)).
  2: {
    destruct (classic (inhabited X)).
    - destruct H0 as [x0].
      right. exists (fun _ => x0).
      split; intros ? **.
      + contradict H.
        inversion H0; subst; clear H0.
        firstorder.
      + contradict H.
        inversion H0; subst; clear H0.
        firstorder.
    - left; split; [firstorder|].
      intros y Hy.
      inversion Hy; subst; clear Hy.
      apply H; exists x. assumption.
  }
  destruct H as [x0 Hx0].
  pose proof
    (surjective_ens_right_inverse
       U (Im U f) f x0 Hx0) as [g [Hg0 Hg1]].
  { apply range_char_Im.
    reflexivity.
  }
  { apply surjective_ens_Im. }
  right. exists g; split; auto.
  intros y0 y1 Hy0 Hy1.
  pose proof (Hg1 y0 Hy0).
  pose proof (Hg1 y1 Hy1).
  congruence.
Qed.

Lemma eq_cardinal_ens_sig {X : Type} (P : X -> Prop) :
  eq_cardinal_ens (@Full_set (sig P)) P.
Proof.
  right.
  exists (@proj1_sig X P).
  split; [|split].
  - intros p _. apply proj2_sig.
  - intros p0 p1 _ _.
    destruct p0, p1.
    apply subset_eq_compat.
  - intros x Hx.
    exists (exist P x Hx).
    split; [constructor|reflexivity].
Qed.

Lemma le_cardinal_ens_Included {X : Type}
  (U V : Ensemble X) :
  Included U V ->
  le_cardinal_ens U V.
Proof.
  right. exists id. firstorder.
Qed.

Lemma le_cardinal_ens_surj {X Y : Type}
  (U : Ensemble X) (V : Ensemble Y) :
  le_cardinal_ens U V <->
    ge_cardinal_ens V U.
Proof.
  split.
  - intros [[H0 H1]|[f [Hf0 Hf1]]].
    { right. exists (fun y : Y => False_rect X (H0 y)).
      split; intros ? ?; firstorder; try contradiction.
    }
    destruct (classic (Inhabited U)).
    2: {
      left. firstorder.
    }
    destruct H as [x0 Hx0].
    right.
    pose proof (injective_ens_left_inverse U V f x0
                  Hx0 Hf0 Hf1) as [g [Hg0 Hg1]].
    exists g; split; auto.
    intros x Hx.
    exists (f x). split; auto.
    symmetry. apply Hg1.
    assumption.
  - intros [H|[f [Hf0 Hf1]]].
    { destruct (classic (inhabited Y)).
      { destruct H0 as [y].
        right. exists (fun _ => y).
        split; intros ? ?; firstorder.
      }
      left. split; auto.
    }
    destruct (classic (Inhabited V)).
    2: {
      destruct (classic (inhabited Y)).
      { destruct H0 as [y0].
        right. exists (fun _ => y0).
        firstorder.
      }
      left. firstorder.
    }
    destruct H as [y Hy].
    pose proof (surjective_ens_right_inverse V U f y Hy Hf0 Hf1)
      as [g [Hg0 Hg1]].
    right. exists g; split; auto.
    intros x0 x1 Hx0 Hx1 Hx.
    pose proof (Hg1 x0 Hx0).
    pose proof (Hg1 x1 Hx1).
    congruence.
Qed.

Lemma le_cardinal_ens_sig_injective
  {X Y : Type} (U : Ensemble X) (V : Ensemble Y)
  (f : sig U -> sig V) :
  injective f -> le_cardinal_ens U V.
Proof.
  destruct (classic (inhabited Y)).
  2: {
    left. split; auto.
    intros x Hx.
    contradict H.
    constructor.
    apply (proj1_sig (f (exist U x Hx))).
  }
  destruct H as [y0].
  right.
  exists (sig_fn_extend (compose (@proj1_sig Y V) f) y0).
  split.
  - apply sig_fn_extend_range.
    intros [x Hx] _.
    apply (proj2_sig (f (exist U x Hx))).
  - apply sig_fn_extend_injective_ens.
    apply injective_compose; auto.
    intros ? ?. apply proj1_sig_injective.
Qed.

(** for each point in [U] at most one point lands in [inverse_image f U] *)
Lemma inverse_image_injective_cardinal_le
  {X Y : Type} (f : X -> Y) (U : Ensemble Y) :
  injective f ->
  le_cardinal_ens (inverse_image f U) U.
Proof.
  intros Hf.
  right. exists f.
  split.
  - apply range_char_inverse_image.
    reflexivity.
  - apply injective_injective_ens, Hf.
Qed.

From Coq Require Import
  Classical
  Lia.
From Coq Require Export
  Finite_sets
  Finite_sets_facts.
From ZornsLemma Require Import
  DecidableDec
  EnsemblesImplicit
  Families
  FiniteImplicit
  FunctionPropertiesEns
  Powerset_facts
  Image
  InverseImage
  ReverseMath.AddSubtract.

(** ** Properties of Finite ensembles *)
Lemma Finite_eqdec {X : Type} (U : Ensemble X) :
  Finite U ->
  forall x y : X, In U x -> In U y -> x = y \/ x <> y.
Proof.
  intros HU x y Hx Hy.
  induction HU.
  { contradiction. }
  destruct Hx, Hy; auto.
  all: repeat match goal with
         | H : In (Singleton _) _ |- _ =>
             apply Singleton_inv in H
         end.
  - right. intros ?; subst; auto.
  - right. intros ?; subst; auto.
  - left. subst. auto.
Qed.

Lemma Finite_Included_In_dec {X : Type} (U V : Ensemble X) :
  Included U V -> Finite U -> Finite V ->
  forall x : X, In V x -> In U x \/ ~ In U x.
Proof.
  intros HUV HU HV.
  pose proof (Finite_eqdec V HV) as HVdec.
  induction HU.
  { intros ?. right. intros ?. contradiction. }
  intros x0 Hx0.
  specialize (HVdec x x0) as [Hxx|Hxx]; auto.
  { apply HUV. right. constructor. }
  { left. right. apply Singleton_intro. assumption. }
  unshelve epose proof (IHHU _ x0 Hx0) as [Hx1|Hx1].
  { intros ? ?; apply HUV; left; auto. }
  - left. left. assumption.
  - right. intros Hx2. inversion Hx2; subst; clear Hx2;
      try contradiction. inversion H0; subst; clear H0; contradiction.
Qed.

Lemma Finite_downward_closed_dec {X : Type}
  (V : Ensemble X)
  (HV : Finite V)
  (U : Ensemble X)
  (HUdec : forall x : X, In V x -> In U x \/ ~ In U x)
  (HUeq : forall x y : X, In U x -> In U y -> x = y \/ x <> y)
  (HUV: Included U V) : Finite U.
Proof.
  revert U HUdec HUeq HUV.
  induction HV; intros U HUdec HUeq HUV.
  { replace U with (@Empty_set X).
    { constructor. }
    apply Extensionality_Ensembles; split; auto.
    intros ? ?; contradiction.
  }
  destruct (HUdec x) as [Hx|Hx].
  { right. constructor. }
  2: {
    apply IHHV; auto.
    - intros y Hy. apply HUdec.
      left. assumption.
    - intros y Hy.
      specialize (HUV y Hy).
      destruct HUV; auto.
      destruct H0. contradiction.
  }
  replace U with (Add (Subtract U x) x).
  2: {
    symmetry.
    apply Extensionality_Ensembles.
    (* here we use [HUeq] *)
    apply Add_Subtract_discouraging.
    split; auto.
  }
  constructor.
  2: apply Subtract_not_in.
  apply IHHV.
  - intros y Hy.
    destruct (HUdec y) as [Hy0|Hy0].
    { left. assumption. }
    2: {
      right. intros [Hy1 Hy2].
      auto.
    }
    destruct (HUeq x y Hx Hy0) as [Hxy|Hxy].
    + right. subst. apply Subtract_not_in.
    + left. split; auto.
      intros Hxy0. apply Singleton_inv in Hxy0.
      auto.
  - intros y0 y1 Hy0 Hy1.
    apply HUeq.
    + apply Hy0.
    + apply Hy1.
  - intros y Hy.
    destruct Hy as [Hy0 Hy1].
    apply HUV in Hy0.
    destruct Hy0 as [y Hy0|y Hy0];
      auto.
    contradiction.
Qed.

(** This shows that [Finite] needs classical logic to be closed under
  [Included]. *)
Theorem Finite_downward_closed_discouraging
  {X : Type} (U V : Ensemble X) :
  Finite V -> Included U V ->
  Finite U <->
    (forall x : X, In V x -> In U x \/ ~ In U x) /\
      (forall x y : X, In U x -> In U y -> x = y \/ x <> y).
Proof.
  intros HV HUV. split.
  - intros HU. split.
    + apply Finite_Included_In_dec; assumption.
    + apply Finite_eqdec; assumption.
  - intros [HU0 HU1].
    apply Finite_downward_closed_dec with V; assumption.
Qed.

(* This is like a choice property for finite sets. And [P] is about pairs, so
   that's the meaning of the name. It is similar to
   [FiniteTypes.finite_choice]. *)
Lemma finite_ens_pair_choice {X Y : Type} (U : Ensemble X)
      (P : X -> Y -> Prop) :
  Finite U ->
  (forall x, In U x -> exists y, P x y) ->
  exists V : Ensemble Y,
    Finite V /\
      (forall x, In U x -> exists y, In V y /\ P x y) /\
      (forall y, In V y -> exists x, In U x /\ P x y).
Proof.
  intros U_fin U_ex.
  induction U_fin as [|U ? ? x].
  { (* U = Empty_set *)
    exists Empty_set. repeat split;
      intros; try contradiction.
    constructor.
  }
  (* U = Add _ _ *)
  specialize IHU_fin as [V0 [H0 [H1 H2]]].
  { intros. apply U_ex. left. assumption. }
  specialize (U_ex x) as [y].
  { right. reflexivity. }
  destruct (classic (In V0 y)).
  - (* In V0 y *)
    exists V0. repeat split; intros; auto.
    + destruct H5.
      { apply H1; auto. }
      exists y. inversion H5; subst; clear H5.
      auto.
    + destruct (H2 y0 H5) as [x0 []];
        exists x0; split; auto with sets.
  - (* ~ In V0 y *)
    exists (Add V0 y). repeat split; intros; auto.
    + constructor; auto.
    + destruct H5 as [x0|x0].
      * destruct (H1 x0 H5) as [y0 []].
        exists y0; split; auto with sets.
      * inversion H5; subst; clear H5.
        exists y; auto with sets.
    + destruct H5 as [y0|y0].
      * destruct (H2 y0 H5) as [x0 []].
        exists x0; split; auto with sets.
      * inversion H5; subst; clear H5.
        exists x; auto with sets.
Qed.

(** ** Constructing finite ensembles *)
Lemma finite_couple {X} (x y : X) :
  Finite (Couple x y).
Proof.
  rewrite <- Couple_as_union.
  apply Union_preserves_Finite.
  all: apply Singleton_is_finite.
Qed.

(* note that the converse direction is not true.
   Consider for example the intersection of the
   open intervals [ (0, 1/n) ], which is empty and thus finite.
   If you like, a non-empty intersection is achieved by
   intersecting the intervals [ [0, 1/n) ].
 *)
Lemma FamilyIntersection_Finite (X : Type) (F : Family X) :
  (exists U, In F U /\ Finite U) ->
  Finite (FamilyIntersection F).
Proof.
  intros.
  destruct H as [U [? ?]].
  apply Finite_downward_closed with U; auto.
  red; intros.
  destruct H1. apply H1. assumption.
Qed.

(** ** Finite and functions *)
Lemma Finite_injective_image_dec {X Y : Type} (f : X -> Y)
  (U : Ensemble X)
  (HUdec : forall x y : X, In U x -> In U y -> x = y \/ x <> y) :
  injective_ens f U -> Finite (Im U f) -> Finite U.
Proof.
  intros Hf Himg.
  remember (Im U f) as V.
  revert U Hf HUdec HeqV.
  induction Himg as [|? ? ? y HAy].
  { intros U Hf HUdec HeqV.
    replace U with (@Empty_set X).
    { constructor. }
    apply Extensionality_Ensembles; split.
    1: intros ? ?; contradiction.
    intros x Hx.
    apply (Im_def U f) in Hx.
    rewrite <- HeqV in Hx.
    contradiction.
  }
  intros U Hf HUdec HeqV.
  assert (exists x, In U x /\ f x = y) as [x [Hx Hxy]].
  { apply Im_inv. rewrite <- HeqV. right. constructor. }
  subst.
  replace U with (Add (Subtract U x) x).
  2: {
    symmetry.
    apply Extensionality_Ensembles.
    (* here we use [HUdec] *)
    apply Add_Subtract_discouraging.
    split; auto.
  }
  constructor.
  2: apply Subtract_not_in.
  apply IHHimg.
  { intros x0 x1 Hx0 Hx1 Hxx.
    destruct Hx0, Hx1.
    apply Hf; assumption.
  }
  { intros x0 x1 Hx0 Hx1.
    destruct Hx0, Hx1.
    apply HUdec; assumption.
  }
  apply Extensionality_Ensembles; split.
  - intros y Hy.
    pose proof (Add_intro1 _ A (f x) y Hy) as Hy0.
    rewrite HeqV in Hy0.
    destruct Hy0 as [x0 Hx0 y Hy0].
    subst. apply Im_def.
    split; auto. intros ?.
    destruct H. auto.
  - intros y Hy.
    destruct Hy as [x0 Hx0 y Hy].
    subst. destruct Hx0.
    pose proof (Im_def _ f x0 H).
    rewrite <- HeqV in H1.
    inversion H1; subst; clear H1; auto.
    inversion H2; subst; clear H2.
    (* here we use injectivity of [f] *)
    apply Hf in H3; auto.
    subst. contradict H0; constructor.
Qed.

Lemma Finite_injective_image {X Y : Type} (f : X -> Y)
  (U : Ensemble X) :
  injective_ens f U -> Finite (Im U f) -> Finite U.
Proof.
  intros Hf Himg.
  apply Finite_injective_image_dec with f; auto.
  intros ? ? ? ?.
  apply classic.
Qed.

(** ** Finite subsets of [nat] *)
Lemma finite_nat_initial_segment_ens (n : nat) :
  Finite (fun m => m < n).
Proof.
  induction n.
  { replace (fun _ => _) with (@Empty_set nat).
    { constructor. }
    apply Extensionality_Ensembles; split; auto with sets.
    intros x Hx. red in Hx. inversion Hx.
  }
  replace (fun _ => _) with (Add (fun m => m < n) n).
  { constructor; auto.
    intros ?. red in H. lia.
  }
  clear IHn.
  apply Extensionality_Ensembles; split; intros m Hm.
  - inversion Hm; subst; clear Hm.
    + cbv in *. lia.
    + inversion H; subst; clear H.
      constructor.
  - cbv in *.
    apply le_S_n in Hm.
    destruct Hm.
    + right. constructor.
    + left. cbv.
      apply le_n_S.
      assumption.
Qed.

Lemma nat_Finite_impl_bounded (U : Ensemble nat) :
  Finite U ->
  (exists n : nat, forall m, In U m -> m < n).
Proof.
  intros HU.
  induction HU.
  { exists 0. intros ? ?. contradiction. }
  destruct IHHU as [n0 Hn0].
  exists (max n0 (S x)).
  intros m Hm.
  destruct Hm.
  - specialize (Hn0 x0 H0).
    lia.
  - destruct H0.
    lia.
Qed.

Lemma Finite_nat_bounded_dec (U : Ensemble nat)
  (HUdec : forall n : nat, In U n \/ ~ In U n) :
  (exists n : nat, forall m, In U m -> m < n) ->
  Finite U.
Proof.
  intros [n Hn].
  eapply Finite_downward_closed_dec.
  - apply (finite_nat_initial_segment_ens n).
  - auto.
  - intros ? ? ? ?.
    destruct (PeanoNat.Nat.eq_dec x y); [left|right]; auto.
  - now intros m Hm; red; auto.
Qed.

Corollary nat_Finite_bounded_char (U : Ensemble nat) :
  Finite U <-> exists n : nat, forall m, In U m -> m < n.
Proof.
  split.
  1: apply nat_Finite_impl_bounded.
  apply Finite_nat_bounded_dec.
  intros ?. apply classic.
Qed.

Lemma injective_finite_inverse_image_Singleton
  {X Y : Type} (f : X -> Y) (y : Y) :
  injective f ->
  Finite (inverse_image f (Singleton y)).
Proof.
  intros Hf.
  destruct (classic (exists x : X, f x = y)) as [H|H].
  - destruct H as [x Hx].
    subst.
    rewrite (proj1 (injective_inverse_image_Singleton f) Hf x).
    apply Singleton_is_finite.
  - replace (inverse_image _ _) with (@Empty_set X).
    { constructor. }
    apply Extensionality_Ensembles; split.
    { intros ? ?; contradiction. }
    intros x Hx.
    destruct Hx.
    contradict H.
    exists x. destruct H0.
    reflexivity.
Qed.

Lemma injective_finite_inverse_image
  {X Y : Type} (f : X -> Y) (U : Ensemble Y) :
  injective f ->
  Finite U ->
  Finite (inverse_image f U).
Proof.
  intros Hf HU.
  induction HU.
  { rewrite inverse_image_empty. constructor. }
  unfold Add.
  rewrite inverse_image_union.
  apply Union_preserves_Finite; auto.
  clear IHHU.
  apply injective_finite_inverse_image_Singleton.
  assumption.
Qed.

Corollary inverse_image_finite {X Y : Type} (f : X -> Y) (F : Family X) :
  surjective f ->
  Finite F ->
  Finite (inverse_image (inverse_image f) F).
Proof.
  intros Hf H.
  apply injective_finite_inverse_image; auto.
  apply inverse_image_surjective_injective.
  assumption.
Qed.

(** Instead of comparing cardinalities of elements of [Type],
    compare cardinalities of ensembles.
    With this technique, we can avoid problems w.r.t. type universes
    that occur with the approach of [ZornsLemma.Cardinals].
*)

From Coq Require Import
  ClassicalChoice
  Description
  Program.Subset.
From ZornsLemma Require Import
  Cardinals
  CountableTypes
  CSB
  FunctionPropertiesEns
  Powerset_facts
  Proj1SigInjective.
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

Instance eq_cardinal_ens_Reflexive (A : Type) :
  Reflexive (@eq_cardinal_ens A A).
Proof.
  right.
  exists id. split; auto.
  - reflexivity.
  - apply bijective_ens_id.
Qed.

Lemma eq_cardinal_ens_sym {A B : Type}
  (U : Ensemble A) (V : Ensemble B) :
  eq_cardinal_ens U V ->
  eq_cardinal_ens V U.
Proof.
  intros [[H0 H1]|[f [Hf0 Hf1]]].
  - right.
    exists (fun b : B =>
         False_rect A (H0 b)).
    split; [|split]; intros ? ?; try contradiction.
    firstorder.
  - destruct (classic (inhabited A)).
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
    pose proof (bijective_ens_impl_invertible_ens
                  f U V a0 Hf0 Hf1) as [g Hfg].
    exists g. split.
    + apply (inverse_pair_ens_surjective_ens_range f); auto.
      apply Hf1.
    + apply (inverse_pair_ens_range_bijective_ens f); auto.
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

Theorem CSB_ens {X Y : Type}
  (U : Ensemble X) (V : Ensemble Y)
  (f : X -> Y) (g : Y -> X) :
  range f U V ->
  range g V U ->
  injective_ens f U ->
  injective_ens g V ->
  exists h : X -> Y,
    range h U V /\
      bijective_ens h U V.
Proof.
  intros.
  assert (exists h0 : sig U -> sig V, bijective h0)
    as [h0 Hh].
  { apply CSB with (f := range_restr f U V H)
                   (g := range_restr g V U H0);
      apply injective_ens_char; assumption.
  }
  destruct (classic (inhabited Y)).
  2: {
    assert (X -> False) as HX.
    { intros x.
      apply H3. constructor.
      apply (f x).
    }
    exists (fun x => False_rect Y (HX x)).
    repeat split; intros ? ?; try contradiction.
    contradict H3; constructor; auto.
  }
  clear f g H H0 H1 H2.
  destruct H3 as [y0].
  exists (sig_fn_extend (compose (@proj1_sig Y V) h0) y0).
  assert (range (compose (proj1_sig (P:=V)) h0)
                Full_set V).
  { apply (range_compose _ Full_set).
    - apply range_full.
    - intros ? _. apply proj2_sig.
  }
  split; [|split].
  - apply sig_fn_extend_range; assumption.
  - apply sig_fn_extend_injective_ens.
    apply injective_compose.
    + apply Hh.
    + intros ? ?. apply proj1_sig_injective.
  - apply sig_fn_extend_surjective_ens.
    intros y Hy.
    destruct Hh as [_ Hh].
    specialize (Hh (exist V y Hy)) as [[x Hx0] Hx1].
    exists (exist U x Hx0); split; [constructor|].
    unfold compose. rewrite Hx1.
    reflexivity.
Qed.

Corollary le_cardinal_ens_antisymmetry
  {X Y : Type} (U : Ensemble X) (V : Ensemble Y) :
  le_cardinal_ens U V ->
  le_cardinal_ens V U ->
  eq_cardinal_ens U V.
Proof.
  intros [H|[f [Hf0 Hf1]]].
  { left. assumption. }
  intros [H|[g [Hg0 Hg1]]].
  { apply eq_cardinal_ens_sym.
    left. assumption.
  }
  right.
  apply (CSB_ens _ _ f g); assumption.
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

Theorem le_cardinal_ens_total {X Y : Type} (U : Ensemble X) (V : Ensemble Y) :
  le_cardinal_ens U V \/ le_cardinal_ens V U.
Proof.
  destruct (types_comparable (sig U) (sig V)) as [[f Hf]|[f Hf]];
    [left|right].
  - eapply le_cardinal_ens_sig_injective; eauto.
  - eapply le_cardinal_ens_sig_injective; eauto.
Qed.

Lemma Countable_as_le_cardinal_ens {X : Type} (U : Ensemble X) :
  Countable U <-> le_cardinal_ens U (@Full_set nat).
Proof.
  split.
  - intros [f Hf].
    pose proof (eq_cardinal_ens_sig U).
    eapply le_cardinal_ens_Proper_l; eauto.
    right. exists f. split; [|firstorder].
    intros ? ?. constructor.
  - intros [[]|[f [_ Hf]]].
    { contradict (H 0). }
    exists (fun p => f (proj1_sig p)).
    intros [x0 H0] [x1 H1] Hx.
    simpl in Hx.
    specialize (Hf x0 x1 H0 H1 Hx).
    apply subset_eq_compat.
    assumption.
Qed.

(** ** Definitions concerning least cardinals *)

(** [U] is an element of [P] with minimal cardinality,
    where [P : Family X] *)
Definition least_cardinal_subset
  {X : Type} (P : Family X) (U : Ensemble X) : Prop :=
  In P U /\
    forall V : Ensemble X,
      In P V -> le_cardinal_ens U V.

(** [U] is an element of [P] with minimal cardinality,
    where [P] is a collection of arbitrary ensembles. *)
Definition least_cardinal
  (P : forall {X : Type} (U : Ensemble X), Prop)
  {X : Type} (U : Ensemble X) : Prop :=
  P U /\
    (forall (Y : Type) (V : Ensemble Y),
        P V -> le_cardinal_ens U V).

Definition least_cardinal_ext
  {X : Type} (P : Family X) {Y : Type} (V : Ensemble Y) :=
  least_cardinal
    (fun Z W =>
       exists U : Ensemble X,
         In P U /\ eq_cardinal_ens U W) V.

Lemma least_cardinal_ext_subset
  {X : Type} (P : Family X) (U : Ensemble X) :
  least_cardinal_subset P U ->
  least_cardinal_ext P U.
Proof.
  intros [HU0 HU1].
  split.
  - exists U; split; auto. reflexivity.
  - intros Y V [U' [HU'0 HU'1]].
    specialize (HU1 U' HU'0).
    eapply le_cardinal_ens_Proper_r; eauto.
Qed.

Lemma least_cardinal_ext_to_subset
  {X : Type} (P : Family X) {Y : Type} (V : Ensemble Y) :
  least_cardinal_ext P V ->
  exists U : Ensemble X,
    least_cardinal_subset P U /\ eq_cardinal_ens U V.
Proof.
  intros [[U [HU0 HU1]] HV1].
  exists U. split; auto.
  split; auto.
  intros W HW.
  apply eq_cardinal_ens_sym in HU1.
  eapply le_cardinal_ens_Proper_l; eauto.
  apply HV1. exists W; split; auto.
  reflexivity.
Qed.

Lemma least_cardinal_unique P {X : Type} (U : Ensemble X)
  {Y : Type} (V : Ensemble Y) :
  least_cardinal P U ->
  least_cardinal P V ->
  eq_cardinal_ens U V.
Proof.
  intros [HU0 HU1] [HV0 HV1].
  specialize (HU1 Y V HV0).
  specialize (HV1 X U HU0).
  apply le_cardinal_ens_antisymmetry;
    assumption.
Qed.

Lemma le_cardinal_ens_wf {X : Type} (F : Family X) :
  Inhabited F ->
  exists U, least_cardinal_subset F U.
Proof.
Admitted.

Corollary least_cardinal_ext_exists {X : Type} (F : Family X) :
  Inhabited F ->
  exists U : Ensemble X, least_cardinal_ext F U.
Proof.
  intros HF.
  destruct (le_cardinal_ens_wf F HF) as [U HU].
  exists U.
  apply least_cardinal_ext_subset.
  assumption.
Qed.

Lemma least_cardinal_exists
  (P : forall {X : Type} (U : Ensemble X), Prop) {X : Type} (U : Ensemble X) :
  P U -> exists (Y : Type) (V : Ensemble Y), least_cardinal (@P) V.
Proof.
  intros HU.
  pose (F := fun V : Ensemble X =>
               exists (Y : Type) (W : Ensemble Y),
                 P Y W /\ eq_cardinal_ens V W).
  assert (F U) as HU0.
  { exists X, U; split; auto; reflexivity. }
  (* every ensemble that satisfies [P] has a representative of the
     possibly smaller cardinality in [X]. *)
  assert (forall {Y : Type} (W : Ensemble Y),
             P Y W -> exists (V : Ensemble X),
               F V /\ le_cardinal_ens V W) as HFmin.
  { intros Y W HW.
    destruct (le_cardinal_ens_total U W).
    { exists U; auto. }
    destruct H as [[]|].
    { exists Empty_set. split.
      - exists Y, W. split; auto.
        apply eq_cardinal_ens_empty.
        apply H0.
      - apply le_cardinal_ens_Empty_set.
    }
    destruct H as [f [Hf0 Hf1]].
    exists (Im W f). split.
    - exists Y, W. split; auto.
      apply eq_cardinal_ens_sym.
      apply eq_cardinal_ens_Im_injective.
      assumption.
    - apply eq_cardinal_ens_le.
      apply eq_cardinal_ens_sym.
      apply eq_cardinal_ens_Im_injective.
      assumption.
  }
  destruct (le_cardinal_ens_wf F) as [V [[Y [W [HV0 HV1]]] HV2]].
  { exists U. assumption. }
  exists Y, W. split; auto.
  intros Z Q HQ.
  eapply le_cardinal_ens_Proper_l; eauto.
  specialize (HFmin Z Q HQ) as [R [HR0 HR1]].
  specialize (HV2 R HR0).
  eapply le_cardinal_ens_transitive; eauto.
Qed.

(** ** Cantor *)
Lemma Prop_contradiction_neq (P Q : Prop) (HP : P) :
  ~ (P /\ Q) ->
  P <> Q.
Proof.
  intros ? ?. subst.
  tauto.
Qed.

(* in analogy to [Cardinals.cantor_diag2] *)
Lemma cantor_diag2 {X : Type} (U : Ensemble X)
  (f : X -> (Ensemble X)) :
  ~ surjective_ens f U (fun V : Ensemble X => Included V U).
Proof.
  intros Hf.
  pose (g := (fun x : X => In U x /\ ~ In (f x) x) : Ensemble X).
  pose proof (Hf g) as [x [Hx Hxg]].
  { intros x [Hx _]. apply Hx. }
  assert (f x x = g x).
  { rewrite Hxg. reflexivity. }
  unfold g in H.
  unfold In in H.
  destruct (classic (f x x)).
  - apply (Prop_contradiction_neq
             (f x x) (U x /\ ~ f x x)); tauto.
  - apply (Prop_contradiction_neq
             (U x /\ ~ f x x) (f x x)); try tauto.
    congruence.
Qed.

Lemma cardinals_unbounded {X : Type} (U : Ensemble X) :
  lt_cardinal_ens
    U (fun V : Ensemble X => Included V U).
Proof.
  split.
  - right. exists Singleton. split.
    + intros x Hx y Hy.
      inversion Hy; subst; clear Hy.
      assumption.
    + intros x0 x1 Hx0 Hx1 Hx.
      apply Singleton_injective in Hx.
      assumption.
  - intros H.
    apply eq_cardinal_ens_sym in H.
    destruct H as [[H _]|[f Hf]].
    + apply (H Empty_set).
    + destruct Hf as [Hf0 [Hf1 Hf2]].
      apply (cantor_diag2 U f).
      assumption.
Qed.

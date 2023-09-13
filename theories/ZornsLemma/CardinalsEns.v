(** Instead of comparing cardinalities of elements of [Type],
    compare cardinalities of ensembles.
    With this technique, we can avoid problems w.r.t. type universes
    that occur with the approach of [ZornsLemma.Cardinals].

    On the other hand, we need classical logic more often, because a
    statement like [eq_cardinal_ens] decides whether the ensemble and
    a type are inhabited or not.

    Similarly, we can not define [eq_cardinal_ens] via
    [inverse_pair_ens], because that leads to a notion incompatible
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
  Cardinals
  CountableTypes
  CSB
  DecidableDec
  Finite_sets
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
    + apply (inverse_pair_ens_surjective_ens_range f); auto.
      apply Hf1.
    + apply (inverse_pair_ens_range_bijective_ens f); auto.
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

Lemma le_lt_cardinal_ens_transitive {X Y Z : Type}
  (U : Ensemble X) (V : Ensemble Y) (W : Ensemble Z) :
  le_cardinal_ens U V ->
  lt_cardinal_ens V W ->
  lt_cardinal_ens U W.
Proof.
  intros HUV [HVW HVWn].
  split.
  { eapply le_cardinal_ens_transitive; eauto. }
  intros Heq.
  contradict HVWn.
  apply eq_cardinal_ens_sym in Heq.
  apply le_cardinal_ens_antisymmetry; auto.
  eapply le_cardinal_ens_Proper_l; eauto.
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

Lemma nat_minimal_element_property_dec
  (U : Ensemble nat) (HUdec : forall n : nat, In U n \/ ~ In U n)
  (HUinh : Inhabited U) :
  exists m : nat, In U m /\ forall n : nat, In U n -> m <= n.
Proof.
  destruct HUinh as [N HN].
  revert U HUdec HN.
  induction N.
  { intros.
    exists 0. split; auto. lia.
  }
  intros U HUdec HN.
  destruct (HUdec 0) as [HU0|HU0].
  { exists 0. split; auto. lia. }
  specialize (IHN (compose U S)) as [m [Hm0 Hm1]];
    auto.
  { intros ?. apply HUdec. }
  destruct (HUdec m) as [HUm|HUm].
  { exists m; split; auto; intros n Hn.
    destruct n; try contradiction.
    apply Hm1 in Hn. lia.
  }
  exists (S m). split; auto.
  intros n Hn.
  destruct n; try contradiction.
  apply le_n_S.
  apply Hm1.
  assumption.
Qed.

Lemma nat_bounded_ens_has_max_dec
  (U : Ensemble nat)
  (HUdec : forall n : nat, In U n \/ ~ In U n)
  (N : nat) :
  (forall n : nat, In U n -> n < N) ->
  Inhabited U ->
  exists n : nat, In U n /\
             forall m : nat, In U m -> m <= n.
Proof.
  intros HN HU.
  induction N.
  { destruct HU as [u Hu].
    specialize (HN u Hu). lia.
  }
  clear HU.
  specialize (HUdec N) as [HN0|HN0].
  - exists N; split; auto.
    intros m Hm. specialize (HN m Hm).
    lia.
  - apply IHN.
    intros n Hn.
    specialize (HN n Hn).
    assert (n <> N).
    { intros ?; congruence. }
    lia.
Qed.

(** if a set [U] has an element [o] and an injective function [succ]
  (possibly defined on a larger set than [U]) such that
  [o] is not in the image of [succ], and
  [U] satisfies an induction principle, then [U] is countably infinite *)
Lemma peano_ensemble_countably_infinite {X : Type}
  (U : Ensemble X) (o : X) (succ : X -> X) :
  In U o ->
  (forall x : X, In U x -> In U (succ x)) ->
  injective_ens succ U ->
  (forall x : X, In U x -> o <> succ x) ->
  (forall P : Ensemble X,
      P o ->
      (forall x, In U x -> P x -> P (succ x)) ->
      forall x, In U x -> P x) ->
  eq_cardinal_ens (@Full_set nat) U.
Proof.
  intros HUo HUsucc Hsucc_inj Hsucc_o HUind.
  right.
  pose (g := fix g (n : nat) : { n : X | In U n } :=
       match n with
       | O => exist U o HUo
       | S n => exist U (succ (proj1_sig (g n)))
                 (HUsucc (proj1_sig (g n)) (proj2_sig (g n)))
       end).
  exists (fun n => proj1_sig (g n)).
  split; [|split].
  - intros x Hx.
    clear Hx.
    induction x.
    { simpl. assumption. }
    simpl. apply HUsucc, IHx.
  - intros x0 x1 Hx0 Hx1 Hx.
    clear Hx0 Hx1.
    revert x1 Hx.
    induction x0; intros x1 Hx.
    { simpl in Hx.
      destruct x1.
      { reflexivity. }
      simpl in Hx.
      apply Hsucc_o in Hx; try contradiction.
      apply proj2_sig.
    }
    simpl in Hx.
    destruct x1.
    { simpl in Hx.
      symmetry in Hx.
      apply Hsucc_o in Hx; try contradiction.
      apply proj2_sig.
    }
    simpl in Hx.
    apply Hsucc_inj in Hx; try now apply proj2_sig.
    apply IHx0 in Hx. congruence.
  - red. apply HUind.
    + exists 0. split; constructor.
    + intros x Hx [y [Hy Hy0]].
      subst.
      exists (S y); split; [constructor|].
      simpl. reflexivity.
Qed.

Theorem nat_unbounded_impl_countably_infinite_dec
  (U : Ensemble nat) (HU : forall n : nat, exists m : nat, In U m /\ n < m)
  (HUdec : forall n : nat, In U n \/ ~ In U n) :
  eq_cardinal_ens U (@Full_set nat).
Proof.
  (* we use [nat_minimal_element_property_dec] to note that [U] is
     well-founded by [lt].
     Then show:
     Hu: the set [U] has a least element [u]
     Hf: the set [U] has a "successor" function [f]
     Hfu: [u] is not in the image of [f]
     Hf_inj: the function [f] is injective on [U]
     HU0: every element of [U] is either [u] or lies in the image of [f]

     Combine these in [peano_ensemble_countably_infinite]
     to obtain a bijection (even an order-isomorphism)
     between [U] and [Full_set].
   *)
  assert (exists u : nat, In U u /\ (forall n : nat, In U n -> u <= n)) as Hu.
  { specialize (HU 0) as [m [Hm0 Hm1]].
    apply nat_minimal_element_property_dec; auto.
    exists m. assumption.
  }
  assert (exists f : nat -> nat,
           (forall n : nat,
             In U n ->
             In U (f n)) /\
             (forall n : nat,
                 In U n ->
                 n < f n) /\
             (forall n : nat,
                 In U n ->
                 forall m : nat,
                   In U m ->
                   n < m -> f n <= m)) as Hf.
  { cut (forall n : nat,
            { fn : nat |
              (In U n ->
               In U fn /\ n < fn /\
                 forall m : nat, In U m -> n < m -> fn <= m) /\
                (~ In U n -> fn = 0) }).
    { intros F.
      exists (fun n => proj1_sig (F n)).
      repeat split; intros n Hn;
        pose proof (proj1 (proj2_sig (F n)) Hn) as [Hn0 [Hn1 Hn2]];
        auto.
    }
    intros n.
    apply constructive_definite_description.
    destruct (HUdec n) as [Hn0|Hn0].
    2: {
      exists 0. repeat split; try contradiction.
      intuition.
    }
    destruct
      (nat_minimal_element_property_dec
         (fun m => In U m /\ n < m)) as [k [[Hk0 Hk1] Hk2]].
    { unfold In.
      intros m.
      destruct (Nat.lt_ge_cases n m).
      2: {
        right. intros []. lia.
      }
      specialize (HUdec m) as [|].
      - left; tauto.
      - right; intros []; tauto.
    }
    { destruct (HU n) as [m Hm].
      exists m. assumption.
    }
    exists k. repeat split; try tauto.
    { firstorder. }
    intros l [Hl _].
    specialize (Hl Hn0) as [Hl0 [Hl1 Hl2]].
    specialize (Hk2 l (conj Hl0 Hl1)).
    specialize (Hl2 k Hk0 Hk1).
    lia.
  }
  destruct Hu as [u [Hu0 Hu1]].
  destruct Hf as [f [Hf0 [Hf1 Hf2]]].
  assert (forall x : nat, In U x -> u <> f x) as Hfu.
  { intros x Hx.
    specialize (Hu1 x Hx).
    specialize (Hf1 x Hx).
    lia.
  }
  (* show that [f] is injective on [U] *)
  assert (injective_ens f U) as Hf_inj.
  { intros x0 x1 Hx0 Hx1 Hx.
    destruct (Nat.lt_trichotomy x0 x1) as [Hxx|[Hxx|Hxx]]; auto.
    - specialize (Hf2 x0 Hx0 x1 Hx1 Hxx).
      specialize (Hf1 x1 Hx1). lia.
    - specialize (Hf2 x1 Hx1 x0 Hx0 Hxx).
      specialize (Hf1 x0 Hx0). lia.
  }
  assert (forall x : nat,
             In U x -> x = u \/ exists y : nat, In U y /\ x = f y) as HU0.
  { intros x Hx.
    destruct (Nat.eq_dec x u); auto.
    right.
    (* [y] must be the greatest element of [U] which satisfies [y < x]. *)
    unshelve epose proof (nat_bounded_ens_has_max_dec
                            (fun y => In U y /\ y < x) _ x)
      as [y Hy].
    - intros k. unfold In.
      destruct (Nat.lt_ge_cases k x).
      2: {
        right. intros []. lia.
      }
      specialize (HUdec k) as [|].
      + left; tauto.
      + right; intros []; tauto.
    - intros k [Hk0 Hk1]. auto.
    - exists u. split; auto.
      specialize (Hu1 x Hx). lia.
    - exists y. split; try apply Hy.
      destruct Hy as [[Hy0 Hy1] Hy2].
      unfold In at 1 in Hy2.
      apply Nat.le_antisymm.
      2: now apply Hf2; auto.
      apply Nat.nlt_ge.
      intros Hfy.
      specialize (Hy2 (f y) (conj (Hf0 y Hy0) Hfy)).
      specialize (Hf1 y Hy0).
      lia.
  }
  assert (forall P : (forall x : nat, Prop),
             P u ->
             (forall (x : nat) (Hx : In U x),
                 P x -> P (f x)) ->
             forall (x : nat), In U x -> P x) as HUind.
  { intros P HP0 HP1 x.
    apply (Wf_nat.lt_wf_rect x (fun x => In U x -> P x)).
    clear x.
    intros x Hind Hx.
    destruct (HU0 x Hx) as [Hx0|[y [Hy Hy0]]]; subst; auto.
  }
  apply eq_cardinal_ens_sym_dec.
  { left. constructor. apply 0. }
  { assumption. }
  apply peano_ensemble_countably_infinite with u f;
    auto.
Qed.

Lemma nat_unbounded_impl_countably_infinite
  (U : Ensemble nat) (HU : forall n : nat, exists m : nat, In U m /\ n < m) :
  eq_cardinal_ens U (@Full_set nat).
Proof.
  apply nat_unbounded_impl_countably_infinite_dec;
    auto.
  intros ?. apply classic.
Qed.

Lemma Finite_as_lt_cardinal_ens
  {X : Type} (U : Ensemble X) :
  Finite U <-> lt_cardinal_ens U (@Full_set nat).
Proof.
  split.
  - (* -> *)
    (* this proof directly constructs a function [X -> nat] using [classic_dec].
       Another proof would do induction over [Finite X] and construct the
       function [X -> nat] inductively *)
    intros HU.
    split.
    + apply Finite_ens_type in HU.
      apply FiniteT_nat_embeds in HU.
      destruct HU as [f Hf].
      right.
      exists (fun x : X =>
           match classic_dec (In U x) with
           | left Hx => f (exist U x Hx)
           | right _ => 0
           end).
      split.
      * apply range_full.
      * intros x0 x1 Hx0 Hx1.
        destruct (classic_dec _); try contradiction.
        destruct (classic_dec _); try contradiction.
        intros Hx.
        apply Hf in Hx.
        inversion Hx; subst; clear Hx.
        reflexivity.
    + intros [[_ H]|H].
      { exact (H 0 ltac:(constructor)). }
      destruct H as [f [Hf0 Hf1]].
      red in Hf0.
      apply InfiniteTypes.nat_infinite.
      apply Finite_ens_type in HU.
      pose (f0 := fun n : nat => exist U (f n) (Hf0 n ltac:(constructor))).
      assert (invertible f0).
      { apply bijective_impl_invertible.
        split.
        - intros n0 n1 Hn.
          inversion Hn; subst; clear Hn.
          apply Hf1 in H0; auto; constructor.
        - intros [x Hx].
          destruct Hf1 as [_ Hf1].
          specialize (Hf1 x Hx) as [n [_ Hn]].
          exists n. subst. unfold f0.
          apply subset_eq. reflexivity.
      }
      destruct H as [g Hg0 Hg1].
      eapply bij_finite with (f := g); eauto.
      eexists; eauto.
  - (* <- *)
    intros [[[H0 H1]|[f [Hf0 Hf1]]] H2].
    { specialize (H0 0). contradiction. }
    destruct (classic (exists n : nat, forall x : X, In U x -> f x < n)).
    2: {
      contradict H2.
      assert (eq_cardinal_ens (Im U f) (@Full_set nat)).
      { apply nat_unbounded_impl_countably_infinite.
        intros n. apply NNPP.
        intros Hn. contradict H.
        exists (S n). intros x Hx.
        apply NNPP. intros Hx0.
        contradict Hn. exists (f x).
        split.
        { apply Im_def; auto. }
        lia.
      }
      apply eq_cardinal_ens_Im_injective in Hf1.
      apply eq_cardinal_ens_sym.
      eapply eq_cardinal_ens_trans; eauto.
    }
    destruct H as [n Hn].
    (* [n] is an upper bound of the image of [U] under [f] *)
    assert (Finite (Im U f)).
    { apply nat_Finite_bounded_char.
      exists n. intros m Hm.
      destruct Hm as [x Hx m Hm]; subst.
      apply Hn; auto.
    }
    apply Finite_injective_image with f;
      auto.
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

Corollary injective_finite_inverse_image
  {X Y : Type} (f : X -> Y) (U : Ensemble Y) :
  injective f ->
  Finite U ->
  Finite (inverse_image f U).
Proof.
  intros Hf HU.
  apply Finite_as_lt_cardinal_ens.
  apply Finite_as_lt_cardinal_ens in HU.
  apply (inverse_image_injective_cardinal_le f U) in Hf.
  eapply le_lt_cardinal_ens_transitive; eauto.
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

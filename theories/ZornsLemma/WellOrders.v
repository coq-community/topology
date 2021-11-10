From Coq Require Export Relation_Definitions.
From Coq Require Import Classical Description
     FunctionalExtensionality Program.Subset.
From ZornsLemma Require Import Classical_Wf EnsemblesSpec
     Relation_Definitions_Implicit Image ZornsLemma.
From ZornsLemma Require Import StrictOrders WellOrders_new.

Section WellOrderMinimum.
Context {T:Type}.
Variable R:relation T.
Context `{well_ord : WellOrder T R}.

Definition WO_minimum:
  forall S:Ensemble T, Inhabited S ->
    { x:T | In S x /\ forall y:T, In S y -> y = x \/ R x y }.
refine (fun S H => constructive_definite_description _ _).
destruct (WF_implies_MEP T R wo_WF S H) as [x [Hx0 Hx1]].
exists x. split.
{ split; auto.
  intros.
  apply Hx1 in H0.
  apply Connected_Classical_le in H0; try tauto;
    typeclasses eauto.
}
intros y [Hy0 Hy1].
specialize (Hx1 y Hy0).
specialize (Hy1 x Hx0) as [|]; tauto.
Defined.

End WellOrderMinimum.

Section WellOrderConstruction.

Variable T:Type.

Record partial_WO : Type := {
  pwo_S: Ensemble T;
  pwo_R: relation T;
  pwo_R_lives_on_S: forall (x y:T), pwo_R x y -> In pwo_S x /\ In pwo_S y;
  pwo_wo:> WellOrder (rel_restriction pwo_R pwo_S);
}.

Instance pwo_trans (WO : partial_WO) :
  RelationClasses.Transitive (pwo_R WO).
Proof.
  intros x y z Hxy Hyz.
  pose proof (pwo_R_lives_on_S _ x y Hxy).
  pose proof (pwo_R_lives_on_S _ y z Hyz).
  unshelve eapply (@wo_trans _ _ (pwo_wo WO)
                     (exist _ x _) (exist _ y _) (exist _ z _));
    try tauto.
Qed.

(* the last condition below says that S WO1 is a downward closed
   subset of S WO2 *)
Record partial_WO_ord (WO1 WO2:partial_WO) : Prop := {
  pwo_S_incl: Included (pwo_S WO1) (pwo_S WO2);
  pwo_restriction: forall x y:T, In (pwo_S WO1) x -> In (pwo_S WO1) y ->
    (pwo_R WO1 x y <-> pwo_R WO2 x y);
  pwo_downward_closed: forall x y:T, In (pwo_S WO1) y -> In (pwo_S WO2) x ->
    pwo_R WO2 x y -> In (pwo_S WO1) x
}.

Lemma partial_WO_preord : preorder partial_WO_ord.
Proof.
constructor.
- unfold reflexive.
  intro.
  destruct x.
  constructor; simpl.
  + auto with sets.
  + split; trivial.
  + auto.
- unfold transitive.
  destruct x.
  destruct y.
  destruct z.
  intros.
  destruct H.
  destruct H0.
  simpl in *.
  constructor; simpl.
  + auto with sets.
  + intros.
    apply iff_trans with (pwo_R1 x y).
    * apply pwo_restriction0; auto with sets.
    * apply pwo_restriction1; auto with sets.
  + intros.
    apply pwo_downward_closed0 with y; trivial.
    * apply pwo_downward_closed1 with y; trivial.
      auto with sets.
    * apply <- (pwo_restriction1 x y); trivial.
      -- auto with sets.
      -- apply pwo_downward_closed1 with y; trivial.
         auto with sets.
Qed.

Section partial_WO_chain_ub.
  Variable (C : Ensemble partial_WO).
  Variable (H : chain partial_WO_ord C).

  Let US := fun x => exists WO, In C WO /\ In (pwo_S WO) x.
  Let UR := fun x y => exists WO, In C WO /\ pwo_R WO x y.

  Lemma partial_WO_chain_ub_WExt_Lemma :
    forall Wx Wy (x y : T) (Hx : In (pwo_S Wx) x) (Hy : In (pwo_S Wy) y)
      (HWW : partial_WO_ord Wx Wy) (HWx : In C Wx) (HWy : In C Wy)
      (Hsame :
        Same_set
          (initial_segment (rel_restriction UR US)
             (exist (fun x : T => In US x) x
                (ex_intro (fun WO : partial_WO => In C WO /\ In (pwo_S WO) x)
                   Wx (conj HWx Hx))))
          (initial_segment (rel_restriction UR US)
             (exist (fun x : T => In US x) y
                (ex_intro (fun WO : partial_WO => In C WO /\ In (pwo_S WO) y)
                   Wy (conj HWy Hy))))),
      x = y.
  Proof.
    intros Wx Wy x y Hx Hy HWW HWx HWy Hsame.
    unshelve epose proof (@wo_wext _ _ Wy (exist _ x _) (exist _ y _));
      simpl; try tauto.
    { apply HWW; tauto. }
    simpl in *.
    unshelve epose proof (H0 _) as Heq.
    2: {
      inversion Heq; subst; clear Heq.
      reflexivity.
    }
    clear H0.
    (* use [Hsame] to do this *)
    destruct Hsame as [Hsame0 Hsame1].
    split; red; intros.
    - unshelve epose proof (Hsame0 (exist _ (proj1_sig x0) _) _) as Hx0.
      { simpl. exists Wy. split; auto.
        apply (proj2_sig x0).
      }
      { lazy. exists Wy. split; auto. }
      clear Hsame0 Hsame1 H0.
      destruct Hx0 as [Wz [HWz HWx0]].
      (* which is greater? [Wy] or [Wz]? *)
      destruct (H Wy Wz HWy HWz) as [HWWW|HWWW].
      + apply HWWW; auto.
        apply (proj2_sig x0).
      + simpl in HWx0.
        pose proof (pwo_R_lives_on_S _ _ _ HWx0).
        rewrite (pwo_restriction _ _ HWWW) in HWx0;
          tauto.
    - unshelve epose proof (Hsame1 (exist _ (proj1_sig x0) _) _) as Hx0.
      { simpl. exists Wy. split; auto.
        apply (proj2_sig x0).
      }
      { lazy. exists Wy. split; auto. }
      clear Hsame0 Hsame1 H0.
      destruct Hx0 as [Wz [HWz HWx0]].
      (* which is greater? [Wy] or [Wz]? *)
      destruct (H Wy Wz HWy HWz) as [HWWW|HWWW].
      { simpl in HWx0.
        pose proof (pwo_R_lives_on_S _ _ _ HWx0).
        do 4 red. simpl.
        rewrite (pwo_restriction _ _ HWWW);
          try tauto.
        - apply (proj2_sig x0).
        - apply HWW. assumption.
      }
      simpl in HWx0.
      do 4 red. simpl.
      pose proof (pwo_R_lives_on_S _ _ _ HWx0).
      apply HWWW; auto; try tauto.
  Qed.

  Lemma partial_WO_chain_ub_WO : WellOrder (rel_restriction UR US).
  Proof.
    constructor.
    - (** well-founded *)
      assert (forall (WO:partial_WO) (x:{z:T | In (pwo_S WO) z}),
         In C WO -> In US (proj1_sig x)).
      { intros.
        exists WO.
        split.
        - assumption.
        - exact (proj2_sig x).
      }
      assert (forall (WO:partial_WO) (iC:In C WO) (x:{z:T | In (pwo_S WO) z}),
        Acc (rel_restriction (pwo_R WO) (pwo_S WO)) x ->
        Acc (rel_restriction UR US)
              (exist _ (proj1_sig x) (H0 WO x iC))).
      { intros WO ? x ?.
        induction H1.
        constructor.
        intros [y iy] ?.
        destruct x as [x ix].
        unfold rel_restriction in H3.
        simpl in H3.
        assert (In (pwo_S WO) y).
        { destruct H3 as [Wy [HWy Hy]].
          pose proof (pwo_R_lives_on_S Wy y x Hy) as [].
          destruct (H WO Wy iC HWy) as [HWOW|HWOW].
          - apply (pwo_downward_closed _ _ HWOW) with x;
              auto.
          - apply (pwo_S_incl _ _ HWOW).
            auto.
        }
        pose proof (H2 (exist (In (pwo_S WO)) y H4)).
        simpl in H5.
        assert (iy = H0 WO (exist (In (pwo_S WO)) y H4) iC).
        { apply proof_irrelevance. }
        subst.
        apply H5. clear H5.
        unfold rel_restriction.
        simpl.
        destruct H3.
        destruct H3.
        destruct (H WO x0 iC H3) as [HWW|HWW].
        - apply <- (pwo_restriction _ _ HWW); auto.
        - pose proof (pwo_R_lives_on_S x0 y x).
          apply -> (pwo_restriction _ _ HWW); tauto.
      }
      red. intro.
      destruct a.
      inversion i.
      destruct H2.
      pose proof (H1 x0 H2 (exist _ x H3)).
      simpl in H4.
      assert (i = H0 x0 (exist _ x H3) H2).
      { apply proof_irrelevance. }
      subst.
      apply H4.
      apply (pwo_wo x0).
    - (** transitivity *)
      intros x y z [W0 [HW0 Hxy]] [W1 [HW1 Hyz]].
      pose proof (pwo_R_lives_on_S _ _ _ Hxy) as [].
      pose proof (pwo_R_lives_on_S _ _ _ Hyz) as [].
      (* decide which of [W0] and [W1] is bigger. *)
      destruct (H W0 W1 HW0 HW1) as [HWW|HWW];
        [exists W1 | exists W0]; split; auto.
      all: unshelve eapply (pwo_trans _ _ (proj1_sig y) _);
          simpl; try tauto; apply HWW; tauto.
    - intros [x [Wx [HWx Hx]]] [y [Wy [HWy Hy]]] ?.
      destruct (H Wx Wy HWx HWy) as [HWW|HWW].
      + apply subset_eq.
        apply (partial_WO_chain_ub_WExt_Lemma
                 Wx Wy x y Hx Hy HWW HWx HWy H0).
      + apply subset_eq.
        symmetry in H0.
        symmetry.
        apply (partial_WO_chain_ub_WExt_Lemma
                 Wy Wx y x Hy Hx HWW HWy HWx H0).
  Qed.

  Program Definition partial_WO_chain_ub : partial_WO :=
      {| pwo_S := US;
         pwo_R := UR;
         pwo_wo := partial_WO_chain_ub_WO;
      |}.
  Next Obligation.
    destruct H0 as [? []].
    apply pwo_R_lives_on_S in H1 as [].
    split; exists x0; auto.
  Qed.
End partial_WO_chain_ub.

Lemma partial_WO_chain_ub_correct: forall (C:Ensemble partial_WO)
  (c:chain partial_WO_ord C), forall WO:partial_WO, In C WO ->
  partial_WO_ord WO (partial_WO_chain_ub C c).
Proof.
intros.
constructor.
- unfold Included.
  intros.
  exists WO.
  tauto.
- intros.
  split.
  { intro.
    exists WO.
    tauto.
  }
  intro.
  destruct H2.
  destruct H2.
  case (c WO x0 H H2).
  { intro.
    destruct H4.
    apply <- pwo_restriction0; assumption.
  }
  intro.
  destruct H4.
  pose proof (pwo_R_lives_on_S x0 x y).
  apply -> pwo_restriction0; tauto.
- intros.
  destruct H2.
  destruct H2.
  case (c WO x0 H H2).
  + intro.
    destruct H4.
    pose proof (pwo_R_lives_on_S x0 x y).
    apply pwo_downward_closed0 with y; tauto.
  + intro.
    apply H4.
    pose proof (pwo_R_lives_on_S x0 x y).
    tauto.
Qed.

Section extend_strictly_partial_WO.
  Variable (WO : partial_WO) (a : T) (H : ~ In (pwo_S WO) a).

  Let S' := Add (pwo_S WO) a.
  Let R' := fun x y => pwo_R WO x y \/ (In (pwo_S WO) x /\ y = a).

  Lemma extend_strictly_partial_S'_In
    (x : {y : T | In (pwo_S WO) y}) :
    In S' (proj1_sig x).
  Proof.
    destruct x.
    left. simpl.
    assumption.
  Qed.

  Lemma extend_strictly_partial_S'_WF_lemma :
    forall x:{y:T | In (pwo_S WO) y},
        Acc (rel_restriction R' S') (exist _ (proj1_sig x) (extend_strictly_partial_S'_In x)).
  Proof.
    intro x.
    pose proof (@wo_WF _ _ (pwo_wo WO) x) as Hx_acc.
    induction Hx_acc.
    constructor.
    intros ? Hyx.
    destruct x.
    destruct y.
    unfold rel_restriction in Hyx.
    simpl in Hyx.
    assert (In (pwo_S WO) x0) as Hx0.
    { case Hyx; try tauto.
      intro.
      pose proof (pwo_R_lives_on_S WO x0 x).
      tauto.
    }
    assert (pwo_R WO x0 x) as Hx0x.
    { case Hyx; try tauto.
      intros [? Heq].
      contradict H.
      rewrite <- Heq.
      assumption.
    }
    pose proof (H1 (exist _ x0 Hx0)).
    simpl in H2.
    assert (i0 = (extend_strictly_partial_S'_In (exist (In (pwo_S WO)) x0 Hx0)))
             as Heq.
    { apply proof_irrelevance. }
    subst.
    apply H2.
    assumption.
  Qed.

  Lemma extend_strictly_partial_WO_WO :
    WellOrder (rel_restriction R' S').
  Proof.
    constructor.
    - intros ?.
      pose extend_strictly_partial_S'_In as H0.
      destruct a0.
      pose proof (extend_strictly_partial_S'_WF_lemma) as H1.
      case i.
      + intros.
        pose proof (H1 (exist _ x0 i0)).
        simpl in H2.
        assert (H0 (exist (In (pwo_S WO)) x0 i0) =
          Union_introl T (pwo_S WO) (Singleton a) x0 i0).
        { apply proof_irrelevance. }
        rewrite <- H3.
        assumption.
      + intros.
        generalize i0.
        destruct i0.
        intro.
        constructor.
        intros.
        unfold rel_restriction in H2.
        destruct y.
        simpl in H2.
        case H2.
        * intro.
          contradict H.
          pose proof (pwo_R_lives_on_S WO x0 a).
          tauto.
        * intros.
          destruct H3.
          pose proof (H1 (exist _ x0 H3)).
          simpl in H5.
          replace (extend_strictly_partial_S'_In (exist (In (pwo_S WO)) x0 H3)) with i1 in H5;
            auto; apply proof_irrelevance.
    - intros [x Hx] [y Hy] [z Hz] Hxy Hyz.
      destruct Hxy as [|[]].
      2: {
        destruct Hyz as [|[]].
        - rewrite H1 in H2.
          apply pwo_R_lives_on_S in H2.
          tauto.
        - rewrite H1 in H2.
          tauto.
      }
      destruct Hyz as [|[]].
      + left.
        simpl in *.
        apply (pwo_trans WO x y z); auto.
      + right.
        split; auto.
        apply pwo_R_lives_on_S in H0.
        tauto.
    - intros [x Hx] [y Hy].
      inversion Hx; subst.
      + inversion Hy; subst.
        * intros. apply subset_eq. simpl.
          pose proof (@wo_wext _ _ (pwo_wo WO) (exist _ x H0) (exist _ y H1)).
          pose (fun z Hz =>
                  initial_segment (rel_restriction R' S') (exist _ z Hz)) as V.
          pose (fun z Hz =>
                  initial_segment (rel_restriction (pwo_R WO) (pwo_S WO)) (exist _ z Hz)) as U.
          cut (forall a Ha0 Ha1 b Hb0 Hb1,
                     Included (V a Ha0) (V b Hb0) ->
                     Included (U a Ha1) (U b Hb1)).
          { intros Hinc.
            unshelve epose proof (H3 _) as Hi.
            2: inversion Hi; subst; clear Hi; reflexivity.
            split; unshelve eapply Hinc; auto; apply H2.
          }
          clear x Hx y Hy H0 H1 H2 H3.
          intros.
          intros [c Hc] Hac.
          do 5 red. simpl.
          do 5 red in Hac. simpl in Hac.
          unshelve epose proof (H0 (exist _ c _) _); auto.
          { left. auto. }
          { left. assumption. }
          destruct H1 as [|[]]; auto.
          simpl in *. subst a. contradiction.
        * intros.
          inversion H1; subst; clear H1.
          exfalso.
          match goal with
          | H : Same_set ?a ?b |- _ =>
              unshelve eassert (In a (exist _ x _))
          end.
          { assumption. }
          { apply Extensionality_Ensembles in H2.
            rewrite H2.
            lazy. right. split; auto.
          }
          lazy in H1.
          destruct H1 as [|[]]; subst; try tauto.
          apply (@wf_irrefl _ _ (@wo_WF _ _ (pwo_wo WO)) (exist _ x H0)) in H1.
          auto.
      + inversion H0; subst; clear H0.
        inversion Hy; subst.
        2: {
          inversion H0; subst; clear H0.
          intros.
          apply subset_eq.
          reflexivity.
        }
        intros.
        exfalso.
        match goal with
        | H : Same_set ?a ?b |- _ =>
            unshelve eassert (In b (exist _ y _))
        end.
        { assumption. }
        { apply Extensionality_Ensembles in H1.
          rewrite <- H1.
          lazy. right. split; auto.
        }
        lazy in H2.
        destruct H2 as [|[]]; subst; try tauto.
        simpl in *.
        apply (@wf_irrefl _ _ (@wo_WF _ _ (pwo_wo WO)) (exist _ y H0)) in H2.
        auto.
  Qed.

  Program Definition extend_strictly_partial_WO : partial_WO :=
    {| pwo_S := S';
       pwo_R := R';
       pwo_wo := extend_strictly_partial_WO_WO;
    |}.
  Next Obligation.
    case H0.
    - intros.
      split.
      + left.
        pose proof (pwo_R_lives_on_S WO x y).
        tauto.
      + left.
        pose proof (pwo_R_lives_on_S WO x y).
        tauto.
    - intros.
      destruct H1.
      split.
      + left.
        assumption.
      + right.
        rewrite H2.
        auto with sets.
  Qed.
End extend_strictly_partial_WO.

Lemma extend_strictly_partial_WO_correct: forall (WO:partial_WO)
  (x:T) (ni:~ In (pwo_S WO) x),
  partial_WO_ord WO (extend_strictly_partial_WO WO x ni).
Proof.
intros.
constructor.
- unfold extend_strictly_partial_WO; simpl.
  constructor 1.
  assumption.
- intros.
  unfold extend_strictly_partial_WO; simpl.
  split.
  + tauto.
  + intro.
    case H1.
    * trivial.
    * intro.
      destruct H2.
      contradict ni.
      rewrite <- H3.
      assumption.
- unfold extend_strictly_partial_WO; simpl.
  intros.
  case H1.
  + intro.
    pose proof (pwo_R_lives_on_S WO x0 y).
    tauto.
  + intro.
    tauto.
Qed.

Lemma premaximal_partial_WO_is_full : forall WO:partial_WO,
  premaximal partial_WO_ord WO -> pwo_S WO = Full_set.
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
{ constructor. }
apply NNPP.
unfold not; intro.
pose (WO' := extend_strictly_partial_WO WO x H1).
assert (partial_WO_ord WO' WO).
{ apply H.
  apply extend_strictly_partial_WO_correct.
}
assert (In (pwo_S WO') x).
{ simpl.
  constructor 2.
  auto with sets.
}
apply H1.
apply H2.
assumption.
Qed.

Lemma premaximal_partial_WO_is_WF
  (WO : partial_WO) `(H : premaximal partial_WO_ord WO) :
  WellFounded (pwo_R WO).
Proof.
  assert (forall x:T, In (pwo_S WO) x).
  { rewrite premaximal_partial_WO_is_full.
    - intro.
      constructor.
    - assumption.
  }
  assert (forall a:{x:T | In (pwo_S WO) x}, Acc (pwo_R WO) (proj1_sig a)).
  { intro.
    pose proof (@wo_WF _ _ (pwo_wo WO)).
    induction (H1 a).
    destruct x.
    simpl.
    unfold rel_restriction in H3; simpl in H3.
    constructor.
    intros.
    apply H3 with (y := exist _ y (H0 y)).
    assumption.
  }
  red; intro.
  apply H1 with (a := exist _ a (H0 a)).
Qed.

Lemma premaximal_partial_WO_is_weakly_extensional
  (WO : partial_WO) (H : premaximal partial_WO_ord WO) :
  WeaklyExtensional (pwo_R WO).
Proof.
  intros ? ? ?.
  unshelve epose proof ((@wo_wext _ _ (pwo_wo WO)) (exist _ x _) (exist _ y _)).
  1, 2: rewrite premaximal_partial_WO_is_full; auto; try constructor.
  unshelve epose proof (H1 _) as Heq.
  2: {
    inversion Heq; subst; reflexivity.
  }
  clear H1.
  destruct H0.
  firstorder.
Qed.

Lemma premaximal_partial_WO_is_WO
  (WO : partial_WO) (H : premaximal partial_WO_ord WO) :
  WellOrder (pwo_R WO).
Proof.
  constructor.
  - apply (premaximal_partial_WO_is_WF WO H).
  - apply (pwo_trans WO).
  - apply (premaximal_partial_WO_is_weakly_extensional WO H).
Qed.

Theorem well_orderable_packed : exists W : well_order_packed,
    wop_carrier W = T.
Proof.
assert (exists WO:partial_WO, premaximal partial_WO_ord WO)
  as [WO H].
{ apply ZornsLemmaForPreorders.
  - exact partial_WO_preord.
  - intros.
    exists (partial_WO_chain_ub S H).
    exact (partial_WO_chain_ub_correct S H).
}
exists {| wop_WO := premaximal_partial_WO_is_WO WO H |}.
reflexivity.
Qed.

Theorem well_orderable: exists (R:relation T), WellOrder R.
Proof.
destruct well_orderable_packed as [WO].
subst.
exists (wop_rel WO).
apply wop_WO.
Qed.

End WellOrderConstruction.

Section WO_implies_AC.

Lemma WO_implies_AC: forall (A B:Type) (R: A -> B -> Prop)
  (WO:relation B) `{W : WellOrder B WO},
  (forall x:A, exists y:B, R x y) ->
  exists f:A->B, forall x:A, R x (f x).
Proof.
intros.
assert (forall a:A, Inhabited [ b:B | R a b ]).
{ intro.
  pose proof (H a) as [x].
  exists x.
  constructor; assumption.
}

exists (fun a:A => proj1_sig
  (WO_minimum WO [ b:B | R a b ] (H0 a))).
intro.
destruct @WO_minimum.
simpl.
destruct a.
destruct H1.
assumption.
Qed.

End WO_implies_AC.

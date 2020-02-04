Require Export Classical.
Require Import ClassicalChoice.
Require Export Relation_Definitions.
Require Import Relation_Definitions_Implicit.
Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Import ProofIrrelevance.
Require Import InverseImage.
Require Export EnsemblesSpec.
Require Import Quotients.

Section ZL'.

Variable T:Type.
Variable R:relation T.
Hypothesis ord:order R.
Definition chain (S: Ensemble T) : Prop :=
  forall x y:T, In S x -> In S y -> (R x y \/ R y x).
Definition maximal (x:T) : Prop :=
  forall y:T, R x y -> x = y.
Variable chain_sup: forall S: Ensemble T, chain S ->
  { x:T | (forall y:T, In S y -> R y x) /\
    (forall z:T, (forall y:T, In S y -> R y z) -> R x z) }.
Variable inflation: forall x:T,
  { y:T | R x y /\ x <> y /\ forall z:T, R x z -> R z y ->
                                     z = x \/ z = y }.

Inductive tower : Ensemble T :=
  | sup_intro: forall (S: Ensemble T), Included S tower ->
      forall c:chain S,
      In tower (proj1_sig (chain_sup S c))
  | inflation_intro: forall x:T, In tower x ->
      In tower (proj1_sig (inflation x)).

Lemma tower_is_chain: chain tower.
Proof.
unfold chain.
intros.
revert x H.
induction H0.
- intros.
  case (classic (forall y:T, In S y -> R y x)).
  + right.
    now apply (proj2_sig (chain_sup S c)).
  + intro.
    left.
    apply not_all_ex_not in H2.
    destruct H2.
    apply imply_to_and in H2.
    destruct H2.
    apply (ord_trans ord) with x0.
    * pose proof (H0 x0 H2 x H1).
      tauto.
    * now apply (proj2_sig (chain_sup S c)).
- pose proof (proj2_sig (inflation x)).
  destruct H0, H1.
  remember (proj1_sig (inflation x)) as x'.
  assert (forall y:T, In tower y -> R y x \/ R x' y).
  + intros.
    induction H3.
    * case (classic (forall x0:T, In S x0 -> R x0 x)); trivial.
      left.
      now apply (proj2_sig (chain_sup S c)).
      right.
      apply not_all_ex_not in H5.
      destruct H5.
      apply imply_to_and in H5.
      destruct H5.
      apply (ord_trans ord) with x0.
      ** pose proof (H4 x0).
         tauto.
      ** now apply (proj2_sig (chain_sup S c)).
    * assert (In tower x').
      rewrite Heqx'.
      now apply inflation_intro.
      destruct IHtower0.
      ** assert (In tower (proj1_sig (inflation x0))) by now apply inflation_intro.
         case (IHtower (proj1_sig (inflation x0)) H6);
         [ now left | ].
         intro.
         pose proof (proj2_sig (inflation x0)).
         simpl in H8.
         assert (x = x0 \/ x = proj1_sig (inflation x0)) by now apply H8.
         case H9.
         *** right.
             rewrite Heqx', H10.
             apply (ord_refl ord).
         *** left.
             rewrite H10.
             apply (ord_refl ord).
      ** right.
         now apply (ord_trans ord) with x0, (proj2_sig (inflation x0)).
  + intros.
    case (H3 x0 H4).
    * left.
      now apply (ord_trans ord) with x.
    * now right.
Qed.

(* can now show the given hypotheses are contradictory *)
Lemma ZL': False.
Proof.
pose proof (proj2_sig (chain_sup tower tower_is_chain)).
simpl in H.
remember (proj1_sig (chain_sup tower tower_is_chain)) as x0.
assert (In tower x0).
rewrite Heqx0.
constructor 1.
auto with sets.

pose (x' := proj1_sig (inflation x0)).
assert (In tower x') by now constructor 2.

pose proof (proj2_sig (inflation x0)).
destruct H2, H3.
contradict H3.
apply (ord_antisym ord); trivial.
destruct H.
now apply H.
Qed.

End ZL'.

Arguments chain {T}.
Arguments maximal {T}.

Require Export EnsemblesSpec.

Section ZL.

(* get rid of the need for a sup function and immediate successors *)

Variable T:Type.
Variable R:relation T.
Hypothesis ord: order R.
Hypothesis ub_of_chain: forall S:Ensemble T, chain R S ->
  exists x:T, forall y:T, In S y -> R y x.

Definition chains := {S:Ensemble T | chain R S}.
Definition chains_ord := (fun S1 S2:chains =>
  Included (proj1_sig S1) (proj1_sig S2)).

Lemma chains_order: order chains_ord.
Proof.
constructor.
- unfold reflexive, chains_ord.
  auto with sets.
- unfold transitive, chains_ord.
  auto with sets.
- intros [?] [?] ? ?.
  apply subset_eq_compat.
  auto with sets.
Qed.

Definition chains_sup_def : forall F: Ensemble chains,
  chain chains_ord F -> chains.
refine (fun F H => exist _ [ x:T | exists S:chains, In F S /\
                             In (proj1_sig S) x ] _).
red; intros.
destruct H0, H1, H0, H1.
pose proof (H x0 x1).
destruct x0, x1, H0, H1.
apply H2 in H0; trivial.
destruct H0;
  apply c0 + apply c;
  trivial;
  now apply H0.
Defined.

Lemma chains_sup_correct (F : Ensemble chains) (P : chain chains_ord F) :
  let U := chains_sup_def F P in
    (forall S:chains, In F S -> chains_ord S U) /\
    (forall T:chains, (forall S:chains, In F S -> chains_ord S T) ->
      chains_ord U T).
Proof.
intros.
unfold chains_ord, Included, U.
split;
  intros.
- constructor.
  now exists S.
- destruct H0 as [[x0 [? H1]]].
  now apply H in H1.
Qed.

Definition chains_sup (F:Ensemble chains) (P:chain chains_ord F) :=
  let U := chains_sup_def F P in
  exist (fun U:chains => 
    (forall S:chains, In F S -> chains_ord S U) /\
    (forall T:chains, (forall S:chains, In F S -> chains_ord S T) ->
      chains_ord U T))
  (chains_sup_def F P) (chains_sup_correct F P).

Lemma chains_ord_exists (x : chains) :
  (forall x:T, exists y:T, R x y /\ x <> y) ->
  exists y : chains, chains_ord x y /\ x <> y /\ (forall z : chains, chains_ord x z -> chains_ord z y -> z = x \/ z = y).
Proof.
intro H3.
destruct x,
  (ub_of_chain x c),
  (H3 x0).
pose (x' := Add x x1).
assert (chain R x').
- red.
  intros.
  case H1.
  + case H2;
      intros.
    * now apply c.
    * destruct H4.
      left.
      apply ord_trans with x0;
        now apply H + destruct H0.
  + intros x3 [].
    destruct H2 as [? | ? []].
    * right.
      apply ord_trans with x0;
        now apply H + destruct H0.
    * left.
      now apply ord_refl.
- exists (exist _ x' H1).
  unfold chains_ord.
  repeat split;
    intros.
  + now constructor.
  + intuition.
    injection H2.
    intro.
    assert (In x x1) by
      (rewrite H0; now constructor 2).
    contradict H5.
    now apply (ord_antisym ord), H.
  + destruct z, (classic (In x2 x1));
    [ right | left ];
      apply subset_eq_compat, Extensionality_Ensembles;
      split; trivial;
      red; intros.
    * case H6; trivial.
      now intros ? [].
    * assert (In x' x3) by now apply H4.
      inversion H7; trivial.
      now destruct H8.
Qed.

Theorem ZornsLemma: exists x:T, maximal R x.
Proof.
pose proof (ZL' chains chains_ord chains_order chains_sup).

apply NNPP.
unfold maximal.
pose proof chains_ord_exists.
dintuition.
assert (forall x:T, exists y:T, R x y /\ x <> y).
- assert (forall x:T, ~ forall y:T, R x y -> x = y)
    by now apply not_ex_all_not.
  assert (forall x:T, exists y:T, ~ (R x y -> x = y)) as H3
    by (intro; now apply not_all_ex_not).
  intro.
  destruct (H3 x) as [x0 H4].
  exists x0.
  now apply imply_to_and.
- assert (forall x:chains, exists y:chains,
    chains_ord x y /\ x <> y /\ forall z:chains, chains_ord x z ->
    chains_ord z y -> z = x \/ z = y) by intuition.
  apply choice in H3.
  destruct H3 as [f].
  apply H.
  intro.
  exists (f x).
  apply H3.
Qed.

End ZL.

Arguments ZornsLemma {T}.

Section ZL_preorder.

Variable T:Type.
Variable R:relation T.
Hypothesis Rpreord: preorder R.
Hypothesis ub_of_chain: forall S:Ensemble T, chain R S ->
  exists x:T, forall y:T, In S y -> R y x.

Definition premaximal (x:T) : Prop :=
  forall y:T, R x y -> R y x.

Local Definition Requiv (x y:T) := R x y /\ R y x.

Local Lemma equivalence_Requiv : equivalence Requiv.
Proof.
constructor.
- intro.
  split; now apply preord_refl.
- intros x y z [H0 H1] [H2 H3].
  split; now apply preord_trans with y.
- intros x y [H1 H2].
  now split.
Qed.

Lemma ZornsLemmaForPreorders: exists x:T, premaximal x.
Proof.
pose (Requiv (x y:T) := R x y /\ R y x).
pose equivalence_Requiv as H.
pose (Rquo := quotient Requiv).
let Hnew:=fresh"_H" in
  unshelve refine (let Hnew:=_ in
     let inducedR := induced_function2arg R H H Hnew in
     let inducedR_prop := induced_function2arg_correct R H H Hnew in _).
- intros.
  assert (True_rect (R a1 b1) = True_rect (R a2 b2)).
  + apply Extensionality_Ensembles; split; red; intros.
    * destruct x.
      red in H2.
      simpl in H2.
      red; simpl.
      apply preord_trans with a1; trivial.
      ** apply H0.
      ** apply preord_trans with b1; trivial.
         apply H1.
    * destruct x.
      red in H2; simpl in H2.
      red; simpl.
      apply preord_trans with a2; trivial.
      ** apply H0.
      ** apply preord_trans with b2; trivial.
         apply H1.
  + now assert (True_rect (R a1 b1) I = True_rect (R a2 b2) I) by now rewrite H2.
- clearbody inducedR_prop.
  fold inducedR in inducedR_prop.
  assert (exists x:Rquo, maximal inducedR x).
  + apply ZornsLemma.
    * constructor.
      red; intros xbar.
      ** destruct (quotient_projection_surjective xbar) as [x []].
         rewrite inducedR_prop.
         now apply preord_refl.
      ** red; intros xbar ybar zbar ? ?.
         destruct (quotient_projection_surjective xbar) as [x].
         destruct (quotient_projection_surjective ybar) as [y].
         destruct (quotient_projection_surjective zbar) as [z].
         subst.
         rewrite inducedR_prop in *.
         now apply preord_trans with y.
      ** red; intros xbar ybar ? ?.
         destruct (quotient_projection_surjective xbar) as [x].
         destruct (quotient_projection_surjective ybar) as [y].
         subst.
         rewrite inducedR_prop in H0, H1.
         unfold quotient_projection.
         apply subset_eq_compat, R_impl_equality_of_equiv_class; trivial.
         now split.
    * intros Sbar ?.
      pose (S := inverse_image (quotient_projection _) Sbar).
      unshelve refine (let H1:=ub_of_chain S _ in _).
      ** red; intros.
         pose proof (H0 (quotient_projection _ x) (quotient_projection _ y)).
         rewrite 2 inducedR_prop in H3.
         destruct H1, H2.
         now apply H3.
      ** destruct H1.
         exists (quotient_projection _ x).
         intros ybar ?.
         destruct (quotient_projection_surjective ybar) as [y].
         destruct H3.
         rewrite inducedR_prop.
         apply H1.
         now constructor.
    + destruct H0 as [xbar],
               (quotient_projection_surjective xbar) as [x], H1.
      exists x.
      red; intros.
      red in H0.
      unshelve refine (let H2:=H0 (quotient_projection Requiv y) _ in _).
      * now rewrite inducedR_prop.
      * unfold quotient_projection in H2.
        injection H2; intros.
        assert (In (equiv_class Requiv x) y).
        ** rewrite H3.
           constructor.
           now apply equiv_refl.
        ** now destruct H4 as [[? ?]].
Qed.

End ZL_preorder.

Arguments premaximal {T}.

Require Export RTopology ProductTopology Homeomorphisms.
Require Import ContinuousFactorization.
From Coq Require Import FunctionalExtensionality Lra ProofIrrelevance.
From ZornsLemma Require Import EnsemblesTactics.

Lemma continuous_at_iff_continuity_pt
  {f : R -> R} {x : R} :
  @continuous_at RTop RTop f x <-> continuity_pt f x.
Proof.
split.
- intros H eps H0.
  assert (neighbourhood (inverse_image f [r : R | Rabs (r - f x) < eps]) x) as H1.
  { apply RTop_neighborhood_is_neighbourhood, H, open_neighborhood_is_neighborhood.
    split.
    - replace [r : R | Rabs (r - f x) < eps] with [r : R | f x - eps < r < f x + eps]
        by (extensionality_ensembles;
            constructor;
            apply Rabs_def1 + apply Rabs_def2 in H1;
            lra).
      apply R_interval_open.
    - constructor.
      apply Rabs_def1; lra.
  }
  destruct H1 as [[alp H1] H2].
  exists alp.
  split; trivial.
  intros x0 [? H3].
  now destruct (H2 _ H3) as [[?]].
- intros H U HU.
  apply RTop_neighborhood_is_neighbourhood.
  pose HU as H0.
  apply RTop_neighborhood_is_neighbourhood in H0.
  destruct H0 as [[eps H0] H1],
          (H eps H0) as [alp [H2 H3]].
  exists (mkposreal alp H2).
  intros x' H'.
  constructor.
  destruct (Req_dec x x').
  + subst.
    destruct HU as [V [[H4 H5] H6]].
    now apply H6.
  + now apply H1, H3.
Qed.

Lemma continuous_iff_continuity
  {f : R -> R} :
  @continuous RTop RTop f <-> continuity f.
Proof.
split;
  intros H ?.
- now apply continuous_at_iff_continuity_pt,
      continuous_func_continuous_everywhere.
- apply pointwise_continuity.
  intro.
  now apply continuous_at_iff_continuity_pt.
Qed.

Lemma Rplus_continuous: continuous_2arg Rplus (X:=RTop) (Y:=RTop) (Z:=RTop).
Proof.
apply pointwise_continuity_2arg.
intros.
red.
pose proof (RTop_metrization (x+y)).
apply continuous_at_neighborhood_basis with
  (metric_topology_neighborhood_basis R_metric (x+y)).
- apply open_neighborhood_basis_is_neighborhood_basis,
        RTop_metrization.
- intros.
  destruct H0.
  exists ([ p:point_set RTop * point_set RTop | let (x',y'):=p in
    In (open_ball R_metric x (r/2)) x' /\
    In (open_ball R_metric y (r/2)) y' ]).
  repeat split;
    try (rewrite metric_zero; apply R_metric_is_metric + lra).
  + apply ProductTopology2_basis_is_basis.
    constructor;
    [ destruct (RTop_metrization x) |
      destruct (RTop_metrization y)];
      apply (open_neighborhood_basis_elements (open_ball _ _ _));
      constructor; lra.
  + destruct x0 as [x' y'],
             H1 as [[[] []]].
    unfold R_metric.
    simpl.
    replace (x'+y' - (x+y)) with ((x'-x) + (y'-y)) by ring.
    apply Rle_lt_trans with (Rabs (x'-x) + Rabs(y'-y)).
    * apply Rabs_triang.
    * replace r with (r/2+r/2) by field.
      now apply Rplus_lt_compat.
Qed.

Corollary sum_continuous: forall (X:TopologicalSpace)
  (f g:point_set X -> point_set RTop) (x:point_set X),
  continuous_at f x -> continuous_at g x ->
  continuous_at (fun x:point_set X => f x + g x) x (Y:=RTop).
Proof.
intros.
apply continuous_composition_at_2arg; trivial.
apply continuous_func_continuous_everywhere,
      Rplus_continuous.
Qed.

(* Ropp_continuous was already proved in RTopology *)

Lemma Rminus_continuous: continuous_2arg Rminus
  (X:=RTop) (Y:=RTop) (Z:=RTop).
Proof.
unfold Rminus.
apply pointwise_continuity_2arg; intros.
red.
pose proof (sum_continuous _
  (fun p:point_set (ProductTopology2 RTop RTop) => fst p)
  (fun p:point_set (ProductTopology2 RTop RTop) => -snd p) (x,y)).
simpl in H.
match goal with |- continuous_at ?f ?q =>
  replace f with (fun p:R*R => fst p + - snd p) end.
- apply sum_continuous.
  + apply continuous_func_continuous_everywhere,
          product2_fst_continuous.
  + eapply (continuous_composition_at (Y:=RTop));
      apply continuous_func_continuous_everywhere.
    * apply Ropp_continuous.
    * apply product2_snd_continuous.
- extensionality p.
  now destruct p.
Qed.

Corollary diff_continuous: forall (X:TopologicalSpace)
  (f g:point_set X -> point_set RTop) (x:point_set X),
  continuous_at f x -> continuous_at g x ->
  continuous_at (fun x:point_set X => f x - g x) x (Y:=RTop).
Proof.
intros.
apply continuous_composition_at_2arg; trivial.
apply continuous_func_continuous_everywhere.
exact Rminus_continuous.
Qed.

Lemma const_multiple_func_continuous: forall c:R,
  continuous (fun x:R => c*x) (X:=RTop) (Y:=RTop).
Proof.
intros.
apply continuous_iff_continuity,
      continuity_mult.
- apply continuity_const.
  red.
  now intros.
- intro.
  apply derivable_continuous_pt, derivable_pt_id.
Qed.

Corollary const_multiple_continuous: forall (X:TopologicalSpace)
  (f:point_set X -> point_set RTop) (c:R) (x:point_set X),
  continuous_at f x -> continuous_at (fun x:point_set X => c * f x) x
                       (Y:=RTop).
Proof.
intros.
apply continuous_composition_at; trivial.
apply continuous_func_continuous_everywhere,
      const_multiple_func_continuous.
Qed.

Lemma Rmult_continuous_at_origin: continuous_at_2arg Rmult 0 0
                                  (X:=RTop) (Y:=RTop) (Z:=RTop).
Proof.
red.
pose proof (RTop_metrization 0).
apply continuous_at_neighborhood_basis with
  (metric_topology_neighborhood_basis R_metric 0).
- apply open_neighborhood_basis_is_neighborhood_basis.
  simpl. rewrite Rmult_0_r.
  assumption.
- intros.
  destruct H0.
  exists (characteristic_function_to_ensemble
    (fun p:point_set RTop * point_set RTop => let (x',y'):=p in
    In (open_ball R_metric 0 r) x' /\
    In (open_ball R_metric 0 1) y' )).
  repeat split.
  + apply ProductTopology2_basis_is_basis.
    constructor;
      destruct H.
    * apply (open_neighborhood_basis_elements (open_ball R_metric 0 r)).
      now constructor.
    * apply (open_neighborhood_basis_elements (open_ball R_metric 0 1)).
      constructor; red; auto with real.
  + rewrite metric_zero; trivial.
    apply R_metric_is_metric.
  + rewrite metric_zero; auto with real.
    apply R_metric_is_metric.
  + destruct H1.
    destruct x as [x y].
    destruct H1 as [[] []].
    unfold R_metric in *.
    simpl.
    rewrite Rminus_0_r in *.
    rewrite Rabs_mult.
    replace r with (r*1) by auto with real.
    apply Rmult_le_0_lt_compat;
      apply Rabs_pos + trivial.
Qed.

Lemma Rmult_continuous: continuous_2arg Rmult (X:=RTop) (Y:=RTop) (Z:=RTop).
Proof.
apply pointwise_continuity_2arg.
intros x0 y0.
red.
match goal with |- continuous_at ?f ?q => replace f with
  (fun p:point_set RTop*point_set RTop =>
   (fst p - x0) * (snd p - y0) + y0 * fst p + x0 * snd p - x0 * y0) end.
- apply diff_continuous.
  + apply sum_continuous.
    * apply sum_continuous.
      ** apply continuous_composition_at_2arg with RTop RTop.
         *** simpl.
             replace (x0-x0) with 0 by ring.
             replace (y0-y0) with 0 by ring.
             apply Rmult_continuous_at_origin.
         *** apply diff_continuous;
               apply continuous_func_continuous_everywhere;
               apply product2_fst_continuous + apply continuous_constant.
         *** apply diff_continuous;
               apply continuous_func_continuous_everywhere;
               apply product2_snd_continuous + apply continuous_constant.
      ** apply const_multiple_continuous,
               continuous_func_continuous_everywhere;
           apply product2_fst_continuous.
    * apply const_multiple_continuous,
            continuous_func_continuous_everywhere;
        apply product2_snd_continuous.
  + apply continuous_func_continuous_everywhere;
      apply continuous_constant.
- extensionality p.
  destruct p.
  simpl.
  ring.
Qed.

Corollary product_continuous: forall (X:TopologicalSpace)
  (f g:point_set X -> point_set RTop) (x:point_set X),
  continuous_at f x -> continuous_at g x ->
  continuous_at (fun x:point_set X => f x * g x) x (Y:=RTop).
Proof.
intros.
apply continuous_composition_at_2arg; trivial.
apply continuous_func_continuous_everywhere.
exact Rmult_continuous.
Qed.

Lemma Rinv_continuous (x : R) :
  x <> 0 -> @continuous_at RTop RTop Rinv x.
Proof.
intros.
apply continuous_at_iff_continuity_pt,
      continuity_pt_inv; trivial.
apply derivable_continuous_pt, derivable_pt_id.
Qed.

Lemma Rdiv_continuous: forall x y:R, y <> 0 ->
  continuous_at_2arg Rdiv x y (X:=RTop) (Y:=RTop) (Z:=RTop).
Proof.
intros.
red.
match goal with |- continuous_at ?f ?q => replace f with
  (fun p:point_set RTop * point_set RTop => fst p * / snd p) end.
- apply product_continuous.
  + apply continuous_func_continuous_everywhere;
      apply product2_fst_continuous.
  + apply continuous_composition_at.
    * simpl.
      now apply Rinv_continuous.
    * apply continuous_func_continuous_everywhere;
        apply product2_snd_continuous.
- extensionality p.
  now destruct p.
Qed.

Corollary quotient_continuous: forall (X:TopologicalSpace)
  (f g:point_set X -> point_set RTop) (x0:point_set X),
  continuous_at f x0 -> continuous_at g x0 -> g x0 <> 0 ->
  continuous_at (fun x:point_set X => f x / g x) x0 (Y:=RTop).
Proof.
intros.
apply continuous_composition_at_2arg; trivial.
apply Rdiv_continuous; trivial.
Qed.

Lemma Rabs_continuous: continuous Rabs (X:=RTop) (Y:=RTop).
Proof.
apply pointwise_continuity.
intros.
apply metric_space_fun_continuity with R_metric R_metric;
  try apply RTop_metrization.
intros.
exists eps; split; trivial.
intros.
apply Rle_lt_trans with (2 := H0).
apply Rabs_triang_inv2.
Qed.

Lemma open_interval_homeomorphic_to_real_line:
  let U:=characteristic_function_to_ensemble
      (fun x:point_set RTop => -1 < x < 1) in
  homeomorphic RTop (SubspaceTopology U).
Proof.
intros.
assert (forall x:R, -1 < x / (1 + Rabs x) < 1).
{ intros.
  assert (0 < 1 + Rabs x).
  { pose proof (Rabs_pos x). lra. }
  apply and_comm, Rabs_def2.
  unfold Rdiv.
  rewrite Rabs_mult, Rabs_Rinv.
  - rewrite (Rabs_right (1 + Rabs x)); [ | now left ].
    pattern 1 at 2.
    replace 1 with ((1 + Rabs x) * / (1 + Rabs x)) by (field; lra).
    apply Rmult_lt_compat_r.
    + now apply Rinv_0_lt_compat.
    + lra.
  - lra. }
assert (forall x:point_set RTop, In U (x / (1 + Rabs x))).
{ intros.
  now constructor. }
exists (continuous_factorization _ _ H0).
exists (fun x => (subspace_inc U x) / (1 - Rabs (subspace_inc U x))).
- apply factorization_is_continuous.
  apply pointwise_continuity.
  intros.
  apply quotient_continuous.
  + apply continuous_func_continuous_everywhere, continuous_identity.
  + apply sum_continuous.
    * apply continuous_func_continuous_everywhere, continuous_constant.
    * apply continuous_func_continuous_everywhere, Rabs_continuous.
  + pose proof (Rabs_pos x).
    lra.
- apply pointwise_continuity.
  intros.
  apply quotient_continuous.
  + apply continuous_func_continuous_everywhere, subspace_inc_continuous.
  + apply diff_continuous.
    * apply continuous_func_continuous_everywhere, continuous_constant.
    * apply continuous_composition_at.
      -- apply continuous_func_continuous_everywhere, Rabs_continuous.
      -- apply continuous_func_continuous_everywhere, subspace_inc_continuous.
  + destruct x as [x [[]]]. simpl.
    cut (Rabs x < 1).
    * lra.
    * apply Rabs_def1; lra.
- simpl.
  intros.
  unfold Rabs at 1 3. destruct Rcase_abs.
  + rewrite Rabs_left.
    * field.
      lra.
    * assert (/ (1 + -x) > 0).
      { apply Rinv_0_lt_compat.
        lra. }
      replace 0 with (x*0) by auto with real.
      now apply Rmult_lt_gt_compat_neg_l.
  + rewrite Rabs_right.
    * field.
      lra.
    * assert (/ (1+x) > 0).
      { apply Rinv_0_lt_compat.
        lra. }
      apply Rle_ge.
      apply Rge_le in r.
      red in H1.
      unfold Rdiv.
      replace 0 with (0 * / (1+x)); auto with real.
- intros.
  destruct y as [x].
  simpl.
  apply subset_eq_compat.
  destruct i.
  destruct H1.
  assert (Rabs x < 1) by now apply Rabs_def1.
  unfold Rabs at 1 3. destruct Rcase_abs.
  + rewrite Rabs_left.
    * field.
      lra.
    * replace (1 - -x) with (1+x) by ring.
      assert (/ (1+x) > 0).
      { apply Rinv_0_lt_compat. lra. }
      unfold Rdiv.
      replace 0 with (x*0) by auto with real.
      now apply Rmult_lt_gt_compat_neg_l.
  + rewrite Rabs_right.
    * field.
      lra.
    * assert (/ (1-x) > 0) by
        now apply Rinv_0_lt_compat, Rgt_minus.
      unfold Rdiv.
      red in H4.
      apply Rge_le in r.
      apply Rle_ge.
      replace 0 with (0 * / (1-x)); auto with real.
Qed.

Lemma Rmin_using_Rabs x y :
  Rmin x y = (x + y - Rabs (x-y))*(1/2).
Proof.
  destruct (classic (x <= y)).
  - rewrite Rmin_left; try assumption.
    rewrite Rabs_minus_sym.
    rewrite Rabs_pos_eq.
    2: { lra. }
    lra.
  - rewrite Rmin_right; try lra.
    rewrite Rabs_pos_eq.
    2: { lra. }
    lra.
Qed.

Lemma Rmax_using_Rabs x y :
  Rmax x y = (x + y + Rabs (x-y))*(1/2).
Proof.
  destruct (classic (x <= y)).
  - rewrite Rmax_right; try assumption.
    rewrite Rabs_minus_sym.
    rewrite Rabs_pos_eq.
    2: { lra. }
    lra.
  - rewrite Rmax_left; try lra.
    rewrite Rabs_pos_eq.
    2: { lra. }
    lra.
Qed.

Lemma continuous_2arg_compose : forall {U X Y Z : TopologicalSpace} (f : U -> X) (g : U -> Y) (h : X -> Y -> Z),
    continuous f -> continuous g -> continuous_2arg h ->
    continuous (fun p => h (f p) (g p)).
Proof.
  intros.
  apply pointwise_continuity.
  intros.
  apply continuous_composition_at_2arg.
  - apply continuous_2arg_func_continuous_everywhere.
    assumption.
  - apply continuous_func_continuous_everywhere.
    assumption.
  - apply continuous_func_continuous_everywhere.
    assumption.
Qed.

Lemma Rmin_continuous : continuous_2arg Rmin (X:=RTop) (Y:=RTop) (Z:=RTop).
Proof.
  red.
  replace (fun p : RTop * RTop => _) with
      (fun p : RTop * RTop => ((fst p) + (snd p) - Rabs (fst p - snd p))*(1/2)).
  2: {
    apply functional_extensionality.
    intros []. simpl.
    symmetry. apply Rmin_using_Rabs.
  }
  apply @continuous_2arg_compose with (X := RTop) (Y := RTop).
  2: { apply continuous_constant. }
  2: { apply Rmult_continuous. }
  apply @continuous_2arg_compose with (X := RTop) (Y := RTop).
  3: { apply Rminus_continuous. }
  - apply @continuous_2arg_compose with (X := RTop) (Y := RTop).
    + apply product2_fst_continuous.
    + apply product2_snd_continuous.
    + apply Rplus_continuous.
  - apply @continuous_composition with (Y := RTop).
    { apply Rabs_continuous. }
    apply @continuous_2arg_compose with (X := RTop) (Y := RTop).
    + apply product2_fst_continuous.
    + apply product2_snd_continuous.
    + apply Rminus_continuous.
Qed.

Lemma Rmax_continuous : continuous_2arg Rmax (X:=RTop) (Y:=RTop) (Z:=RTop).
Proof.
  red.
  replace (fun p : RTop * RTop => _) with
      (fun p : RTop * RTop => ((fst p) + (snd p) + Rabs (fst p - snd p))*(1/2)).
  2: {
    apply functional_extensionality.
    intros []. simpl.
    symmetry. apply Rmax_using_Rabs.
  }
  apply @continuous_2arg_compose with (X := RTop) (Y := RTop).
  2: { apply continuous_constant. }
  2: { apply Rmult_continuous. }
  apply @continuous_2arg_compose with (X := RTop) (Y := RTop).
  3: { apply Rplus_continuous. }
  - apply @continuous_2arg_compose with (X := RTop) (Y := RTop).
    + apply product2_fst_continuous.
    + apply product2_snd_continuous.
    + apply Rplus_continuous.
  - apply @continuous_composition with (Y := RTop).
    { apply Rabs_continuous. }
    apply @continuous_2arg_compose with (X := RTop) (Y := RTop).
    + apply product2_fst_continuous.
    + apply product2_snd_continuous.
    + apply Rminus_continuous.
Qed.

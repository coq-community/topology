Require Export TopologicalSpaces OrderTopology MetricSpaces.
From Coq Require Import Lra Lia.
From ZornsLemma Require Import EnsemblesTactics FiniteIntersections.
Require Import RationalsInReals.
From Topology Require Export Completeness Connectedness.
From Topology Require Export Compactness.

Definition RTop := OrderTopology Rle.
Definition R_metric (x y:R) : R := Rabs (y-x).

Lemma R_metric_is_metric: metric R_metric.
Proof.
constructor;
  intros;
  unfold R_metric in *.
- replace (y-x) with (-(x-y)) by ring.
  apply Rabs_Ropp.
- replace (z-x) with ((y-x) + (z-y)) by ring.
  apply Rabs_triang.
- replace (x-x) with 0 by ring.
  exact Rabs_R0.
- apply NNPP.
  intro.
  assert (y - x <> 0) by lra.
  now apply Rabs_no_R0 in H1.
Qed.

Lemma Rmetric_bound: forall x y z:R, R_metric x z < y - x ->
  z < y.
Proof.
intros.
replace z with (x + (z-x)) by ring.
apply Rle_lt_trans with (x + R_metric x z);
[ assert (z - x <= R_metric x z) by apply Rle_abs |
  replace y with (x + (y-x)) by ring ];
  lra.
Qed.

Lemma Rmetric_bound2: forall x y z:R, R_metric y z < y - x ->
  x < z.
Proof.
intros.
replace z with (y + (z-y)) by ring.
cut (y - z <= R_metric y z).
- lra.
- rewrite (metric_sym _ _ R_metric_is_metric).
  apply Rle_abs.
Qed.

Lemma R_interval_open : forall p q,
  @open RTop [r : R | p < r < q].
Proof.
intros p q.
replace [r : R | p < r < q] with
  (Intersection (lower_open_ray Rle q) (upper_open_ray Rle p))
  by (extensionality_ensembles; repeat constructor; lra).
eapply (@open_intersection2 RTop).
- apply (lower_open_ray_open
           (OrderTopology_orders_top Rle)).
- apply (upper_open_ray_open
           (OrderTopology_orders_top Rle)).
Qed.

Lemma RTop_neighborhood_is_neighbourhood
  (U : Ensemble R)
  (r : R) :
  @neighborhood RTop U r <-> neighbourhood U r.
Proof.
split.
- intros [H1 [[[F H2] [V x H4 H5]] H6]].
  eapply (neighbourhood_P1 V).
  { intros x' H'.
    apply H6.
    econstructor.
    - exact H4.
    - exact H'. }
  apply H2 in H4.
  clear H2 H6 F H1.
  induction H4.
  + exists (RinvN 1).
    now intros ? ?.
  + destruct H as [y|y];
      destruct H5 as [[H5 H6]];
    [ refine (ex_intro _ (mkposreal (y - x) _) _) |
      refine (ex_intro _ (mkposreal (x - y) _) _) ];
      intros ? H;
      apply Rabs_def2 in H;
      simpl in H;
      destruct H;
      repeat constructor; lra.
      Unshelve.
      all: lra.
  + destruct H5 as [x H2 H3],
             (IHfinite_intersections H2) as [[p Hp] H4],
             (IHfinite_intersections0 H3) as [[q Hq] H5],
             (Rlt_or_le p q);
    [ exists (mkposreal p Hp) |
      exists (mkposreal q Hq) ];
      intros x' H';
      apply Rabs_def2 in H';
      simpl in H';
      destruct H';
      constructor;
      apply H4 + apply H5;
      apply Rabs_def1; simpl;
      try assumption;
      (try now (eapply Rlt_trans; try exact H7);
      eapply Rlt_trans;
      try exact H8); lra.
- intros [[p Hp] H].
  exists [x : R | r - p < x < r + p].
  repeat split; try lra.
  + apply R_interval_open.
  + intros y [[H1 H2]].
    apply H, Rabs_def1; simpl; lra.
Qed.

Lemma R_metric_open_ball_as_Intersection_ray (x r : R) :
  open_ball R_metric x r =
    Intersection
      (upper_open_ray Rle (x - r))
      (lower_open_ray Rle (x + r)).
Proof.
  apply Extensionality_Ensembles; split.
  - intros y [Hy]. unfold R_metric, Rabs in Hy.
    split; constructor; destruct Rcase_abs; lra.
  - intros y Hy.
    destruct Hy as [y [[]] [[]]].
    constructor. unfold R_metric, Rabs.
    destruct Rcase_abs; lra.
Qed.

Lemma RTop_metrization: metrizes RTop R_metric.
Proof.
pose proof (Hsubbasis := Build_TopologicalSpace_from_subbasis_subbasis
  _ (order_topology_subbasis Rle)).
red. intros x.
split.
- intros U HU. destruct HU as [r Hr].
  split.
  2: {
    apply metric_open_ball_In; auto.
    apply R_metric_is_metric.
  }
  rewrite R_metric_open_ball_as_Intersection_ray.
  apply (@open_intersection2 RTop);
    apply Hsubbasis; constructor.
- intros U HUx.
  apply open_neighborhood_is_neighborhood,
    RTop_neighborhood_is_neighbourhood in HUx.
  destruct HUx.
  exists (open_ball R_metric x x0).
  split.
  + now destruct x0.
  + intros r [H0].
    now apply H.
Qed.

Corollary RTop_metrizable: metrizable RTop.
Proof.
exists R_metric.
- exact R_metric_is_metric.
- exact RTop_metrization.
Qed.

Lemma bounded_real_net_has_cluster_point: forall (I:DirectedSet)
  (x:Net I RTop) (a b:R), (forall i:I, a <= x i <= b) ->
  exists x0:RTop, net_cluster_point x x0.
Proof.
(* idea: the liminf is a cluster point *)
intros.
destruct (classic (inhabited I)) as [Hinh|Hempty].
2: {
  exists a.
  red. intros.
  red. intros.
  contradiction Hempty.
  now exists.
}
assert (forall i:I, { y:R | is_glb
                         (Im [ j:I | DS_ord i j ] x) y }).
{ intro.
  apply inf.
  - exists a.
    red. intros.
    destruct H0.
    destruct (H x0).
    lra.
  - exists (x i), i; trivial.
    constructor.
    apply preord_refl, DS_ord_cond. }
assert ({ x0:R | is_lub (Im Full_set (fun i => proj1_sig (X i))) x0 }).
{ apply sup.
  - exists b.
    red. intros.
    destruct H0 as [i].
    destruct (X i).
    simpl in H1.
    rewrite H1.
    destruct i0.
    cut (b >= x0); auto with real.
    apply Rge_trans with (x i).
    + destruct (H i). lra.
    + apply H2.
      exists i; trivial.
      constructor.
      apply preord_refl, DS_ord_cond.
  - destruct Hinh as [i0].
    exists (proj1_sig (X i0)).
    exists i0; trivial.
    constructor.
}
destruct H0 as [x0].
exists x0.
assert (forall i j:I,
           DS_ord i j -> proj1_sig (X i) <= proj1_sig (X j)).
{ intros.
  destruct (X i0), (X j).
  simpl.
  destruct i1, i2.
  apply H4.
  red. intros.
  destruct H5.
  destruct H5.
  apply H1.
  exists x3; trivial.
  constructor.
  apply preord_trans with j; trivial.
  apply DS_ord_cond.
}
red. intros.
destruct (RTop_metrization x0).
destruct (open_neighborhood_basis_cond U).
{ now split. }
destruct H3.
destruct H3.
destruct (lub_approx _ _ r i); trivial.
destruct H5.
destruct H5.
destruct H6.
red; intros.
destruct (DS_join_cond x1 i0).
destruct H9.
remember (X x2) as y2.
destruct y2.
destruct (glb_approx _ _ r i1); trivial.
destruct H11.
destruct H11.
destruct H11.
destruct H12.
exists x4.
split.
+ apply preord_trans with x2; trivial.
  apply DS_ord_cond.
+ apply H4.
  constructor.
  assert (y <= proj1_sig (X x2)).
  { rewrite H7.
    now apply H0. }
  rewrite <- Heqy2 in H15.
  simpl in H15.
  assert (proj1_sig (X x2) <= x0).
  { apply i.
    exists x2; trivial.
    constructor. }
  rewrite <- Heqy2 in H16.
  simpl in H16.
  apply Rabs_def1; lra.
Qed.

Lemma R_closed_interval_compact: forall a b:R, a <= b ->
  compact (SubspaceTopology ([x:RTop | a <= x <= b])).
Proof.
intros a b Hbound.
apply net_cluster_point_impl_compact.
intros.
pose (y := fun i:I => proj1_sig (x i)).
destruct (bounded_real_net_has_cluster_point _ y a b).
{ intros.
  unfold y.
  destruct (x i).
  now destruct i0.
}
assert (closed [x:RTop | a <= x <= b]).
{ replace [x:RTop | a <= x <= b] with
        (Intersection
          [ x:RTop | a <= x ]
          [ x:RTop | x <= b ]) by
    (extensionality_ensembles;
      do 2 constructor; lra).
  apply closed_intersection2.
  - apply upper_closed_ray_closed.
    + constructor; red; intros; auto with real.
      apply Rle_trans with y0; trivial.
    + apply OrderTopology_orders_top.
    + intros.
      destruct (total_order_T x1 y0) as [[|]|]; auto with real.
  - apply lower_closed_ray_closed.
    + constructor; red; intros; auto with real.
      apply Rle_trans with y0; trivial.
    + apply OrderTopology_orders_top.
    + intros.
      destruct (total_order_T x1 y0) as [[|]|]; auto with real. }
assert (Ensembles.In [x:RTop | a <= x <= b] x0).
{ rewrite <- (closure_fixes_closed _ H1).
  apply net_cluster_point_in_closure with y; trivial.
  destruct H as [i0].
  exists i0.
  intros.
  constructor.
  unfold y.
  destruct (x j).
  now destruct i. }
exists (exist _ x0 H2).
red. intros.
rewrite subspace_open_char in H3.
destruct H3 as [V []].
subst U.
destruct H4.
red. intros.
assert (Ensembles.In V x0).
{ assumption. }
destruct (H0 V H3 H4 i) as [j []].
exists j.
split; trivial.
now constructor.
Qed.

Lemma R_compact_subset_bounded: forall A:Ensemble RTop,
  compact (SubspaceTopology A) -> bound A.
Proof.
intros.
destruct (H (Im Full_set (fun y => inverse_image (subspace_inc _)
                   [ x:RTop | y - 1 < x < y + 1 ]))).
- intros U [H0].
  subst.
  apply subspace_inc_continuous, R_interval_open.
- extensionality_ensembles;
    econstructor.
  + now exists (proj1_sig x).
  + do 2 constructor.
    destruct x.
    simpl.
    lra.
- destruct H0, H1.
  assert (exists a:R, forall S:Ensemble (SubspaceTopology A),
    forall b:SubspaceTopology A,
    Ensembles.In x S -> Ensembles.In S b -> proj1_sig b < a).
  { clear H2.
    induction H0.
    - exists 0.
      intros.
      destruct H0.
    - destruct IHFinite.
      + cut (Included A0 (Add A0 x)); auto with sets.
      + assert (Ensembles.In (Add A0 x) x).
        { right.
          constructor. }
        apply H1 in H4.
        destruct H4.
        exists (Rmax x0 (x+1)).
        intros.
        destruct H6.
        * specialize (H3 x1 b); intuition.
          apply Rlt_le_trans with x0; auto.
          apply Rmax_l.
        * destruct H6.
          rewrite H5 in H7.
          destruct H7.
          destruct H6.
          apply Rlt_le_trans with (x+1).
          ** apply H6.
          ** apply Rmax_r. }
  destruct H3 as [a].
  exists a.
  red. intros.
  assert (Ensembles.In (FamilyUnion x)
    (exist (fun x:R => Ensembles.In A x) x0 H4)).
  { rewrite H2. constructor. }
  inversion H5.
  pose proof (H3 _ _ H6 H7).
  simpl in H9.
  auto with real.
Qed.

Lemma Ropp_continuous: continuous Ropp (X:=RTop) (Y:=RTop).
Proof.
apply pointwise_continuity.
intro.
apply metric_space_fun_continuity with R_metric R_metric;
  try apply RTop_metrization.
intros.
exists eps.
split; trivial.
intros.
unfold R_metric.
replace (-x' - -x) with (x-x') by ring.
now rewrite Rabs_minus_sym.
Qed.

Lemma R_connected: connected RTop.
Proof.
apply connected_iff_inh_clopen_is_full with (x := 0).
cut (forall S:Ensemble RTop,
  clopen S -> In S 0 -> forall x:R, x > 0 -> In S x).
{ intro.
  assert (forall S:Ensemble RTop,
    clopen S -> In S 0 -> forall x:R, x < 0 ->
                                    Ensembles.In S x).
  { (* this sub-proof uses the fact,
       that [Ropp] has been shown to be continuous,
       that it is involutive, order-reversing and has [0] as fixed point.
     *)
    intros.
    pose (T := inverse_image Ropp S).
    assert (Ensembles.In T (-x)).
    { apply H.
      - destruct H0.
        split.
        + now apply Ropp_continuous.
        + red.
          subst T.
          rewrite <- inverse_image_complement.
          now apply Ropp_continuous.
      - constructor.
        replace (-0) with 0; trivial; ring.
      - cut (0 < -x); auto with real. }
    destruct H3.
    now rewrite Ropp_involutive in H3.
  }
  intros.
  (* since the order on [R] is trichotomous, [Full_set] splits into
     the two open rays and the singleton of [0]. *)
  extensionality_ensembles.
  { constructor. }
  destruct (total_order_T x 0) as [[|]|].
  - now apply H0.
  - congruence.
  - now apply H.
}
intros.
apply NNPP.
intro.
pose (T := [ y:R | forall z:R, 0 <= z <= y -> Ensembles.In S z ]).
assert (Ensembles.In T 0).
{ constructor.
  intros.
  now replace z with 0 by lra.
}
destruct (sup T).
{ exists x.
  red. intros.
  cut (~ x0>x).
  { lra. }
  intro.
  destruct H4.
  apply H2, H4.
  lra.
}
{ now exists 0. }
assert (0 <= x0) by now apply i.
destruct (RTop_metrization x0).
assert (Ensembles.In S x0).
{ rewrite <- (closure_fixes_closed S); [ | apply H ].
  apply meets_every_open_neighborhood_impl_closure.
  intros.
  destruct (open_neighborhood_basis_cond U).
  { now split. }
  destruct H7.
  destruct H7.
  destruct (lub_approx _ _ r i); trivial.
  destruct H9.
  exists (Rmax x1 0).
  constructor.
  - unfold Rmax.
    destruct Rle_dec; trivial.
    apply H9.
    auto with real.
  - apply H8.
    constructor.
    unfold Rmax.
    destruct Rle_dec;
      apply Rabs_def1; lra.
}
destruct (open_neighborhood_basis_cond S).
{ split; trivial.
   apply H.
}
destruct H6.
destruct H6.
destruct (lub_approx _ _ r i); trivial.
destruct H8.
assert (Ensembles.In T (x0+r/2)).
{ constructor.
  intros.
  destruct H10.
  destruct (total_order_T z x1) as [[|]|].
  - apply H8. lra.
  - apply H8. lra.
  - apply H7.
    constructor.
    apply Rabs_def1; lra.
}
assert (x0 + r/2 <= x0) by now apply i.
lra.
Qed.

Lemma R_bounded_char (U : Ensemble R) :
  bounded R_metric U <-> Coq.Reals.Rtopology.bounded U.
Proof.
unfold bounded, Rtopology.bounded.
split.
- intros [x [r H]].
  exists (x-r-1), (x+r+1).
  intros y Hy.
  specialize (H y Hy).
  destruct H.
  unfold R_metric in H.
  unfold Rabs in H.
  destruct (Rcase_abs _); lra.
- intros [m [M H]].
  exists ((m+M)/2), (M-m+1).
  intros y Hy.
  specialize (H y Hy).
  constructor.
  unfold R_metric, Rabs.
  destruct (Rcase_abs _); lra.
Qed.

Lemma R_cauchy_sequence_bounded: forall x:nat->R,
  cauchy R_metric x -> bound (Im Full_set x).
Proof.
intros x Hx.
pose proof (cauchy_impl_bounded
              R_metric R_metric_is_metric x Hx)
  as [p [r]].
clear Hx.
exists (p + r).
intros y Hy.
apply H in Hy.
clear H x.
destruct Hy.
unfold R_metric, Rabs in H.
destruct (Rcase_abs _); lra.
Qed.

Lemma R_cauchy_sequence_lower_bound: forall x:nat->R,
  cauchy R_metric x -> lower_bound (Im Full_set x).
Proof.
intros x Hx.
pose proof (cauchy_impl_bounded
              R_metric R_metric_is_metric x Hx)
  as [p [r]].
clear Hx.
exists (p - r).
intros y Hy.
apply H in Hy.
clear H x.
destruct Hy.
unfold R_metric, Rabs in H.
destruct (Rcase_abs _); lra.
Qed.

Lemma R_metric_complete: complete R_metric.
Proof.
apply complete_cauchy_cluster_points with (X := RTop).
1: apply R_metric_is_metric.
1: apply RTop_metrization.
intros x Hx.
pose proof (cauchy_impl_bounded _ R_metric_is_metric x Hx)
  as [p [r Hpr]].
destruct (bounded_real_net_has_cluster_point
            nat_DS x (p - r) (p + r)) as [x0].
{ intros n.
  unshelve epose proof (Hpr (x n) _) as [Hn].
  { apply Im_def. constructor. }
  unfold R_metric, Rabs in Hn.
  destruct (Rcase_abs _); lra.
}
exists x0. assumption.
Qed.

Lemma RTop_subbasis_rational_rays :
  @subbasis RTop
    (Union (ImageFamily (fun q => lower_open_ray Rle (Q2R q)))
           (ImageFamily (fun q => upper_open_ray Rle (Q2R q)))).
Proof.
split.
- intros S H.
  destruct H as [S [[q Hq] H]| S [[q Hq] H]]; subst.
  + apply (lower_open_ray_open
             (OrderTopology_orders_top Rle)).
  + apply (upper_open_ray_open
             (OrderTopology_orders_top Rle)).
- intros U r H1 H2.
  assert (neighborhood U r) as H by now exists U.
  apply RTop_neighborhood_is_neighbourhood in H.
  destruct H as [[d ?] H],
          (rationals_dense_in_reals (r - d) r) as [p ?],
          (rationals_dense_in_reals r (r + d)) as [q ?];
    exists (Intersection (upper_open_ray Rle (Q2R p))
         (lower_open_ray Rle (Q2R q))) + lra.
  repeat split;
    simpl; try lra.
  + do 2 constructor;
    [ right | left ];
      repeat econstructor.
  + intros ? [y [?] [?]].
    apply H, Rabs_def1;
      simpl; lra.
Qed.

Corollary RTop_second_countable : second_countable RTop.
Proof.
apply (second_countable_subbasis
         RTop (Union (ImageFamily (fun q => lower_open_ray Rle (Q2R q)))
                     (ImageFamily (fun q => upper_open_ray Rle (Q2R q))))).
2: {
  apply countable_union2;
  now apply countable_img, countable_type_ensemble, Q_countable.
}
apply RTop_subbasis_rational_rays.
Qed.

Lemma rationals_dense_in_RTop :
  @dense RTop (Im Full_set Q2R).
Proof.
  eapply meets_every_nonempty_open_nbhd_basis_equiv_dense.
  { apply (fun x => RTop_metrization x). }
  intros x U [] _.
  destruct (rationals_dense_in_reals (x - r) (x + r)) as [q].
  { lra. }
  exists (Q2R q).
  split.
  - apply Im_def.
    constructor.
  - do 2 red.
    constructor.
    unfold R_metric.
    apply Rabs_def1; lra.
Qed.

Lemma RTop_separable : separable RTop.
Proof.
  exists (Im Full_set Q2R); split.
  2: exact rationals_dense_in_RTop.
  apply countable_img.
  apply countable_type_ensemble.
  apply Q_countable.
Qed.

Lemma R_metric_unbounded : ~ bounded R_metric Full_set.
Proof.
  intros [x [r Hxr]].
  specialize (Hxr (x + r + r)).
  destruct Hxr as [Hxr].
  { constructor. }
  unfold R_metric, Rabs in Hxr.
  destruct Rcase_abs; lra.
Qed.

Lemma RTop_non_compact : ~ compact RTop.
Proof.
  intros H. red in H.
  (* cover [R] with open intervals of length 2 *)
  pose (F :=
          fun U : Ensemble RTop =>
            exists n : Z, U = [r : R | IZR n < r < IZR n + 2]).
  specialize (H F) as [C HC].
  { intros U HU. destruct HU as [n HU]; subst U.
    apply R_interval_open.
  }
  { apply Extensionality_Ensembles; split.
    { intros ? ?; constructor. }
    intros r0 _.
    exists [r : R | IZR ((Int_part r0) - 1) < r < IZR ((Int_part r0) - 1) + 2].
    { eexists; reflexivity. }
    constructor.
    pose proof (base_fp r0) as [].
    rewrite <- Z_R_minus.
    pose proof (base_Int_part r0); lra.
  }
  destruct HC as [HC_fin [HCF HC_full]].
  apply R_metric_unbounded. cbn in HC_full. rewrite <- HC_full.
  clear HC_full.
  apply bounded_FamilyUnion_Finite; auto.
  1: apply R_metric_is_metric.
  2: constructor; exact 0.
  intros U HU.
  apply HCF in HU. clear C HC_fin HCF.
  destruct HU as [n HU]; subst U; clear F.
  exists (IZR n + 1), 1. intros r [Hr].
  constructor. unfold R_metric, Rabs.
  destruct Rcase_abs; lra.
Qed.

From Coq Require Import Reals.Ratan Lra Logic.IndefiniteDescription.
From ZornsLemma Require Import Quotients.
From Topology Require Import ProductTopology AdjunctionSpace SubspaceTopology RTopology RFuncContinuity Homeomorphisms.

Section RealLemmas.

Lemma Rabs_le_1 : forall x y, y >= 0 -> Rabs x <= y -> -y <= x <= y.
Proof.
intros.
destruct (classic (x < 0));
  rewrite Rabs_left in H0 + rewrite Rabs_right in H0; lra.
Qed.

Lemma Rdiv_le_mult : forall x y z, y > 0 -> x / y <= z <-> x <= y * z.
Proof.
intros.
split; intro.
- eapply Rmult_le_reg_r.
  + apply Rinv_0_lt_compat.
    exact H.
  + replace (y * z * /y) with z; trivial.
    rewrite Rmult_comm, <- Rmult_assoc, Rinv_l;
      lra.
- unfold Rdiv.
  eapply Rmult_le_reg_r.
  + eassumption.
  + rewrite Rmult_assoc, Rinv_l, Rmult_1_r; lra.
Qed.

Lemma Rdiv_ge_mult : forall x y z, y > 0 -> z <= x / y <-> y * z <= x.
Proof.
intros.
split; intro.
- cut (y * z <= x); try lra.
  eapply Rmult_le_reg_r.
  + apply Rinv_0_lt_compat in H.
    exact H.
  + replace (y * z * /y) with z.
    * lra.
    * rewrite Rmult_comm, <- Rmult_assoc, Rinv_l;
      lra.
- cut (z <= x * / y); try lra.
  eapply Rmult_le_reg_r.
  + eassumption.
  + rewrite Rmult_assoc, Rinv_l; lra.
Qed.

Lemma Rdiv_lt_mult : forall x y z, y > 0 -> x / y < z <-> x < y * z.
Proof.
intros.
split; intro.
- eapply Rmult_lt_reg_r.
  + apply Rinv_0_lt_compat.
    exact H.
  + replace (y * z * /y) with z; trivial.
    rewrite Rmult_comm, <- Rmult_assoc, Rinv_l;
      lra.
- unfold Rdiv.
  eapply Rmult_lt_reg_r.
  + eassumption.
  + rewrite Rmult_assoc, Rinv_l; lra.
Qed.

Lemma Rdiv_gt_mult : forall x y z, y > 0 -> x / y > z <-> x > y * z.
Proof.
intros.
split; intro.
- eapply Rmult_lt_reg_r.
  + apply Rinv_0_lt_compat.
    exact H.
  + replace (y * z * /y) with z; trivial.
    rewrite Rmult_comm, <- Rmult_assoc, Rinv_l;
      lra.
- unfold Rdiv.
  eapply Rmult_lt_reg_r.
  + eassumption.
  + rewrite Rmult_assoc, Rinv_l; lra.
Qed.

Lemma Rmin_l_r : forall x y z, z < Rmin x y -> z < x /\ z < y.
Proof.
intros.
pose proof (Rmin_l x y).
pose proof (Rmin_r x y).
lra.
Qed.

Lemma Rmax_l_gt : forall x y z : R, z < x -> z < Rmax x y.
Proof.
intros.
destruct (classic (y <= x)).
- now rewrite Rmax_left.
- rewrite Rmax_right; lra.
Qed.

Lemma Rsqr_sum_1_bound_l: forall x y, x²+y²=1 -> -1 <= x <= 1.
Proof.
intros.
apply Rabs_le_1; try lra.
rewrite <- Rabs_R1.
apply Rsqr_le_abs_0.
unfold Rsqr at 2.
pose proof (Rle_0_sqr y).
lra.
Qed.

Lemma Rsqr_sum_1_bound_r: forall x y, x²+y²=1 -> -1 <= y <= 1.
Proof.
intros.
rewrite Rplus_comm in H.
now apply Rsqr_sum_1_bound_l in H.
Qed.

End RealLemmas.

Section TrigLemmas.

Lemma sin_neg_bound : forall x, 0 < x <= 2 * PI -> sin x <= 0 -> x >= PI.
Proof.
intros.
apply NNPP. intro.
assert (x <= PI) by lra.
apply sin_ge_0 in H2; try lra.
assert (sin x = 0) by lra.
Search (sin _ = 0).
destruct (classic (x <= PI / 2)).
- apply (f_equal asin) in H3.
  rewrite asin_0, asin_sin in H3;
    lra.
- assert (PI / 2 <= x <= PI) by lra.
  apply (f_equal asin) in H3.
  rewrite <- sin_PI_x, asin_sin, asin_0 in H3; lra.
Qed.

Lemma sin_pos_bound : forall x, 0 < x <= 2 * PI -> sin x > 0 -> x < PI.
Proof.
intros.
apply NNPP. intro.
assert (PI <= x) by lra.
apply sin_le_0 in H2; try lra.
Qed.

Lemma cos_2PI : forall x, cos (2 * PI + x) = cos x.
Proof.
intro.
replace (2 * PI + x) with (x + PI + PI) by lra.
rewrite neg_cos, neg_cos.
lra.
Qed.

Lemma cos_2PI_neg : forall x, cos (2 * PI - x) = cos x.
Proof.
intro.
unfold Rminus.
now rewrite cos_2PI, cos_neg.
Qed.

Lemma sin_2PI : forall x, sin (2 * PI + x) = sin x.
Proof.
intro.
replace (2 * PI + x) with (x + PI + PI) by lra.
rewrite neg_sin, neg_sin.
lra.
Qed.

Lemma sin_2PI_neg : forall x, sin (2 * PI - x) = - sin x.
Proof.
intro.
unfold Rminus.
now rewrite sin_2PI, sin_neg.
Qed.

Lemma acos_decreasing_1 (x y : R) : -1 <= x <= 1 -> -1 <= y <= 1 -> x < y -> acos y < acos x.
Proof.
intros.
destruct (acos_bound x), (acos_bound y).
apply cos_decreasing_0; trivial.
now rewrite cos_acos, cos_acos.
Qed.

Lemma asin_increasing_1 (x y : R) : -1 <= x <= 1 -> -1 <= y <= 1 -> x < y -> asin x < asin y.
Proof.
intros.
destruct (asin_bound x), (asin_bound y).
apply sin_increasing_0; trivial.
now rewrite sin_asin, sin_asin.
Qed.

Lemma acos_inj: forall x y : R, -1 <= x <= 1 -> -1 <= y <= 1 -> acos x = acos y -> x = y.
Proof.
intros.
now rewrite <- (cos_acos x),  <- (cos_acos y), H1.
Qed.

Lemma acos_gt_0: forall x : R, -1 <= x < 1 -> 0 < acos x.
Proof.
intros.
destruct (acos_bound x).
cut (acos x <> 0); try lra.
rewrite <- acos_1.
intro.
apply acos_inj in H2; lra.
Qed.

Lemma asin_gt_0: forall x : R, 0 < x <= 1 -> 0 < asin x.
Proof.
intros.
rewrite <- asin_0.
apply asin_increasing_1; lra.
Qed.

End TrigLemmas.

Definition S1_Ensemble := [s : @ProductTopology2 RTop RTop | let (x, y) := s in x² + y² = 1].
Definition S1 := SubspaceTopology S1_Ensemble.
Definition UnitInterval_Ensemble := [x : RTop | 0 <= x <= 1].
Definition UnitInterval := SubspaceTopology [x : RTop | 0 <= x <= 1].
Definition U0 : UnitInterval.
refine (exist _ 0 _).
constructor.
lra.
Defined.

Definition U1 : UnitInterval.
refine (exist _ 1 _).
constructor.
lra.
Defined.

Definition ClosedUnitInterval := AdjunctionSpace (Couple U0 U1).

Lemma Singleton_neq_Couple {T : Type} : forall x y z : T, x <> y -> Singleton z <> Couple x y.
Proof.
intros x y z H H0.
destruct (classic (x = z)).
- subst.
  contradict H.
  assert (In (Couple z y) y) by constructor.
  rewrite <- H0 in H.
  now destruct H.
- contradict H1.
  assert (In (Couple x y) x) by constructor.
  rewrite <- H0 in H1.
  now destruct H1.
Qed.

Lemma Singleton_neq_Couple_U0_U1 : forall x, Singleton x <> Couple U0 U1.
Proof.
intro.
apply Singleton_neq_Couple.
injection.
lra.
Qed.

Definition f1 (x y : R) : R :=
  if (Rle_lt_dec y 0) then 1 - acos x / (2 * PI) else acos x / (2 * PI).

Lemma f1_helper : forall x : R * R, In S1_Ensemble x ->
  In UnitInterval_Ensemble ((uncurry f1) x).
Proof.
intros [x y] [H].
unfold f1, uncurry.
pose proof PI_RGT_0.
destruct (acos_bound x).
cut (0 <= acos x / (2 * PI) <= 1);
  constructor.
- destruct (Rle_lt_dec y 0); lra.
- apply Rdiv_ge_mult; lra.
- apply Rdiv_le_mult; lra.
Qed.

Definition f (x: point_set S1) : point_set ClosedUnitInterval :=
  quotient_projection _ (exist _ ((uncurry f1) (proj1_sig x)) (f1_helper _ (proj2_sig x))).

Definition f_inv1 (S: Ensemble UnitInterval) : (R * R).
destruct (DecidableDec.decidable_dec _ (classic (S = Couple U0 U1))).
- exact (1, 0).
- destruct (DecidableDec.decidable_dec _ (classic (exists x, S = Singleton x))).
  + exact (cos ((proj1_sig (proj1_sig (constructive_indefinite_description _ e))) * (2 * PI)),
                 sin ((proj1_sig (proj1_sig (constructive_indefinite_description _ e))) * (2 * PI))).
  + exact (0, 0).
Defined.

Lemma f_inv1_def : forall x : UnitInterval,
  f_inv1 (equiv_class (SpaceAdjunction (Couple U0 U1)) x) = (cos ((proj1_sig x) * (2 * PI)), sin ((proj1_sig x) * (2 * PI))).
Proof.
intros.
unfold f_inv1.
match goal with
| [ |- (if ?X then _ else _) = _ ] => destruct X
end.
- destruct (SpaceAdjunction_equiv_class_cases (Couple U0 U1) x) as [[? ?] | ?].
  + contradict e.
    rewrite H0.
    apply Singleton_neq_Couple_U0_U1.
  + destruct H.
    * now rewrite Rmult_0_l, cos_0, sin_0.
    * replace (2 * PI) with (PI + PI) by lra.
      rewrite Rmult_1_l, neg_cos, neg_sin, cos_PI, sin_PI.
      f_equal; lra.
- match goal with
  | [ |- (match ?X with | _ => _ end) = _ ] => destruct X
  end.
  + match goal with
    | [ |- (cos (proj1_sig (proj1_sig ?X) * (2 * PI)), _) = _ ] => destruct X
    end.
    simpl.
    destruct (SpaceAdjunction_equiv_class_cases (Couple U0 U1) x) as [[? ?] | ?].
    * rewrite H0 in e0.
      apply Singleton_injective in e0.
      now subst.
    * destruct H;
         symmetry in e0;
         contradict e0;
         rewrite SpaceAdjunction_equiv_class_S;
         apply Singleton_neq_Couple_U0_U1 +
         left + right.
  + contradict n0.
    destruct (SpaceAdjunction_equiv_class_cases (Couple U0 U1) x) as [[? ?] | ?].
    * now exists x.
    * destruct H; rewrite SpaceAdjunction_equiv_class_S in n;
        left + right + easy.
Qed.

Lemma f_inv1_helper (S: Ensemble UnitInterval) : In (equiv_classes (SpaceAdjunction (Couple U0 U1))) S ->
  In S1_Ensemble (f_inv1 S).
Proof.
intros [? ? ? ?].
subst.
rewrite f_inv1_def.
constructor.
now rewrite Rplus_comm, sin2_cos2.
Defined.

Definition f_inv (s1 : point_set ClosedUnitInterval) : point_set S1 :=
  exist _ (f_inv1 (proj1_sig s1)) (f_inv1_helper _ (proj2_sig s1)).

Lemma f1_ext_continuous_impl : forall s1,
  @continuous_at (@ProductTopology2 RTop RTop) RTop (uncurry (fun x y => if (Rle_lt_dec x (-1)) then 1/2 else f1 x y)) (proj1_sig s1) ->
  continuous_at f s1.
Proof.
intros.
intros S HS.
unfold f.
change (neighborhood
  (inverse_image
     (fun x1 : S1 =>
      quotient_projection (SpaceAdjunction (Couple U0 U1))
        ((fun x1 => exist (In UnitInterval_Ensemble)
           (uncurry f1 (proj1_sig x1))
           (f1_helper (proj1_sig x1) (proj2_sig x1))) x1)) S) s1).
apply continuous_composition_at; trivial.
- apply continuous_func_continuous_everywhere, quotient_projection_continuous.
- intros U [? [[? ?] ?]].
  eapply subspace_open_char in H0.
  destruct H0, H0.
  rewrite H3 in H1.
  destruct H1.
  unfold subspace_inc in H1.
  simpl in H1.
  assert (neighborhood x0 (uncurry (fun x y : R => if (Rle_lt_dec x (-1)) then 1/2 else f1 x y) (proj1_sig s1))).
  { econstructor.
    split; [split | intros ? H4; exact H4]; trivial.
    unfold uncurry.
    destruct s1, x1.
    simpl in *.
    pose proof PI_RGT_0.
    assert (-1 <= p <= 1).
    { destruct i.
      eapply Rsqr_sum_1_bound_l; eassumption. }
    destruct (Rle_lt_dec p (-1)); trivial.
    assert (p = -1) by lra.
    subst.
    cut (f1 (-1) p0 = 1/2).
    + intro.
      now rewrite <- H3.
    + unfold f1.
      replace (-1) with (-(1)) by trivial.
      rewrite acos_opp, acos_1, Rminus_0_r, Rmult_comm.
      unfold Rdiv.
      rewrite Rinv_mult_distr, <- Rmult_assoc, Rinv_r; try lra.
      destruct (Rle_lt_dec p0 0); lra. }
  apply H in H4.
  assert (@neighborhood S1 (inverse_image (fun z => (uncurry (fun x y : R => if (Rle_lt_dec x (-1)) then 1/2 else f1 x y))
                           (@subspace_inc (@ProductTopology2 RTop RTop) S1_Ensemble z)) x0) s1).
  { apply continuous_composition_at; trivial.
    - apply continuous_func_continuous_everywhere, subspace_inc_continuous.
    - unfold subspace_inc.
      destruct H4, H4, H4.
      econstructor.
      split;
        [ split | intros ? HH; exact HH];
        trivial.
      destruct s1, x2; simpl in *.
      assert (-1 <= p <= 1).
      { destruct i.
        eapply Rsqr_sum_1_bound_l; eassumption. }
      destruct (Rle_lt_dec p (-1)); trivial.
      assert (p = -1) by lra.
      subst.
      apply H5 in H6.
      destruct H6.
      unfold uncurry in H3.
      destruct (Rle_lt_dec (-1) (-1)); trivial.
      lra. }
  destruct H5, H5, H5.
  econstructor.
  split.
  + split; eassumption.
  + red. intros.
    apply H6 in H8.
    constructor.
    apply H2.
    rewrite H3.
    constructor.
    destruct H8.
    unfold subspace_inc in *.
    destruct x2, x2.
    assert (-1 <= p <= 1).
    { destruct i.
      eapply Rsqr_sum_1_bound_l; eassumption. }
    simpl in *.
    pose proof PI_RGT_0.
    destruct (Rle_lt_dec p (-1)); trivial.
    cut (f1 p p0 = 1/2).
    { intro. now rewrite H11. }
    assert (p = -1) by lra.
    subst.
    unfold f1, uncurry.
    replace (-1) with (-(1)) by trivial.
    rewrite acos_opp, acos_1, Rminus_0_r.
    unfold Rdiv.
    rewrite (Rmult_comm 2), Rinv_mult_distr, <- Rmult_assoc, Rinv_r, Rmult_1_l; try lra.
    destruct (Rle_lt_dec p0 0); lra.
Qed.

Lemma f1_continuous_impl : forall s1,
  -1 <= fst (proj1_sig s1) ->
  @continuous_at (@ProductTopology2 RTop RTop) RTop (uncurry f1) (proj1_sig s1) ->
  continuous_at f s1.
Proof.
intros.
intros S HS.
unfold f.
change (neighborhood
  (inverse_image
     (fun x1 : S1 =>
      quotient_projection (SpaceAdjunction (Couple U0 U1))
        ((fun x1 => exist (In UnitInterval_Ensemble)
           (uncurry f1 (proj1_sig x1))
           (f1_helper (proj1_sig x1) (proj2_sig x1))) x1)) S) s1).
apply continuous_composition_at; trivial.
- apply continuous_func_continuous_everywhere, quotient_projection_continuous.
- intros U [? [[? ?] ?]].
  eapply subspace_open_char in H1.
  destruct H1, H1.
  rewrite H4 in H2.
  destruct H2.
  unfold subspace_inc in H2.
  simpl in H2.
  assert (neighborhood x0 (uncurry f1 (proj1_sig s1))).
  { esplit. split. split. exact H1.
    unfold uncurry.
    now destruct s1, x1.
    now intro. }
  apply H0 in H5.
  assert (@neighborhood S1 (inverse_image 
    (fun z => (uncurry f1) (subspace_inc S1_Ensemble z)) x0) s1).
  { apply continuous_composition_at; trivial.
    - apply continuous_func_continuous_everywhere, subspace_inc_continuous.
    - unfold subspace_inc.
      destruct H5, H5, H5.
      esplit.
      + split.
        * split. exact H1.
          now destruct s1, x2.
        * now intro. }
  destruct H6, H6, H6.
  esplit.
  + split.
    * split; eassumption.
    * red. intros.
      apply H7 in H9.
      constructor.
      apply H3.
      rewrite H4.
      constructor.
      destruct H9.
      unfold subspace_inc in *.
      now destruct x2, x2.
Qed.

Inductive small_metric_topology_neighborhood_basis {X : Type} (d : X -> X -> R) (x:X) (r_max : R) : Family X :=
  | intro_small_open_ball: forall r:R, 0 < r < r_max ->
    In (small_metric_topology_neighborhood_basis d x r_max) (open_ball d x r).

Lemma small_neighborhood_basis : forall x r, r > 0 ->
  @neighborhood_basis RTop (small_metric_topology_neighborhood_basis R_metric x r) x.
Proof.
intros.
apply open_neighborhood_basis_is_neighborhood_basis.
split; intros.
- destruct H0.
  split.
  + apply metric_space_open_ball_open.
    * apply RTop_metrization.
    * apply R_metric_is_metric.
  + constructor.
    unfold R_metric, f1, uncurry.
    replace (x - x) with 0 by lra.
    rewrite Rabs_R0.
    lra.
- apply RTop_metrization in H0.
  destruct H0, H0, H0, (classic (r0 < r)).
  + exists (open_ball R_metric x r0).
    split; trivial.
    constructor; lra.
  + exists (open_ball R_metric x (r / 2)).
    split; try lra.
    constructor; lra.
    red. intros.
    apply H1.
    unfold open_ball in *.
    destruct H3.
    constructor.
    assert (r <= r0) by lra.
    eapply Rlt_le_trans;
    [ | apply H4].
    eapply Rlt_trans;
    [ apply H3 |].
    lra.
Qed.

Definition Ensemble_Product {X Y : Type} (U : Ensemble X) (V : Ensemble Y) : Ensemble (X*Y) :=
  fun x => In U (fst x) /\ In V (snd x).

Lemma Ensemble_Product_open {X Y : TopologicalSpace} (U : Ensemble X) (V : Ensemble Y) :
open U -> open V -> @open (@ProductTopology2 X Y) (Ensemble_Product U V).
Proof.
intros.
apply ProductTopology2_basis_is_basis.
replace (Ensemble_Product U V) with [p: @ProductTopology2 X Y | let (x,y):=p in (In U x /\ In V y)].
- now constructor.
- extensionality_ensembles;
    now destruct x.
Qed.

Lemma f1_gt_0_continuous_at : forall x, -1 < x < 1 ->
  continuous_at (fun x1 : RTop => acos x1 / (2 * PI) : RTop) x.
Proof.
intros.
apply continuous_at_iff_continuity_pt.
unfold Rdiv.
apply continuity_pt_mult.
- apply derivable_continuous_pt, derivable_pt_acos.
  destruct (acos_bound x).
  pose proof PI_RGT_0.
  lra.
- apply continuity_pt_const.
  now intro.
Qed.

Lemma f1_lt_0_continuous_at : forall x, -1 < x < 1 ->
  continuous_at (fun x1 : RTop => 1 - acos x1 / (2 * PI) : RTop) x.
Proof.
intros.
apply continuous_at_iff_continuity_pt, continuity_pt_minus.
- apply continuity_pt_const.
  now intro.
- now apply continuous_at_iff_continuity_pt, f1_gt_0_continuous_at.
Qed.

Definition UnitInterval_U0_U1: Family UnitInterval := Im
  (Im [r : R | r > 0] (fun r => Union (open_ball R_metric 0 r) (open_ball R_metric 1 r)))
  (inverse_image (@subspace_inc RTop _)).

Definition ClosedUnitInterval_basis: Family ClosedUnitInterval :=
  inverse_image (inverse_image (quotient_projection (SpaceAdjunction (Couple U0 U1)))) UnitInterval_U0_U1.

Lemma ClosedUnitInterval_basis_is_basis : forall s1, proj1_sig s1 = (Couple U0 U1) ->
  @neighborhood_basis _ ClosedUnitInterval_basis s1.
Proof.
intros.
destruct s1.
unfold proj1_sig in H.
subst.
constructor; intros.
- destruct H.
  inversion H.
  destruct H0, H0.
  subst.
  exists (Im (inverse_image (subspace_inc UnitInterval_Ensemble)
       (Union (open_ball R_metric 0 x) (open_ball R_metric 1 x))) (quotient_projection (SpaceAdjunction (Couple U0 U1)))).
  + repeat split.
    * apply quotient_projection_open_iff.
      match goal with
      | [ |- open ?X ] => replace X with 
        (inverse_image (subspace_inc UnitInterval_Ensemble)
                       (Union (open_ball R_metric 0 x) (open_ball R_metric 1 x)))
      end.
      -- apply subspace_inc_continuous.
         apply (@open_union2 RTop); apply metric_space_open_ball_open;
           apply R_metric_is_metric + apply RTop_metrization.
      -- extensionality_ensembles_inv;
           subst; constructor;
           try (econstructor; constructor; now do 2 constructor);
           apply quotient_projection_minimally_collapses_R in H4;
           try apply SpaceAdjunction_equivalence;
           destruct H4; subst;
           try (now repeat constructor);
           destruct H, H;
           [ left | right | left | right];
           destruct H4;
           constructor;
           trivial;
           unfold R_metric;
           simpl;
           rewrite Rminus_0_r + replace (1-1) with 0 by lra;
           now rewrite Rabs_R0.
    * exists U0.
      -- constructor. left. constructor. simpl. unfold R_metric. now rewrite Rminus_0_r, Rabs_R0.
      -- unfold quotient_projection. apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
         rewrite SpaceAdjunction_equiv_class_S; constructor.
    * red. intros.
      inversion H2.
      subst.
      unfold UnitInterval_Ensemble in H3.
      rewrite <- H1 in H3.
      now destruct H3.
- destruct H, H, H.
  apply quotient_projection_continuous, subspace_open_char in H.
  destruct H, H.
  pose proof H1.
  pose proof H1.
  replace (exist
          (fun S : Ensemble UnitInterval =>
           In (equiv_classes (SpaceAdjunction (Couple U0 U1))) S) 
          (Couple U0 U1) i) with (quotient_projection (SpaceAdjunction (Couple U0 U1)) U0) in H3;
  [ | unfold quotient_projection; apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat;
      rewrite SpaceAdjunction_equiv_class_S; constructor ].
  replace (exist
          (fun S : Ensemble UnitInterval =>
           In (equiv_classes (SpaceAdjunction (Couple U0 U1))) S) 
          (Couple U0 U1) i) with (quotient_projection (SpaceAdjunction (Couple U0 U1)) U1) in H4;
  [ | unfold quotient_projection; apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat;
      rewrite SpaceAdjunction_equiv_class_S; constructor ].
  apply (in_inverse_image (quotient_projection (SpaceAdjunction (Couple U0 U1)))) in H3, H4.
  change (inverse_image (quotient_projection (SpaceAdjunction (Couple U0 U1))) x =
     inverse_image (subspace_inc UnitInterval_Ensemble) x0) in H2.
  rewrite H2 in H3, H4.
  destruct H3, H4.
  simpl in H3, H4.
  assert (exists N' : Ensemble RTop,
         In (metric_topology_neighborhood_basis R_metric 0) N' /\ Included N' x0).
  { apply (@neighborhood_basis_cond RTop (metric_topology_neighborhood_basis R_metric 0) 0).
    - apply open_neighborhood_basis_is_neighborhood_basis, RTop_metrization.
    - now apply open_char_neighborhood. }
  destruct H5, H5, H5.
  assert (exists N' : Ensemble RTop,
         In (metric_topology_neighborhood_basis R_metric 1) N' /\ Included N' x0).
  { apply (@neighborhood_basis_cond RTop (metric_topology_neighborhood_basis R_metric 1) 1).
    - apply open_neighborhood_basis_is_neighborhood_basis, RTop_metrization.
    - now apply open_char_neighborhood. }
  destruct H7, H7, H7.
  pose (Rmin r r0) as rm.
  assert (rm > 0).
  { unfold rm. cut (0 < Rmin r r0); try lra. apply Rmin_glb_lt; lra. }
  exists (Im (inverse_image (subspace_inc UnitInterval_Ensemble)
       (Union (open_ball R_metric 0 rm) (open_ball R_metric 1 rm))) (quotient_projection (SpaceAdjunction (Couple U0 U1)))).
  constructor.
  + constructor.
    repeat econstructor.
    {  exact H9. }
    extensionality_ensembles_inv; subst; try now repeat econstructor.
    * constructor.
      destruct (classic (x1 = U0)).
      -- subst. left. constructor. simpl.  unfold R_metric. now rewrite Rminus_0_r, Rabs_R0.
      -- destruct (classic (x1 = U1)).
         ++ subst. right. constructor. simpl. unfold R_metric. replace (1-1) with 0 by lra. now rewrite Rabs_R0. 
         ++ apply SpaceAdjunction_quotient_projection_injective in H12.
            ** subst.
               now do 2 constructor.
            ** intro.
               now destruct H14.
    * destruct (SpaceAdjunction_equiv_class_cases (Couple U0 U1) x1) as [[? ?] | ?].
      -- apply SpaceAdjunction_quotient_projection_injective in H12; trivial.
         subst.
         now repeat constructor.
      -- destruct H10; subst;
         constructor;
         [ left | right ];
         constructor;
         simpl;
         unfold R_metric;
         rewrite Rminus_0_r + replace (1-1) with 0 by lra;
         now rewrite Rabs_R0.
  + red. intros.
    inversion H10.
    subst.
    apply H0.
    cut (In (@inverse_image UnitInterval (AdjunctionSpace (Couple U0 U1))
       (@quotient_projection UnitInterval (SpaceAdjunction (Couple U0 U1))) x) x2); [now intros [?] |].
    change (In (inverse_image (quotient_projection _) x) x2).
    rewrite H2.
    constructor.
    destruct H11, H11, H11;
    apply Rmin_l_r in H11;
    destruct H11;
      apply H6 + apply H8;
      now constructor.
Qed.

Lemma f_continuous: continuous f.
Proof.
apply pointwise_continuity.
intros [[x y] i].
simpl in x, y.
pose proof i.
destruct H.
apply Rsqr_sum_1_bound_l in H.
pose proof i.
destruct H0.
apply Rsqr_sum_1_bound_r in H0.
destruct (classic (x = 1));
[ | destruct (classic (y = 0)) ];
[ | | destruct (Rdichotomy _ _ H2) ].
- subst.
  assert (y² = 0) by (destruct i as [H1]; unfold Rsqr in H1 at 1; lra).
  apply Rsqr_0_uniq in H1.
  subst.
  apply (@continuous_at_neighborhood_basis S1 ClosedUnitInterval f (exist _ (1,0) i) ClosedUnitInterval_basis ).
  + apply ClosedUnitInterval_basis_is_basis.
    unfold f, f1.
    simpl.
    match goal with
    | [ |- equiv_class _ ?X = _ ] => replace X with U1
    end.
    * change (equiv_class (SpaceAdjunction (Couple U0 U1)) U1 = Couple U0 U1).
      apply SpaceAdjunction_equiv_class_S.
      constructor.
    * apply Proj1SigInjective.proj1_sig_injective.
      simpl.
      destruct (Rle_lt_dec 0 0);
        rewrite acos_1;
        lra.
  + intros.
    destruct H1.
    inversion H1.
    subst.
    destruct H2, H2.
    apply open_neighborhood_is_neighborhood.
    * destruct (Rle_lt_dec x (1/2)).
     -- replace (inverse_image f V) with (inverse_image
           (subspace_inc S1_Ensemble)
           (Ensemble_Product [x0 : RTop | cos (x * (2 * PI)) < x0] Full_set)).
         ++ split.
            ** apply subspace_inc_continuous, Ensemble_Product_open.
               --- apply R_upper_beam_open.
               --- apply open_full.
            ** constructor; constructor; constructor. simpl.
               destruct (COS_bound (x * (2 * PI))).
               cut (cos (x * (2 * PI)) <> 1); try lra.
               intro.
               rewrite <- cos_0 in H7.
               pose proof PI_RGT_0.
               apply cos_inj in H7; try lra.
               --- apply Rmult_integral in H7.
                   destruct H7; lra.
               --- apply (Rmult_le_compat_r (2* PI)) in r; try lra.
                   split; try lra.
                   apply Rmult_le_pos; lra.
          ++ extensionality_ensembles_inv; subst.
             ** destruct x0, x0, i.
                simpl in *.
                assert (-1 <= p <= 1) by now apply Rsqr_sum_1_bound_l in y.
                constructor.
                apply (in_inverse_image (quotient_projection (SpaceAdjunction (Couple U0 U1)))).
                simpl.
                rewrite H3.
                constructor.
                simpl in *.
                unfold f1.
                pose proof PI_RGT_0.
                assert (0 < PI * x) by now apply Rmult_lt_0_compat.
                destruct (Rle_lt_dec p0 0); [right | left ]; constructor; unfold R_metric; apply Rabs_def1.
                --- destruct (classic (p= 1)).
                    +++ subst. unfold Rdiv. rewrite acos_1, Rmult_0_l. lra.
                    +++ cut (0 < acos p / (2 * PI)); try lra.
                        apply Rdiv_gt_mult; try lra.
                        rewrite Rmult_0_r, <- acos_1.
                        apply acos_decreasing_1; lra.
                --- cut (acos p / (2 * PI) < x); try lra.
                    apply Rdiv_lt_mult; try lra.
                    destruct (acos_bound p).
                    apply cos_decreasing_0; try lra.
                    +++ replace PI with ((2*PI) * (1/2)) at 2 by lra.
                        apply Rmult_le_compat_l; lra.
                    +++ rewrite Rmult_comm, cos_acos; lra.
                --- rewrite Rminus_0_r.
                    apply Rdiv_lt_mult; try lra.
                    destruct (acos_bound p).
                    apply cos_decreasing_0; try lra.
                    +++ replace PI with ((2*PI) * (1/2)) at 2 by lra.
                        apply Rmult_le_compat_l; lra.
                    +++ rewrite Rmult_comm, cos_acos; lra.
                --- destruct (classic (p= 1)).
                    +++ subst. unfold Rdiv. rewrite acos_1, Rmult_0_l. lra.
                    +++ cut (0 < acos p / (2 * PI)); try lra.
                        apply Rdiv_gt_mult; try lra.
                        rewrite Rmult_0_r.
                        destruct (acos_bound p).
                        cut (acos p <> 0); try lra.
                        rewrite <- acos_1.
                        intro.
                        apply acos_inj in H13; lra.
            ** constructor.
               apply (in_inverse_image (quotient_projection (SpaceAdjunction (Couple U0 U1)))) in H6.
               rewrite H3 in H6.
               destruct x0, x0, H6, i.
               simpl in *.
               pose proof y as y1.
               apply Rsqr_sum_1_bound_l in y1.
               constructor; constructor.
               simpl.
               unfold f1 in H4.
               pose proof PI_RGT_0.
               destruct (Rle_lt_dec p0 0); inversion H4; subst; destruct H8;
                 unfold R_metric in H8; apply Rabs_def2 in H8; destruct H8.
                --- rewrite Rminus_0_r in *.
                    cut (acos p / (2 * PI) <= 1/2); try lra.
                    destruct (acos_bound p).
                    apply Rdiv_le_mult; lra.
                --- assert (acos p / (2 * PI) < x) by lra.
                    rewrite <- (cos_acos p); trivial.
                    destruct (acos_bound p).
                    apply cos_decreasing_1; trivial.
                    +++ apply Rmult_le_pos; lra.
                    +++ replace PI with ((1/2)*(2*PI)) at 2 by lra.
                        apply Rmult_le_compat_r; lra.
                    +++ apply Rdiv_lt_mult in H10; lra.
                --- rewrite <- (cos_acos p); trivial.
                    destruct (acos_bound p).
                    apply cos_decreasing_1; trivial.
                    +++ apply Rmult_le_pos; lra.
                    +++ replace PI with ((1/2)*(2*PI)) at 2 by lra.
                        apply Rmult_le_compat_r; lra.
                    +++ rewrite Rminus_0_r in H8.
                        apply Rdiv_lt_mult in H8; lra.
                --- cut (acos p / (2 * PI) <= 1 / 2); try lra.
                    destruct (acos_bound p).
                    apply Rdiv_le_mult; try lra.
      -- subst.
         replace (inverse_image (subspace_inc [x : RTop | 0 <= x <= 1])
           (Union (open_ball R_metric 0 x) (open_ball R_metric 1 x))) with (@Full_set UnitInterval) in H3.
         ++ replace V with (@Full_set ClosedUnitInterval).
            ** rewrite inverse_image_full. split. apply open_full. constructor.
            ** extensionality_ensembles_inv; subst;
                 [ destruct (quotient_projection_surjective x0) | constructor ].
               rewrite <- H5.
               apply (in_inverse_image (quotient_projection (SpaceAdjunction (Couple U0 U1)))).
               rewrite H3.
               constructor.
         ++ extensionality_ensembles_inv; subst; constructor.
            destruct x0, i.
            simpl.
            destruct (Rle_lt_dec (1/2) x0);
              do 2 constructor;
              unfold R_metric;
              apply Rabs_def1; lra.
- subst.
  assert (x = -1).
  { destruct i.
    unfold Rsqr in H2 at 2.
    assert (x²=1²) by (unfold Rsqr at 2; lra).
    apply Rsqr_eq in H3; lra. }
  subst.
  apply f1_ext_continuous_impl.
  apply (continuous_at_neighborhood_basis (@ProductTopology2 RTop RTop) RTop
        (uncurry (fun x y : R => if Rle_lt_dec x (-1) then 1/2 else f1 x y)) (-1, 0)
        (small_metric_topology_neighborhood_basis R_metric (1 / 2) (1 / 2))).
  { replace (uncurry (fun x y : R => if Rle_lt_dec x (-1) then 1 / 2 else f1 x y) (-1, 0)) with (1 / 2).
    - apply small_neighborhood_basis. lra.
    - unfold f1, uncurry.
      destruct (Rle_lt_dec 0 0); try lra.
      replace (-1) with (-(1)) by trivial.
      rewrite acos_opp, acos_1, Rminus_0_r, Rmult_comm.
      unfold Rdiv.
      pose proof PI_RGT_0.
      destruct (Rle_lt_dec (- (1)) (- (1))); lra. }
  red. intros.
  simpl.
  destruct H2.
  pose proof PI_RGT_0.
  assert (0 < r * PI) by (apply Rmult_lt_0_compat; lra).
  exists (@Ensemble_Product RTop RTop [x : R | x < cos ((2*r - 1) * PI)] [y : R | -sin (r * PI) < y < sin (r * PI)]).
  repeat split.
  + apply Ensemble_Product_open.
    * apply R_lower_beam_open.
    * apply R_interval_open.
  + simpl.
    destruct (COS_bound ((2*r - 1) * PI)).
    cut (cos ((2*r - 1) * PI) <> -(1)); try lra.
    intro.
    cut (r = 0); try lra.
    rewrite cos_sym in H7.
    replace (- ((2*r - 1) * PI)) with (PI - r * (2 * PI)) in H7 by lra.
    apply Ropp_eq_compat in H7.
    rewrite Rtrigo_facts.cos_pi_minus, Ropp_involutive, Ropp_involutive, <- cos_0 in H7.
    apply cos_inj, Rmult_integral in H7; lra + split.
    * apply Rmult_le_pos; lra.
    * rewrite <- Rmult_1_l, <- Rmult_assoc.
      apply Rmult_le_compat_r; lra.
  + simpl.
    cut (0 < sin (r * PI)); try lra.
    rewrite <- sin_0.
    apply sin_increasing_1; try lra.
    unfold Rdiv.
    rewrite Rmult_comm.
    apply Rmult_le_compat_l; lra.
  + simpl.
    rewrite <- sin_0.
    apply sin_increasing_1; try lra.
    unfold Rdiv.
    rewrite Rmult_comm.
    apply Rmult_le_compat_l; lra.
  + destruct x, H5.
    simpl in H5, H6.
    destruct H5, H6.
    unfold f1, uncurry, R_metric.
    pose proof PI_RGT_0.
    destruct (Rle_lt_dec r0 (-1)); [| destruct (Rle_lt_dec r1 0)].
    * replace (1/2-1/2) with 0 by lra.
      now rewrite Rabs_R0.
    * replace (1 - acos r0 / (2 * PI) - 1 / 2) with (1/2 - acos r0 / (2 * PI)) by lra.
      pose proof H5.
      apply Rabs_def1.
      ++ apply acos_decreasing_1 in H5; try lra.
         ** rewrite cos_sym, acos_cos in H5.
            --- unfold Rdiv.
                apply (Rmult_lt_reg_r (2 * PI)); try lra.
                rewrite Rmult_minus_distr_r, Rmult_assoc, Rmult_assoc, Rinv_l; lra.
            --- split; try lra.
                cut ((2 * r - 1) * PI <= 0 * PI); try lra.
                apply Rmult_le_compat_r; lra.
         ** destruct (COS_bound ((2 * r - 1) * PI)).
            lra.
         ** apply COS_bound.
      ++ cut (acos r0 / (2 * PI) < 1/2); try lra.
         unfold Rdiv.
         apply (Rmult_lt_reg_r (2*PI)); try lra.
         rewrite Rmult_assoc, Rinv_l; try lra.
         destruct (acos_bound r0).
         cut (acos r0 <> PI - 0); try lra.
         cut (r0 <> -1).
         { intros.
           intro.
           rewrite <- acos_1, <- acos_opp in H12.
           destruct (COS_bound ((2 * r - 1) * PI)).
           apply acos_inj in H12; lra. }
         apply acos_decreasing_1 in H5; try lra.
         ** destruct (COS_bound ((2 * r - 1) * PI)). lra.
         ** apply COS_bound.
   * assert (0 < PI * r) by (apply Rmult_lt_0_compat; lra).
     apply Rabs_def1.
      ++ cut (acos r0 / (2 * PI) < r + 1 / 2); try lra.
         apply Rdiv_lt_mult; try lra.
         rewrite Rmult_plus_distr_l.
         destruct (acos_bound r0).
         cut (acos r0 <> PI); try lra.
         replace PI with (acos (-1)).
         ** intro.
            destruct (COS_bound ((2 * r - 1) * PI)).
            apply acos_inj in H11; lra.
         ** replace (-1) with (-(1)) by trivial.
            rewrite acos_opp, acos_1. lra.
      ++ cut (1 / 2 - r < acos r0 / (2 * PI)); try lra.
         apply Rdiv_gt_mult; try lra.
         rewrite Rmult_comm, <- Rmult_assoc, Rmult_minus_distr_r.
         replace (1 / 2 * 2 - r * 2) with (-(2 * r - 1)) by lra.
         rewrite cos_sym in H5.
         destruct (COS_bound (- ((2 * r - 1) * PI))).
         apply acos_decreasing_1 in H5; try lra.
         rewrite acos_cos in H5; try lra.
         rewrite Ropp_mult_distr_l, Ropp_minus_distr, Rmult_minus_distr_r, Rmult_1_l.
         split; try lra.
         cut (2 * r * PI <= 1 * PI); try lra.
         apply Rmult_le_compat_r; lra.
- apply f1_continuous_impl; simpl; try lra.
  unfold f1, uncurry.
  apply (continuous_at_neighborhood_basis (@ProductTopology2 RTop RTop) RTop (uncurry f1) (x, y)
         (small_metric_topology_neighborhood_basis R_metric (f1 x y) (-y / 2))).
  { apply small_neighborhood_basis. lra. }
  intros.
  destruct H4.
  assert (neighborhood
      (inverse_image (fun x1 : RTop => 1 - acos x1 / (2 * PI))
         (open_ball R_metric (1 - acos x / (2 * PI)) r)) x).
  { apply f1_lt_0_continuous_at.
    - cut (x <> -1); try lra.
      intro.
      subst.
      contradict H2.
      apply Rsqr_eq_0.
      destruct i.
      unfold Rsqr in H2 at 1.
      lra.
    - apply open_neighborhood_is_neighborhood, RTop_metrization.
      now constructor. }
  replace (open_ball R_metric (f1 x y) r) with
          (open_ball R_metric (1 - acos x / (2 * PI)) r) by
    (unfold f1; now destruct (Rle_lt_dec y 0); try lra).
  destruct H5, H5, H5.
  exists (@Ensemble_Product RTop RTop x0 [y : RTop | y < 0]).
  repeat split; trivial.
  + now apply Ensemble_Product_open, R_lower_beam_open.
  + destruct H8, x1.
    simpl in *.
    apply H6 in H8.
    destruct H9, H8, H8.
    unfold f1, uncurry.
    destruct (Rle_lt_dec p0 0); lra.
- apply f1_continuous_impl; simpl; try lra.
  unfold f1, uncurry.
  apply (continuous_at_neighborhood_basis (@ProductTopology2 RTop RTop) RTop (uncurry f1) (x, y)
         (small_metric_topology_neighborhood_basis R_metric (f1 x y) (y / 2))).
  { apply small_neighborhood_basis. lra. }
  intros.
  destruct H4.
  assert (neighborhood
      (inverse_image (fun x1 : RTop => acos x1 / (2 * PI))
         (open_ball R_metric (acos x / (2 * PI)) r)) x).
  { apply f1_gt_0_continuous_at.
    - cut (x <> -1); try lra.
      intro.
      subst.
      contradict H2.
      apply Rsqr_eq_0.
      destruct i as [i].
      unfold Rsqr in i at 1.
      lra.
    - apply open_neighborhood_is_neighborhood, RTop_metrization.
      now constructor. }
  replace (open_ball R_metric (f1 x y) r) with
          (open_ball R_metric (acos x / (2 * PI)) r) by
    (unfold f1; now destruct (Rle_lt_dec y 0); try lra).
  destruct H5, H5, H5.
  exists (@Ensemble_Product RTop RTop x0 [y : RTop | y > 0]).
  repeat split; trivial.
  + now apply Ensemble_Product_open, R_upper_beam_open.
  + destruct H8, x1.
    simpl in *.
    apply H6 in H8.
    destruct H9, H8, H8.
    unfold f1, uncurry.
    destruct (Rle_lt_dec p0 0); lra.
Qed.

Definition R2_0_1: Family (@ProductTopology2 RTop RTop) := 
  (Im [r : R | r < 1] (fun r => Ensemble_Product [x : R | r < x] Full_set)).

Definition S1_basis_0: Family S1 :=
 Im R2_0_1 (inverse_image (subspace_inc _)).

Inductive small_metric_topology_neighborhood_basis2 (X : TopologicalSpace) (d : X -> X -> R) (x y : X) (r_max : R)
 : Family (@ProductTopology2 X X) :=
  intro_small_open_ball2 : forall r : R,
                           0 < r < r_max ->
                           In (small_metric_topology_neighborhood_basis2 X d x y r_max)
                           (Ensemble_Product (open_ball d x r) (open_ball d y r)).

Lemma open_ball_included_smaller : forall x r1 r2,
  r1 <= r2 -> Included (open_ball R_metric x r1) (open_ball R_metric x r2).
Proof.
intros. red. intros.
destruct H0.
constructor.
unfold R_metric in *.
lra.
Qed.

Lemma small_neighborhood_basis2:
  forall x y r : R, r > 0 -> neighborhood_basis (small_metric_topology_neighborhood_basis2 RTop R_metric x y r) (x, y).
Proof.
intros.
constructor; intros.
- destruct H0.
  apply open_neighborhood_is_neighborhood.
  split.
  + apply Ensemble_Product_open; apply metric_space_open_ball_open;
      apply RTop_metrization + apply R_metric_is_metric.
  + repeat constructor; simpl;
      unfold R_metric;
      now rewrite Rminus_eq_0, Rabs_R0.
- destruct H0, H0, H0.
  assert (exists U : Ensemble (ProductTopology2 RTop RTop), In (ProductTopology2_basis RTop RTop) U /\ Included U x0 /\ In U (x, y))
    by now apply ProductTopology2_basis_is_basis.
  destruct H3, H3, H3, H4, H6, H6.
  assert ((exists U1 : Ensemble RTop, In (small_metric_topology_neighborhood_basis R_metric x r) U1 /\ Included U1 U) /\
          (exists V1 : Ensemble RTop, In (small_metric_topology_neighborhood_basis R_metric y r) V1 /\ Included V1 V)).
  { split; apply small_neighborhood_basis; try lra;
      [ exists U | exists V];
      repeat split; trivial;
      red; tauto. }
  destruct H8, H8, H8, H8, H9, H9, H9.
  pose (Rmin r0 r1) as rm.
  assert (0 < rm < r).
  { split.
    - apply Rmin_glb_lt; try lra.
    - pose proof (Rmin_r r0 r1).
      unfold rm. lra. }
  exists (Ensemble_Product (open_ball R_metric x rm) (open_ball R_metric y rm)).
  repeat constructor; try lra.
  red. intros.
  apply H1, H4.
  destruct x1.
  destruct H13.
  simpl in H13, H14.
  assert (rm <= r0) by apply Rmin_l.
  assert (rm <= r1) by apply Rmin_r.
  repeat constructor;
    apply H10 + apply H11;
    eapply open_ball_included_smaller;
    eassumption.
Qed.

Lemma S1_basis_0_is_basis : forall s1, proj1_sig s1 = (1, 0) ->
  @neighborhood_basis _ S1_basis_0 s1.
Proof.
intros.
destruct s1.
simpl in H.
subst.
destruct i as [i].
split; intros.
- destruct H, H, H.
  subst.
  apply open_neighborhood_is_neighborhood.
  split.
  + apply subspace_inc_continuous.
    change (@open (ProductTopology2 RTop RTop) (@Ensemble_Product RTop RTop [x0 : RTop | x < x0] (@Full_set RTop))).
    apply Ensemble_Product_open.
    * apply R_upper_beam_open.
    * apply open_full.
  + constructor. simpl.
    now repeat constructor.
- destruct H, H, H.
  apply subspace_open_char in H.
  destruct H, H.
  subst.
  destruct H1.
  simpl in H1.
  assert (exists V : Ensemble (ProductTopology2 RTop RTop), In (small_metric_topology_neighborhood_basis2 RTop R_metric 1 0 1) V /\ Included V x0).
  { apply small_neighborhood_basis2, open_neighborhood_is_neighborhood; try lra.
    now split. }
  destruct H2, H2, H2.
  pose (Rmax (sqrt (1 - r²)) (1 - r)) as r1.
  assert (0 < 1 - r² < 1).
  { split.
    - cut (r² < 1²); unfold Rsqr;
      try apply neg_pos_Rsqr_lt; lra.
    - cut (0 < r²); unfold Rsqr;
      try apply Rsqr_pos_lt; lra. }
  assert (0 < r1 < 1).
  { split.
    - apply Rmax_l_gt, sqrt_lt_R0; lra.
    - apply Rmax_lub_lt; try lra.
      rewrite <- (sqrt_Rsqr 1) at 2; try lra.
      replace (1²) with 1 by (unfold Rsqr; lra).
      apply sqrt_lt_1_alt; lra. }
  exists (inverse_image (@subspace_inc (ProductTopology2 RTop RTop) _) (Ensemble_Product [x : R | r1 < x] Full_set)).
  split.
  + repeat econstructor.
    lra.
  + red. intros x H6.
    destruct H6, H6, H6.
    clear H7.
    apply H0.
    constructor.
    apply H3.
    destruct x, x, i0.
    simpl in H6.
    pose proof y.
    apply Rsqr_sum_1_bound_l in H7.
    assert (sqrt (1 - r²) <= r1) by apply Rmax_l.
    assert (1 - r <= r1) by apply Rmax_r.
    constructor;
      simpl;
      constructor;
      unfold R_metric.
    * rewrite Rabs_left1; lra.
    * rewrite Rminus_0_r, <- (Rabs_pos_eq r); try lra.
      apply Rsqr_lt_abs_0.
      cut (1 - r² < p²); try lra.
      apply sqrt_lt_0_alt.
      rewrite sqrt_Rsqr; lra.
Qed.

Lemma f_inv_continuous: continuous f_inv.
Proof.
apply pointwise_continuity.
intro.
unfold f_inv.
destruct (classic (x=quotient_projection _ U0)).
- subst.
  eapply continuous_at_neighborhood_basis with (NB:=S1_basis_0).
  { apply S1_basis_0_is_basis. simpl.
    rewrite f_inv1_def.
    simpl.
    now rewrite Rmult_0_l, cos_0, sin_0. }
  intros.
  destruct H.
  subst.
  destruct H, H.
  subst.
  destruct (classic (x < -1)).
  + replace (inverse_image (subspace_inc S1_Ensemble)
          (Ensemble_Product [x0 : R | x < x0] Full_set)) with (@Full_set S1).
    * rewrite inverse_image_full.
      apply open_neighborhood_is_neighborhood.
      repeat constructor.
      apply open_full.
    * extensionality_ensembles; constructor.
      destruct x0, x0, i.
      repeat constructor.
      simpl.
      apply Rsqr_sum_1_bound_l in y.
      lra.
  + assert (x >= -1) by lra.
    clear H0.
    pose proof PI_RGT_0.
    rewrite <- inverse_image_composition.
    match goal with
    | [ |- neighborhood ?X _ ] => 
      replace X with
        (Im
        (inverse_image (subspace_inc UnitInterval_Ensemble)
        (Union (open_ball R_metric 0 ((acos x) / (2 * PI)))
               (open_ball R_metric 1 ((acos x) / (2 * PI))))) (quotient_projection (SpaceAdjunction (Couple U0 U1))))
    end.
    apply open_neighborhood_is_neighborhood.
    split.
    * apply saturated_subset_quotient_projection_open.
      -- apply SpaceAdjunction_equivalence.
      -- intros.
         red. intros.
         constructor.
         destruct H2, H3.
         red in H2.
         destruct x0, x1, i, i0.
         simpl in *.
         destruct H3 as [? | [? ?]];
           [ apply Subset.subset_eq in H3 | inversion H3; inversion H4 ];
           destruct H2, H2; simpl in *; subst;
           try (now repeat constructor);
           [ right | right | left | left ];
           constructor;
           unfold R_metric;
           rewrite Rminus_0_r + replace (1-1) with 0 by lra;
           rewrite Rabs_R0;
           apply Rdiv_lt_0_compat;
           try apply acos_gt_0; lra.
      -- apply subspace_inc_continuous.
         apply (@open_union2 RTop); apply metric_space_open_ball_open;
           apply RTop_metrization + apply R_metric_is_metric.
    * exists U0; repeat constructor.
      unfold R_metric.
      simpl.
      rewrite Rminus_0_r, Rabs_R0.
      apply Rdiv_lt_0_compat; try lra.
      apply acos_gt_0; lra.
    * extensionality_ensembles_inv; subst.
      -- constructor.
         simpl.
         unfold subspace_inc in H2.
         constructor; constructor.
         destruct x1, i.
         simpl in *.
         unfold R_metric in H2.
         rewrite Rminus_0_r, Rabs_pos_eq in H2; try lra.
         rewrite f_inv1_def.
         simpl.
  rewrite <- (cos_acos x); try lra.
  destruct (acos_bound x).
  apply cos_decreasing_1; trivial.
  ** apply Rmult_le_pos; lra.
  ** cut (x0 * (2 * PI) < acos x); try lra.
     rewrite Rmult_comm.
     apply Rdiv_gt_mult; lra.
  ** rewrite Rmult_comm.
     apply Rdiv_gt_mult; lra.
  -- constructor.
     simpl.
     unfold subspace_inc, R_metric in H2.
     rewrite f_inv1_def.
     rewrite Rabs_left1 in H2;
     [ | destruct x1, i; simpl in *; lra ].
     constructor; constructor.
     simpl.
        rewrite Ropp_minus_distr in H2.
        apply Rdiv_gt_mult in H2; try lra.
        rewrite Rmult_minus_distr_l, Rmult_1_r in H2.
        destruct x1, i.
        simpl in *.
        assert (PI + (PI - acos x) < x0 * (2 * PI)) by lra.
        rewrite <- acos_opp in H3.
        destruct (acos_bound (-x)).
        apply cos_increasing_1 in H3; try lra.
        ** rewrite Rtrigo_facts.cos_pi_plus, cos_acos in H3; lra.
        ** replace (2 * PI) with (1 * (2 * PI)) at 2 by lra.
           apply Rmult_le_compat_r; lra.
  -- destruct (quotient_projection_surjective x0).
     subst.
     simpl in *.
     rewrite f_inv1_def in H4.
     simpl in H4.
     econstructor; [| reflexivity].
     constructor.
     destruct x1, i.
     simpl in *.
     destruct (classic (x0 <= 1/2)).
     ++ left.
        constructor.
        unfold R_metric.
        rewrite Rminus_0_r, Rabs_pos_eq; try lra.
        apply Rdiv_gt_mult; try lra.
        destruct (acos_bound x).
        apply cos_decreasing_0; try lra.
        ** apply Rmult_le_pos; lra.
        ** replace PI with (2 * PI * (1 / 2)) at 2 by lra.
           apply Rmult_le_compat_l; lra.
        ** rewrite cos_acos; try lra.
           now replace (2 * PI * x0) with (x0 * (2 * PI)) by lra.
     ++ right.
        constructor.
        unfold R_metric.
        replace (Rabs (x0 - 1)) with (1 - x0).
        ** apply Rdiv_gt_mult; try lra.
        destruct (acos_bound x).
        apply cos_decreasing_0; try lra.
        --- apply Rmult_le_pos; lra.
        --- replace PI with (2 * PI * (1 / 2)) at 2 by lra.
            apply Rmult_le_compat_l; lra.
        --- rewrite cos_acos; try lra.
            replace (2 * PI * (1 - x0)) with (PI + (PI + - (x0 * (2 * PI)))) by lra.
            now rewrite Rtrigo_facts.cos_pi_plus, Rtrigo_facts.cos_pi_plus, Ropp_involutive,cos_neg.
        ** destruct (classic (x0 = 1)).
           --- subst.
               replace (1-1) with 0 by lra.
               now rewrite Rabs_R0.
           --- rewrite Rabs_left; lra.
- apply continuous_at_open_neighborhoods.
  intros.
  destruct H0.
  apply subspace_open_char in H0.
  destruct H0, H0.
  subst.
  destruct H1.
  simpl in H1.
  destruct (quotient_projection_surjective x),
           (SpaceAdjunction_equiv_class_cases (Couple U0 U1) x1); subst.
  + simpl in H1.
    destruct H3.
    assert (proj1_sig x1 <> proj1_sig U0 /\ proj1_sig x1 <> proj1_sig U1).
    { split; intro; apply Proj1SigInjective.proj1_sig_injective in H4; subst; contradict H2; left + right. }
    simpl in H4.
    destruct H4.
    assert (continuous_at (quotient_projection (SpaceAdjunction (Couple U0 U1)): UnitInterval -> ClosedUnitInterval) x1) by
      apply continuous_func_continuous_everywhere, quotient_projection_continuous.
    rewrite <- inverse_image_composition.
    simpl.
    rewrite f_inv1_def in H1; trivial.
    destruct x1, i.
    simpl in H1, H4, H5.
    assert (0 < x < 1) by lra.
    assert (exists r, 0 < r < 1 - x /\ r < x /\ r < 1/4 /\
      Included [z : ProductTopology2 RTop RTop | (cos (x * (2 * PI)) - fst z)² + (sin (x * (2 * PI)) - snd z)² < 4 * (sin (r * PI))²] x0).
    { pose (Rmin (Rmin x (1 - x)) (1 / 4)) as rm.
      assert (exists V : Ensemble (ProductTopology2 RTop RTop), In (small_metric_topology_neighborhood_basis2 RTop R_metric (cos (x * (2 * PI))) (sin (x * (2 * PI))) rm) V /\ Included V x0).
      { apply small_neighborhood_basis2, open_neighborhood_is_neighborhood.
        - repeat apply Rmin_pos; lra.
        - now split. }
      destruct H8, H8, H8.
      assert (rm <= 1/4) by apply Rmin_r.
      assert (rm <= x /\ rm <= 1 - x).
      { pose proof (Rmin_l (Rmin x (1 - x)) (1 / 4)).
        pose proof (Rmin_l x (1 - x)).
        pose proof (Rmin_r x (1 - x)).
        change (rm <= Rmin x (1 - x)) in H11. lra. }
      exists (Rmin r ((asin (r / 2)) / PI)).
      pose proof PI_RGT_0.
      pose proof (Rmin_l r (asin (r / 2) / PI)).
      repeat split; try lra.
      - apply Rmin_glb_lt; try lra.
        apply Rdiv_gt_mult; trivial.
        rewrite Rmult_0_r.
        apply asin_gt_0; lra.
      - red. intros.
        destruct x1, H14.
        simpl in H14.
        apply H9.
        destruct (asin_bound (r / 2)).
        split; simpl;
          constructor;
          unfold R_metric.
        + rewrite <- (Rabs_pos_eq r); try lra.
          apply Rsqr_lt_abs_0.
          rewrite Rsqr_neg_minus.
          pose proof (Rmin_r r (asin (r / 2) / PI)) as H20.
          apply Rdiv_ge_mult in H20; try lra.
          rewrite Rmult_comm in H20.
          apply sin_incr_1 in H20; try lra.
          * rewrite sin_asin in H20; try lra.
            apply Rdiv_ge_mult in H20; try lra.
            apply neg_pos_Rsqr_le in H20.
            -- rewrite Rsqr_mult in H20.
               replace 2² with 4 in H20 by (unfold Rsqr; lra).
               pose proof (Rle_0_sqr (sin (x * (2 * PI)) - p0)).
               lra.
            -- cut (0 < sin (Rmin r (asin (r / 2) / PI) * PI)); try lra.
               apply sin_gt_0.
               ++ apply Rmult_lt_0_compat; try lra.
                  apply Rmin_glb_lt; try lra.
                  apply Rdiv_lt_0_compat; try lra.
                  apply asin_gt_0; lra.
               ++ rewrite Rmult_comm.
                  apply Rdiv_gt_mult; try lra.
                  unfold Rdiv at 1. rewrite Rinv_r; lra.
          * cut (0 < Rmin r (asin (r / 2) / PI) * PI); try lra.
            apply Rmult_lt_0_compat; try lra.
            apply Rmin_glb_lt; try lra.
            apply Rdiv_lt_0_compat; try lra.
            apply asin_gt_0; lra.
        + rewrite <- (Rabs_pos_eq r); try lra.
          apply Rsqr_lt_abs_0.
          rewrite Rsqr_neg_minus.
          pose proof (Rmin_r r (asin (r / 2) / PI)) as H20.
          apply Rdiv_ge_mult in H20; try lra.
          rewrite Rmult_comm in H20.
          apply sin_incr_1 in H20; try lra.
          * rewrite sin_asin in H20; try lra.
            apply Rdiv_ge_mult in H20; try lra.
            apply neg_pos_Rsqr_le in H20.
            -- rewrite Rsqr_mult in H20.
               replace 2² with 4 in H20 by (unfold Rsqr; lra).
               pose proof (Rle_0_sqr (cos (x * (2 * PI)) - p)).
               lra.
            -- cut (0 < sin (Rmin r (asin (r / 2) / PI) * PI)); try lra.
               apply sin_gt_0.
               ++ apply Rmult_lt_0_compat; try lra.
                  apply Rmin_glb_lt; try lra.
                  apply Rdiv_lt_0_compat; try lra.
                  apply asin_gt_0; lra.
               ++ rewrite Rmult_comm.
                  apply Rdiv_gt_mult; try lra.
                  unfold Rdiv at 1. rewrite Rinv_r; lra.
          * cut (0 < Rmin r (asin (r / 2) / PI) * PI); try lra.
            apply Rmult_lt_0_compat; try lra.
            apply Rmin_glb_lt; try lra.
            apply Rdiv_lt_0_compat; try lra.
            apply asin_gt_0; lra. }
    destruct H8 as [r H8], H8, H9.
    exists (Im (inverse_image (@subspace_inc RTop _) (open_ball R_metric x r))
            (quotient_projection (SpaceAdjunction (Couple U0 U1)))).
    split; [split |].
    * apply saturated_subset_quotient_projection_open.
      -- apply SpaceAdjunction_equivalence.
      -- intros. red. intros.
         destruct H11, H11.
         rewrite SpaceAdjunction_equiv_class_Singleton in H12.
         ++ destruct H12.
            now repeat constructor.
         ++ intro.
            destruct H13; subst;
            contradict H11;
            unfold R_metric;
            simpl;
            rewrite Rabs_pos_eq + rewrite Rabs_minus_sym, Rminus_0_r, Rabs_pos_eq; lra.
      -- apply subspace_inc_continuous, metric_space_open_ball_open.
         ++ apply RTop_metrization.
         ++ apply R_metric_is_metric.
    * repeat econstructor.
      simpl.
      unfold R_metric.
      replace (x-x) with 0 by lra.
      rewrite Rabs_R0. lra.
    * red. intros.
      constructor.
      destruct x1, i.
      inversion H11.
      apply Subset.subset_eq in H13.
      simpl in H13.
      destruct H12, H12.
      pose proof H13.
      change (y = equiv_class (SpaceAdjunction (Couple U0 U1)) x2) in H15.
      rewrite SpaceAdjunction_equiv_class_Singleton in H15.
      -- rewrite H15 in H13.
         symmetry in H13.
         subst.
         apply SpaceAdjunction_equiv_class_Singleton_eq in H15;
           [ | intro H14; symmetry in H14; now apply Singleton_neq_Couple_U0_U1 in H14 ].
         subst.
         simpl.
         rewrite f_inv1_def.
         apply H10.
         constructor.
         destruct x2.
         simpl in *.
         unfold R_metric in H12.
         rewrite form2, form4, Rsqr_mult, Rsqr_mult, Rsqr_mult, Rsqr_mult,
           <- Rmult_minus_distr_r, <- Rmult_plus_distr_r.
         replace (-2)² with 4 by (unfold Rsqr; lra).
         replace 2² with 4 by (unfold Rsqr; lra).
         assert (forall z, z * (2 * PI) / 2 = z * PI).
         { intros. unfold Rdiv. rewrite Rmult_assoc. now replace (2 * PI * / 2) with PI by lra. }
         rewrite H14, H14, Rmult_assoc, Rmult_assoc, <- Rmult_plus_distr_l.
         apply Rmult_lt_compat_l; try lra.
         pose proof PI_RGT_0.
         apply (Rmult_lt_compat_r PI) in H12; try lra.
         rewrite <- (Rabs_pos_eq PI) in H12 at 1; try lra.
         rewrite Rabs_minus_sym, <- Rabs_mult in H12.
         apply Rabs_def2 in H12.
         destruct H12, H10.
         rewrite Rmult_comm at 1.
         rewrite <- Rmult_plus_distr_r, sin2_cos2, Rmult_1_l.
         assert ((r * PI) <= (PI / 2)).
         { rewrite Rmult_comm. unfold Rdiv.
           apply Rmult_le_compat_l; lra. }
         apply neg_pos_Rsqr_lt;
           [ rewrite <- sin_neg |];
           apply sin_increasing_1; lra.
      -- intro.
         destruct H16; subst;
         unfold R_metric in H12;
         simpl in H12;
         rewrite Rabs_minus_sym, Rminus_0_r, Rabs_pos_eq in H12 +
         rewrite Rabs_pos_eq in H12; lra.
  + contradict H.
    apply Proj1SigInjective.proj1_sig_injective.
    simpl.
    change (equiv_class (SpaceAdjunction (Couple U0 U1)) x1 = equiv_class (SpaceAdjunction (Couple U0 U1)) U0).
    destruct H3;
    repeat (constructor + rewrite SpaceAdjunction_equiv_class_S).
Qed.

Lemma f_bijection_1: forall x, f_inv (f x) = x.
intro S1x.
destruct S1x as [[x y] i].
pose proof i.
destruct H.
apply Rsqr_sum_1_bound_l in H.
pose proof i.
destruct H0.
pose proof i.
destruct H1.
apply Rsqr_sum_1_bound_r in H0.
unfold f, f1, uncurry.
apply Proj1SigInjective.proj1_sig_injective.
simpl in *.
rewrite f_inv1_def.
simpl.
pose proof PI_RGT_0.
destruct (Rle_lt_dec y 0);
  f_equal; unfold Rdiv.
- rewrite Rmult_minus_distr_r, Rmult_assoc, Rinv_l, Rmult_1_l, Rmult_1_r, cos_2PI_neg, cos_acos; lra.
- rewrite Rmult_minus_distr_r, Rmult_assoc, Rinv_l, Rmult_1_l, Rmult_1_r, sin_2PI_neg, sin_acos; try lra.
  cut (sqrt (1 - x²) = -y); try lra.
  apply Rsqr_inj; try lra.
  + apply sqrt_pos.
  + rewrite <- Rsqr_neg, Rsqr_sqrt; try lra.
    replace 1 with (1²) by (unfold Rsqr; lra).
    cut(x²<=1²); try lra.
    apply Rsqr_le_abs_1, Rabs_le.
    rewrite Rabs_R1.
    lra.
- rewrite Rmult_assoc, Rinv_l, Rmult_1_r, cos_acos; lra.
- rewrite Rmult_assoc, Rinv_l, Rmult_1_r, sin_acos; try lra.
  apply Rsqr_inj; try lra.
  + apply sqrt_pos.
  + rewrite Rsqr_sqrt; try lra.
    replace 1 with (1²) by (unfold Rsqr; lra).
    cut(x²<=1²); try lra.
    apply Rsqr_le_abs_1, Rabs_le.
    rewrite Rabs_R1.
    lra.
Qed.

Lemma f_bijection_2: forall x, f (f_inv x) = x.
Proof.
intro.
destruct (quotient_projection_surjective x).
subst.
unfold f, f_inv.
apply Proj1SigInjective.proj1_sig_injective.
simpl.
apply R_impl_equality_of_equiv_class.
{ change (equivalence (SpaceAdjunction (Couple U0 U1))). apply SpaceAdjunction_equivalence. }
unfold uncurry.
destruct x0, i.
simpl.
pose proof PI_RGT_0.
destruct (classic (x = 0)), (classic (x = 1)); lra + subst.
- right.
  split.
  + match goal with | [ |- In _ ?x ] => cut(x=U1) end.
    * intro. rewrite H0; constructor.
    * apply Proj1SigInjective.proj1_sig_injective.
      simpl.
      rewrite f_inv1_def, Rmult_0_l, cos_0, sin_0.
      unfold f1, Rdiv.
      destruct (Rle_lt_dec 0 0); try lra.
      rewrite acos_1; lra.
  + match goal with | [ |- In _ ?x ] => cut(x=U0) end.
    * intro. rewrite H0; constructor.
    * now apply Proj1SigInjective.proj1_sig_injective.
- right.
  split.
  + match goal with | [ |- In _ ?x ] => cut(x=U1) end.
    * intro. rewrite H1; constructor.
    * apply Proj1SigInjective.proj1_sig_injective.
      simpl.
      rewrite f_inv1_def.
      simpl.
      rewrite Rmult_1_l, <- (Rplus_0_r (2 * PI)), cos_2PI, sin_2PI, cos_0, sin_0.
      unfold f1, Rdiv.
      destruct (Rle_lt_dec 0 0); try lra.
      rewrite acos_1; lra.
  + match goal with | [ |- In _ ?x ] => cut(x=U1) end.
    * intro. rewrite H1; constructor.
    * now apply Proj1SigInjective.proj1_sig_injective.
- left.
  apply Proj1SigInjective.proj1_sig_injective.
  simpl.
  rewrite f_inv1_def.
  simpl.
  unfold f1, Rdiv.
  destruct (Rle_lt_dec (sin (x * (2 * PI))) 0).
  + rewrite <- cos_2PI_neg, acos_cos.
    * rewrite Rmult_minus_distr_r, (Rmult_assoc x), Rinv_r; lra.
    * assert (x * (2 * PI) <= 2 * PI).
      { rewrite Rmult_comm.
        apply Rdiv_ge_mult; try lra.
        unfold Rdiv.
        rewrite Rinv_r; lra. }
      apply sin_neg_bound in r; try lra.
      split; trivial.
      apply Rmult_lt_0_compat; lra.
  + rewrite acos_cos, Rmult_assoc, Rinv_r, Rmult_1_r; try lra.
    split.
    * apply Rmult_le_pos; lra.
    * apply sin_pos_bound in r; try lra.
      split.
      -- apply Rmult_lt_0_compat; lra.
      -- replace (2 * PI) with (1 * (2 * PI)) at 2 by lra.
         apply Rmult_le_compat_r; lra.
Qed.

Goal homeomorphic S1 ClosedUnitInterval.
Proof.
econstructor.
apply (intro_homeomorphism f f_inv f_continuous f_inv_continuous f_bijection_1 f_bijection_2).
Qed.
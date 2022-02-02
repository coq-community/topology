From Coq Require Import Reals.Ratan Lia Lra Logic.IndefiniteDescription Program.Subset.
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

End TrigLemmas.

Definition circle_cover (t : RTop) : ProductTopology2 RTop RTop :=
  (cos (2*PI*t), sin (2*PI*t)).

Lemma circle_cover_continuous : continuous circle_cover.
Proof.
  apply product2_map_continuous.
  - apply (@continuous_composition RTop RTop RTop cos).
    { apply cos_continuous. }
    apply (@continuous_composition_2arg RTop RTop RTop).
    + apply continuous_constant.
    + apply continuous_identity.
    + apply Rmult_continuous.
  - apply (@continuous_composition RTop RTop RTop sin).
    { apply sin_continuous. }
    apply (@continuous_composition_2arg RTop RTop RTop).
    + apply continuous_constant.
    + apply continuous_identity.
    + apply Rmult_continuous.
Qed.

Definition S1_Ensemble := [s : @ProductTopology2 RTop RTop | let (x, y) := s in x² + y² = 1].
Definition S1 := SubspaceTopology S1_Ensemble.

Lemma circle_cover_image t :
  In S1_Ensemble (circle_cover t).
Proof.
  constructor. simpl.
  rewrite Rplus_comm.
  apply sin2_cos2.
Qed.

Lemma trig_period_lemma (f : R -> R) (q : R) :
  q > 0 ->
  (forall x k, f (x + q * INR k) = f x) ->
  (forall x z, f (x + q * IZR z) = f x).
Proof.
  intros Hq Hperiod x z.
  destruct z.
  - (* z = 0 *)
    f_equal. lra.
  - (* z > 0 *)
    rewrite <- (Hperiod x (Pos.to_nat p)).
    f_equal.
    rewrite INR_IZR_INZ.
    rewrite positive_nat_Z.
    reflexivity.
  - (* z < 0 *)
    rewrite <- (Hperiod (x + q * IZR (Z.neg p)) (Pos.to_nat p)).
    f_equal.
    rewrite <- Rplus_0_r.
    rewrite Rplus_assoc.
    apply Rplus_eq_compat_l.
    rewrite <- Rmult_plus_distr_l.
    apply Rmult_eq_0_compat_l.
    rewrite INR_IZR_INZ.
    rewrite positive_nat_Z.
    rewrite <- plus_IZR.
    apply f_equal.
    lia.
Qed.

Lemma cos_period_Z x z :
  cos (x + 2 * PI * IZR z) = cos x.
Proof.
  pose proof PI_RGT_0.
  apply trig_period_lemma; try lra.
  intros.
  rewrite <- (cos_period x0 k).
  f_equal. lra.
Qed.

Lemma sin_period_Z x z :
  sin (x + 2 * PI * IZR z) = sin x.
Proof.
  pose proof PI_RGT_0.
  apply trig_period_lemma; try lra.
  intros.
  rewrite <- (sin_period x0 k).
  f_equal. lra.
Qed.

Lemma neg_cos_PI (x : R): cos (x - PI) = - cos x.
Proof.
  rewrite <- (cos_period _ 1).
  simpl.
  replace (x - PI + 2 * 1 * PI) with (x + PI) by lra.
  apply neg_cos.
Qed.

Lemma circle_cover_inj t0 t1 :
  0 <= t0 < 1 ->
  0 <= t1 < 1 ->
  circle_cover t0 = circle_cover t1 ->
  t0 = t1.
Proof.
  intros.
  pose proof PI_RGT_0.
  assert (forall x, 0 <= x < 1 -> 0 <= 2 * PI * x < 2 * PI).
  { intros.
    split.
    - apply Rmult_le_pos; lra.
    - rewrite <- Rmult_1_r.
      apply Rmult_lt_compat_l; lra.
  }
  apply H3 in H.
  apply H3 in H0.
  apply (Rmult_eq_reg_l (2*PI)); try lra.
  apply pair_equal_spec in H1.
  destruct H1, (Rle_or_lt (2 * PI * t0) PI), (Rle_or_lt (2 * PI * t1) PI).
  - apply cos_inj; lra.
  - apply sin_ge_0 in H5; try lra.
    apply sin_lt_0 in H6; lra.
  - apply sin_ge_0 in H6; try lra.
    apply sin_lt_0 in H5; lra.
  - apply Ropp_eq_compat in H1.
    rewrite <- neg_cos_PI, <- neg_cos_PI in H1.
    apply cos_inj in H1; lra.
Qed.

Lemma circle_cover_preimage t0 t1 :
  circle_cover t0 = circle_cover t1 ->
  exists z : Z, t0 - t1 = IZR z.
Proof.
  unfold circle_cover.
  intros.
  inversion H; subst; clear H.
  destruct (euclidian_division t0 1) as [k0 [r0 [H00 H01]]].
  { pose proof PI_neq0. lra. }
  destruct (euclidian_division t1 1) as [k1 [r1 [H10 H11]]].
  { pose proof PI_neq0. lra. }
  subst.
  rewrite !Rmult_1_r in *.
  rewrite !Rmult_plus_distr_l in *.
  rewrite Rplus_comm in H1.
  rewrite cos_period_Z in H1.
  rewrite Rplus_comm in H1.
  rewrite cos_period_Z in H1.
  rewrite Rplus_comm in H2.
  rewrite sin_period_Z in H2.
  rewrite Rplus_comm in H2.
  rewrite sin_period_Z in H2.
  cut (r0 = r1).
  { intros. subst.
    exists (k0 - k1)%Z.
    rewrite <- Z_R_minus.
    lra.
  }
  rewrite Rabs_R1 in *.
  eapply circle_cover_inj; try lra.
  unfold circle_cover.
  congruence.
Qed.

Definition UnitInterval_Ensemble := [x : RTop | 0 <= x <= 1].
Definition UnitInterval := SubspaceTopology [x : RTop | 0 <= x <= 1].
Definition U0 : UnitInterval := exist UnitInterval_Ensemble 0 ltac:(constructor; lra).
Definition U1 : UnitInterval := exist UnitInterval_Ensemble 1 ltac:(constructor; lra).
Definition ClosedUnitInterval := AdjunctionSpace (Couple U0 U1).

Definition f1 (p : R*R) : R :=
  if (Rle_lt_dec (snd p) 0) then
    1 - acos (fst p) / (2 * PI)
  else
    acos (fst p) / (2 * PI).

Lemma f1_helper : forall x : R * R, In S1_Ensemble x ->
  In UnitInterval_Ensemble (f1 x).
Proof.
intros [x y] [H].
unfold f1. simpl.
pose proof PI_RGT_0.
destruct (acos_bound x).
cut (0 <= acos x / (2 * PI) <= 1);
  constructor.
- destruct (Rle_lt_dec y 0); lra.
- apply Rdiv_ge_mult; lra.
- apply Rdiv_le_mult; lra.
Qed.

Definition f (x: point_set S1) : point_set ClosedUnitInterval :=
  quotient_projection _ (exist _ (f1 (proj1_sig x)) (f1_helper _ (proj2_sig x))).

Lemma f_inv_helper (x y : UnitInterval) :
  SpaceAdjunction (Couple U0 U1) x y ->
  (fun x => exist _ (circle_cover (subspace_inc _ x)) (circle_cover_image _)) x =
  (fun x => exist _ (circle_cover (subspace_inc _ x)) (circle_cover_image _)) y.
Proof.
  intros.
  destruct x as [x Hx].
  destruct y as [y Hy].
  apply subset_eq.
  simpl.
  red in H. destruct H as [|[]].
  - inversion H; subst; clear H.
    reflexivity.
  - inversion H; subst; clear H;
      inversion H0; subst; clear H0;
      try reflexivity.
    all: unfold circle_cover.
    all: rewrite Rmult_0_r.
    all: rewrite Rmult_1_r.
    all: rewrite cos_0, sin_0.
    all: rewrite Rtrigo1.cos_2PI.
    all: rewrite Rtrigo1.sin_2PI.
    all: reflexivity.
Qed.

Definition f_inv : ClosedUnitInterval -> S1 :=
  induced_function
    (fun x => exist _ (circle_cover (subspace_inc _ x)) _)
    (SpaceAdjunction_equivalence _) f_inv_helper.

Lemma f_inv_continuous : continuous f_inv.
Proof.
  apply induced_function_continuous.
  apply subspace_continuous_char.
  unfold compose.
  simpl.
  apply (continuous_composition circle_cover).
  - apply circle_cover_continuous.
  - apply subspace_inc_continuous.
Qed.

Lemma f_inv_bijective : bijective f_inv.
Proof.
  split.
  - (* first handle the technicalities *)
    intros [x Hx] [y Hy].
    intros.
    apply subset_eq; simpl.
    inversion Hx as [x0 _]; subst.
    inversion Hy as [y0 _]; subst.
    apply R_impl_equality_of_equiv_class.
    { apply SpaceAdjunction_equivalence. }
    unfold f_inv in H.
    rewrite !induced_function_correct in H.
    clear Hx Hy.
    destruct x0 as [x Hx0].
    destruct y0 as [y Hy0].
    simpl in *.
    assert (circle_cover x = circle_cover y).
    { inversion H; subst.
      unfold circle_cover.
      congruence.
    }
    clear H.
    destruct Hx0 as [Hx0], Hy0 as [Hy0].
    (* The rest follows from the properties of [sin] and [cos]. *)
    apply circle_cover_preimage in H0 as [z Hz].
    (* either [z=0] or [z=1] or [z=-1] *)
    assert (-1 <= z <= 1)%Z.
    { split; apply le_IZR; lra.
    }
    destruct z.
    + (* z = 0 *)
      assert (x = y) by lra.
      subst.
      left. apply subset_eq. reflexivity.
    + (* z > 0 i.e. z = 1 *)
      destruct p; try lia.
      assert (x = 1) by lra.
      assert (y = 0) by lra.
      subst.
      replace (exist _ 1 _) with U1.
      2: { apply subset_eq. reflexivity. }
      replace (exist _ 0 _) with U0.
      2: { apply subset_eq. reflexivity. }
      right. split; [right|left].
    + (* z < 0 i.e. z = -1 *)
      destruct p; try lia.
      assert (x = 0) by lra.
      assert (y = 1) by lra.
      subst.
      replace (exist _ 1 _) with U1.
      2: { apply subset_eq. reflexivity. }
      replace (exist _ 0 _) with U0.
      2: { apply subset_eq. reflexivity. }
      right. split; [left|right].
  - red. intros y.
    exists (f y).
    unfold f_inv, f.
    simpl.
    unfold quotient_projection.
    rewrite (induced_function_correct
               (fun x : { x : RTop | _} =>
                  exist (In S1_Ensemble)
                        (circle_cover (subspace_inc _ x)) _)).
    apply subset_eq. simpl.
    unfold f1.
    destruct y as [[x y] H].
    simpl.
    replace (circle_cover _) with
      (if Rle_lt_dec y 0 then
         circle_cover (1 - acos x / (2*PI))
       else
         circle_cover (acos x / (2 * PI))).
    2: {
      destruct (Rle_lt_dec y 0); auto.
    }
    unfold circle_cover.
    rewrite !Rmult_minus_distr_l.
    rewrite Rmult_1_r.
    rewrite cos_2PI_neg.
    rewrite sin_2PI_neg.
    destruct H.
    pose proof (Rsqr_sum_1_bound_l _ _ H).
    replace (_ * _ * (acos x / _)) with (acos x).
    2: {
      pose proof PI_neq0.
      unfold Rdiv.
      rewrite Rmult_comm.
      rewrite Rmult_assoc.
      replace (/ _ * _) with 1; try lra.
      symmetry.
      apply Rinv_l.
      lra.
    }
    rewrite cos_acos; auto.
    replace (sin (acos x)) with (sqrt y²).
    2: {
      rewrite sin_acos; auto.
      apply f_equal.
      lra.
    }
    rewrite sqrt_Rsqr_abs.
    unfold Rabs.
    destruct (Rle_lt_dec y 0), (Rcase_abs y);
      auto; try lra.
    + rewrite Ropp_involutive.
      reflexivity.
    + assert (y = 0) by lra.
      subst. rewrite Ropp_0.
      reflexivity.
Qed.

Corollary f_inv_homeomorphism :
  homeomorphism f_inv.
Proof.
  apply compact_hausdorff_homeo.
  - apply quotient_compact.
    apply R_closed_interval_compact.
    lra.
  - apply Hausdorff_Subspace.
    apply Hausdorff_ProductTopology2.
    all: apply metrizable_Hausdorff.
    all: apply RTop_metrizable.
    (* for this the class hierarchy would be useful *)
  - apply f_inv_bijective.
  - apply f_inv_continuous.
Qed.

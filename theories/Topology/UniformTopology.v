Require Export MetricSpaces.
Require Import FunctionalExtensionality.
Require Export Completeness.
Require Import Description.
Require Import Max.
Require Import Psatz.
Require Import Lra.
From Coq Require ProofIrrelevance.

Section UniformTopology.

Variable X Y:Type.
Variable d:Y->Y->R.
Variable y0:X->Y. (* base function limiting the extents of the
                  range of a function X->Y *)
Hypothesis d_metric: metric d.
Hypothesis X_inhabited: inhabited X.

Definition uniform_space := { f:X->Y | bound (Im Full_set
                                      (fun x:X => d (y0 x) (f x))) }.

Definition uniform_metric (f g:uniform_space) : R.
refine (match f, g with exist f0 Hf, exist g0 Hg =>
  proj1_sig (sup (Im Full_set (fun x:X => d (f0 x) (g0 x))) _ _) end).
- destruct Hf as [mf].
  destruct Hg as [mg].
  exists (mf + mg).
  red; intros.
  destruct H1.
  rewrite H2.
  apply Rle_trans with (d (y0 x) (f0 x) + d (y0 x) (g0 x)).
  + rewrite (metric_sym _ d d_metric (y0 x) (f0 x)); trivial;
      apply triangle_inequality; trivial.
  + assert (d (y0 x) (f0 x) <= mf) by (apply H; exists x; trivial).
    assert (d (y0 x) (g0 x) <= mg) by (apply H0; exists x; trivial).
    auto with real.
- destruct X_inhabited as [x0].
  exists (d (f0 x0) (g0 x0)); exists x0; trivial; constructor.
Defined.

Lemma uniform_metric_bound_below (f g : uniform_space) (x : X) :
  d (proj1_sig f x) (proj1_sig g x) <= uniform_metric f g.
Proof.
  unfold uniform_metric.
  destruct f as [f Hf]; destruct g as [g Hg];
    destruct sup.
  simpl.
  apply i.
  exists x; trivial; constructor.
Qed.

Lemma uniform_metric_lt (f g : uniform_space) (r : R) :
  uniform_metric f g < r ->
  forall x : X, d (proj1_sig f x) (proj1_sig g x) < r.
Proof.
  intros Hfg x.
  destruct f as [f Hf], g as [g Hg].
  simpl.
  unfold uniform_metric in Hfg.
  destruct sup as [d_fg].
  simpl in *.
  eapply Rle_lt_trans; eauto.
  clear r Hfg.
  apply i.
  exists x; auto with sets.
Qed.

Lemma uniform_metric_is_metric: metric uniform_metric.
Proof.
constructor; intros.
- unfold uniform_metric.
  destruct x as [f0 Hf]; destruct y as [g0 Hg].
  destruct sup.
  destruct sup.
  simpl.
  assert (Im Full_set (fun x:X => d (f0 x) (g0 x)) =
        Im Full_set (fun x:X => d (g0 x) (f0 x))).
  { apply Extensionality_Ensembles; split; red; intros.
    - destruct H.
      exists x1.
      + constructor.
      + rewrite metric_sym; trivial.
    - destruct H.
      exists x1.
      + constructor.
      + rewrite metric_sym; trivial.
  }
  apply Rle_antisym.
  + apply i.
    rewrite H.
    apply i0.
  + apply i0.
    rewrite <- H.
    apply i.
- destruct x as [f0 Hf]; destruct y as [g0 Hg]; destruct z as [h0 Hh].
  simpl.
  repeat destruct sup; simpl.
  apply i.
  red; intros.
  destruct H.
  rewrite H0.
  apply Rle_trans with (d (f0 x2) (g0 x2) + d (g0 x2) (h0 x2)).
  + apply d_metric.
  + assert (d (f0 x2) (g0 x2) <= x0) by
      (apply i0; exists x2; trivial).
    assert (d (g0 x2) (h0 x2) <= x1) by
      (apply i1; exists x2; trivial).
    auto with real.
- destruct x as [f0 Hf].
  simpl.
  destruct sup; simpl.
  apply Rle_antisym.
  + apply i.
    red; intros.
    destruct H.
    rewrite metric_zero in H0; trivial.
    right; trivial.
  + apply i.
    destruct X_inhabited as [x0].
    exists x0.
    * constructor.
    * symmetry; apply d_metric.
- destruct x as [f0 Hf]; destruct y as [g0 Hg].
  apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
  extensionality x.
  apply d_metric.
  simpl in H.
  destruct sup in H.
  simpl in H.
  subst x0.
  apply Rle_antisym.
  + apply i; exists x; trivial.
    constructor.
  + cut (d (f0 x) (g0 x) >= 0); auto with real.
    apply metric_nonneg.
    assumption.
Qed.

Definition UniformTopology : TopologicalSpace :=
  MetricTopology uniform_metric uniform_metric_is_metric.

Definition UniformTopology_metrizable :
  metrizable UniformTopology :=
  MetricTopology_metrizable _ _ _.

Lemma uniform_metric_complete: complete d d_metric ->
  complete uniform_metric uniform_metric_is_metric.
Proof.
intros.
assert (forall y:Net nat_DS (MetricTopology d d_metric), cauchy d y ->
  { y0:Y | net_limit y y0 }) as cauchy_limit.
{ intros.
  apply constructive_definite_description.
  apply -> unique_existence; split.
  - apply H; trivial.
  - apply (Hausdorff_impl_net_limit_unique y).
    apply T3_sep_impl_Hausdorff.
    apply normal_sep_impl_T3_sep.
    apply metrizable_impl_normal_sep.
    exists d; trivial; apply MetricTopology_metrized.
}
red; intros f ?.
unshelve refine (let H1 := _ in let H2 := _ in ex_intro _
  (exist _ (fun x:X => proj1_sig (cauchy_limit
                  (fun n:nat => proj1_sig (f n) x) (H1 x))) H2) _); [ | clearbody H1 | clearbody H1 H2 ].
- intros.
  red; intros.
  destruct (H0 eps H1) as [N].
  exists N; intros.
  apply Rle_lt_trans with (uniform_metric (f m) (f n)).
  + apply uniform_metric_bound_below.
  + apply H2; trivial.
- assert (1 > 0) by (red; auto with real).
  destruct (H0 1 H2) as [N].
  pose (fN := f N).
  assert (f N = fN) by reflexivity.
  destruct fN as [fN [M]].
  assert (forall (n:nat) (x:X), (n >= N)%nat -> d (proj1_sig (f n) x)
                                                 (proj1_sig (f N) x) < 1).
  { intros.
    apply uniform_metric_lt; auto.
  }
  assert (forall x:X,
    d (fN x) (proj1_sig (cauchy_limit _ (H1 x))) <= 1).
  { intros.
    apply lt_plus_epsilon_le.
    intros.
    destruct cauchy_limit; simpl.
    pose proof (metric_space_net_limit_converse _ _
      (MetricTopology_metrized _ d d_metric) nat_DS
      (fun n:nat => proj1_sig (f n) x) x0 n).
    destruct (H7 eps H6) as [i0].
    pose (N' := Nat.max N i0).
    apply Rle_lt_trans with (d (fN x) (proj1_sig (f N') x) +
                             d x0 (proj1_sig (f N') x)).
    { rewrite metric_sym with (x:=x0) (y:=proj1_sig (f N') x); trivial.
      apply d_metric.
    }
    replace (fN x) with (proj1_sig (f N) x).
    2: { rewrite H4; reflexivity. }
    assert (d (proj1_sig (f N) x) (proj1_sig (f N') x) < 1).
    { rewrite metric_sym; trivial.
      apply H5.
      lia.
    }
    assert (d x0 (proj1_sig (f N') x) < eps).
    { apply H8. simpl. lia.
    }
    auto with real.
  }
  exists (M+1).
  red; intros.
  destruct H7.
  rewrite H8; clear H8.
  apply Rle_trans with (d (y0 x) (fN x) + d (fN x)
                                     (proj1_sig (cauchy_limit _ (H1 x)))).
  { apply d_metric. }
  assert (d (y0 x) (fN x) <= M).
  { apply i.
    exists x; trivial.
  }
  auto with real.
- apply metric_space_net_limit with uniform_metric.
  { apply MetricTopology_metrized. }
  intros.
  assert (eps/2 > 0) by lra.
  destruct (H0 (eps/2) H4) as [N].
  exists N; intros.
  apply Rle_lt_trans with (eps/2); try lra.
  unfold uniform_metric; remember (f j) as fj; destruct fj as [fj].
  destruct sup; simpl.
  apply i.
  red; intros.
  destruct H7.
  rewrite H8; clear y H8.
  apply lt_plus_epsilon_le; intros.
  destruct (cauchy_limit (fun n:nat => proj1_sig (f n) x0) (H1 x0));
    simpl.
  pose proof (metric_space_net_limit_converse _ _
    (MetricTopology_metrized _ d d_metric) nat_DS
    (fun n:nat => proj1_sig (f n) x0) x1 n).
  destruct (H9 eps0 H8) as [N'].
  pose (N'' := Nat.max N N').
  apply Rle_lt_trans with (d x1 (proj1_sig (f N'') x0) +
                           d (proj1_sig (f N'') x0) (proj1_sig (f j) x0)).
  { repeat rewrite <- Heqfj; simpl.
    apply d_metric.
  }
  assert (d x1 (proj1_sig (f N'') x0) < eps0).
  { apply H10. simpl. lia.
  }
  cut (d (proj1_sig (f N'') x0) (proj1_sig (f j) x0) < eps/2); [lra|].
  apply Rle_lt_trans with (uniform_metric (f N'') (f j)).
  + unfold uniform_metric; destruct (f N'') as [f1];
    destruct (f j) as [f2]; destruct sup; simpl.
    apply i0; exists x0; trivial.
  + apply H5; trivial.
    lia.
Qed.

End UniformTopology.

Arguments uniform_space {X} {Y}.
Arguments uniform_metric {X} {Y}.
Arguments UniformTopology {X} {Y}.

Section UniformTopology_and_continuity.

Variable X:TopologicalSpace.
Variable Y:Type.
Variable d:Y->Y->R.
Variable y0:point_set X -> Y.
Hypothesis d_metric: metric d.
Hypothesis X_inh: inhabited (point_set X).

Lemma continuous_functions_at_point_closed_in_uniform_metric:
  forall x0:point_set X,
  closed (fun f:uniform_space d y0 => continuous_at (proj1_sig f) x0
                                      (Y:=MetricTopology d d_metric))
    (X:=UniformTopology d y0 d_metric X_inh).
Proof.
intros.
apply first_countable_sequence_closed.
{ apply metrizable_impl_first_countable.
  apply UniformTopology_metrizable.
}
intros f f0 Hf Hf0.
(* we need to show that [f0] is continuous.
   we switch to the def. of continuity which uses the nbhd. basis.
   We do this to be able to work with the definition of [UniformTopology].
*)
pose proof (MetricTopology_metrized _ d d_metric
  (proj1_sig f0 x0)) as Hf0_nbhd_basis.
apply open_neighborhood_basis_is_neighborhood_basis in Hf0_nbhd_basis.
apply continuous_at_neighborhood_basis with (1:=Hf0_nbhd_basis).
clear Hf0_nbhd_basis.

intros V HV.
destruct HV as [r Hr].
assert (r/3>0) as Hr3 by lra.
destruct (metric_space_net_limit_converse _ _
  (MetricTopology_metrized _ _
     (uniform_metric_is_metric X Y d y0 d_metric X_inh))
  nat_DS f f0 Hf0 (r/3) Hr3) as [N HN].
assert (neighborhood
  (inverse_image (proj1_sig (f N))
     (open_ball d (proj1_sig (f N) x0) (r/3))) x0) as Hx0_nbhd.
{ apply Hf.
  pose proof (MetricTopology_metrized _ d d_metric
    (proj1_sig (f N) x0)) as Hnbhd.
  apply open_neighborhood_basis_is_neighborhood_basis in Hnbhd.
  apply Hnbhd.
  constructor; trivial.
}
eapply neighborhood_upward_closed; eauto.
clear Hx0_nbhd.

intros x [[Hx]].
constructor.
constructor.
apply Rle_lt_trans with
  (d (proj1_sig f0 x0) (proj1_sig (f N) x0) +
   d (proj1_sig (f N) x0) (proj1_sig f0 x)).
{ apply d_metric. }
apply Rle_lt_trans with
  (d (proj1_sig f0 x0) (proj1_sig (f N) x0) +
   d (proj1_sig (f N) x0) (proj1_sig (f N) x) +
   d (proj1_sig (f N) x) (proj1_sig f0 x)).
{ assert (d (proj1_sig (f N) x0) (proj1_sig f0 x) <=
          d (proj1_sig (f N) x0) (proj1_sig (f N) x) +
          d (proj1_sig (f N) x) (proj1_sig f0 x)) by apply d_metric.
  lra.
}
rewrite (metric_sym _ d d_metric (proj1_sig (f N) x) (proj1_sig f0 x)).
pose proof (uniform_metric_lt X Y d y0 d_metric X_inh
              f0 (f N) _ (HN N ltac:(reflexivity)) x0).
pose proof (uniform_metric_lt X Y d y0 d_metric X_inh
              f0 (f N) _ (HN N ltac:(reflexivity)) x).
lra.
Qed.

Lemma continuous_functions_closed_in_uniform_metric:
  closed (fun f:uniform_space d y0 => continuous (proj1_sig f)
                                      (Y:=MetricTopology d d_metric))
    (X:=UniformTopology d y0 d_metric X_inh).
Proof.
replace (fun f:uniform_space d y0 => continuous (proj1_sig f)
                                     (Y:=MetricTopology d d_metric)) with
  (IndexedIntersection (fun (x0:point_set X) (f:uniform_space d y0) =>
         continuous_at (proj1_sig f) x0 (Y:=MetricTopology d d_metric))).
{ apply (@closed_indexed_intersection (UniformTopology d y0 d_metric X_inh)),
  continuous_functions_at_point_closed_in_uniform_metric.
}
apply Extensionality_Ensembles; split; intros f ?.
- destruct H.
  now apply pointwise_continuity.
- constructor. intros x.
  unfold In in *.
  now apply continuous_func_continuous_everywhere.
Qed.

Lemma bounded_functions_closed_in_uniform_metric:
  closed (fun f:uniform_space d y0 =>
            bounded d (Im Full_set (proj1_sig f)))
    (X:=UniformTopology d y0 d_metric X_inh).
Proof.
apply first_countable_sequence_closed.
{ apply metrizable_impl_first_countable.
  apply UniformTopology_metrizable.
}
intros f f0 Hf0 Hf1.
unfold In in Hf0.
pose proof
  (metric_space_net_limit_converse
     _ _ (MetricTopology_metrized _ _
            (uniform_metric_is_metric _ _ _ y0 d_metric X_inh))
     nat_DS f f0 Hf1 1 ltac:(lra)) as [N HN].
clear Hf1.
specialize (Hf0 N) as [y1 [r Hr]].
exists y1, (r+1).
intros y Hy.
destruct Hy as [x Hx]; subst.
specialize (Hr (proj1_sig (f N) x)) as [HfN].
{ apply Im_def; auto. }
constructor.
specialize (HN N ltac:(reflexivity)).
pose proof (uniform_metric_lt _ _ _ _ _ _ _ _ _ HN x).
pose proof (triangle_inequality
              _ d d_metric y1 (proj1_sig (f N) x) (proj1_sig f0 x)).
rewrite metric_sym in H; auto.
lra.
Qed.

End UniformTopology_and_continuity.

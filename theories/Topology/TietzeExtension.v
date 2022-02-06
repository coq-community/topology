Require Export RTopology SeparatednessAxioms.
Require Import RFuncContinuity UniformTopology ContinuousFactorization.
From Coq Require Import Description Max Psatz ClassicalChoice.
From ZornsLemma Require Import Proj1SigInjective.
Require Import UrysohnsLemma.

(* This proof of the Tietze extension theorem is heavily based on
   the proof described on planetmath.org. *)

Section Tietze_extension_construction.

Variable X:TopologicalSpace.
Variable F:Ensemble X.
Hypothesis F_closed: closed F.
Variable f:SubspaceTopology F -> RTop.
Hypothesis f_continuous: continuous f.
Hypothesis f_bound: forall x:SubspaceTopology F,
  -1 <= f x <= 1.
Hypothesis X_nonempty: inhabited X.

Variable Urysohns_lemma_function:
  forall F G:Ensemble X,
  closed F -> closed G -> Intersection F G = Empty_set ->
  { f:X -> RTop |
  continuous f /\ (forall x:X, 0 <= f x <= 1) /\
  (forall x:X, In F x -> f x = 0) /\
  (forall x:X, In G x -> f x = 1) }.

Lemma Rle_order: order Rle.
Proof.
constructor;
  red; intros.
- apply Rle_refl.
- eapply Rle_trans;
    eassumption.
- now apply Rle_antisym.
Qed.

Section extension_approximation.

Variable f0:SubspaceTopology F -> RTop.
Hypothesis f0_cont: continuous f0.
Hypothesis f0_bound: forall x:SubspaceTopology F,
                     -1 <= f0 x <= 1.

Definition extension_approximation: X -> RTop.
refine (
  let F0:=Im [ x:SubspaceTopology F | f0 x <= -1/3 ]
             (subspace_inc F) in
  let G0:=Im [ x:SubspaceTopology F | f0 x >= 1/3 ]
             (subspace_inc F) in
  let g:=proj1_sig (Urysohns_lemma_function F0 G0 _ _ _) in
  fun x:X => -1/3 + 2/3 * g x).
- apply subspace_inc_takes_closed_to_closed; [assumption|].
  replace ([ x:SubspaceTopology F | f0 x <= -1/3 ]) with
    (inverse_image f0 [ y:RTop | y <= -1/3 ]).
  + red.
    rewrite <- inverse_image_complement.
    apply f0_cont.
    apply lower_closed_interval_closed.
    * apply Rle_order.
    * intros.
      destruct (total_order_T x y) as [[|]|];
        auto with real.
  + extensionality_ensembles.
    * now constructor.
    * constructor.
      now constructor.
- apply subspace_inc_takes_closed_to_closed; [assumption|].
  replace ([ x:SubspaceTopology F | f0 x >= 1/3 ]) with
    (inverse_image f0 [ y:RTop | 1/3 <= y ]).
  + red.
    rewrite <- inverse_image_complement.
    apply f0_cont.
    apply upper_closed_interval_closed.
    * apply Rle_order.
    * intros.
      destruct (total_order_T x y) as [[|]|];
        auto with real.
  + extensionality_ensembles.
    * constructor. lra.
    * constructor. constructor. lra.
- extensionality_ensembles.
  destruct x, x0.
  simpl in *.
  subst.
  destruct (proof_irrelevance _ i i0).
  lra.
Defined.

Lemma extension_approximation_bound: forall x:X,
  -1/3 <= extension_approximation x <= 1/3.
Proof.
intros.
unfold extension_approximation.
destruct Urysohns_lemma_function as [g].
simpl.
destruct a as [? [? []]].
destruct (H0 x).
lra.
Qed.

Lemma extension_approximation_diff_bound:
  forall x:SubspaceTopology F,
  -2/3 <= f0 x - extension_approximation (subspace_inc F x) <= 2/3.
Proof.
intros.
unfold extension_approximation.
destruct Urysohns_lemma_function as [g [? [? []]]].
simpl.
destruct (f0_bound x).
destruct (Rle_or_lt (f0 x) (-1/3)).
- replace (g (subspace_inc F x)) with 0.
  { lra. }
  symmetry. apply e.
  econstructor; trivial.
  now constructor.
- destruct (Rle_or_lt (1/3) (f0 x)).
  + replace (g (subspace_inc F x)) with 1.
    { lra. }
    symmetry. apply e0.
    econstructor; trivial.
    constructor.
    lra.
  + destruct (a (subspace_inc F x)).
    lra.
Qed.

Lemma extension_approximation_continuous:
  continuous extension_approximation.
Proof.
unfold extension_approximation.
destruct Urysohns_lemma_function as [g [? [? []]]].
simpl.
apply pointwise_continuity.
intros.
apply sum_continuous.
- apply continuous_func_continuous_everywhere,
        continuous_constant.
- now apply const_multiple_continuous,
            continuous_func_continuous_everywhere.
Qed.

End extension_approximation.

Lemma missing_pow_mult: forall (x y:R) (n:nat),
  (x*y)^n = x^n * y^n.
Proof.
induction n.
- lra.
- simpl.
  rewrite IHn.
  lra.
Qed.

Definition extension_approximation_seq: forall n:nat,
  { g0:X -> RTop |
    continuous g0 /\
    (forall x:X, -1 + (2/3)^n <= g0 x <= 1 - (2/3)^n) /\
    (forall x:SubspaceTopology F,
      -(2/3)^n <= f x - g0 (subspace_inc F x) <= (2/3)^n) }.
simple refine (fix g (n:nat) {struct n} := match n return
  { g0:X -> RTop |
    continuous g0 /\
    (forall x:X, -1 + (2/3)^n <= g0 x <= 1 - (2/3)^n) /\
    (forall x:SubspaceTopology F,
      -(2/3)^n <= f x - g0 (subspace_inc F x) <= (2/3)^n) } with
| O => exist _ (fun _ => 0) _
| S m => match g m with
         | exist gm y =>
         let H := _ in
         let approx := extension_approximation
                       (fun x:SubspaceTopology F =>
                       (3/2)^m * (f x - gm (subspace_inc F x))) H in
         exist _ (fun x:X => gm x + (2/3)^m * approx x) _
         end
end); clear g; [ | | clearbody H ].
- simpl.
  split.
  + apply continuous_constant.
  + split; intros.
    * lra.
    * destruct (f_bound x).
      lra.
- apply pointwise_continuity.
  intros.
  apply const_multiple_continuous.
  apply diff_continuous.
  + now apply continuous_func_continuous_everywhere.
  + apply continuous_composition_at.
    * destruct y.
      now apply continuous_func_continuous_everywhere.
    * apply continuous_func_continuous_everywhere,
            subspace_inc_continuous.
- assert (H023m: 0 <= (2/3)^m).
  {
    apply pow_le. lra.
  }
  assert (H032m: 0 <= (3/2)^m).
  {
    apply pow_le. lra.
  }
  assert (forall x,
             -1 <= (3/2)^m * (f x - gm (subspace_inc F x)) <= 1).
  {
    intros.
    destruct y as [? []].
    destruct (H2 x).
    assert ((3/2)^m * (2/3)^m = 1).
    {
      rewrite <- missing_pow_mult.
      replace (3/2*(2/3)) with 1 by field.
      apply pow1.
    }
    replace (-1) with ((3/2)^m * (- (2/3)^m)) by lra.
    replace 1 with ((3/2)^m * (2/3)^m) by lra.
    auto with real.
  }
  assert (forall x, -1/3 <= approx x <= 1/3) by
    apply extension_approximation_bound.
  assert (forall x,
             -2/3 <= (3/2)^m * (f x - gm (subspace_inc F x)) -
                           approx (subspace_inc F x) <= 2/3) by
    now apply extension_approximation_diff_bound.
  destruct y as [? []].
  split.
  + apply pointwise_continuity.
    intros.
    apply sum_continuous.
    * now apply continuous_func_continuous_everywhere.
    * apply const_multiple_continuous.
      apply continuous_func_continuous_everywhere.
      apply extension_approximation_continuous.
  + split; intros.
    * destruct (H4 x), (H1 x).
      assert (0 <= (2/3)^m) by
        auto with real.
      assert ((2/3)^m * (-1/3) <= (2/3)^m * approx x <= (2/3)^m * (1/3)) by
        auto with real.
      simpl.
      lra.
    * simpl.
      replace (-(2/3*(2/3)^m)) with ((2/3)^m * (-2/3)) by field.
      replace (2/3*(2/3)^m) with ((2/3)^m * (2/3)) by ring.
      replace (f x - (gm (subspace_inc F x) + (2/3)^m * approx (subspace_inc F x)))
        with ((2/3)^m * ((3/2)^m * (f x - gm (subspace_inc F x)) -
                               approx (subspace_inc F x))).
      ** destruct (H2 x).
         auto with real.
      ** ring_simplify.
         replace ((2/3)^m*(3/2)^m) with 1.
         { ring. }
         rewrite <- missing_pow_mult.
         replace (2/3*(3/2)) with 1 by field.
         now rewrite pow1.
Defined.

Lemma extension_approximation_seq_diff: forall (n:nat) (x:X),
  -(1/3 * (2/3)^n) <= proj1_sig (extension_approximation_seq (S n)) x -
                      proj1_sig (extension_approximation_seq n) x
                   <= 1/3*(2/3)^n.
Proof.
intros.
simpl extension_approximation_seq.
destruct extension_approximation_seq.
simpl.
match goal with |- context [extension_approximation ?A ?B x] =>
  cut (-1/3 <= extension_approximation A B x <= 1/3);
  [ generalize (extension_approximation A B x) |
    apply extension_approximation_bound ] end.
intros.
assert (0 <= (2/3)^n).
{ apply pow_le. lra. }
replace (-(1/3*(2/3)^n)) with ((2/3)^n*(-1/3)) by field.
replace (1/3*(2/3)^n) with ((2/3)^n*(1/3)) by ring.
replace (x0 x + (2/3)^n*p - x0 x) with ((2/3)^n*p) by ring.
destruct H.
split;
  now apply Rmult_le_compat_l.
Qed.

(* now we've gotten what we need from the concrete definition, make
   it opaque so it doesn't slow down searches in the future *)
Global Opaque extension_approximation_seq.
Opaque extension_approximation_seq.

Lemma Rle_R1_pow: forall (x:R) (m n:nat), 0 <= x <= 1 -> (m <= n)%nat ->
  x^n <= x^m.
Proof.
induction 2;
  auto with real.
simpl.
replace (x^m) with (1*x^m) by
  auto with real.
destruct H.
apply Rmult_le_compat; trivial.
now apply pow_le.
Qed.

Lemma extension_approximation_seq_cauchy_aux:
  forall (m n:nat) (x:X),
  Rabs (proj1_sig (extension_approximation_seq m) x -
        proj1_sig (extension_approximation_seq n) x) <=
  Rabs ((2/3)^m - (2/3)^n).
Proof.
cut (forall (m n:nat) (x:X), (m <= n)%nat ->
  Rabs (proj1_sig (extension_approximation_seq m) x -
        proj1_sig (extension_approximation_seq n) x) <=
  (2/3)^m - (2/3)^n).
- intros.
  destruct (le_or_lt m n).
  + rewrite (Rabs_right ((2/3)^m - (2/3)^n)).
    { now apply H. }
    apply Rge_minus.
    cut ((2/3)^n <= (2/3)^m); auto with real.
    apply Rle_R1_pow; trivial.
    lra.
  + apply lt_le_weak in H0.
    rewrite (Rabs_left1 ((2/3)^m - (2/3)^n)).
    * replace (- ((2/3)^m - (2/3)^n)) with ((2/3)^n - (2/3)^m) by ring.
      rewrite Rabs_minus_sym.
      now apply H.
    * apply Rle_minus.
      apply Rle_R1_pow; trivial.
      lra.
- induction 1.
  + repeat match goal with |- context [ ?y - ?y ] =>
      replace (y-y) with 0 by ring end.
    rewrite Rabs_R0. lra.
  + simpl pow.
    apply Rle_trans with
      (Rabs (proj1_sig (extension_approximation_seq m) x -
             proj1_sig (extension_approximation_seq m0) x) +
       Rabs (proj1_sig (extension_approximation_seq m0) x -
             proj1_sig (extension_approximation_seq (S m0)) x)).
    * rewrite Rplus_comm.
      apply R_metric_is_metric.
    * pose proof (extension_approximation_seq_diff m0 x).
      cut (Rabs (proj1_sig (extension_approximation_seq m0) x -
                    proj1_sig (extension_approximation_seq (S m0)) x) <=
              1/3 * (2/3)^m0).
      { lra. }
      destruct H0.
      unfold Rabs.
      destruct Rcase_abs; lra.
Qed.

Definition convert_approx_to_uniform_space:
  nat -> uniform_space R_metric (fun _:X => 0).
refine (fun n:nat => exist _ (proj1_sig (extension_approximation_seq n)) _).
destruct extension_approximation_seq as [g [? []]].
simpl.
unfold R_metric.
exists (1 - (2/3)^n).
red. intros.
destruct H.
rewrite H0. clear y H0.
destruct (a x).
unfold Rabs.
destruct Rcase_abs; lra.
Defined.

Lemma extension_approximation_seq_cauchy:
  cauchy (uniform_metric R_metric (fun _:X => 0)
          R_metric_is_metric X_nonempty)
    convert_approx_to_uniform_space.
Proof.
red. intros.
assert (Rabs (2/3) < 1).
{ rewrite Rabs_right; lra. }
assert (0 < eps/2) by lra.
destruct (pow_lt_1_zero (2/3) H0 (eps/2) H1) as [N].
exists N.
intros.
apply Rle_lt_trans with (Rabs ((2/3)^m - (2/3)^n)).
- unfold uniform_metric, convert_approx_to_uniform_space.
  destruct sup.
  simpl.
  apply i.
  red. intros.
  destruct H5.
  rewrite H6. clear y H6.
  rewrite metric_sym.
  + apply extension_approximation_seq_cauchy_aux.
  + exact R_metric_is_metric.
- apply Rle_lt_trans with (Rabs ((2/3)^m) + Rabs((2/3)^n)).
  + rewrite <- (Rabs_Ropp ((2/3)^n)).
    unfold Rminus.
    apply Rabs_triang.
  + replace eps with (eps/2 + eps/2) by field.
    apply Rplus_lt_compat;
      now apply H2.
Qed.

Definition Tietze_extension_func : X -> RTop.
refine (proj1_sig (proj1_sig (constructive_definite_description
  (fun f:(UniformTopology R_metric (fun _:X => 0)
                    R_metric_is_metric X_nonempty) =>
  net_limit convert_approx_to_uniform_space f
    (I:=nat_DS) (X:=UniformTopology R_metric (fun _:X => 0)
                    R_metric_is_metric X_nonempty)) _))).
apply -> unique_existence.
split.
- assert (complete (uniform_metric R_metric (fun _:X => 0)
                      R_metric_is_metric X_nonempty)
            (uniform_metric_is_metric _ _ _ _ _ _)).
  { apply uniform_metric_complete.
    exact R_metric_complete. }
  apply H.
  exact extension_approximation_seq_cauchy.
- apply Hausdorff_impl_net_limit_unique.
  apply T3_sep_impl_Hausdorff.
  apply normal_sep_impl_T3_sep.
  apply metrizable_impl_normal_sep.
  exists (uniform_metric R_metric (fun _:X => 0)
            R_metric_is_metric X_nonempty).
  + apply (uniform_metric_is_metric _ _ R_metric (fun _:X => 0)
              R_metric_is_metric X_nonempty).
  + apply MetricTopology_metrized.
Defined.

Lemma Tietze_extension_func_bound: forall x:X,
  -1 <= Tietze_extension_func x <= 1.
Proof.
intros.
cut (Rabs (Tietze_extension_func x) <= 1).
{ intros.
  unfold Rabs in H.
  destruct Rcase_abs in H; lra. }
unfold Tietze_extension_func.
destruct constructive_definite_description as [[g]].
simpl.
assert (bound (Im Full_set (fun x:X => R_metric 0 0))).
{ exists 0.
  red. intros.
  destruct H.
  right.
  rewrite H0.
  apply R_metric_is_metric. }
apply Rle_trans with (uniform_metric _ _ R_metric_is_metric X_nonempty
                    (exist _ (fun _:X => 0) H)
                    (exist _ g b)).
- unfold uniform_metric.
  simpl.
  destruct sup.
  simpl.
  apply i.
  exists x.
  + constructor.
  + unfold R_metric.
    f_equal.
    auto with real.
- apply lt_plus_epsilon_le.
  intros.
  unshelve refine (let H1:=metric_space_net_limit_converse _ _ _ _ _ _ n eps H0 in _); [ | | clearbody H1 ]; shelve_unifiable.
  { apply MetricTopology_metrized. }
  destruct H1 as [N].
  refine (Rle_lt_trans _ _ _
    (triangle_inequality _ _ _ _ (convert_approx_to_uniform_space N) _) _).
  { apply uniform_metric_is_metric. }
  apply Rplus_lt_compat.
  + apply Rle_lt_trans with (1 - (2/3)^N).
    * unfold uniform_metric. simpl. destruct sup. simpl.
      apply i.
      red. intros.
      destruct H2.
      rewrite H3. clear y H3.
      unfold R_metric.
      destruct extension_approximation_seq as [h [? []]].
      destruct (a x1).
      simpl.
      unfold Rabs. destruct Rcase_abs; lra.
    * assert ((2/3)^N > 0).
      { apply pow_lt; lra. }
      lra.
  + rewrite metric_sym.
    * apply H1.
      constructor.
    * apply uniform_metric_is_metric.
Qed.

Lemma Tietze_extension_func_is_extension:
  forall x:SubspaceTopology F,
  Tietze_extension_func (subspace_inc F x) = f x.
Proof.
intros.
apply R_metric_is_metric.
apply Rle_antisym.
2: {
  apply Rge_le, metric_nonneg, R_metric_is_metric.
}
apply lt_plus_epsilon_le; intros.
unfold Tietze_extension_func;
  destruct constructive_definite_description as [[g]]; simpl.
assert (eps/2 > 0) by lra.
unshelve refine (let H1:=metric_space_net_limit_converse _ _ _ _ _ _ n (eps/2) H0
          in _); [ | | clearbody H1 ]; shelve_unifiable.
{ apply MetricTopology_metrized. }
destruct H1 as [N1].
assert (Rabs (2/3) < 1).
{ rewrite Rabs_right; lra. }
destruct (pow_lt_1_zero (2/3) H2 (eps/2) H0) as [N2].
pose (N := max N1 N2).
apply Rle_lt_trans with (R_metric (g (subspace_inc F x))
          (proj1_sig (extension_approximation_seq N) (subspace_inc F x)) +
  R_metric (proj1_sig (extension_approximation_seq N) (subspace_inc F x))
    (f x)).
{ apply triangle_inequality, R_metric_is_metric. }
replace (0+eps) with (eps/2+eps/2) by field.
apply Rplus_lt_compat.
- rewrite metric_sym; try apply R_metric_is_metric.
  assert (DS_ord N1 N) by apply le_max_l.
  apply Rle_lt_trans with (2:=H1 N H4).
  unfold uniform_metric; simpl; destruct sup; simpl.
  apply i.
  exists (subspace_inc F x).
  { constructor. }
  apply R_metric_is_metric.
- assert ((N >= N2)%nat) by apply le_max_r.
  apply Rle_lt_trans with (2:=H3 N H4).
  rewrite Rabs_right.
  + destruct extension_approximation_seq as [h [? []]]; simpl.
    unfold R_metric.
    destruct (a0 x).
    unfold Rabs; destruct Rcase_abs; lra.
  + apply Rle_ge, pow_le; lra.
Qed.

Let convert_continuity: forall h:X -> R,
  continuous h (Y:=RTop) <-> continuous h (Y:=MetricTopology R_metric
                                           R_metric_is_metric).
Proof.
assert (continuous (fun x:R => x)
  (X:=RTop) (Y:=MetricTopology R_metric R_metric_is_metric)).
{ apply pointwise_continuity.
  intros.
  apply metric_space_fun_continuity with R_metric R_metric;
    intros.
  - apply RTop_metrization.
  - apply MetricTopology_metrized.
  - now exists eps. }
assert (continuous (fun x:R => x)
  (X:=MetricTopology R_metric R_metric_is_metric) (Y:=RTop)).
{ apply pointwise_continuity.
  intros.
  apply metric_space_fun_continuity with R_metric R_metric;
    intros.
  - apply MetricTopology_metrized.
  - apply RTop_metrization.
  - now exists eps. }
intros.
split; intros.
- apply continuous_composition with (1:=H) (2:=H1).
- apply continuous_composition with (1:=H0) (2:=H1).
Qed.

Lemma Tietze_extension_func_continuous: continuous Tietze_extension_func.
Proof.
unfold Tietze_extension_func;
  destruct constructive_definite_description as [g];
  simpl.
apply net_limit_in_closure with
  (S:=fun h:UniformTopology R_metric (fun _:X => 0)
                          R_metric_is_metric X_nonempty =>
     continuous (proj1_sig h)
     (Y:=MetricTopology R_metric R_metric_is_metric)) in n.
- rewrite closure_fixes_closed in n.
  + unfold In in n.
    now apply <- convert_continuity.
  + apply continuous_functions_closed_in_uniform_metric.
- red. intros.
  exists i.
  split.
  + constructor.
  + red.
    unfold convert_approx_to_uniform_space. simpl.
    destruct extension_approximation_seq as [h [? []]]. simpl.
    now apply -> convert_continuity.
Qed.

End Tietze_extension_construction.

Lemma bounded_Tietze_extension_theorem: forall (X:TopologicalSpace)
  (F:Ensemble X) (f:SubspaceTopology F -> RTop),
  normal_sep X -> closed F -> continuous f ->
  (forall x:SubspaceTopology F, -1 <= f x <= 1) ->
  exists g:X -> RTop,
    continuous g /\ (forall x:SubspaceTopology F,
                     g (subspace_inc F x) = f x) /\
    (forall x:X, -1 <= g x <= 1).
Proof.
intros.
destruct (classic (inhabited X)) as [Hinh|Hempty].
- destruct (choice (fun
    (FG:{FG:Ensemble X * Ensemble X | let (F,G):=FG in
                      closed F /\ closed G /\ Intersection F G = Empty_set})
    (phi:X -> RTop) =>
     let (F,G):=proj1_sig FG in
     continuous phi /\ (forall x:X, 0 <= phi x <= 1) /\
     (forall x:X, In F x -> phi x = 0) /\
     (forall x:X, In G x -> phi x = 1))) as [choice_fun].
  + intros.
    destruct x as [[F' G] [? []]].
    now apply UrysohnsLemma.
  + pose (Urysohns_lemma_function := fun (F G:Ensemble X)
      (HF:closed F) (HG:closed G) (Hdisj:Intersection F G = Empty_set) =>
      exist (fun (f:X -> RTop) =>
               continuous f /\ (forall x:X, 0 <= f x <= 1) /\
               (forall x:X, In F x -> f x = 0) /\
               (forall x:X, In G x -> f x = 1))
        (choice_fun (exist _ (F,G) (conj HF (conj HG Hdisj))))
        (H3 (exist _ (F,G) (conj HF (conj HG Hdisj))))).
    clearbody Urysohns_lemma_function. clear choice_fun H3.
    exists (Tietze_extension_func X F H0 f H1 H2 Hinh
      Urysohns_lemma_function).
    split.
    * apply Tietze_extension_func_continuous.
    * split; intros.
      ** apply Tietze_extension_func_is_extension.
      ** apply Tietze_extension_func_bound.
- exists (fun x:X => False_rect _ (Hempty (inhabits x))).
  split.
  + apply pointwise_continuity.
    intros.
    destruct (Hempty (inhabits x)).
  + split;
      intros.
    * destruct x.
      destruct (Hempty (inhabits x)).
    * destruct (Hempty (inhabits x)).
Qed.

Lemma open_bounded_Tietze_extension_theorem: forall (X:TopologicalSpace)
  (F:Ensemble X) (f:SubspaceTopology F -> RTop),
  normal_sep X -> closed F -> continuous f ->
  (forall x:SubspaceTopology F, -1 < f x < 1) ->
  exists g:X -> RTop,
    continuous g /\ (forall x:SubspaceTopology F,
                     g (subspace_inc F x) = f x) /\
    (forall x:X, -1 < g x < 1).
Proof.
intros.
destruct (bounded_Tietze_extension_theorem _ F f) as [g0 [? []]]; trivial.
{ intros. split; left; apply H2. }
pose (G := characteristic_function_to_ensemble (fun x:X =>
  g0 x = 1 \/ g0 x = -1)).
destruct (UrysohnsLemma _ H G F) as [phi [? [? []]]]; trivial.
- replace G with (inverse_image g0 (Union (Singleton 1) (Singleton (-1)))).
  + red. rewrite <- inverse_image_complement.
    apply H3.
    apply (closed_union2 (X:=RTop)); apply Hausdorff_impl_T1_sep;
      apply T3_sep_impl_Hausdorff; apply normal_sep_impl_T3_sep;
      apply metrizable_impl_normal_sep; exists R_metric;
      (apply R_metric_is_metric || apply RTop_metrization).
  + extensionality_ensembles_inv;
      constructor.
    * now left.
    * now right.
    * destruct H7;
        [left | right ];
        now rewrite H6.
- extensionality_ensembles.
  assert (-1 < g0 x < 1).
  { change x with (subspace_inc F (exist _ x H7)).
    now rewrite H4. }
  lra.
- exists (fun x => phi x * g0 x).
  split.
  { apply pointwise_continuity.
    intros.
    apply product_continuous;
      now apply continuous_func_continuous_everywhere.
  }
  split.
  { intros.
    rewrite H9.
    - replace (1*g0 (subspace_inc F x)) with (g0 (subspace_inc F x)) by
        auto with real.
      apply H4.
    - now destruct x.
  }
  intros.
  apply and_comm, Rabs_def2.
  rewrite Rabs_mult.
  rewrite (Rabs_right (phi x));
    [ | apply Rle_ge; apply H7 ].
  destruct (classic (In G x)).
  { rewrite H8; trivial. lra. }
  assert (Rabs (g0 x) < 1).
  { assert (Rabs (g0 x) <= 1).
    { destruct (H5 x).
      unfold Rabs; destruct Rcase_abs; lra. }
    destruct H11; trivial.
    contradiction H10.
    unfold Rabs in H11.
    destruct Rcase_abs in H11;
      constructor.
    - lra.
    - now left. }
  destruct (H7 x).
  apply Rle_lt_trans with (Rabs (g0 x)); trivial.
  pattern (Rabs (g0 x)) at 2.
  replace (Rabs (g0 x)) with (1*Rabs (g0 x)) by
    auto with real.
  apply Rmult_le_compat_r; trivial.
  apply Rabs_pos.
Qed.

Theorem Tietze_extension_theorem: forall (X:TopologicalSpace)
  (F:Ensemble X) (f:SubspaceTopology F -> RTop),
  normal_sep X -> closed F -> continuous f ->
  exists g:X -> RTop,
    continuous g /\ (forall x:SubspaceTopology F,
                     g (subspace_inc F x) = f x).
Proof.
intros.
pose (U := characteristic_function_to_ensemble
      (fun x:RTop => -1 < x < 1)).
pose proof (open_interval_homeomorphic_to_real_line).
fold U in H2.
simpl in H2.
destruct H2 as [a [b]].
pose (f0 := fun x:SubspaceTopology F => subspace_inc U (a (f x))).
destruct (open_bounded_Tietze_extension_theorem X F f0) as [g0 [? []]];
  trivial.
- unfold f0.
  apply continuous_composition.
  + apply subspace_inc_continuous.
  + now apply continuous_composition.
- intros.
  unfold f0.
  destruct (a (f x)).
  now destruct i.
- assert (forall x:X, In U (g0 x)).
  { intros.
    constructor.
    apply H8. }
  pose (g0_U := continuous_factorization g0 U H9).
  assert (continuous g0_U) by
    now apply factorization_is_continuous.
  exists (fun x:X => b (g0_U x)).
  split.
  { now apply continuous_composition. }
  intros.
  unfold g0_U, continuous_factorization.
  generalize (H9 (subspace_inc F x)).
  rewrite H7.
  intros.
  replace (exist _ (f0 x) i) with (a (f x)) by
    now apply (proj1_sig_injective (In U)).
  apply H4.
Qed.

From Coq Require Import
  Lra
  Reals.
From Topology Require Import
  MetricSpaces.

Lemma Rlt_div_pos_r (a b c : R) :
  0 < c ->
  a < b / c -> a * c < b.
Proof.
  intros Hc Habc.
  apply Rmult_lt_reg_r with (r := / c).
  { apply Rinv_0_lt_compat; assumption. }
  rewrite Rmult_assoc.
  rewrite Rinv_r; lra.
Qed.

Definition Lipschitz
  {X Y : Type} (dx : X -> X -> R) (dy : Y -> Y -> R) (f : X -> Y) (q : R) :=
  forall x1 x2 : X,
    dy (f x1) (f x2) <= q * dx x1 x2.

(* what happens if the Lipschitz-constant is negative or zero? *)
Lemma Lipschitz_zero_impl_constant
  {X Y : Type} dx dy
  (dy_metric : metric dy)
  (f : X -> Y) :
  Lipschitz dx dy f 0%R ->
  forall x1 x2 : X, f x1 = f x2.
Proof.
  intros Hf x1 x2.
  apply (metric_strict dy_metric).
  apply Rle_antisym.
  - specialize (Hf x1 x2). lra.
  - pose proof (metric_nonneg dy_metric (f x1) (f x2));
      lra.
Qed.

(* it is impossible for [f : X -> Y] to have a negative lipschitz constant,
  if [X] has at least two points *)
Lemma Lipschitz_neg_nontriv
  {X Y : Type} dx dy
  (dx_metric : metric dx)
  (dy_metric : metric dy)
  (f : X -> Y) (L : R)
  (x1 x2 : X) (Hx : x1 <> x2) :
  L < 0 ->
  Lipschitz dx dy f L -> False.
Proof.
  intros HL HfL.
  specialize (HfL x1 x2).
  (* since [L] is negative and [dx x1 x2] is positive,
     we can conclude that [dy (f x1) (f x2)] is negative. *)
  assert (dy (f x1) (f x2) < 0).
  { eapply Rle_lt_trans; eauto.
    rewrite <- (Rmult_0_l (dx x1 x2)).
    apply Rmult_lt_compat_r; auto.
    apply metric_distinct_pos; auto.
  }
  pose proof (metric_nonneg dy_metric (f x1) (f x2)).
  lra.
Qed.

Lemma Lipschitz_impl_continuous
  {X Y : TopologicalSpace}
  dx dy (dx_metric : metric dx) (dy_metric : metric dy)
  (dx_metrizes : metrizes X dx) (dy_metrizes : metrizes Y dy)
  (f : X -> Y) (L : R) :
  0 <= L -> Lipschitz dx dy f L ->
  continuous f.
Proof.
  intros HL HfL.
  apply pointwise_continuity.
  intros x0.
  apply metric_space_fun_continuity
    with (dX := dx) (dY := dy); auto.
  intros eps Heps.
  destruct HL as [HL|HL].
  2: {
    (* if [L = 0] *)
    subst L.
    pose proof (Lipschitz_zero_impl_constant
                  dx dy dy_metric f HfL) as Hf.
    exists 1%R. split; try lra.
    intros x1 _. rewrite (Hf x1 x0).
    rewrite metric_zero; auto.
  }
  (* if [0 < L] *)
  exists (eps/L). split.
  { apply Rlt_gt.
    apply Rdiv_lt_0_compat; lra.
  }
  intros x1 Hxx.
  specialize (HfL x0 x1).
  eapply Rle_lt_trans; eauto.
  apply Rlt_div_pos_r in Hxx; lra.
Qed.

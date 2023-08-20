From Topology Require Export TopologicalSpaces NeighborhoodBases Nets Continuity CountabilityAxioms SupInf SeparatednessAxioms.
From Topology Require Import RationalsInReals.
From ZornsLemma Require Export EnsemblesSpec.
From ZornsLemma Require Import EnsemblesTactics DecidableDec.
From Coq Require Import Reals ClassicalChoice Program.Subset.
From Coq Require Import Lia Lra.

Open Scope R_scope.

Section metric.

Variable X:Type.
Variable d:X->X->R.

Record metric : Prop := {
  metric_sym: forall x y:X, d x y = d y x;
  triangle_inequality: forall x y z:X, d x z <= d x y + d y z;
  metric_zero: forall x:X, d x x = 0;
  metric_strict: forall x y:X, d x y = 0 -> x = y
}.

Lemma metric_nonneg :
  metric ->
  forall x y : X, d x y >= 0.
Proof.
  intros.
  pose proof (triangle_inequality H x y x).
  rewrite (metric_sym H y x) in H0.
  rewrite (metric_zero H) in H0.
  lra.
Qed.

End metric.

Arguments metric {X}.

Section metric_topology.

Context {X:Type}.
Variable d:X->X->R.
Hypothesis d_is_metric: metric d.

Definition open_ball (x0:X) (r:R) : Ensemble X :=
  [ x:X | d x0 x < r ].

Definition closed_ball (x0 : X) (r : R) : Ensemble X :=
  [x : X | d x0 x <= r].

Inductive metric_topology_neighborhood_basis (x:X) : Family X :=
  | intro_open_ball: forall r:R, r > 0 ->
    In (metric_topology_neighborhood_basis x) (open_ball x r).

Definition MetricTopology : TopologicalSpace.
refine (Build_TopologicalSpace_from_open_neighborhood_bases
  X metric_topology_neighborhood_basis _ _ _ _);
  intros.
- destruct H as [r1 ?].
  destruct H0 as [r2 ?].
  exists (open_ball x (Rmin r1 r2)); split.
  + constructor.
    apply Rmin_Rgt_r; split; trivial.
  + red. intros.
    destruct H1.
    constructor;
      constructor;
      apply Rlt_le_trans with (Rmin r1 r2); trivial.
    * apply Rmin_l.
    * apply Rmin_r.
- destruct H.
  constructor.
  now rewrite metric_zero.
- exists (open_ball x 1).
  constructor.
  auto with *.
- destruct H.
  destruct H0.
  exists (open_ball y (r - d x y)); split.
  + constructor.
    now apply Rgt_minus.
  + red. intros z ?.
    destruct H1.
    constructor.
    apply Rle_lt_trans with (d x y + d y z).
    * now apply triangle_inequality.
    * assert (d x y + d y z < d x y + (r - d x y)) by
        auto with *.
      now ring_simplify in H2.
Defined.

End metric_topology.

Arguments metric_topology_neighborhood_basis {X}.
Arguments MetricTopology {X}.

Definition bounded {X : Type} (d : X -> X -> R) (A : Ensemble X) :=
  exists x r, Included A (open_ball d x r).

Definition metrizes (X:TopologicalSpace)
  (d:X -> X -> R) : Prop :=
  forall x:X, open_neighborhood_basis
             (metric_topology_neighborhood_basis d x) x.

Inductive metrizable (X:TopologicalSpace) : Prop :=
  | intro_metrizable: forall d:X -> X -> R,
    metric d -> metrizes X d ->
    metrizable X.

Lemma MetricTopology_metrized: forall (X:Type) (d:X->X->R)
  (d_metric: metric d),
  metrizes (MetricTopology d d_metric) d.
Proof.
intros.
red.
intros.
apply Build_TopologicalSpace_from_open_neighborhood_bases_basis.
Qed.

Corollary MetricTopology_metrizable X (d:X->X->R) d_metric :
  metrizable (MetricTopology d d_metric).
Proof.
apply intro_metrizable with (d := d).
- assumption.
- apply MetricTopology_metrized.
Qed.

Lemma metric_open_ball_In X (d : X -> X -> R) :
  metric d -> forall x r,
    0 < r <->
    In (open_ball d x r) x.
Proof.
  intros.
  split.
  - intros.
    constructor.
    rewrite metric_zero; assumption.
  - intros.
    destruct H0.
    rewrite metric_zero in H0; assumption.
Qed.

Lemma metric_open_ball_radius_nonpositive X d :
  @metric X d ->
  forall x r,
    r <= 0 ->
    open_ball d x r = Empty_set.
Proof.
  intros.
  apply Extensionality_Ensembles; split; red; intros; try contradiction.
  destruct H1.
  pose proof (metric_nonneg X d H x x0).
  lra.
Qed.

Lemma metric_open_ball_radius_nonpositive0 X d :
  @metric X d ->
  forall x r,
    open_ball d x r = Empty_set ->
    r <= 0.
Proof.
  intros.
  apply NNPP. intros ?.
  apply Rnot_le_lt in H1.
  apply (metric_open_ball_In X d H x) in H1.
  rewrite H0 in H1.
  destruct H1.
Qed.

Lemma closed_ball_radius_zero X d (x0 : X) :
  metric d ->
  closed_ball d x0 0 = Singleton x0.
Proof.
  intros.
  apply Extensionality_Ensembles; split; red; intros.
  - destruct H0.
    apply Singleton_intro.
    apply (metric_strict _ _ H).
    apply Rle_antisym; try assumption.
    pose proof (metric_nonneg _ _ H x0 x).
    lra.
  - constructor. destruct H0.
    rewrite metric_zero; auto; lra.
Qed.

Lemma metric_closed_ball_In X (d : X -> X -> R) :
  metric d -> forall x r,
    0 <= r <->
    In (closed_ball d x r) x.
Proof.
  intros.
  pose proof (metric_zero X d H x).
  split.
  - intros.
    constructor.
    lra.
  - intros.
    destruct H1.
    lra.
Qed.

Lemma closed_ball_radius_negative X d :
  @metric X d ->
  forall x r,
    r < 0 <->
    closed_ball d x r = Empty_set.
Proof.
  intros.
  split.
  - intros.
    apply Extensionality_Ensembles; split; red; intros; try contradiction.
    destruct H1.
    pose proof (metric_nonneg X d H x x0).
    lra.
  - intros.
    apply NNPP.
    intros ?.
    apply not_Rlt in H1.
    apply Rge_le in H1.
    apply (metric_closed_ball_In X d H x r) in H1.
    rewrite H0 in H1.
    destruct H1.
Qed.

Lemma metric_open_closed_ball_Included X d (x : X) r :
  Included (open_ball d x r) (closed_ball d x r).
Proof.
  intros ? ?.
  destruct H.
  constructor.
  lra.
Qed.

Lemma metric_space_open_ball_open :
  forall (X:TopologicalSpace) (d:X -> X -> R),
    metrizes X d -> metric d ->
    forall x r, open (open_ball d x r).
Proof.
  intros.
  specialize (H x).
  destruct (classic (r > 0)).
  - assert (In (metric_topology_neighborhood_basis d x) (open_ball d x r)).
    { constructor. assumption. }
    apply H in H2.
    destruct H2.
    assumption.
  - rewrite metric_open_ball_radius_nonpositive;
      auto with topology; lra.
Qed.

Lemma metric_space_closed_ball_closed {X : TopologicalSpace} (d : X -> X -> R) :
  metrizes X d -> metric d ->
  forall x r, closed (closed_ball d x r).
Proof.
  intros.
  red.
  apply open_char_neighborhood.
  intros.
  exists (open_ball d x0 (d x x0 - r)).
  split.
  - split.
    + apply metric_space_open_ball_open; assumption.
    + apply metric_open_ball_In; auto.
      apply NNPP. intros ?.
      apply H1. constructor. lra.
  - intros ? ?.
    destruct H2.
    intros ?.
    destruct H3.
    pose proof (triangle_inequality X d H0 x x1 x0).
    rewrite (metric_sym X d H0 x1 x0) in H4.
    lra.
Qed.

Lemma metric_space_net_limit: forall (X:TopologicalSpace)
  (d:X -> X -> R), metrizes X d ->
  forall (I:DirectedSet) (x:Net I X) (x0:X),
  (forall eps:R, eps > 0 -> for large i:DS_set I, d x0 (x i) < eps) ->
  net_limit x x0.
Proof.
intros.
red. intros.
destruct (H x0).
destruct (open_neighborhood_basis_cond U) as [V []].
- now split.
- destruct H3.
  apply eventually_impl_base with (2:=H0 r H3).
  intros.
  apply H4.
  now constructor.
Qed.

Lemma metric_space_net_limit_converse: forall (X:TopologicalSpace)
  (d:X -> X -> R), metrizes X d ->
  forall (I:DirectedSet) (x:Net I X) (x0:X),
    net_limit x x0 -> forall eps:R, eps > 0 ->
                         for large i:DS_set I, d x0 (x i) < eps.
Proof.
intros.
pose (U:=open_ball d x0 eps).
assert (open_neighborhood U x0).
{ apply H.
  now constructor. }
destruct H2.
destruct (H0 U) as [i]; trivial.
exists i.
intros.
now apply H4.
Qed.

Lemma metric_space_net_cluster_point: forall (X:TopologicalSpace)
  (d:X -> X -> R), metrizes X d ->
  forall (I:DirectedSet) (x:Net I X) (x0:X),
  (forall eps:R, eps > 0 ->
     exists arbitrarily large i:DS_set I, d x0 (x i) < eps) ->
  net_cluster_point x x0.
Proof.
intros.
red. intros.
destruct (H x0).
destruct (open_neighborhood_basis_cond U) as
  [? [[]]].
- now split.
- red. intros.
  destruct (H0 r H3 i) as [j []].
  exists j; split; trivial.
  apply H4.
  now constructor.
Qed.

Lemma metric_space_net_cluster_point_converse: forall (X:TopologicalSpace)
  (d:X -> X -> R), metrizes X d ->
  forall (I:DirectedSet) (x:Net I X) (x0:X),
    net_cluster_point x x0 -> forall eps:R, eps > 0 ->
                exists arbitrarily large i:DS_set I, d x0 (x i) < eps.
Proof.
intros.
pose (U:=open_ball d x0 eps).
assert (open_neighborhood U x0).
{ apply H.
  now constructor. }
destruct H2.
pose proof (H0 U H2 H3).
red. intros.
destruct (H4 i) as [j []].
exists j.
split; trivial.
now destruct H6.
Qed.

Lemma metric_space_fun_continuity_converse: forall (X Y:TopologicalSpace)
  (f:X->Y) (x:X)
  (dX:X -> X -> R)
  (dY:Y -> Y -> R),
  metrizes X dX -> metrizes Y dY ->
  continuous_at f x -> forall eps:R, eps > 0 ->
                         exists delta:R, delta > 0 /\
                         forall x':X, dX x x' < delta ->
                                 dY (f x) (f x') < eps.
Proof.
intros.
destruct (H x).
destruct (H0 (f x)).
assert (neighborhood (open_ball dY (f x) eps) (f x)).
{ apply open_neighborhood_is_neighborhood.
  apply open_neighborhood_basis_elements0.
  now constructor. }
apply H1 in H3.
destruct H3 as [U].
destruct H3.
destruct (open_neighborhood_basis_cond U H3) as [V].
destruct H5.
destruct H5 as [delta].
exists delta.
split; trivial.
intros.
assert (In (inverse_image f (open_ball dY (f x) eps)) x').
{ apply H4, H6.
  now constructor. }
destruct H8.
now destruct H8.
Qed.

Lemma metric_space_fun_continuity: forall (X Y:TopologicalSpace)
  (f:X->Y) (x:X)
  (dX:X -> X -> R)
  (dY:Y -> Y -> R),
  metrizes X dX -> metrizes Y dY ->
  (forall eps:R, eps > 0 -> exists delta:R, delta > 0 /\
                         forall x':X, dX x x' < delta ->
                                 dY (f x) (f x') < eps) ->
  continuous_at f x.
Proof.
intros.
destruct (H x).
destruct (H0 (f x)).
red; intros.
destruct H2 as [V'].
destruct H2.
destruct (open_neighborhood_basis_cond0 V' H2).
destruct H4.
destruct H4 as [eps].
destruct (H1 eps H4) as [delta []].
exists (open_ball dX x delta).
split.
- apply open_neighborhood_basis_elements.
  now constructor.
- intros x' ?.
  destruct H8.
  constructor.
  apply H3, H5.
  constructor.
  now apply H7.
Qed.

Open Scope R_scope.

Lemma metrizable_impl_first_countable: forall X:TopologicalSpace,
  metrizable X -> first_countable X.
Proof.
intros.
destruct H.
red. intros.
exists (Im [n:nat | (n>0)%nat]
           (fun n:nat => open_ball d x (/ (INR n)))).
split.
- apply open_neighborhood_basis_is_neighborhood_basis.
  constructor; intros.
  + destruct H1 as [n ? V].
    destruct H1.
    apply H0.
    rewrite H2; constructor.
    auto with *.
  + destruct (H0 x).
    destruct (open_neighborhood_basis_cond U) as [V [[eps] ?]]; trivial.
    destruct (inverses_of_nats_approach_0 eps H2) as [n [? ?]].
    exists (open_ball d x (/ (INR n))).
    split.
    * now exists n.
    * red. intros y ?.
      apply H3.
      destruct H6.
      constructor.
      now apply Rlt_trans with (/ INR n).
- apply countable_img.
  apply countable_type_ensemble.
  now exists (fun n => n).
Qed.

Lemma metrizable_separable_impl_second_countable:
  forall X:TopologicalSpace, metrizable X -> separable X ->
    second_countable X.
Proof.
intros.
destruct H, H0 as [S []].
exists (Im [p:(Q*X)%type |
            let (r,x):=p in (r>0)%Q /\ In S x]
  (fun p:(Q*X)%type =>
      let (r,x):=p in open_ball d x (Q2R r))).
split.
- constructor.
  + intros.
    destruct H3.
    subst.
    destruct x as [r x].
    destruct H3 as [[]].
    destruct (H1 x).
    destruct (open_neighborhood_basis_elements (open_ball d x (Q2R r)));
      trivial.
    constructor; try lra.
    rewrite <- RMicromega.Q2R_0.
    now apply Qlt_Rlt.
  + intros.
    destruct (H1 x).
    destruct (open_neighborhood_basis_cond U) as [V [[r]]].
    { now split. }
    destruct (dense_meets_every_nonempty_open _ _ H2
      (open_ball d x (r/2))).
    { apply metric_space_open_ball_open; auto. }
    { exists x.
      apply metric_open_ball_In; auto.
      lra.
    }
    destruct H7, H8.
    destruct (rationals_dense_in_reals (d x x0) (r - d x x0)) as [r'].
    { lra. }
    exists (open_ball d x0 (Q2R r')).
    repeat split.
    * exists ( (r', x0) ); trivial.
      constructor.
      split; trivial.
      assert (Q2R r' > 0).
      { apply Rgt_ge_trans with (d x x0).
        - apply H9.
        - now apply metric_nonneg.
      }
      apply Rlt_Qlt.
      unfold Q2R at 1.
      simpl.
      now ring_simplify.
    * red. intros y ?.
      destruct H10.
      apply H6.
      constructor.
      eapply Rle_lt_trans.
      -- now apply triangle_inequality.
      -- apply Rlt_trans with (d x x0 + Q2R r');
           auto with real.
         lra.
    * destruct H9.
      now rewrite metric_sym.
- apply countable_img.
  destruct H0 as [h].
  destruct Q_countable.
  destruct countable_nat_product as [g].
  red.
  match goal with |- CountableT ?T =>
  exists (fun x:T =>
    match x with
    | exist (r, x0) (intro_characteristic_sat (conj r_pos i)) =>
      g (h (exist _ x0 i), f r)
    end)
  end.
  red. intros x y H5.
  destruct x as [[r1 x1] [[pos_r1 i1]]].
  destruct y as [[r2 x2] [[pos_r2 i2]]].
  apply subset_eq.
  simpl.
  apply H4 in H5.
  inversion H5; subst; clear H5.
  apply H3 in H8. subst.
  apply H0 in H7.
  inversion H7; subst; clear H7.
  reflexivity.
Qed.

Lemma open_ball_half_radius_included X d r s x0 x1 :
  @metric X d ->
  In (open_ball d x1 s) x0 ->
  0 < s < r / 2 ->
  Included (open_ball d x1 s) (open_ball d x0 r).
Proof.
  intros ? ? ? z Hz.
  constructor.
  destruct Hz.
  destruct H0.
  apply (Rle_lt_trans _ (d x0 x1 + d x1 z)).
  { now apply triangle_inequality. }
  rewrite (metric_sym _ _ H x0 x1).
  lra.
Qed.

Lemma metrizable_Lindelof_impl_second_countable:
  forall X:TopologicalSpace, metrizable X -> Lindelof X ->
    second_countable X.
Proof.
intros X [d Hmetric Hmetrizes] HLindelof.
(* For each [n], [small_balls n] is the open cover of [X] by balls of radius
   [1 / n]. *)
pose (small_balls := (fun n : { n : nat | (n > 0)%nat } =>
                        Im Full_set (fun x : X =>
                                       open_ball d x (/ (INR (proj1_sig n)))))).
assert (forall n, open_cover (small_balls n)) as Hballs_cover.
{ destruct n as [n].
  split.
  - intros U H.
    destruct H as [x ? U].
    destruct (Hmetrizes x).
    subst.
    apply metric_space_open_ball_open; auto.
  - extensionality_ensembles.
    { constructor. }
    simpl.
    exists (open_ball d x (/ INR n)).
    + now exists x.
    + constructor.
      rewrite metric_zero; auto with real.
}
(* We can choose for each (positive) [n:nat], a countable family of
   the small balls that still cover the whole space (using the Lindelof property). *)
destruct (choice (fun (n:{n:nat | (n > 0)%nat}) (S:Family X) =>
  subcover S (small_balls n) /\ Countable S))
  as [choice_fun Hchoice_fun].
{ intros. auto. (* here we use the [HLindelof] assumption. *) }
exists (IndexedUnion choice_fun). split.
2: {
  (* Countability *)
  apply countable_indexed_union.
  - apply countable_type_ensemble.
    exists (fun n:nat => n).
    now red.
  - intro.
    apply Hchoice_fun.
}
split.
{ intros V HV.
  destruct HV as [n V HV].
  apply (Hballs_cover n).
  apply (Hchoice_fun n).
  assumption.
}
intros.
destruct (open_neighborhood_basis_cond _ x (Hmetrizes x) U)
  as [V [HVbasis HVU]].
{ now split. }
inversion HVbasis; subst; clear HVbasis.
destruct (inverses_of_nats_approach_0 (r/2)) as [n [Hnpos ?]].
{ lra. }
pose (nsig := exist _ n Hnpos).
destruct (Hchoice_fun nsig) as [[Hnsig_subcover0 Hnsig_subcover1] Hnsig_countable].
assert (In (FamilyUnion (choice_fun nsig)) x) as Hx.
{ apply Hnsig_subcover1.
  exists (open_ball d x (/ INR n)).
  { exists x; constructor. }
  apply metric_open_ball_In; auto.
  apply Rinv_0_lt_compat.
  apply lt_0_INR.
  lia.
}
destruct Hx as [W x HW_nsig HWx].
exists W.
repeat split.
{ exists nsig. assumption. }
2: {
  assumption.
}
assert (Included W (open_ball d x r)); auto with sets.
pose proof (Hnsig_subcover0 _ HW_nsig) as HW_small_balls.
destruct HW_small_balls. subst.
simpl in *.
apply open_ball_half_radius_included; auto.
split; auto with real.
Qed.

Lemma metrizable_Hausdorff :
  forall X, metrizable X -> Hausdorff X.
Proof.
  intros. red; intros.
  destruct H.
  exists (open_ball d x ((d x y)/2)).
  exists (open_ball d y ((d x y)/2)).
  assert (0 < d x y).
  { apply NNPP. intro.
    contradict H0.
    apply not_Rlt in H2.
    apply metric_strict with (d := d).
    { assumption. }
    apply Rle_antisym.
    + apply Rge_le. assumption.
    + apply Rge_le. apply metric_nonneg. assumption.
  }
  assert (d x y / 2 > 0). {
    apply Rdiv_lt_0_compat; try assumption.
    apply Rlt_0_2.
  }
  repeat split.
  - apply metric_space_open_ball_open; assumption.
  - apply metric_space_open_ball_open; assumption.
  - rewrite metric_zero; assumption.
  - rewrite metric_zero; assumption.
  - apply Extensionality_Ensembles; split; red; intros.
    2: { contradiction. }
    destruct H4. destruct H4, H5.
    assert (d x x0 + d x0 y < d x y).
    { rewrite double_var.
      apply Rplus_lt_compat; try assumption.
      rewrite metric_sym; assumption.
    }
    pose proof (triangle_inequality _ _ H x x0 y).
    pose proof (Rle_lt_trans _ _ _ H7 H6).
    apply Rlt_irrefl in H8.
    contradiction.
Qed.

Section dist_to_set.

Variable X:Type.
Variable d:X->X->R.
Hypothesis d_is_metric: metric d.
Variable S:Ensemble X.
Hypothesis S_nonempty: Inhabited S.

Definition dist_to_set (x:X) : R.
refine (proj1_sig (inf (Im S (d x)) _ _)).
- exists 0.
  red. intros.
  destruct H.
  rewrite H0.
  now apply metric_nonneg.
- destruct S_nonempty.
  now exists (d x x0), x0.
Defined.

Lemma dist_to_set_triangle_inequality: forall (x y:X),
  dist_to_set y <= dist_to_set x + d x y.
Proof.
intros.
unfold dist_to_set at 1. destruct inf as [dSy [? ?]].
simpl.
unfold dist_to_set at 1. destruct inf as [dSx].
simpl.
clear r.
apply lt_plus_epsilon_le.
intros.
destruct (glb_approx _ _ _ i0 H) as [dxz [[z]]].
rewrite H1 in H2. clear y0 H1.
destruct H2.
apply Rle_lt_trans with (d y z).
- assert (d y z >= dSy);
    auto with real.
  apply i.
  now exists z.
- eapply Rle_lt_trans.
  + now apply triangle_inequality.
  + rewrite (metric_sym _ _ d_is_metric y x).
    lra.
Qed.

End dist_to_set.

Arguments dist_to_set {X}.
Arguments dist_to_set_triangle_inequality {X}.

Section dist_to_set_and_topology.

Import InteriorsClosures.

Variable X:TopologicalSpace.
Variable d:X -> X -> R.
Hypothesis d_is_metric: metric d.
Hypothesis d_metrizes_X: metrizes X d.
Variable S:Ensemble X.
Hypothesis S_nonempty: Inhabited S.

Lemma dist_to_set_zero_impl_closure: forall x:X,
  dist_to_set d d_is_metric S S_nonempty x = 0 -> In (closure S) x.
Proof.
intros.
apply NNPP; intro.
destruct (d_metrizes_X x).
destruct (open_neighborhood_basis_cond (Complement (closure S))) as [V [? ?]].
- split; trivial.
  apply closure_closed.
- destruct H1 as [r].
  unfold dist_to_set in H.
  destruct inf in H.
  simpl in H.
  rewrite H in i; clear x0 H.
  destruct i.
  assert (is_lower_bound (Im S (d x)) r).
  { red. intros y ?.
    destruct H4 as [y].
    rewrite H5. clear y0 H5.
    destruct (total_order_T (d x y) r) as [[?|?]|?]; auto with real rorders.
    assert (In (open_ball d x r) y) by
      now constructor.
    apply H2 in H5.
    contradiction H5.
    now apply closure_inflationary. }
  apply H3 in H4.
  lra.
Qed.

Lemma closure_impl_dist_to_set_zero: forall x:X,
  In (closure S) x -> dist_to_set d d_is_metric S S_nonempty x = 0.
Proof.
intros.
unfold dist_to_set; destruct inf.
destruct i.
simpl.
apply Rle_antisym.
- apply lt_plus_epsilon_le.
  intros.
  ring_simplify.
  assert (exists y:X, In S y /\ d x y < eps).
  { apply NNPP; intro.
    pose proof (not_ex_all_not _ _ H1).
    clear H1.
    simpl in H2.
    assert (In (interior (Complement S)) x).
    { exists (open_ball d x eps).
      - red. split.
        destruct (d_metrizes_X x).
        destruct (open_neighborhood_basis_elements (open_ball d x eps)).
        + constructor. lra.
        + split; trivial.
          red. intros y ?.
          destruct H4.
          red; red; intro.
          contradiction (H2 y).
          now split.
      - constructor.
        now rewrite metric_zero. }
    rewrite interior_complement in H1.
    now contradiction H1. }
  destruct H1 as [y [? ?]].
  assert (d x y >= x0).
  { apply i.
    now exists y. }
  lra.
- apply r.
  red. intros.
  destruct H0.
  rewrite H1.
  now apply metric_nonneg.
Qed.

Variable T:Ensemble X.
Hypothesis T_nonempty: Inhabited T.

Lemma closer_to_S_than_T_open: open
  [x:X | dist_to_set d d_is_metric S S_nonempty x <
           dist_to_set d d_is_metric T T_nonempty x].
Proof.
apply open_char_neighborhood.
intros.
destruct H.
match type of H with ?d1 < ?d2 => pose (eps := d2 - d1) end.
exists (open_ball d x (eps/2)).
split.
{ split.
  - apply metric_space_open_ball_open; assumption.
  - apply metric_open_ball_In; try assumption.
    assert (0 < eps).
    { apply Rgt_minus. auto with real. }
    lra.
}
intros ? ?.
destruct H0.
constructor.
eapply Rle_lt_trans with
  (dist_to_set d d_is_metric S S_nonempty x +
   d x x0).
- apply dist_to_set_triangle_inequality.
- apply Rlt_le_trans with
     (dist_to_set d d_is_metric T T_nonempty x - d x x0).
  * apply Rminus_lt.
    match goal with
      |- ?LHS < 0 =>
      replace LHS with (2 * d x x0 - eps)
    end; [| unfold eps]; lra.
  * assert (dist_to_set d d_is_metric T T_nonempty x <=
            dist_to_set d d_is_metric T T_nonempty x0 + d x x0).
    { rewrite (metric_sym _ d d_is_metric x x0).
      apply dist_to_set_triangle_inequality.
    }
    lra.
Qed.

End dist_to_set_and_topology.

Lemma metrizable_impl_T1_sep: forall X:TopologicalSpace,
  metrizable X -> T1_sep X.
Proof.
intros.
destruct H.
red. intros.
rewrite <- closed_ball_radius_zero with (d := d); try assumption.
apply metric_space_closed_ball_closed; assumption.
Qed.

Lemma metrizable_impl_normal_sep: forall X:TopologicalSpace,
  metrizable X -> normal_sep X.
Proof.
intros.
split.
{ apply metrizable_impl_T1_sep.
  assumption.
}
destruct H.
intros.
case (classic_dec (Inhabited F)); intro.
2: {
  apply Powerset_facts.not_inhabited_empty in n.
  subst.
  exists Empty_set, Full_set.
  repeat split; auto with sets topology.
}
case (classic_dec (Inhabited G)); intro.
2: {
  apply Powerset_facts.not_inhabited_empty in n.
  subst.
  exists Full_set, Empty_set.
  repeat split; auto with sets topology.
}
pose (U := [ x:X | dist_to_set d H F i x < dist_to_set d H G i0 x ]).
pose (V := [ x:X | dist_to_set d H G i0 x < dist_to_set d H F i x ]).
exists U, V; repeat split.
- now apply closer_to_S_than_T_open.
- now apply closer_to_S_than_T_open.
- replace (dist_to_set d H F i x) with 0.
  + destruct (total_order_T 0 (dist_to_set d H G i0 x)) as [[?|?]|?]; trivial.
    * symmetry in e.
      apply dist_to_set_zero_impl_closure in e; trivial.
      rewrite closure_fixes_closed in e; trivial.
      assert (In Empty_set x).
      { rewrite <- H3. now constructor. }
      destruct H5.
    * destruct (Rlt_irrefl 0).
      apply Rle_lt_trans with (dist_to_set d H G i0 x); auto with sets.
      unfold dist_to_set. destruct inf.
      simpl.
      apply i1.
      red. intros.
      destruct H5.
      rewrite H6.
      now apply metric_nonneg.
  + unfold dist_to_set. destruct inf.
    simpl.
    apply Rle_antisym.
    * apply i1.
      red. intros.
      destruct H5.
      rewrite H6.
      now apply metric_nonneg.
    * destruct i1.
      assert (0 >= x0); auto with real.
      apply H5.
      exists x; trivial.
      rewrite metric_zero; auto with real.
- replace (dist_to_set d H G i0 x) with 0.
  + destruct (total_order_T 0 (dist_to_set d H F i x)) as [[?|?]|?]; trivial.
    * symmetry in e.
      apply dist_to_set_zero_impl_closure in e; trivial.
      rewrite closure_fixes_closed in e; trivial.
      now assert (In Empty_set x) by
        now rewrite <- H3.
    * destruct (Rlt_irrefl 0).
      apply Rle_lt_trans with (dist_to_set d H F i x);
        auto with real.
      unfold dist_to_set. destruct inf.
      simpl.
      apply i1.
      red. intros.
      destruct H5.
      rewrite H6.
      now apply metric_nonneg.
  + symmetry.
    apply closure_impl_dist_to_set_zero; trivial.
    now apply closure_inflationary.
- extensionality_ensembles;
    lra.
Qed.

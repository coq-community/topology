Require Export Reals TopologicalSpaces NeighborhoodBases Continuity CountabilityAxioms SupInf SeparatednessAxioms.
Require Import RationalsInReals.
From ZornsLemma Require Export EnsemblesSpec.
From ZornsLemma Require Import EnsemblesTactics DecidableDec.
From Coq Require ProofIrrelevance ClassicalChoice.
From Coq Require Import Lra.

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

Variable X:Type.
Variable d:X->X->R.
Hypothesis d_is_metric: metric d.

Definition open_ball (x0:X) (r:R) : Ensemble X :=
  [ x:X | d x0 x < r ].

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

Definition metrizes (X:TopologicalSpace)
  (d:point_set X -> point_set X -> R) : Prop :=
  forall x:point_set X, open_neighborhood_basis
             (metric_topology_neighborhood_basis d x) x.

Inductive metrizable (X:TopologicalSpace) : Prop :=
  | intro_metrizable: forall d:point_set X -> point_set X -> R,
    metric d -> metrizes X d ->
    metrizable X.

Lemma MetricTopology_metrizable: forall (X:Type) (d:X->X->R)
  (d_metric: metric d),
  metrizes (MetricTopology d d_metric) d.
Proof.
intros.
red.
intros.
apply Build_TopologicalSpace_from_open_neighborhood_bases_basis.
Qed.

Lemma metric_space_open_ball_open :
  forall (X:TopologicalSpace) (d:point_set X -> point_set X -> R),
    metrizes X d -> metric d ->
    forall x r, r > 0 -> open (open_ball _ d x r).
Proof.
  intros.
  specialize (H x).
  assert (In (metric_topology_neighborhood_basis d x) (open_ball _ d x r)).
  { constructor. assumption. }
  apply H in H2.
  destruct H2.
  assumption.
Qed.

Require Export Nets.

Lemma metric_space_net_limit: forall (X:TopologicalSpace)
  (d:point_set X -> point_set X -> R), metrizes X d ->
  forall (I:DirectedSet) (x:Net I X) (x0:point_set X),
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
  (d:point_set X -> point_set X -> R), metrizes X d ->
  forall (I:DirectedSet) (x:Net I X) (x0:point_set X),
    net_limit x x0 -> forall eps:R, eps > 0 ->
                         for large i:DS_set I, d x0 (x i) < eps.
Proof.
intros.
pose (U:=open_ball _ d x0 eps).
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
  (d:point_set X -> point_set X -> R), metrizes X d ->
  forall (I:DirectedSet) (x:Net I X) (x0:point_set X),
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
  (d:point_set X -> point_set X -> R), metrizes X d ->
  forall (I:DirectedSet) (x:Net I X) (x0:point_set X),
    net_cluster_point x x0 -> forall eps:R, eps > 0 ->
                exists arbitrarily large i:DS_set I, d x0 (x i) < eps.
Proof.
intros.
pose (U:=open_ball _ d x0 eps).
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
  (f:point_set X->point_set Y) (x:point_set X)
  (dX:point_set X -> point_set X -> R)
  (dY:point_set Y -> point_set Y -> R),
  metrizes X dX -> metrizes Y dY ->
  continuous_at f x -> forall eps:R, eps > 0 ->
                         exists delta:R, delta > 0 /\
                         forall x':point_set X, dX x x' < delta ->
                                        dY (f x) (f x') < eps.
Proof.
intros.
destruct (H x).
destruct (H0 (f x)).
assert (neighborhood (open_ball _ dY (f x) eps) (f x)).
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
assert (In (inverse_image f (open_ball _ dY (f x) eps)) x').
{ apply H4, H6.
  now constructor. }
destruct H8.
now destruct H8.
Qed.

Lemma metric_space_fun_continuity: forall (X Y:TopologicalSpace)
  (f:point_set X->point_set Y) (x:point_set X)
  (dX:point_set X -> point_set X -> R)
  (dY:point_set Y -> point_set Y -> R),
  metrizes X dX -> metrizes Y dY ->
  (forall eps:R, eps > 0 -> exists delta:R, delta > 0 /\
                         forall x':point_set X, dX x x' < delta ->
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
exists (open_ball _ dX x delta).
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
           (fun n:nat => open_ball _ d x (/ (INR n)))).
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
    exists (open_ball _ d x (/ (INR n))).
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
destruct H, H0.
exists (Im [p:(Q*X)%type |
            let (r,x):=p in (r>0)%Q /\ In S x]
  (fun p:(Q*X)%type =>
      let (r,x):=p in open_ball _ d x (Q2R r))).
- constructor.
  + intros.
    destruct H3.
    destruct H3.
    destruct x as [r x].
    destruct H3.
    destruct (H1 x).
    destruct (open_neighborhood_basis_elements y); trivial.
    rewrite H4.
    constructor; trivial.
    rewrite <- RMicromega.Q2R_0.
    now apply Qlt_Rlt.
  + intros.
    destruct (H1 x).
    destruct (open_neighborhood_basis_cond U) as [V [[r]]].
    * now split.
    * destruct (dense_meets_every_nonempty_open _ _ H2
        (open_ball _ d x (r/2))).
      ** destruct (open_neighborhood_basis_elements
           (open_ball _ d x (r/2))).
         *** constructor.
             lra.
         *** destruct (open_neighborhood_basis_elements
               (open_ball X d x (r/2))); trivial.
             constructor.
             lra.
      ** exists x.
         constructor.
         rewrite metric_zero; trivial.
         lra.
      ** destruct H7, H8.
         destruct (rationals_dense_in_reals (d x x0) (r - d x x0)) as [r'].
         *** lra.
         *** exists (open_ball _ d x0 (Q2R r')).
             repeat split.
             **** exists ( (r', x0) ); trivial.
                  constructor.
                  split; trivial.
                  assert (Q2R r' > 0).
                  { apply Rgt_ge_trans with (d x x0).
                    - apply H9.
                    - now apply metric_nonneg. }
                  apply Rlt_Qlt.
                  unfold Q2R at 1.
                  simpl.
                  now ring_simplify.
             **** red. intros y ?.
                  destruct H10.
                  apply H6.
                  constructor.
                  eapply Rle_lt_trans.
                  ***** now apply triangle_inequality.
                  ***** apply Rlt_trans with (d x x0 + Q2R r');
                          auto with real.
                        lra.
             **** destruct H9.
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
  apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
  apply H4 in H5.
  f_equal;
    injection H5;
    intros.
  + now apply H3.
  + apply H0 in H7.
    now injection H7.
Qed.

Lemma metrizable_Lindelof_impl_second_countable:
  forall X:TopologicalSpace, metrizable X -> Lindelof X ->
    second_countable X.
Proof.
intros.
destruct H.
destruct (ClassicalChoice.choice (fun (n:{n:nat | (n > 0)%nat}) (S:Family X) =>
  Included S (Im Full_set (fun x:point_set X =>
                            open_ball _ d x (/ (INR (proj1_sig n)))))
  /\ Countable S /\ FamilyUnion S = Full_set))
as [choice_fun].
- destruct x as [n].
  apply H0.
  + intros.
    destruct H2 as [x ? U].
    destruct (H1 x).
    Opaque In. apply open_neighborhood_basis_elements. Transparent In.
    rewrite H3.
    constructor.
    simpl.
    auto with real rorders.
  + extensionality_ensembles.
    * constructor.
    * simpl.
      exists (open_ball _ d x (/ INR n)).
      ** now exists x.
      ** constructor.
         rewrite metric_zero; auto with real.
- exists (IndexedUnion choice_fun).
  + constructor.
    * intros.
      destruct H3 as [n V].
      destruct (H2 n) as [? [? ?]].
      apply H4 in H3.
      destruct H3 as [x ? V].
      destruct (H1 x).
      Opaque In. apply open_neighborhood_basis_elements. Transparent In.
      rewrite H7.
      constructor.
      destruct n as [n g].
      simpl.
      auto with real rorders.
    * intros.
      destruct (H1 x).
      destruct (open_neighborhood_basis_cond U) as [V [? ?]].
      { now split. }
      inversion H5.
      destruct (inverses_of_nats_approach_0 (r/2)) as [n [? ?]].
      { lra. }
      pose (nsig := exist _ n H9).
      destruct (H2 nsig) as [? [? ?]].
      assert (In (FamilyUnion (choice_fun nsig)) x) by
        now rewrite H13.
      destruct H14 as [W].
      destruct (H11 _ H14) as [y ? W].
      rewrite H17 in H15. destruct H15.
      exists W.
      repeat split.
      ** now exists nsig.
      ** assert (Included W V); auto with sets.
         rewrite H17, <- H8.
         red. intros z ?.
         destruct H18.
         constructor.
         eapply Rle_lt_trans.
         { now apply triangle_inequality. }
         rewrite (metric_sym _ d H x y).
         apply Rlt_trans with (/ INR (proj1_sig nsig) + / INR (proj1_sig nsig));
           auto with real.
         simpl.
         lra.
      ** rewrite H17.
         now constructor.
  + apply countable_indexed_union.
    * apply countable_type_ensemble.
      exists (fun n:nat => n).
      now red.
    * intro.
      now destruct (H2 a) as [? [? ?]].
Qed.

Lemma metrizable_Hausdorff :
  forall X, metrizable X -> Hausdorff X.
Proof.
  intros. red; intros.
  destruct H.
  exists (open_ball _ d x ((d x y)/2)).
  exists (open_ball _ d y ((d x y)/2)).
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
    2: { destruct H4. }
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
Variable d:point_set X -> point_set X -> R.
Hypothesis d_is_metric: metric d.
Hypothesis d_metrizes_X: metrizes X d.
Variable S:Ensemble X.
Hypothesis S_nonempty: Inhabited S.

Lemma dist_to_set_zero_impl_closure: forall x:point_set X,
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
    assert (In (open_ball _ d x r) y) by
      now constructor.
    apply H2 in H5.
    contradiction H5.
    now apply closure_inflationary. }
  apply H3 in H4.
  lra.
Qed.

Lemma closure_impl_dist_to_set_zero: forall x:point_set X,
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
  assert (exists y:point_set X, In S y /\ d x y < eps).
  { apply NNPP; intro.
    pose proof (not_ex_all_not _ _ H1).
    clear H1.
    simpl in H2.
    assert (In (interior (Complement S)) x).
    { exists (open_ball _ d x eps).
      - red. split.
        destruct (d_metrizes_X x).
        destruct (open_neighborhood_basis_elements (open_ball _ d x eps)).
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
  [x:point_set X | dist_to_set d d_is_metric S S_nonempty x <
                   dist_to_set d d_is_metric T T_nonempty x].
Proof.
match goal with |- open ?U => replace U with (interior U) end.
{ apply interior_open. }
apply Extensionality_Ensembles; split.
{ apply interior_deflationary. }
red. intros.
destruct H.
match type of H with ?d1 < ?d2 => pose (eps := d2 - d1) end.
match goal with |- In (interior ?U) x =>
  assert (Included (open_ball _ d x (eps/2)) (interior U)) end.
{ apply interior_maximal.
  * destruct (d_metrizes_X x).
    destruct (open_neighborhood_basis_elements
      (open_ball _ d x (eps/2))); trivial.
    constructor.
    assert (eps > 0).
    { apply Rgt_minus. auto with real. }
    lra.
  * red. intros.
    destruct H0.
    constructor.
    eapply Rle_lt_trans with
      (dist_to_set d d_is_metric S S_nonempty x +
       d x x0).
    ** apply dist_to_set_triangle_inequality.
    ** apply Rlt_le_trans with
         (dist_to_set d d_is_metric T T_nonempty x - d x x0).
       *** apply Rminus_lt.
           match goal with |- ?LHS < 0 => replace LHS with (2 * d x x0 - eps) end;
             [| unfold eps]; lra.
       *** assert (dist_to_set d d_is_metric T T_nonempty x <=
             dist_to_set d d_is_metric T T_nonempty x0 + d x x0).
           { rewrite (metric_sym _ d d_is_metric x x0).
             apply dist_to_set_triangle_inequality. }
           lra. }
apply H0.
constructor.
rewrite metric_zero; trivial.
apply Rmult_gt_0_compat; auto with real rorders.
now apply Rgt_minus.
Qed.

End dist_to_set_and_topology.

Lemma metrizable_impl_normal_sep: forall X:TopologicalSpace,
  metrizable X -> normal_sep X.
Proof.
intros.
destruct H.
split.
- red. intros.
  replace (Singleton x) with (closure (Singleton x)).
  { apply closure_closed. }
  apply Extensionality_Ensembles. split.
  + red. intros.
    replace x0 with x.
    { constructor. }
    apply metric_strict with d; trivial.
    apply NNPP; intro.
    assert (d x0 x > 0).
    { destruct (total_order_T (d x0 x) 0) as [[?|?]|?]; trivial.
      - assert (0 < 0).
        { apply Rle_lt_trans with (d x0 x); trivial.
          assert (d x0 x >= 0); auto with *.
          now apply metric_nonneg. }
        contradict H3; apply Rlt_irrefl.
      - destruct H. now rewrite metric_sym0 in e. }
    assert (In (interior (Complement (Singleton x))) x0).
    { exists (open_ball _ d x0 (d x0 x));
        constructor.
      - destruct (H0 x0).
        destruct (open_neighborhood_basis_elements
          (open_ball X d x0 (d x0 x))).
        + now constructor.
        + split; trivial.
          red. intros.
          intro.
          destruct H7, H6.
          lra.
      - now rewrite metric_zero. }
    rewrite interior_complement in H4.
    contradiction H4.
  + apply closure_inflationary.
- intros.
  case (classic_dec (Inhabited F)); intro.
  + case (classic_dec (Inhabited G)); intro.
    * pose (U := [ x:point_set X | dist_to_set d H F i x <
                                   dist_to_set d H G i0 x ]).
      pose (V := [ x:point_set X | dist_to_set d H G i0 x <
                                   dist_to_set d H F i x ]).
      exists U, V; repeat split.
      ** now apply closer_to_S_than_T_open.
      ** now apply closer_to_S_than_T_open.
      ** replace (dist_to_set d H F i x) with 0.
         *** destruct (total_order_T 0 (dist_to_set d H G i0 x)) as [[?|?]|?]; trivial.
             **** symmetry in e.
                  apply dist_to_set_zero_impl_closure in e; trivial.
                  rewrite closure_fixes_closed in e; trivial.
                  assert (In Empty_set x).
                  { rewrite <- H3. now constructor. }
                  destruct H5.
             **** assert (0 < 0).
                  { apply Rle_lt_trans with (dist_to_set d H G i0 x); auto with sets.
                    unfold dist_to_set. destruct inf.
                    simpl.
                    apply i1.
                    red. intros.
                    destruct H5.
                    rewrite H6.
                    now apply metric_nonneg. }
                  lra.
         *** unfold dist_to_set. destruct inf.
             simpl.
             apply Rle_antisym.
             **** apply i1.
                  red. intros.
                  destruct H5.
                  rewrite H6.
                  now apply metric_nonneg.
             **** destruct i1.
                  assert (0 >= x0); auto with real.
                  apply H5.
                  exists x; trivial.
                  rewrite metric_zero; auto with real.
      ** replace (dist_to_set d H G i0 x) with 0.
         *** destruct (total_order_T 0 (dist_to_set d H F i x)) as [[?|?]|?]; trivial.
             **** symmetry in e.
                  apply dist_to_set_zero_impl_closure in e; trivial.
                  rewrite closure_fixes_closed in e; trivial.
                  now assert (In Empty_set x) by
                    now rewrite <- H3.
             **** assert (0 < 0).
                  { apply Rle_lt_trans with (dist_to_set d H F i x);
                      auto with real.
                    unfold dist_to_set. destruct inf.
                    simpl.
                    apply i1.
                    red. intros.
                    destruct H5.
                    rewrite H6.
                    now apply metric_nonneg. }
                  lra.
         *** symmetry.
             apply closure_impl_dist_to_set_zero; trivial.
             now apply closure_inflationary.
      ** extensionality_ensembles;
           lra.
    * exists Full_set, Empty_set.
      repeat split; auto with sets topology.
      red. intros.
      contradiction n.
      now exists x.
  + exists Empty_set, Full_set.
    repeat split; auto with sets topology.
    red. intros.
    contradiction n.
    now exists x.
Qed.

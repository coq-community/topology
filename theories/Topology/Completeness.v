From Topology Require Export MetricSpaces.
From Topology Require Import SubspaceTopology.
Require Import Psatz.
From Coq Require Import ProofIrrelevance.

Section Completeness.
Context {X : Type}.
Variable (d : X -> X -> R) (d_metric : metric d).

Definition cauchy (x:nat->X) : Prop :=
  forall eps:R, eps > 0 -> exists N:nat, forall m n:nat,
    (m >= N)%nat -> (n >= N)%nat -> d (x m) (x n) < eps.

Definition complete : Prop :=
  forall x:nat -> X, cauchy x ->
    exists x0 : X, forall eps:R,
      eps > 0 -> for large i:nat_DS,
      d x0 (x i) < eps.

Lemma cauchy_impl_bounded (x : nat -> X) :
  cauchy x -> bounded d (Im Full_set x).
Proof.
intros Hx.
destruct (Hx 1) as [N HN].
{ lra. }
assert (exists r : R,
         0 < r /\ forall n : nat, (n < N)%nat -> d (x N) (x n) <= r)
         as [r [Hr0 Hr1]].
{ (* this holds in all lattices, because only finitely
     many points [x n] have to be considered. *)
  clear HN Hx.
  induction N.
  { exists 1. split; intros.
    - lra.
    - lia.
  }
  destruct IHN as [r0 [Hr0 Hr1]].
  exists (r0 + (d (x (S N)) (x N))).
  split.
  { pose proof (metric_nonneg d_metric (x (S N)) (x N)).
    lra.
  }
  intros n Hn.
  inversion Hn; subst; clear Hn.
  - lra.
  - unshelve epose proof (Hr1 n _) as Hr1.
    { lia. }
    pose proof (triangle_inequality
                  d_metric (x (S N)) (x N) (x n)).
    lra.
}
exists (x N), ((Rmax r 0) + 1).
intros y Hy.
inversion Hy; subst; clear Hy.
rename x0 into n. clear Hx d_metric.
constructor.
destruct (Nat.le_gt_cases N n).
- apply Rlt_le_trans with 1; auto.
  unfold Rmax.
  destruct (Rle_dec _ _); lra.
- specialize (Hr1 n H0).
  unfold Rmax.
  destruct (Rle_dec _ _); lra.
Qed.
End Completeness.

Section Completeness.
Context (X:TopologicalSpace)
  (d:X->X->R) (d_metric: metric d) (d_metrizes: metrizes X d).

Lemma complete_net_limit_char :
  complete d <->
  forall x:nat -> X, cauchy d x ->
    exists x0:X, net_limit x x0 (I:=nat_DS).
Proof.
  split; intros Hcomp;
    intros x Hx; specialize (Hcomp x Hx) as [x0 Hx0];
    exists x0.
  - eapply metric_space_net_limit; eauto.
  - intros eps Heps.
    eapply metric_space_net_limit_converse in Hx0;
      eauto.
Qed.

Lemma complete_net_limit_ex_unique :
  complete d ->
  forall x:nat -> X, cauchy d x ->
    exists! x0:X, net_limit x x0 (I:=nat_DS).
Proof.
  intros Hd x Hx.
  rewrite complete_net_limit_char in Hd.
  specialize (Hd x Hx) as [x0 Hx0].
  exists x0. split; auto.
  intros x1 Hx1.
  unshelve eapply (Hausdorff_impl_net_limit_unique _ _ x0 x1 Hx0 Hx1).
  apply metrizable_Hausdorff. exists d; auto.
Qed.

Lemma convergent_sequence_is_cauchy:
  forall (x:Net nat_DS X)
    (x0:point_set X),
  net_limit x x0 -> cauchy d x.
Proof.
intros.
destruct (d_metrizes x0).
red; intros.
destruct (H (open_ball d x0 (eps/2))) as [N].
- Opaque In. apply open_neighborhood_basis_elements. Transparent In.
  constructor.
  lra.
- constructor.
  rewrite metric_zero; trivial.
  lra.
- simpl in N.
  exists N.
  intros.
  destruct (H1 m H2).
  destruct (H1 n H3).
  apply Rle_lt_trans with (d x0 (x m) + d x0 (x n)).
  + rewrite (metric_sym d_metric x0 (x m)); trivial.
    now apply triangle_inequality.
  + lra.
Qed.

Lemma cauchy_sequence_with_cluster_point_converges:
  forall (x:Net nat_DS X) (x0:point_set X),
  cauchy d x -> net_cluster_point x x0 -> net_limit x x0.
Proof.
intros x x0 Hx Hx0.
apply metric_space_net_limit with d; auto.
intros.
red; intros.
destruct (Hx (eps/2)) as [N HN].
{ lra. }
pose (U := open_ball d x0 (eps/2)).
assert (open_neighborhood U x0) as [HU0 HU1].
{ unfold U.
  split; auto.
  - apply metric_space_open_ball_open; auto.
  - apply metric_open_ball_In; auto; lra.
}
destruct (Hx0 U HU0 HU1 N) as [m [Hm [Hxm]]].
simpl in m, Hm.
exists N; intros n Hn.
simpl in n, Hn.
apply Rle_lt_trans with (d x0 (x m) + d (x m) (x n)).
- now apply triangle_inequality.
- cut (d (x m) (x n) < eps/2).
  + lra.
  + now apply HN.
Qed.

Corollary complete_cauchy_cluster_points :
  (forall x:nat -> X, cauchy d x ->
      exists x0:X, net_cluster_point x x0 (I:=nat_DS)) ->
  complete d.
Proof.
  intros H.
  apply complete_net_limit_char.
  intros x Hx.
  specialize (H x Hx) as [x0 Hx0].
  exists x0.
  apply cauchy_sequence_with_cluster_point_converges;
    auto.
Qed.

End Completeness.

Section closed_subset_of_complete.
Context {X : TopologicalSpace}
  (d : X -> X -> R) (d_metric : metric d)
  (d_metrizes : metrizes X d)
  (F : Ensemble X).

Let FT := { x:X | In F x }.
Let d_restriction := fun x y:FT => d (proj1_sig x) (proj1_sig y).
Let d_restriction_metric :=
      MetricSpaces.d_restriction_metric d d_metric F.

Lemma cauchy_restriction (x : nat -> X)
  (HUx : forall n , In F (x n)) (Hx : cauchy d x) :
  cauchy d_restriction (fun n => exist F (x n) (HUx n)).
Proof.
  intros eps Heps.
  destruct (Hx eps Heps) as [N HN].
  exists N; intros.
  unfold d_restriction.
  simpl. auto.
Qed.

Lemma closed_subset_of_complete_is_complete:
  complete d ->
  closed F ->
  complete d_restriction.
Proof.
intros Hcomp HF.
apply (complete_net_limit_char
         (SubspaceTopology F) d_restriction).
{ apply metric_space_subspace_topology_metrizes;
    auto.
}
rewrite complete_net_limit_char in Hcomp;
  auto.
intros x Hx.
pose (y := fun n:nat => proj1_sig (x n)).
destruct (Hcomp y) as [y0 Hy0].
{ red; intros eps Heps.
  destruct (Hx eps Heps) as [N].
  now exists N.
}
- assert (In F y0) as HFy0.
  { rewrite <- (closure_fixes_closed _ HF); trivial.
    apply @net_limit_in_closure with (I:=nat_DS) (x:=y); trivial.
    apply exists_arbitrarily_large_all.
    intros ?.
    apply proj2_sig.
  }
  exists (exist _ y0 HFy0).
  apply metric_space_net_limit with d_restriction.
  + apply metric_space_subspace_topology_metrizes; auto.
  + intros.
    unfold d_restriction; simpl.
    apply metric_space_net_limit_converse; auto.
Qed.

Lemma complete_subset_is_closed:
  complete d_restriction ->
  closed F.
Proof.
intros.
cut (Included (closure F) F).
{ intros.
  assert (closure F = F) as H1.
  { apply Extensionality_Ensembles.
    split; trivial; apply closure_inflationary.
  }
  rewrite <- H1; apply closure_closed.
}
red; intros.
(* consider a sequence [y] in [X] which converges to [x] and lies
   completely in [F] *)
assert (exists y:Net nat_DS X,
  (forall n:nat, In F (y n)) /\ net_limit y x) as [y [HyF Hyx]].
{ apply first_countable_sequence_closure; trivial.
  apply metrizable_impl_first_countable.
  exists d; trivial.
}
(* consider [y] as sequence [y'] in the subspace of [F] *)
pose (y' := ((fun n:nat => exist _ (y n) (HyF n)) :
              Net nat_DS (SubspaceTopology F))).
(* since [y] converges, it is cauchy. Hence [y'] is cauchy as well. *)
assert (cauchy d_restriction y') as Hy'.
{ apply cauchy_restriction; auto.
  apply convergent_sequence_is_cauchy with x;
    trivial.
}
(* since [F] is complete, the sequence [y'] has a limit [x0]. *)
destruct (H y' Hy') as [[x0 Hx0] Hy'x0].
(* we claim that [y] also converges to [x0] *)
cut (net_limit y x0).
- intros Hyx0.
  assert (x = x0).
  { eapply Hausdorff_impl_net_limit_unique;
      eauto.
    apply metrizable_Hausdorff.
    exists d; auto.
  }
  congruence.
- apply metric_space_net_limit with d;
    auto.
Qed.

End closed_subset_of_complete.

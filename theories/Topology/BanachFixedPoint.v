(* Prove the Banach fixed-point theorem. *)

From Coq Require Import
  Lia
  List
  Lra.
From Topology Require Import
  Completeness
  LipschitzMaps
  MetricSpaces.

(** ** Fact about Nat.iter to stdlib? *)
Lemma Nat_iter_fix {A : Type} (f : A -> A) (a : A) :
  f a = a -> forall n : nat, Nat.iter n f a = a.
Proof.
  intros Ha n. induction n.
  { reflexivity. }
  simpl. congruence.
Qed.

(** ** Facts about [R] *)
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

Lemma Rsum_seq_S (f : nat -> R) (n k : nat) :
  fold_right Rplus 0 (map f (seq n (S k))) =
    fold_right Rplus 0 (map f (seq n k)) + (f (k + n)%nat).
Proof.
  revert n.
  induction k; intros n.
  { cbn. lra. }
  cbn.
  rewrite !Rplus_assoc.
  apply Rplus_eq_compat_l.
  specialize (IHk (S n)).
  rewrite plus_n_Sm.
  rewrite <- IHk.
  clear IHk.
  reflexivity.
Qed.

Lemma Rle_pow_pos_lt_1 (x : R) (m n : nat) :
  0 <= x < 1 -> (m <= n)%nat ->
  x ^ n <= x ^ m.
Proof.
  intros Hx Hmn.
  induction Hmn.
  { lra. }
  cbn.
  rewrite <- (Rmult_1_l (x ^ m)).
  apply Rmult_le_compat; auto; try lra.
  apply pow_le. lra.
Qed.

Lemma Rle_pow_abs_lt_1 (x : R) (m n : nat) :
  Rabs x < 1 -> (m <= n)%nat ->
  Rabs (x ^ n) <= Rabs (x ^ m).
Proof.
  intros Hx Hmn.
  rewrite <- !RPow_abs.
  apply Rle_pow_pos_lt_1; auto.
  split; auto. apply Rabs_pos.
Qed.

Lemma Rsum_le_compat (f g : nat -> R) (n k : nat) :
  (forall i : nat, (n <= i < n + k)%nat ->
            0 <= f i <= g i) ->
  fold_right Rplus 0 (map f (seq n k)) <=
    fold_right Rplus 0 (map g (seq n k)).
Proof.
  revert n; induction k.
  { intros ? _. cbn. lra. }
  intros n Hfg.
  cbn.
  apply Rplus_le_compat.
  { apply Hfg. lia. }
  apply IHk.
  intros i Hi. apply Hfg.
  lia.
Qed.

Lemma Rsum_mult_distr_r (f : nat -> R) (n k : nat) (r : R) :
  fold_right Rplus 0 (map (fun i => f i * r) (seq n k)) =
    (fold_right Rplus 0 (map f (seq n k))) * r.
Proof.
  revert n; induction k; intros n.
  { cbn. lra. }
  cbn. specialize (IHk (S n)). lra.
Qed.

Lemma Rsum_pow_dist_l (n k : nat) (r : R) :
  fold_right Rplus 0 (map (pow r) (seq n k)) =
    r ^ n * fold_right Rplus 0 (map (pow r) (seq 0 k)).
Proof.
  revert n; induction k; intros n.
  { cbn. lra. }
  cbn. rewrite Rmult_plus_distr_l.
  rewrite Rmult_1_r. f_equal.
  rewrite (IHk 1%nat), (IHk (S n)).
  rewrite <- Rmult_assoc. f_equal.
  rewrite <- pow_add. f_equal.
  lia.
Qed.

Lemma Rsum_diff_telescope1 (f : nat -> R) (n k : nat) :
  fold_right Rplus 0 (map f (seq n k))%nat -
    fold_right Rplus 0 (map f (seq (S n) k))%nat =
    f n - f (k + n)%nat.
Proof.
  revert n; induction k; intros n.
  { cbn. lra. }
  cbn.
  specialize (IHk (S n)).
  rewrite Nat.add_succ_r in IHk.
  lra.
Qed.

(* is helpful, because the stdlib of coq v8.16 is missing useful facts. *)
Lemma Rdiv_mult_cancel_r (a b : R) :
  b <> 0 ->
  a / b * b = a.
Proof.
  intros Hb. field. assumption.
Qed.

Lemma Rsum_geometric_eval (m : nat) (q : R) :
  q <> 1 ->
  fold_right Rplus 0 (map (pow q) (seq 0 m)) =
    (q ^ m - 1) / (q - 1).
Proof.
  intros Hq.
  apply Rmult_eq_reg_r with (r := q - 1).
  2: lra.
  rewrite Rdiv_mult_cancel_r; [|lra].
  rewrite Rmult_minus_distr_l.
  rewrite Rmult_1_r.
  rewrite (Rmult_comm _ q).
  rewrite <- (pow_1 q) at 1.
  rewrite <- Rsum_pow_dist_l.
  rewrite <- (Ropp_involutive (_ - _)).
  rewrite Ropp_minus_distr.
  rewrite Rsum_diff_telescope1.
  rewrite Nat.add_0_r.
  lra.
Qed.

Lemma Rsum_geometric_upper_bound (m : nat) (q : R) :
  0 <= q < 1 ->
  fold_right Rplus 0 (map (fun i : nat => q ^ i) (seq 0 m)) <= / (1 - q).
Proof.
  intros Hq.
  rewrite Rsum_geometric_eval.
  2: lra.
  apply Rmult_le_reg_r with (r := 1 - q).
  1: lra.
  rewrite Rinv_l.
  2: lra.
  rewrite <- (Ropp_minus_distr q 1).
  rewrite <- Ropp_mult_distr_r.
  rewrite Rdiv_mult_cancel_r; [|lra].
  rewrite Ropp_minus_distr.
  cut (0 <= q ^ m); [intros; lra|].
  destruct m.
  { cbn. lra. }
  rewrite <- pow_i with (i := S m).
  2: lia.
  apply pow_incr.
  lra.
Qed.

Local Lemma Rmult_eq_same_cases (a b : R) :
  a = b * a ->
  a = 0 \/ b = 1.
Proof.
  intros Hab.
  destruct (Req_dec a 0) as [Ha|Ha].
  { auto. }
  rewrite <- (Rmult_1_l a) in Hab at 1.
  apply Rmult_eq_reg_r in Hab; auto.
Qed.

(* used in [BanachFixedPoint_unique] *)
Local Lemma Rle0_char' (x q : R) :
  0 <= q < 1 ->
  x <= q * x <-> x <= 0.
Proof.
  intros Hq.
  split.
  - (* -> *)
    intros Hxq.
    destruct (Rle_or_lt x 0); auto.
    destruct Hq as [Hq0 Hq1].
    pose proof (Rmult_le_compat x x q 1 ltac:(lra) Hq0 ltac:(lra) ltac:(lra)) as H2.
    rewrite Rmult_1_r in H2.
    pose proof (Rle_antisym x (q * x) Hxq ltac:(lra)) as H0.
    apply Rmult_eq_same_cases in H0 as [|].
    + (* impossible by [0 < x] *) lra.
    + (* impossible by [1 = q < 1] *) subst. lra.
  - (* <- *)
    intros Hx.
    remember (- x) as x0.
    rewrite <- (Ropp_involutive x).
    rewrite <- (Ropp_involutive x) in Hx.
    rewrite <- Heqx0.
    rewrite <- Heqx0 in Hx.
    clear x Heqx0.
    assert (0 <= x0) as Hx0 by lra.
    clear Hx.
    rewrite <- Ropp_mult_distr_r.
    apply Ropp_le_contravar.
    rewrite <- (Rmult_1_l x0) at 2.
    apply Rmult_le_compat; lra.
Qed.

(* given a sequence of points [f : nat -> X], the distance between [f n]
  and [f (m + n)] can be bounded by the sum of the distances from
  [f i] to [f (S i)], for appropriate [i]. *)
Lemma triangle_inequality_seq {X : Type} (d : X -> X -> R) (d_metric : metric d)
  (f : nat -> X) (n m : nat) :
  d (f n) (f (m + n)%nat) <=
    fold_right
      Rplus 0
      (map (fun i => d (f i) (f (S i))) (seq n m)).
Proof.
  induction m.
  { simpl fold_right.
    rewrite Nat.add_0_l.
    rewrite metric_zero; auto.
    lra.
  }
  rewrite Rsum_seq_S.
  eapply Rle_trans.
  { apply triangle_inequality
      with (y := f (m + n)%nat);
      auto.
  }
  apply Rplus_le_compat; auto.
  cbn. lra.
Qed.

Lemma Subnet_nat_iter_S {X : Type} (f : X -> X) (x0 : X) :
  @Subnet
    nat_DS _ (fun i : nat => Nat.iter i f x0)
    nat_DS (fun i : nat => (Nat.iter (S i) f x0)).
Proof.
  exists S. split; [|split].
  - cbn. lia.
  - cbn. intros i. cbn.
    exists (S i). split; try lia.
    exists i; reflexivity.
  - intros j. reflexivity.
Qed.

(** ** Banach Fixed Point Theorem
  Proof taken from https://en.wikipedia.org/wiki/Banach_fixed-point_theorem
 *)
Section BanachFixedPoint.
  Context
    {X : TopologicalSpace}
      (d : X -> X -> R)
      (d_metric : metric d)
      (d_metrizes : metrizes X d)
      (Hd_comp : complete d)
      (T : X -> X)
      {q : R}
      (Hq : 0 <= q < 1)
      (HT : Lipschitz d d T q).

  Lemma BanachFixedPoint_unique (x1 x2 : X) :
    T x1 = x1 -> T x2 = x2 -> x1 = x2.
  Proof.
    intros Hx1 Hx2.
    apply (metric_strict d_metric).
    specialize (HT x1 x2).
    rewrite Hx1, Hx2 in HT. clear Hx1 Hx2 T.
    pose proof (metric_nonneg d_metric x1 x2) as Hnneg.
    (* reduce the problem to algebra in [R]. [D := d x1 x2] *)
    remember (d x1 x2) as D. clear HeqD x1 x2 X d d_metric d_metrizes Hd_comp.
    apply Rle_antisym; try lra.
    apply Rle0_char' in HT; auto.
  Qed.

  Local Definition BanachFixedPoint_seq
    (x : X) (n : nat) : X :=
    Nat.iter n T x.

  Local Lemma BanachFixedPoint_seq_dist_succ (x : X)
    (n : nat) :
    d (BanachFixedPoint_seq x n)
      (BanachFixedPoint_seq x (S n)) <=
      q^n * d x (T x).
  Proof.
    induction n.
    { simpl. lra. }
    simpl.
    eapply Rle_trans.
    { apply HT. }
    rewrite Rmult_assoc.
    apply Rmult_le_compat_l; auto.
    lra.
  Qed.

  (* repeatedly apply [BanachFixedPoint_seq_dist_succ] *)
  Local Lemma BanachFixedPoint_seq_dist_add (x : X)
    (n m : nat) :
    d (BanachFixedPoint_seq x n)
      (BanachFixedPoint_seq x (m + n)) <=
      q^n * d (T x) x * (/ (1 - q)).
  Proof.
    apply Rle_trans
      with (r2 :=
              q^n * d (T x) x * (fold_right Rplus 0 (map (fun i => q ^ i) (seq 0 m)))).
    2: {
      apply Rmult_le_compat_l.
      - apply Rmult_le_pos.
        + apply pow_le. apply Hq.
        + apply (metric_nonneg d_metric).
      - apply Rsum_geometric_upper_bound. exact Hq.
    }
    apply Rle_trans
      with (r2 :=
              fold_right Rplus 0
                (map (fun i => d (BanachFixedPoint_seq x i)
                              (BanachFixedPoint_seq x (S i)))
                   (seq n m))).
    { apply triangle_inequality_seq. exact d_metric. }
    apply Rle_trans with
      (r2 := fold_right Rplus 0 (map (fun i : nat => q^i * (d (T x) x)) (seq n m))).
    - apply Rsum_le_compat. intros i Hi.
      split.
      { apply metric_nonneg; auto. }
      rewrite (metric_sym d_metric (T x) x).
      apply BanachFixedPoint_seq_dist_succ.
    - rewrite Rsum_mult_distr_r.
      rewrite !(Rmult_comm _ (d (T x) x)).
      rewrite Rmult_assoc. apply Rmult_le_compat_l.
      { apply metric_nonneg, d_metric. }
      rewrite Rsum_pow_dist_l. apply Rle_refl.
  Qed.

  Local Lemma BanachFixedPoint_seq_cauchy (x : X) :
    cauchy d (BanachFixedPoint_seq x).
  Proof.
    (* do a case distinction, if [T x = x], since we want to
       divide by [d (T x) x] *)
    destruct (Req_dec 0 (d (T x) x)) as [Hx|Hx].
    { (* [T x = x], hence the sequence is constant. *)
      symmetry in Hx; apply metric_strict in Hx; auto.
      intros eps Heps.
      exists 0%nat. intros m n _ _.
      unfold BanachFixedPoint_seq.
      rewrite !Nat_iter_fix; auto.
      rewrite metric_zero; auto.
    }
    intros eps Heps.
    assert
      (exists N : nat,
          q^N < (eps * (1 - q))/(d (T x) x))
      as [N HN].
    { unshelve epose proof
        (pow_lt_1_zero q _ (eps * (1 - q) / d (T x) x) _) as [N HN].
      { rewrite Rabs_right; lra. }
      { apply Rmult_lt_0_compat.
        - apply Rmult_lt_0_compat; lra.
        - apply Rinv_0_lt_compat.
          pose proof (metric_nonneg d_metric (T x) x).
          lra.
      }
      exists N. specialize (HN N ltac:(lia)).
      rewrite Rabs_right in HN; auto.
      apply Rle_ge. apply pow_le. lra.
    }
    exists N.
    (* w.l.o.g. one of [m, n] is bigger than the other … *)
    cut
      (forall m n : nat,
          (n >= N)%nat ->
          d (BanachFixedPoint_seq x n)
            (BanachFixedPoint_seq x (m + n)) < eps).
    { intros H0.
      intros m n Hm Hn.
      destruct (Compare.le_dec m n) as [Hmn|Hnm].
      - destruct (Nat.le_exists_sub
                    m n Hmn) as [k [? _]].
        subst n. apply H0. assumption.
      - destruct (Nat.le_exists_sub
                    n m Hnm) as [k [? _]].
        subst m.
        rewrite metric_sym; try assumption.
        apply H0. assumption.
    }
    intros m n Hn.
    eapply Rle_lt_trans.
    { apply BanachFixedPoint_seq_dist_add. }
    (* some algebra of real numbers … *)

    assert (0 < d (T x) x) as Hx_pos. (* as a helper *)
    { pose proof (metric_nonneg d_metric (T x) x).
      lra.
    }

    (* remove all divisions. first in the goal, then in [HN] *)
    apply Rmult_lt_reg_r with (r := (1 - q)).
    1: lra.
    rewrite !Rmult_assoc.
    rewrite Rinv_l; [|lra]; rewrite Rmult_1_r.

    apply Rmult_lt_compat_l with (r := d (T x) x) in HN; auto.
    rewrite (Rmult_comm (d _ _) (_ / _)) in HN.
    rewrite Rdiv_mult_cancel_r in HN; auto.

    (* make the goal and [HN] match in structure. Note that [n] vs.
      [N] is the only difference. *)
    rewrite (Rmult_comm (q ^ n)).
    (* end proof *)
    apply Rle_lt_trans with (r2 := d (T x) x * q ^ N); auto.
    apply Rmult_le_compat_l; [lra|].
    apply Rle_pow_pos_lt_1; auto.
  Qed.

  Local Lemma BanachFixedPoint_seq_shift (x0 : X) :
    forall i : nat, compose T (BanachFixedPoint_seq x0) i =
      compose (BanachFixedPoint_seq x0) S i.
  Proof.
    intros ?. reflexivity.
  Qed.

  Local Lemma BanachFixedPoint_seq_net_limit_shift
    (x0 x1 x2 : X) :
    @net_limit nat_DS X (BanachFixedPoint_seq x0) x1 ->
    @net_limit nat_DS X (fun i => T (BanachFixedPoint_seq x0 i)) x2 ->
    x1 = x2.
  Proof.
    intros Hx1 Hx2.
    (* one sequence/net is a subsequence/subnet of the other *)
    pose proof (Subnet_nat_iter_S T x0) as Hx12.
    (* hence they have the same limits *)
    apply subnet_limit with (x0 := x1) in Hx12; auto.
    (* since metric spaces are Hausdorff, i.e., with unique limit
       points, the claim follows *)
    unshelve eapply
      (Hausdorff_impl_net_limit_unique
         (fun i : DS_set nat_DS => T (BanachFixedPoint_seq x0 i)) _
         x1 x2 Hx12 Hx2).
    apply metrizable_Hausdorff. exists d; assumption.
  Qed.

  Local Lemma BanachFixedPoint_seq_limit_fixed (x0 x : X) :
    @net_limit nat_DS X (BanachFixedPoint_seq x0) x ->
    T x = x.
  Proof.
    intros Hx.
    unshelve epose proof
      (continuous_func_preserves_net_limits
         X X T _ x Hx _) as HTx.
    { apply continuous_func_continuous_everywhere.
      eapply Lipschitz_impl_continuous.
      6: eassumption. all: auto. apply Hq.
    }
    symmetry.
    apply BanachFixedPoint_seq_net_limit_shift with (x0 := x0);
      assumption.
  Qed.

  Theorem BanachFixedPoint :
    inhabited X ->
    exists! x : X, T x = x.
  Proof.
    intros [x0].
    (* consider [BanachFixedPoint_seq_cauchy] and obtain its
      limit-point using completeness of [X].
      The fancy invocation is needed, to immediately obtain a [net_limit].
     *)
    specialize (Hd_comp (BanachFixedPoint_seq x0)
                  (BanachFixedPoint_seq_cauchy x0)) as [x Hx].
    apply metric_space_net_limit in Hx; auto.
    exists x. apply BanachFixedPoint_seq_limit_fixed in Hx.
    split; auto.
    intros. apply BanachFixedPoint_unique; auto.
  Qed.
End BanachFixedPoint.

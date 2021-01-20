Require Export Reals Qreals.
Require Import Lra.
Open Scope R_scope.

Local Lemma archimed_1
     : forall r : R, r < IZR (up r).
Proof. apply archimed. Qed.

Local Hint Resolve archimed_1 : real.

Lemma inverses_of_nats_approach_0:
  forall eps:R, eps > 0 -> exists n:nat, (n > 0)%nat /\
                                         / (INR n) < eps.
Proof.
  intros.
  assert (exists n:Z, (n>0)%Z /\ / (IZR n) < eps).
  {
    exists (up (/ eps)).
    split.
    - assert (IZR (up (/ eps)) > 0).
      {
        eapply Rgt_trans;
          auto with real rorders.
      }
      apply lt_0_IZR in H0.
      now apply Z.lt_gt.
    - pattern eps at 2.
      rewrite <- Rinv_involutive; auto with real.
      apply Rinv_lt_contravar; auto with real.
      apply Rmult_lt_0_compat; auto with real.
      apply Rlt_trans with (/ eps); auto with real.
  }
  destruct H0 as [[ | p | p ]];
    destruct H0;
    try inversion H0.
  exists (nat_of_P p).
  unfold IZR in H1.
  rewrite <- INR_IPR in H1.
  auto with real.
Qed.

Lemma Z_interpolation: forall x y:R, y > x+1 ->
  exists n:Z, x < IZR n < y.
Proof.
intros.
exists (up x).
split; auto with real.
eapply Rle_lt_trans;
    [ | eassumption ].
destruct (archimed x).
lra.
Qed.

Local Notation " ' x " := (Zpos x) (at level 20, no associativity) : Z_scope.

Lemma rational_interpolation: forall (x y:R) (n:positive),
  x<y -> IZR (' n) > 1/(y-x) ->
  exists m:Z, x < Q2R (m # n) < y.
Proof.
intros.
assert (0 < / IZR (' n)) by
  auto with real.
destruct (Z_interpolation (IZR (' n) * x)
  (IZR (' n) * y)) as [m].
- apply Rgt_minus in H.
  assert (IZR (' n) * (y - x) > 1).
  {
    replace 1 with ((1 / (y-x)) * (y-x)) by
      (field; auto with real).
    now apply Rmult_gt_compat_r.
  }
  apply Rgt_minus in H2.
  apply Rminus_gt.
  match goal with H2: ?a > 0 |- ?b > 0 => replace b with a end;
    lra.
- exists m.
  unfold Q2R.
  simpl.
  replace x with ((IZR (' n) * x) / IZR (' n)) by
    (field; auto with real).
  replace y with ((IZR (' n) * y) / IZR (' n)) by
    (field; auto with real).
  destruct H2.
  split;
    now apply Rmult_lt_compat_r.
Qed.

Lemma rationals_dense_in_reals: forall x y:R, x<y ->
  exists q:Q, x < Q2R q < y.
Proof.
intros.
pose (d := up (/ (y - x))).
assert (0 < d)%Z.
{
  apply lt_IZR, Rlt_trans with (/ (y - x)).
  - apply Rgt_minus in H.
    auto with real.
  - apply archimed.
}
assert (/ (y - x) < IZR d) by apply archimed.
destruct d as [|d|]; try discriminate H0.
destruct (rational_interpolation x y d) as [n]; trivial.
- replace (1 / (y-x)) with (/(y-x)); lra.
- now exists (n # d).
Qed.

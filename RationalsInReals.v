Require Export Reals.
Require Export QArith.
Require Export Qreals.

Open Scope R_scope.

Lemma inverses_of_nats_approach_0:
  forall eps:R, eps > 0 -> exists n:nat, (n > 0)%nat /\
                                         / (INR n) < eps.
Proof.
intros.
assert (exists n:Z, (n>0)%Z /\ / (IZR n) < eps).
exists (up (/ eps)); split.
assert (IZR (up (/ eps)) > 0).
apply Rgt_trans with (/ eps).
apply archimed.
auto with *.
assert ((0 < up (/ eps))%Z).
apply lt_IZR.
simpl.
assumption.
auto with *.
pattern eps at 2.
rewrite <- Rinv_involutive.
apply Rinv_lt_contravar.
apply Rmult_lt_0_compat; auto with *.
apply Rlt_trans with (/ eps); auto with *.
apply archimed.
apply archimed.
auto with *.

(* we've just proved the result for Z, now need to bring it to N *)
destruct H0. destruct H0.
exists (Z.to_nat x). split.

apply (Z2Nat.inj_lt 0 x).
auto with zarith.
auto with zarith. apply Z.gt_lt. assumption.

assert (L: forall z, (0 <= z)%Z -> INR (Z.to_nat z) = IZR z).
intros z GE0. assert (T := INR_IZR_INZ (Z.to_nat z)).
rewrite (Z2Nat.id z GE0) in T. assumption.
rewrite L. assumption. auto with zarith.
Qed.

Lemma Z_interpolation: forall x y:R, y > x+1 ->
  exists n:Z, x < IZR n < y.
Proof.
intros.
exists (up x).
split.
apply archimed.
apply Rle_lt_trans with (x+1).
pose proof (archimed x).
destruct H0.
assert (x + (IZR (up x) - x) <= x + 1).
auto with real.
ring_simplify in H2.
assumption.
assumption.
Qed.

Lemma rational_interpolation: forall (x y:R) (n:positive),
  x<y -> IZR (' n) > 1/(y-x) ->
  exists m:Z, x < Q2R (m # n) < y.
Proof.
intros.
assert (0 < / IZR (' n)).
cut (0 < IZR (' n)); auto with real.

destruct (Z_interpolation (IZR (' n) * x)
  (IZR (' n) * y)) as [m].
apply Rgt_minus in H.
assert (IZR (' n) * (y - x) > 1).
replace 1 with ((1 / (y-x)) * (y-x)); try field.
apply Rmult_gt_compat_r; trivial.
auto with real.
apply Rgt_minus in H2.
apply Rminus_gt.
match goal with H2: ?a > 0 |- ?b > 0 => replace b with a end.
trivial.
ring.

exists m.
unfold Q2R.
simpl.
replace (INR (nat_of_P n)) with (IZR (' n)); auto with real.
replace x with ((IZR (' n) * x) / IZR (' n)).
replace y with ((IZR (' n) * y) / IZR (' n)).

destruct H2.
split.
apply Rmult_lt_compat_r; trivial.
apply Rmult_lt_compat_r; trivial.
field.
auto with *.
field.
auto with *.
rewrite <- positive_nat_Z.
rewrite <- INR_IZR_INZ.
reflexivity.
Qed.

Lemma rationals_dense_in_reals: forall x y:R, x<y ->
  exists q:Q, x < Q2R q < y.
Proof.
intros.
pose (d := up (/ (y - x))).
assert ((0 < d)%Z).
apply lt_IZR.
simpl.
apply Rlt_trans with (/ (y - x)).
apply Rgt_minus in H.
auto with *.
apply archimed.
assert (/ (y - x) < IZR d) by apply archimed.
destruct d as [|d|]; try discriminate H0.

destruct (rational_interpolation x y d) as [n]; trivial.
replace (1 / (y-x)) with (/(y-x)).
trivial.
field.
apply Rgt_minus in H.
auto with real.

exists (n # d); trivial.
Qed.

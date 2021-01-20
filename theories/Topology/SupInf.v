From Coq Require Export Reals.
From Coq Require Import Lra.
From ZornsLemma Require Import EnsemblesImplicit ImageImplicit.

Definition sup := completeness.

Open Scope R_scope.

Definition is_lower_bound (E:R->Prop) (m:R) :=
  forall x:R, E x -> x >= m.
Definition lower_bound (E:R->Prop) :=
  exists m:R, is_lower_bound E m.
Definition is_glb (E:R->Prop) (m:R) :=
  is_lower_bound E m /\ (forall b:R, is_lower_bound E b -> b <= m).

Ltac cut_by_lra H := cut H; [ lra | ].

Definition inf: forall E:R->Prop, lower_bound E -> (exists x:R, E x) ->
  { m:R | is_glb E m }.
unshelve refine (fun E Hlb Hinh =>
  let H:=_ in let H0:=_ in
  exist _ (- (proj1_sig (sup (Im E Ropp) H H0))) _).
- destruct Hlb as [m].
  exists (-m).
  red. intros.
  destruct H0.
  rewrite H1.
  auto with real.
- destruct Hinh as [x].
  now exists (-x), x.
- destruct sup as [m].
  simpl.
  split; red; intros.
  + cut_by_lra (-x <= m).
    apply i.
    now exists x.
  + cut_by_lra (m <= -b).
    apply i.
    red. intros.
    cut_by_lra (-x >= b).
    apply H1.
    destruct H2.
    rewrite H3.
    now replace (--x) with x by ring.
Defined.

Lemma lub_approx: forall (S:Ensemble R) (m:R) (eps:R),
  is_lub S m -> eps > 0 -> exists x:R, In S x /\
    m - eps < x <= m.
Proof.
intros.
assert (exists x:R, In S x /\ m - eps < x).
{ apply NNPP.
  intro.
  pose proof (not_ex_all_not _ _ H1). clear H1.
  simpl in H2.
  assert (is_upper_bound S (m-eps)).
  { red. intros.
    assert (~ x > m - eps).
    { intro.
      now contradiction (H2 x). }
    destruct (total_order_T x (m-eps)) as [[?|?]|?];
      auto with real.
  now contradiction H3. }
  destruct H.
  pose proof (H3 _ H1).
  lra. }
destruct H1 as [x [? ?]].
exists x.
repeat split; trivial.
destruct H.
now apply H.
Qed.

Lemma glb_approx: forall (S:Ensemble R) (m:R) (eps:R),
  is_glb S m -> eps > 0 -> exists x:R, In S x /\ m <= x < m + eps.
Proof.
intros.
assert (exists x:R, In S x /\ x < m + eps).
{ apply NNPP; intro.
  pose proof (not_ex_all_not _ _ H1). clear H1.
  simpl in H2.
  assert (is_lower_bound S (m+eps)).
  { red. intros.
    assert (~ x < m + eps).
    { intro.
      contradiction (H2 x).
      now split. }
    destruct (total_order_T x (m+eps)) as [[?|?]|?];
      auto with real.
    now contradiction H3.
    destruct H.
    lra. }
  destruct H.
  pose proof (H3 _ H1).
  lra. }
destruct H1 as [x [? ?]].
exists x.
repeat split; trivial.
destruct H.
cut_by_lra (x >= m).
auto with real.
Qed.

Lemma lt_plus_epsilon_le: forall x y:R,
  (forall eps:R, eps > 0 -> x < y + eps) -> x <= y.
Proof.
intros.
destruct (total_order_T x y) as [[?|?]|?];
  lra || cut_by_lra (x < y + (x - y)).
apply H.
lra.
Qed.

Lemma gt_minus_epsilon_ge: forall x y:R,
  (forall eps:R, eps > 0 -> x > y - eps) -> x >= y.
Proof.
intros.
destruct (total_order_T x y) as [[?|?]|?];
  lra || cut_by_lra (x > y - (y - x)).
apply H.
lra.
Qed.

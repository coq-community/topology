From Coq Require Import Reals Lia Lra ClassicalChoice.
From Coq Require Export Qreals.
Require Import RationalsInReals.
Local Close Scope Q_scope.
Local Close Scope R_scope.

Set Asymmetric Patterns.

(* define nonnegative dyadic rationals *)
Inductive dyadic_rational : Type :=
  | m_over_2_to_n: forall m n:nat, dyadic_rational.
Inductive dr_eq : dyadic_rational -> dyadic_rational -> Prop :=
  | dr_eq_refl: forall x:dyadic_rational, dr_eq x x
  | dr_eq_sym: forall x y:dyadic_rational, dr_eq x y -> dr_eq y x
  | dr_eq_trans: forall x y z:dyadic_rational,
    dr_eq x y -> dr_eq y z -> dr_eq x z
  | dr_eq_scale: forall (m n:nat),
    dr_eq (m_over_2_to_n m n)
          (m_over_2_to_n (2*m) (S n)).
Inductive dr_lt : dyadic_rational -> dyadic_rational -> Prop :=
  | intro_dr_lt: forall m m' n:nat, m < m' ->
    dr_lt (m_over_2_to_n m n) (m_over_2_to_n m' n)
  | dr_lt_wd: forall x x' y y':dyadic_rational,
    dr_lt x y -> dr_eq x x' -> dr_eq y y' -> dr_lt x' y'.

Lemma dr_incr_denom: forall (m n n':nat), n<=n' ->
  exists m':nat, dr_eq (m_over_2_to_n m' n')
                       (m_over_2_to_n m n).
Proof.
induction 1.
- exists m.
  apply dr_eq_refl.
- destruct IHle as [m'].
  exists (2*m').
  apply dr_eq_trans with (m_over_2_to_n m' m0); trivial.
  apply dr_eq_sym.
  apply dr_eq_scale.
Qed.

Lemma dr_total_order: forall x y:dyadic_rational,
  dr_lt x y \/ dr_eq x y \/ dr_lt y x.
Proof.
intros.
destruct x as [m n].
destruct y as [m' n'].
destruct (Nat.le_gt_cases n n').
- destruct (dr_incr_denom m n n') as [m0]; trivial.
  destruct (Nat.le_gt_cases m0 m').
  + apply Nat.lt_eq_cases in H1.
    destruct H1.
    * left.
      apply dr_lt_wd with
          (m_over_2_to_n m0 n') (m_over_2_to_n m' n'); trivial.
      -- apply intro_dr_lt; trivial.
      -- apply dr_eq_refl.
    * right; left.
      apply dr_eq_trans with (m_over_2_to_n m0 n').
      -- apply dr_eq_sym; trivial.
      -- rewrite H1; apply dr_eq_refl.
  + right; right.
    apply dr_lt_wd with
        (m_over_2_to_n m' n') (m_over_2_to_n m0 n'); trivial.
    * apply intro_dr_lt; trivial.
    * apply dr_eq_refl.
- assert (n' <= n) by auto with arith.
  destruct (dr_incr_denom m' n' n) as [m0]; trivial.
  destruct (Nat.le_gt_cases m m0).
  + apply Nat.lt_eq_cases in H2.
    destruct H2.
    * left.
      apply dr_lt_wd with
          (m_over_2_to_n m n) (m_over_2_to_n m0 n).
      -- apply intro_dr_lt; trivial.
      -- apply dr_eq_refl.
      -- trivial.
    * right; left.
      apply dr_eq_trans with (m_over_2_to_n m0 n); trivial.
      rewrite H2; apply dr_eq_refl.
  + right; right.
    apply dr_lt_wd with
        (m_over_2_to_n m0 n) (m_over_2_to_n m n); trivial.
    * apply intro_dr_lt; trivial.
    * apply dr_eq_refl.
Qed.

Local Notation " ' x " := (Zpos x) (at level 20, no associativity) : Z_scope.

Fixpoint pos_power2 (n:nat) : positive := match n with
  | O => 1%positive
  | S m => ((pos_power2 m)~0)%positive
end.

Definition dr2Q (x:dyadic_rational) : Q :=
  match x with
  | m_over_2_to_n m n => (Z_of_nat m) # (pos_power2 n)
  end.

Local Open Scope Q_scope.

Lemma dr2Q_wd: forall x y:dyadic_rational,
  dr_eq x y -> dr2Q x == dr2Q y.
Proof.
intros.
induction H;
  auto with qarith.
{ now transitivity (dr2Q y). }
unfold Qeq.
simpl.
change ((' (pos_power2 n)~0)%Z) with
    ((2 * ' pos_power2 n)%Z).
repeat rewrite inj_plus.
ring.
Qed.

Lemma dr2Q_incr: forall x y:dyadic_rational,
  dr_lt x y -> dr2Q x < dr2Q y.
Proof.
  induction 1.
  - unfold dr2Q, Qlt.
    cbn.
    apply Zmult_lt_compat_r.
    + easy.
    + now apply Znat.inj_lt.
  - now rewrite <- (dr2Q_wd _ _ H0),
                <- (dr2Q_wd _ _ H1).
Qed.

Lemma Qlt_dr_lt: forall x y:dyadic_rational,
  (dr2Q x < dr2Q y)%Q -> dr_lt x y.
Proof.
intros.
destruct (dr_total_order x y) as [|[|]];
  [ trivial | apply dr2Q_wd in H0 | apply dr2Q_incr in H0 ];
  contradict H0;
  auto with qarith.
Qed.

Open Scope R_scope.

Lemma dyadic_rationals_dense_in_reals: forall x y:R,
  0 <= x < y -> exists q:dyadic_rational,
  x < Q2R (dr2Q q) < y.
Proof.
intros.
assert (forall m:Z, exists n:nat, ((m < ' pos_power2 n)%Z)).
{ intros.
  case m; intros;
    try now exists O.
  induction p.
  - destruct IHp as [n].
    exists (S n).
    unfold Z.lt.
    simpl.
    rewrite Pos.compare_xI_xO.
    unfold Z.lt in H0.
    simpl in H0.
    now rewrite H0.
  - destruct IHp as [n].
    now exists (S n).
  - now exists 1%nat. }
destruct (H0 (up (1/(y-x)))) as [n].
destruct (rational_interpolation x y (pos_power2 n)) as [m].
- apply H.
- eapply Rlt_trans.
  + apply archimed.
  + now apply IZR_lt.
- destruct m as [|m|].
  + unfold Q2R in H2.
    simpl in H2.
    replace (0 * _) with 0 in H2 by ring.
    destruct H, H2.
    contradict H.
    auto with real.
  + exists (m_over_2_to_n (nat_of_P m) n).
    unfold dr2Q.
    now rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
  + assert (x < 0).
    { eapply Rlt_trans.
      - apply H2.
      - replace 0 with (Q2R 0) by lra.
        apply Qlt_Rlt.
        auto with qarith. }
    lra.
Qed.

Require Export TopologicalSpaces.
Require Export InteriorsClosures.
Require Import Arith.
Require Export RTopology.

Section Urysohns_Lemma_construction.

Variable X:TopologicalSpace.
Variable normal_sep_fun: forall F U:Ensemble X,
  closed F -> open U -> Included F U ->
  { V:Ensemble X | open V /\ Included F V /\
    Included (closure V) U }.
Variable U0 U1:Ensemble X.
Hypothesis U0_open: open U0.
Hypothesis U1_open: open U1.
Hypothesis U0_in_U1: Included (closure U0) U1.

Definition Un (n:nat) : Ensemble X :=
  match n with
  | O => U0
  | S O => U1
  | S (S _) => Full_set
  end.

Lemma Un_open: forall n:nat, open (Un n).
Proof.
destruct n as [|[|]]; trivial.
simpl.
apply open_full.
Qed.

Lemma Un_incr: forall n:nat, Included (closure (Un n))
                                    (Un (S n)).
Proof.
destruct n as [|].
- simpl.
  trivial.
- simpl.
  red; intros; constructor.
Qed.

Definition expand_U_dyadic (f:nat -> Ensemble X)
  (Hopen: forall n:nat, open (f n))
  (Hincr: forall n:nat, Included (closure (f n)) (f (S n)))
  (n:nat) : Ensemble X :=
if (Nat.Even_Odd_dec n) then f (Nat.div2 n) else
let m := Nat.div2 n in proj1_sig
  (normal_sep_fun (closure (f m)) (f (S m))
     (closure_closed _) (Hopen _) (Hincr _)).

Lemma expand_U_dyadic_open: forall f Hopen Hincr n,
  open (expand_U_dyadic f Hopen Hincr n).
Proof.
intros.
unfold expand_U_dyadic.
destruct Nat.Even_Odd_dec.
- apply Hopen.
- destruct normal_sep_fun.
  simpl.
  apply a.
Qed.

Lemma expand_U_dyadic_incr: forall f Hopen Hincr n,
  Included (closure (expand_U_dyadic f Hopen Hincr n))
     (expand_U_dyadic f Hopen Hincr (S n)).
Proof.
intros.
unfold expand_U_dyadic.
simpl.
destruct Nat.Even_Odd_dec.
- destruct normal_sep_fun.
  simpl.
  destruct n.
  + simpl.
    apply a.
  + rewrite <- Nat.Odd_div2.
    * apply a.
    * apply Nat.Even_succ.
      exact e.
- simpl.
  destruct normal_sep_fun as [x [Hx0 [Hx1 Hx2]]].
  simpl.
  destruct n.
  { (* ~ Nat.Odd 0 *)
    contradict o. clear.
    intros []. lia.
  }
  apply Nat.Odd_succ in o.
  rewrite Nat.Even_div2.
  + exact Hx2.
  + exact o.
Qed.

Definition packaged_expand_U_dyadic :
  { f:nat->Ensemble X |
    (forall m:nat, open (f m)) /\
    (forall m:nat, Included (closure (f m)) (f (S m))) } ->
  { f:nat->Ensemble X |
    (forall m:nat, open (f m)) /\
    (forall m:nat, Included (closure (f m)) (f (S m))) }.
refine (fun fsig => match fsig with
  | exist f (conj Hopen Hincr as a) => exist _ (expand_U_dyadic f Hopen Hincr) _
  end).
destruct a.
split.
- apply expand_U_dyadic_open.
- apply expand_U_dyadic_incr.
Defined.

Definition U_dyadic_level_n (n:nat) :
  { f:nat->Ensemble X |
    (forall m:nat, open (f m)) /\
    (forall m:nat, Included (closure (f m)) (f (S m))) }.
refine (let lev_n := fix lev_n (n:nat) :
  { f:nat->Ensemble X |
    (forall m:nat, open (f m)) /\
    (forall m:nat, Included (closure (f m)) (f (S m))) } :=
  match n with
  | O => exist _ Un _
  | S n' => packaged_expand_U_dyadic (lev_n n')
  end in lev_n n).
split.
- apply Un_open.
- apply Un_incr.
Defined.

Definition U_dyadic (x:dyadic_rational) :
  Ensemble X :=
match x with
| m_over_2_to_n m n => (proj1_sig (U_dyadic_level_n n)) m
end.

Lemma U_dyadic_wd: forall x y:dyadic_rational, dr_eq x y ->
  U_dyadic x = U_dyadic y.
Proof.
intros.
induction H; auto.
{ now transitivity (U_dyadic y). }
simpl.
unfold packaged_expand_U_dyadic.
destruct U_dyadic_level_n.
destruct a.
simpl.
unfold expand_U_dyadic.
change ((m + (m + 0))%nat) with ((2*m)%nat).
rewrite div2_double.
assert (forall m:nat, Nat.Even (2*m)).
{ intros ?. apply Nat.Even_mul_l.
  exists 1%nat. reflexivity.
}
destruct Nat.Even_Odd_dec; trivial.
now contradiction Nat.Even_Odd_False with (2 * m)%nat.
Qed.

Lemma U_dyadic_open: forall x:dyadic_rational,
  open (U_dyadic x).
Proof.
intro.
destruct x.
unfold U_dyadic.
now destruct U_dyadic_level_n.
Qed.

Lemma U_dyadic_incr: forall x y:dyadic_rational, dr_lt x y ->
  Included (closure (U_dyadic x)) (U_dyadic y).
Proof.
intros.
induction H.
- induction H.
  + unfold U_dyadic.
    destruct U_dyadic_level_n.
    simpl.
    apply a.
  + cut (Included (closure (U_dyadic (m_over_2_to_n m0 n)))
       (U_dyadic (m_over_2_to_n (S m0) n))).
    * intro.
      pose proof (closure_inflationary
        (U_dyadic (m_over_2_to_n m0 n))).
      auto with sets.
    * unfold U_dyadic.
      destruct U_dyadic_level_n.
      simpl.
      apply a.
- now rewrite <- (U_dyadic_wd _ _ H0),
              <- (U_dyadic_wd _ _ H1).
Qed.

Definition Urysohns_Lemma_function : X -> RTop.
refine (fun x:X => proj1_sig (inf
 (Add
  (Im [ alpha:dyadic_rational | In (U_dyadic alpha) x ]
      (fun alpha:dyadic_rational => Q2R (dr2Q alpha)))
  1)
  _ _)).
- exists 0.
  red. intros.
  destruct H.
  + destruct H.
    destruct x0.
    simpl in H0.
    rewrite H0.
    replace 0 with (Q2R 0) by lra.
    cut (Q2R 0 <= Q2R (Z_of_nat m # pos_power2 n));
      auto with real.
    apply Qle_Rle.
    unfold Qle.
    simpl.
    auto with zarith.
  + destruct H.
    lra.
- exists 1.
  right.
  constructor.
Defined.

Lemma Urysohns_Lemma_function_range:
  forall x:X, 0 <= Urysohns_Lemma_function x <= 1.
Proof.
intros.
unfold Urysohns_Lemma_function.
destruct inf as [y].
simpl.
split.
- apply i.
  red; intros.
  destruct H.
  + destruct H.
    rewrite H0.
    replace 0 with (Q2R 0) by lra.
    cut (Q2R 0 <= Q2R (dr2Q x0));
      auto with real.
    apply Qle_Rle.
    destruct x0.
    unfold dr2Q, Qle.
    simpl.
    auto with zarith.
  + destruct H.
    auto with real.
- cut (1 >= y); auto with real.
  apply i.
  right.
  constructor.
Qed.

Lemma Urysohns_Lemma_function_0: forall x:X,
  In U0 x -> Urysohns_Lemma_function x = 0.
Proof.
intros.
apply Rle_antisym;
  [ | apply Urysohns_Lemma_function_range ].
unfold Urysohns_Lemma_function.
destruct inf as [y].
simpl.
cut (0 >= y); auto with real.
apply i.
left.
exists (m_over_2_to_n 0 0).
- now constructor.
- unfold Q2R.
  simpl.
  ring.
Qed.

Lemma Urysohns_Lemma_function_1: forall x:X,
  ~ In U1 x -> Urysohns_Lemma_function x = 1.
Proof.
intros.
apply Rle_antisym.
{ apply Urysohns_Lemma_function_range. }
unfold Urysohns_Lemma_function.
destruct inf as [y].
simpl.
apply i.
red. intros.
destruct H0;
  [ | destruct H0; now right ].
destruct H0.
destruct x0.
destruct H0.
assert (~ (m < (nat_of_P (pos_power2 n)))%nat).
{ intro.
  assert (forall n:nat, dr_eq
    (m_over_2_to_n (nat_of_P (pos_power2 n)) n)
    (m_over_2_to_n 1 0)).
  { induction n0.
    - simpl.
      unfold nat_of_P.
      simpl.
      apply dr_eq_refl.
    - apply dr_eq_trans with (2:=IHn0).
      apply dr_eq_sym.
      replace (nat_of_P (pos_power2 (S n0))) with
        ((2 * nat_of_P (pos_power2 n0))%nat).
      + apply dr_eq_scale.
      + simpl pos_power2.
        now rewrite Pos2Nat.inj_xO. }
  assert (dr_lt (m_over_2_to_n m n) (m_over_2_to_n 1 0)).
  { apply dr_lt_wd with (m_over_2_to_n m n)
      (m_over_2_to_n (nat_of_P (pos_power2 n)) n); trivial.
    - now apply intro_dr_lt.
    - apply dr_eq_refl. }
  pose proof (U_dyadic_incr _ _ H4).
  simpl (U_dyadic (m_over_2_to_n 1 0)) in H5.
  assert (Included (U_dyadic (m_over_2_to_n m n)) U1).
  { red. intros.
    now apply H5, closure_inflationary. }
  contradiction H.
  now apply H6. }
assert ((m >= nat_of_P (pos_power2 n))%nat) by
  auto with zarith.
red in H3.
assert ((nat_of_P (pos_power2 n) < m \/
        (nat_of_P (pos_power2 n) = m))%nat) by
  now apply Nat.lt_eq_cases.
rewrite H1.
replace 1 with (Q2R (dr2Q (m_over_2_to_n 1 0))).
- match goal with |- ?a >= ?b =>
    cut (b <= a); auto with real end.
  apply Qle_Rle.
  unfold dr2Q.
  unfold Qle.
  simpl.
  ring_simplify.
  rewrite Zpos_eq_Z_of_nat_o_nat_of_P.
  auto with zarith.
- unfold Q2R.
  simpl.
  field.
Qed.

Lemma Urysohns_Lemma_function_inv_image_lower_ray_full (r : R) :
  1 < r ->
  inverse_image
    Urysohns_Lemma_function (lower_open_ray Rle r) = Full_set.
Proof.
  intros Hr. apply Extensionality_Ensembles; split.
  { constructor. }
  intros x _. constructor. constructor.
  pose proof (Urysohns_Lemma_function_range x). lra.
Qed.

Lemma Urysohns_Lemma_function_inv_image_lower_ray (x : R) :
  x <= 1 ->
  inverse_image
    Urysohns_Lemma_function (lower_open_ray Rle x) =
    IndexedUnion
      (fun alpha : { alpha : dyadic_rational | Q2R (dr2Q alpha) < x } =>
         U_dyadic (proj1_sig alpha)).
Proof.
  intros Hx. apply Extensionality_Ensembles; split.
  - intros x0 [[Hx1]].
    assert (Urysohns_Lemma_function x0 < x) as Hx0 by lra.
    clear Hx1.
    remember (Urysohns_Lemma_function x0) as y.
    unfold Urysohns_Lemma_function in Heqy.
    destruct inf in Heqy; simpl in Heqy.
    destruct Heqy.
    destruct (glb_approx _ _ (x-y) i) as [x1 [Hx1 Hxy]].
    { now apply Rgt_minus. }
    destruct Hx1.
    2: {
      destruct H; lra.
    }
    destruct H as [alpha [Halpha] x1].
    subst x1.
    unshelve eexists (exist _ alpha _).
    { lra. }
    cbn. assumption.
  - intros y Hy. constructor. constructor.
    destruct Hy as [[alpha Halpha] y Hy].
    cbn in Hy.
    cut (Urysohns_Lemma_function y < x);
      [intros; lra|].
    apply Rle_lt_trans with (2:=Halpha).
    unfold Urysohns_Lemma_function. destruct inf. simpl.
    cut (Q2R (dr2Q alpha) >= x0); auto with real.
    apply i. left. now exists alpha.
Qed.

Lemma Urysohns_Lemma_function_inv_image_upper_ray_full (r : R) :
  r < 0 ->
  inverse_image Urysohns_Lemma_function (upper_open_ray Rle r) =
    Full_set.
Proof.
  intros Hr. apply Extensionality_Ensembles; split.
  { constructor. }
  intros x _. constructor. constructor.
  pose proof (Urysohns_Lemma_function_range x). lra.
Qed.

Lemma Urysohns_Lemma_function_inv_image_upper_ray_empty (r : R) :
  1 <= r ->
  inverse_image Urysohns_Lemma_function (upper_open_ray Rle r) =
    Empty_set.
Proof.
  intros Hr. apply Extensionality_Ensembles; split.
  2: { intros ? []. }
  intros x [[Hx]].
  pose proof (Urysohns_Lemma_function_range x). lra.
Qed.

Lemma Urysohns_Lemma_function_inv_image_upper_ray (r : R) :
  0 <= r < 1 ->
  inverse_image Urysohns_Lemma_function (upper_open_ray Rle r) =
    IndexedUnion (fun alpha:{alpha:dyadic_rational |
                       r < Q2R (dr2Q alpha) < 1} =>
               (Complement (closure (U_dyadic (proj1_sig alpha))))).
Proof.
  intros Hr.
  apply Extensionality_Ensembles; split.
  - intros x [[Hx]].
    remember (Urysohns_Lemma_function x) as y.
    assert (y <= 1).
    { rewrite Heqy. apply Urysohns_Lemma_function_range. }
    unfold Urysohns_Lemma_function in Heqy.
    destruct inf in Heqy. simpl in Heqy.
    destruct Heqy.
    assert (r < y) as Hry by lra.
    clear Hx.
    destruct (dyadic_rationals_dense_in_reals r y) as [alpha].
    { lra. }
    assert (~ In (U_dyadic alpha) x).
    { intro.
      absurd (Q2R (dr2Q alpha) >= y).
      - lra.
      - apply i. left. now exists alpha.
    }
    destruct (dyadic_rationals_dense_in_reals r (Q2R (dr2Q alpha)))
      as [beta Hbeta].
    { lra. }
    unshelve eexists (exist _ beta _).
    { cbn. lra. }
    cbn. intros Hx.
    assert (dr_lt beta alpha) as Hab by
      apply Qlt_dr_lt, Rlt_Qlt, Hbeta.
    pose proof (U_dyadic_incr _ _ Hab).
    auto with sets.
  - intros x Hx. constructor. constructor.
    cut (r < Urysohns_Lemma_function x); auto with real.
    destruct Hx as [a x Hx].
    destruct a as [alpha Ha].
    simpl in Hx.
    apply Rlt_le_trans with (Q2R (dr2Q alpha)).
    { apply Ha. }
    unfold Urysohns_Lemma_function. destruct inf as [y]. simpl.
    apply i. red. intros x0 Hx0.
    destruct Hx0.
    2: {
      destruct H. lra.
    }
    destruct H as [beta [Hb]].
    assert (dr_lt alpha beta \/ dr_eq alpha beta) as Hab.
    { cut (~ dr_lt beta alpha).
      - destruct (dr_total_order alpha beta) as [|[|]]; auto.
        intro. tauto.
      - intro.
        pose proof (U_dyadic_incr _ _ H0) as H1.
        subst y0. contradiction Hx.
        apply closure_inflationary.
        apply H1.
        now apply closure_inflationary.
    }
    destruct Hab; rewrite H.
    + pose proof (dr2Q_incr _ _ H0).
      cut (Q2R (dr2Q alpha) <= Q2R (dr2Q beta)); auto with real.
      apply Qle_Rle.
      auto with qarith.
    + cut (Q2R (dr2Q alpha) <= Q2R (dr2Q beta)); auto with real.
      apply Qle_Rle.
      pose proof (dr2Q_wd _ _ H0).
      auto with zarith qarith.
Qed.

Lemma Urysohns_Lemma_function_continuous:
  continuous Urysohns_Lemma_function.
Proof.
apply continuous_subbasis with (order_topology_subbasis Rle).
{ apply Build_TopologicalSpace_from_subbasis_subbasis. }
intros.
destruct H.
- (* proving that inverse image of lower open interval is open *)
  destruct (classic (1<x)).
  { (* if [1<x], inverse image is everything *)
    rewrite Urysohns_Lemma_function_inv_image_lower_ray_full;
      auto with topology.
  }
  (* if x<=1, inverse image is union of U_alpha for alpha < x *)
  assert (x<=1) by
    now apply Rnot_gt_le.
  rewrite Urysohns_Lemma_function_inv_image_lower_ray; auto.
  apply open_indexed_union.
  intros ?. apply U_dyadic_open.
- (* proving that inverse image of upper open interval is open *)
  destruct (classic (x<0)) as [Hx0|Hx0].
  { (* if x<0, inverse image is everything *)
    rewrite Urysohns_Lemma_function_inv_image_upper_ray_full;
      auto with topology.
  }
  destruct (classic (1<=x)) as [Hx1|Hx1].
  { (* if x>=1, inverse image is empty *)
    rewrite Urysohns_Lemma_function_inv_image_upper_ray_empty;
      auto with topology.
  }
  (* if 0 <= x < 1, inverse image is union of
     Complement (closure U_alpha) for x < alpha < 1 *)
  rewrite Urysohns_Lemma_function_inv_image_upper_ray.
  2: lra.
  apply open_indexed_union.
  intros. apply closure_closed.
Qed.

End Urysohns_Lemma_construction.

Theorem UrysohnsLemma: forall X:TopologicalSpace, normal_sep X ->
  forall F G:Ensemble X,
  closed F -> closed G -> Intersection F G = Empty_set ->
  exists f:X -> RTop,
  continuous f /\ (forall x:X, 0 <= f x <= 1) /\
  (forall x:X, In F x -> f x = 0) /\
  (forall x:X, In G x -> f x = 1).
Proof.
intros X [_ HX_normal] F G HF HG HFG.
destruct (HX_normal F G HF HG HFG) as [U [V [HU [HV [HFU [HGV HUV]]]]]].
assert (inhabited (forall F U:Ensemble X, closed F ->
  open U -> Included F U ->
  { V:Ensemble X | open V /\ Included F V /\
                               Included (closure V) U }))
       as [normal_sep_fun].
{ destruct (choice (fun (FU_pair:
    {p:Ensemble X * Ensemble X |
     closed (fst p) /\ open (snd p) /\ Included (fst p) (snd p)})
    (V0:Ensemble X) =>
     open V0 /\ Included (fst (proj1_sig FU_pair)) V0 /\
     Included (closure V0) (snd (proj1_sig FU_pair)))) as
    [pre_choice_fun Hpre_choice_fun].
  2: {
    exists.
    intros F0 U0 HF0 HU0 HF0U0.
    exists (pre_choice_fun (exist _ (F0,U0)
      (conj HF0 (conj HU0 HF0U0)))).
    apply Hpre_choice_fun. }
  intros [[F0 U0] [HF0 [HU0 HF0U0]]].
  simpl in *.
  destruct (HX_normal F0 (Complement U0))
    as [U1 [V1 [? [? [? [H_CU0_V1 HU1V1]]]]]]; trivial.
  { red. now rewrite Complement_Complement. }
  { extensionality_ensembles_inv.
    subst.
    match goal with
    | H : In F0 _ |- _ =>
      apply HF0U0 in H
    end.
    contradiction. }
  exists U1.
  repeat split; trivial.
  transitivity (Complement V1).
  - apply closure_minimal.
    + red. now rewrite Complement_Complement.
    + red. intros.
      intro.
      eapply Noone_in_empty.
      rewrite <- HU1V1.
      constructor;
        eassumption.
  - red. intros.
    apply NNPP. intros Hx.
    apply H_CU0_V1 in Hx.
    contradiction. }
unshelve eexists (Urysohns_Lemma_function _ normal_sep_fun
  U (Complement G) HU HG _).
{ transitivity (Complement V).
  - apply closure_minimal.
    + red. now rewrite Complement_Complement.
    + red. intros.
      intro.
      eapply Noone_in_empty.
      rewrite <- HUV.
      econstructor;
        eassumption.
  - red. intros x Hx ?.
    contradiction Hx.
    now apply HGV. }
split.
{ apply Urysohns_Lemma_function_continuous. }
split.
{ apply Urysohns_Lemma_function_range. }
split;
  intros.
- apply Urysohns_Lemma_function_0; auto.
- apply Urysohns_Lemma_function_1; auto.
Qed.

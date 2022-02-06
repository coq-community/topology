From Coq Require Import Reals Lra ClassicalChoice.
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
destruct (le_or_lt n n').
- destruct (dr_incr_denom m n n') as [m0]; trivial.
  destruct (le_or_lt m0 m').
  + destruct (le_lt_or_eq _ _ H1).
    * left.
      apply dr_lt_wd with
          (m_over_2_to_n m0 n') (m_over_2_to_n m' n'); trivial.
      -- apply intro_dr_lt; trivial.
      -- apply dr_eq_refl.
    * right; left.
      apply dr_eq_trans with (m_over_2_to_n m0 n').
      -- apply dr_eq_sym; trivial.
      -- rewrite H2; apply dr_eq_refl.
  + right; right.
    apply dr_lt_wd with
        (m_over_2_to_n m' n') (m_over_2_to_n m0 n'); trivial.
    * apply intro_dr_lt; trivial.
    * apply dr_eq_refl.
- assert (n' <= n) by auto with arith.
  destruct (dr_incr_denom m' n' n) as [m0]; trivial.
  destruct (le_or_lt m m0).
  + destruct (le_lt_or_eq _ _ H2).
    * left.
      apply dr_lt_wd with
          (m_over_2_to_n m n) (m_over_2_to_n m0 n).
      -- apply intro_dr_lt; trivial.
      -- apply dr_eq_refl.
      -- trivial.
    * right; left.
      apply dr_eq_trans with (m_over_2_to_n m0 n); trivial.
      rewrite H3; apply dr_eq_refl.
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
Require Import Div2.
Require Import Even.
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

Definition expand_U_dyadic (f:nat->Ensemble X)
  (Hopen: forall n:nat, open (f n))
  (Hincr: forall n:nat, Included (closure (f n)) (f (S n)))
  (n:nat) : Ensemble X :=
if (even_odd_dec n) then f (div2 n) else
let m := div2 n in proj1_sig
  (normal_sep_fun (closure (f m)) (f (S m))
     (closure_closed _) (Hopen _) (Hincr _)).

Lemma expand_U_dyadic_open: forall f Hopen Hincr n,
  open (expand_U_dyadic f Hopen Hincr n).
Proof.
intros.
unfold expand_U_dyadic.
destruct even_odd_dec.
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
destruct even_odd_dec.
- destruct normal_sep_fun.
  simpl.
  destruct n.
  + simpl.
    apply a.
  + rewrite <- odd_div2.
    * apply a.
    * now inversion e.
- simpl.
  destruct normal_sep_fun.
  simpl.
  destruct o.
  rewrite even_div2.
  + now apply a.
  + trivial.
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
assert (forall m:nat, even (2*m)).
{ induction m0.
  { constructor. }
  replace ((2 * S m0)%nat) with ((S (S (2 * m0)))%nat) by ring.
  constructor.
  now constructor. }
destruct even_odd_dec; trivial.
now contradiction not_even_and_odd with ((2 * m)%nat).
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
  now apply le_lt_or_eq.
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

Lemma Urysohns_Lemma_function_continuous:
  continuous Urysohns_Lemma_function.
Proof.
apply continuous_subbasis with (order_topology_subbasis _ Rle).
{ apply Build_TopologicalSpace_from_subbasis_subbasis. }
intros.
destruct H.
- (* proving that inverse image of lower open interval is open *)
  destruct (classic (x>1)).
  (* if x>1, inverse image is everything *)
  + match goal with |- open ?U => assert (U = Full_set) end.
    * extensionality_ensembles;
        constructor.
      constructor.
      cut (Urysohns_Lemma_function x0 < x);
        auto with real.
      apply Rle_lt_trans with 1; trivial.
      apply Urysohns_Lemma_function_range.
    * rewrite H0.
      apply open_full.
  + (* if x<=1, inverse image is union of U_alpha for alpha < x *)
    assert (x<=1) by
      now apply Rnot_gt_le.
    match goal with |- open ?U => assert (U =
      IndexedUnion (fun alpha:{alpha:dyadic_rational |
                               Q2R (dr2Q alpha) < x} =>
                    U_dyadic (proj1_sig alpha))) end.
    * extensionality_ensembles.
      ** destruct H1.
         assert (Urysohns_Lemma_function x0 < x).
         { destruct H1.
           { destruct (Rdichotomy _ _ H2); trivial. }
           contradict H2.
           auto with real. }
         clear H1.
         remember (Urysohns_Lemma_function x0) as y.
         unfold Urysohns_Lemma_function in Heqy.
         destruct inf in Heqy; simpl in Heqy.
         destruct Heqy.
         destruct (glb_approx _ _ (x-y) i).
         { now apply Rgt_minus. }
         destruct H1.
         destruct H1.
         *** destruct H1 as [alpha].
             destruct H1.
             destruct H4.
             ring_simplify in H6.
             rewrite H5 in H6.
             now exists (exist (fun beta:dyadic_rational => Q2R (dr2Q beta) < x)
               alpha H6).
         *** destruct H1.
             lra.
      ** destruct a as [alpha].
         simpl in H1.
         constructor.
         constructor.
         cut (Urysohns_Lemma_function x0 < x);
           auto with real.
         apply Rle_lt_trans with (2:=r).
         unfold Urysohns_Lemma_function. destruct inf. simpl.
         cut (Q2R (dr2Q alpha) >= x1); auto with real.
         apply i.
         left.
         now exists alpha.
    * rewrite H1.
      apply open_indexed_union.
      intro.
      apply U_dyadic_open.
- (* proving that inverse image of upper open interval is open *)
  destruct (classic (x<0)).
  + (* if x<0, inverse image is everything *)
    match goal with |- open ?U => assert (U = Full_set) end.
    * extensionality_ensembles;
        constructor.
      constructor.
      cut (x < Urysohns_Lemma_function x0); auto with real.
      apply Rlt_le_trans with (1:=H), Urysohns_Lemma_function_range.
    * rewrite H0.
      apply open_full.
  + assert (x >= 0) by now apply Rnot_lt_ge.
    clear H.
    (* if x>=1, inverse image is empty *)
    destruct (classic (x>=1)).
    * match goal with |- open ?U => assert (U = Empty_set) end.
      2 : { rewrite H1. apply open_empty. }
      extensionality_ensembles.
      destruct H1.
      assert (x < Urysohns_Lemma_function x0).
      { destruct (total_order_T x (Urysohns_Lemma_function x0)) as
        [[|]|]; trivial.
        - now contradiction H2.
        - contradict r.
          now apply Rle_not_gt. }
      exfalso.
      apply (Rlt_irrefl x).
      apply Rlt_le_trans with (Urysohns_Lemma_function x0); trivial.
      apply Rle_trans with 1; auto with real.
      apply Urysohns_Lemma_function_range.
    * (* if 0 <= x < 1, inverse image is union of
         Complement (closure U_alpha) for x < alpha < 1 *)
      assert (x < 1) by now apply Rnot_ge_lt.
      clear H.
      match goal with |- open ?U => assert (U =
        IndexedUnion (fun alpha:{alpha:dyadic_rational |
                           x < Q2R (dr2Q alpha) < 1} =>
                   (Complement (closure (U_dyadic (proj1_sig alpha))))))
       end.
      2 : {
        rewrite H.
        apply open_indexed_union.
        intros.
        apply closure_closed. }
      apply Extensionality_Ensembles; split; red; intros.
      ** destruct H.
         destruct H.
         destruct H.
         remember (Urysohns_Lemma_function x0) as y.
         assert (y <= 1).
         { rewrite Heqy. apply Urysohns_Lemma_function_range. }
         unfold Urysohns_Lemma_function in Heqy.
         destruct inf in Heqy. simpl in Heqy.
         destruct Heqy.
         assert (x < y).
         { destruct (total_order_T x y) as [[|]|]; trivial.
           - now contradiction H2.
           - contradict r.
             now apply Rle_not_gt. }
         destruct (dyadic_rationals_dense_in_reals x y) as [alpha].
         { auto with real. }
         assert (~ In (U_dyadic alpha) x0).
         { intro.
           absurd (Q2R (dr2Q alpha) >= y).
           - destruct H5.
             now apply Rlt_not_ge.
           - apply i.
             left.
             now exists alpha. }
         destruct (dyadic_rationals_dense_in_reals x (Q2R (dr2Q alpha)))
           as [beta].
         { split; auto with real.
           apply H5. }
         assert (dr_lt beta alpha) by
           apply Qlt_dr_lt, Rlt_Qlt, H7.
         pose proof (U_dyadic_incr _ _ H8).
         assert (x < Q2R (dr2Q beta) < 1).
         { split.
           { apply H7. }
           apply Rlt_trans with (Q2R (dr2Q alpha)).
           { apply H7. }
           apply Rlt_le_trans with y; trivial.
           apply H5. }
         exists (exist (fun alpha0:dyadic_rational =>
                        x < Q2R (dr2Q alpha0) < 1)
                 beta H10).
         simpl.
         intro.
         contradiction H6.
         now apply H9.
      ** destruct H.
         destruct a as [alpha].
         simpl in H.
         constructor.
         constructor.
         cut (x < Urysohns_Lemma_function x0); auto with real.
         apply Rlt_le_trans with (Q2R (dr2Q alpha)).
         { apply a. }
         unfold Urysohns_Lemma_function. destruct inf as [y]. simpl.
         apply i.
         red. intros.
         destruct H2.
         *** destruct H2 as [beta].
             assert (dr_lt alpha beta \/ dr_eq alpha beta).
             { cut (~ dr_lt beta alpha).
               - destruct (dr_total_order alpha beta) as [|[|]]; auto.
                 intro.
                 contradiction H5.
               - intro.
                 pose proof (U_dyadic_incr _ _ H4).
                 destruct H2.
                 contradiction H.
                 apply closure_inflationary.
                 apply H5.
                 now apply closure_inflationary. }
             destruct H4;
               rewrite H3.
             **** pose proof (dr2Q_incr _ _ H4).
                 cut (Q2R (dr2Q alpha) <= Q2R (dr2Q beta)); auto with real.
                 apply Qle_Rle.
                 auto with qarith.
             **** cut (Q2R (dr2Q alpha) <= Q2R (dr2Q beta)); auto with real.
                  apply Qle_Rle.
                  pose proof (dr2Q_wd _ _ H4).
                  auto with zarith qarith.
         *** destruct H2.
             destruct a.
             auto with real rorders.
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
intros.
destruct H.
destruct (H3 F G H0 H1 H2) as [U [V [? [? [? [? ?]]]]]].
assert (Included (closure U) (Complement G)).
{ assert (Included (closure U) (Complement V)).
  { apply closure_minimal.
    - red. now rewrite Complement_Complement.
    - red. intros.
      intro.
      eapply Noone_in_empty.
      rewrite <- H8.
      econstructor;
        eassumption. }
  assert (Included (Complement V) (Complement G)).
  { red. intros.
    intro.
    contradiction H10.
    now apply H7. }
  auto with sets. }
assert (inhabited (forall F U:Ensemble X, closed F ->
  open U -> Included F U ->
  { V:Ensemble X | open V /\ Included F V /\
                               Included (closure V) U })).
{ destruct (choice (fun (FU_pair:
    {p:Ensemble X * Ensemble X |
     closed (fst p) /\ open (snd p) /\ Included (fst p) (snd p)})
    (V0:Ensemble X) =>
     open V0 /\ Included (fst (proj1_sig FU_pair)) V0 /\
     Included (closure V0) (snd (proj1_sig FU_pair)))) as
    [pre_choice_fun].
  - intro p.
    destruct p as [[F0 U0]].
    simpl in a.
    simpl.
    destruct a as [? []].
    destruct (H3 F0 (Complement U0)) as [U1 [V1 []]]; trivial.
    + red. now rewrite Complement_Complement.
    + extensionality_ensembles_inv.
      contradiction H15.
      now apply H12.
    + destruct H14 as [? [? []]].
      exists U1.
      repeat split; trivial.
      assert (Included (closure U1) (Complement V1)).
      { apply closure_minimal.
        - red. now rewrite Complement_Complement.
        - red. intros.
          intro.
          eapply Noone_in_empty.
          rewrite <- H17.
          constructor;
            eassumption. }
      assert (Included (Complement V1) U0).
      { red. intros.
        apply NNPP. intro.
        contradiction H19.
        now apply H16. }
      auto with sets.
  - exists.
    intros.
    exists (pre_choice_fun (exist _ (F0,U0)
      (conj H11 (conj H12 H13)))).
    apply H10. }
destruct H10 as [normal_sep_fun].
exists (Urysohns_Lemma_function _ normal_sep_fun
  U (Complement G) H4 H1 H9).
split.
{ apply Urysohns_Lemma_function_continuous. }
split.
{ apply Urysohns_Lemma_function_range. }
split;
  intros.
- apply Urysohns_Lemma_function_0; auto.
- apply Urysohns_Lemma_function_1; auto.
Qed.

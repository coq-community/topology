(* Formalize the standard topologies of the ℝ^n spaces. *)

(* Every closed interval admits a uniform (probability) distribution.
   Does S^1 admit a uniform probability distribution?
   Does every compact manifold (or topological-space (maybe Hausdorff is necessary)) admit a uniform probability distribution?
*)

Require Import FunctionalExtensionality.
Require Import RTopology RFuncContinuity.
Require Import ProductTopology.
Require Import Ensembles.
Require Import Compactness.
Require Import Psatz.

Definition Rinfty : TopologicalSpace :=
  ProductTopology (fun n : nat => RTop).

Definition Rinfty_add (p0 p1 : Rinfty) : Rinfty :=
  fun n => p0 n + p1 n.

Arguments Rinfty_add p0 p1 /.

Lemma Rinfty_fst_proj_cts {X : TopologicalSpace} n :
  continuous (fun p : ProductTopology2 Rinfty X => fst p n).
Proof.
  replace (fun p : ProductTopology2 Rinfty Rinfty => fst p n) with
    (compose (fun p => p n) (@fst Rinfty Rinfty)).
  2: {
    unfold compose.
    reflexivity.
  }
  apply (@continuous_composition
           (ProductTopology2 Rinfty X) _ _ (fun p : Rinfty => p n) fst).
  2: apply product2_fst_continuous.
  apply (product_space_proj_continuous nat (fun _ => RTop) n).
Qed.

Lemma Rinfty_snd_proj_cts {X : TopologicalSpace} n :
  continuous (fun p : ProductTopology2 X Rinfty => snd p n).
Proof.
  replace (fun p : ProductTopology2 Rinfty Rinfty => snd p n) with
    (compose (fun p => p n) (@snd Rinfty Rinfty)).
  2: {
    unfold compose.
    reflexivity.
  }
  apply (@continuous_composition
           (ProductTopology2 X Rinfty) _ _ (fun p : Rinfty => p n) snd).
  2: apply product2_snd_continuous.
  apply (product_space_proj_continuous nat (fun _ => RTop) n).
Qed.

Lemma Rinfty_add_cts : continuous_2arg Rinfty_add.
Proof.
  apply weak_topology_continuous_char.
  intros.
  unfold compose, product_space_proj.
  unfold Rinfty_add.
  apply continuous_composition_2arg.
  3: apply Rplus_continuous.
  - apply Rinfty_fst_proj_cts.
  - apply Rinfty_snd_proj_cts.
Qed.

Lemma Rinfty_add_assoc x y z :
  Rinfty_add x (Rinfty_add y z) = Rinfty_add (Rinfty_add x y) z.
Proof.
  apply functional_extensionality_dep.
  intros.
  simpl.
  lra.
Qed.

Lemma Rinfty_add_comm x y :
  Rinfty_add x y = Rinfty_add y x.
Proof.
  apply functional_extensionality_dep.
  intros.
  simpl.
  lra.
Qed.

Definition Rinfty_scale (r : RTop) (p : Rinfty) : Rinfty :=
  fun n => r * p n.

Arguments Rinfty_scale r p /.

Program Definition DiscreteTopology (X : Type) : TopologicalSpace :=
  {| point_set := X;
     open := Full_set;
  |}.
Next Obligation.
  constructor.
Qed.
Next Obligation.
  constructor.
Qed.
Next Obligation.
  constructor.
Qed.

Lemma Rinfty_scale_cts : continuous_2arg Rinfty_scale.
Proof.
  apply weak_topology_continuous_char.
  intros.
  unfold compose, product_space_proj.
  unfold Rinfty_scale.
  apply continuous_composition_2arg.
  { apply product2_fst_continuous. }
  2: apply Rmult_continuous.
  apply Rinfty_snd_proj_cts.
Qed.

Definition Rinfty_zero : Rinfty := fun n => 0.
Arguments Rinfty_zero a /.

Definition Rinfty_subspace (U : Ensemble Rinfty) : Prop :=
  Inhabited U /\
  forall r0 r1 p0 p1,
    In U p0 -> In U p1 ->
    In U (Rinfty_add (Rinfty_scale r0 p0) (Rinfty_scale r1 p1)).

Lemma Rinfty_scale_distr r0 r1 p :
  Rinfty_add (Rinfty_scale r0 p) (Rinfty_scale r1 p) =
    Rinfty_scale (r0 + r1) p.
Proof.
  apply functional_extensionality_dep.
  intros. simpl.
  lra.
Qed.

Lemma Rinfty_scale_0_l p :
  Rinfty_scale 0 p = Rinfty_zero.
Proof.
  apply functional_extensionality_dep.
  intros. simpl.
  lra.
Qed.

Lemma Rinfty_subspace_zero U :
  Rinfty_subspace U ->
  In U Rinfty_zero.
Proof.
  intros [[p]].
  specialize (H0 1 (-1) p p).
  intuition.
  rewrite Rinfty_scale_distr in H0.
  rewrite Rplus_opp_r in H0.
  rewrite Rinfty_scale_0_l in H0.
  assumption.
Qed.

Definition Rn_ens (n : nat) : Ensemble Rinfty :=
  fun p =>
    forall m, (n <= m)%nat -> p m = 0.

Lemma Rn_ens_subspace n :
  Rinfty_subspace (Rn_ens n).
Proof.
  split.
  { exists Rinfty_zero.
    do 2 red. intros.
    reflexivity.
  }
  intros ? ? ? ?. intros. intros ?. intros.
  simpl.
  rewrite (H m H1).
  rewrite (H0 m H1).
  lra.
Qed.

Require Import List.
Import ListNotations.

Import EnsemblesImplicit.

Definition Rinfty_linear_combination (l : list (R * Rinfty)) : Rinfty :=
  fold_right Rinfty_add Rinfty_zero
             (map (fun pp => Rinfty_scale (fst pp) (snd pp)) l).
Arguments Rinfty_linear_combination l /.

Definition Rinfty_span (U : Ensemble Rinfty) : Ensemble Rinfty :=
  Im (fun l => Forall (In U) (map snd l)) Rinfty_linear_combination.

Lemma Rinfty_linear_combination_scale r l :
  Rinfty_scale r (Rinfty_linear_combination l) =
  Rinfty_linear_combination (map (fun pp => (r * (fst pp), snd pp)) l).
Proof.
  induction l.
  { simpl.
    apply functional_extensionality_dep.
    intros. simpl.
    lra.
  }
  apply functional_extensionality_dep.
  intros ?.
  simpl.
  rewrite !Rmult_plus_distr_l.
  rewrite <- Rmult_assoc.
  apply f_equal.
  simpl in IHl.
  rewrite <- IHl.
  reflexivity.
Qed.

Lemma Rinfty_linear_combination_add l0 l1 :
  Rinfty_add (Rinfty_linear_combination l0)
             (Rinfty_linear_combination l1) =
  Rinfty_linear_combination (l0 ++ l1).
Proof.
  generalize dependent l1.
  induction l0.
  - intros.
    apply functional_extensionality_dep.
    intros. simpl.
    lra.
  - intros.
    simpl in *.
    apply functional_extensionality_dep.
    intros.
    rewrite Rplus_assoc.
    apply f_equal.
    rewrite <- IHl0.
    reflexivity.
Qed.

Lemma Rinfty_span_subspace U :
  Rinfty_subspace (Rinfty_span U).
Proof.
  split.
  { exists Rinfty_zero.
    unfold Rinfty_span.
    exists []; try auto.
    constructor.
  }
  red; intros.
  inversion H; subst; clear H.
  inversion H0; subst; clear H0.
  rewrite !Rinfty_linear_combination_scale.
  rewrite Rinfty_linear_combination_add.
  apply Im_def.
  red.
  rewrite map_app.
  rewrite !map_map.
  apply Forall_app.
  red in H1.
  red in H.
  split.
  - apply H1.
  - apply H.
Qed.

Definition Rinfty_linearly_independent (U : Ensemble Rinfty) : Prop :=
  forall l,
    Forall (In U) (map snd l) ->
    NoDup (map snd l) ->
    Rinfty_linear_combination l = Rinfty_zero ->
    Forall (fun i => i = 0) (map fst l).

Lemma Rinfty_linearly_independent_subset U V :
  Included U V ->
  Rinfty_linearly_independent V ->
  Rinfty_linearly_independent U.
Proof.
  intros.
  red.
  intros.
  apply H0; try assumption.
  apply Forall_impl with (P := In U);
    assumption.
Qed.

Definition Rinfty_subspace_basis V B :=
  Rinfty_span B = V /\ Rinfty_linearly_independent B.

Definition Rinfty_unit_vector (n : nat) : Rinfty :=
  fun i => if Nat.eq_dec n i then 1 else 0.

Lemma Rinfty_linear_combination_cons_scale_zero p l :
  fst p = 0 ->
  Rinfty_linear_combination (p :: l) =
  Rinfty_linear_combination l.
Proof.
  intros.
  simpl in *.
  apply functional_extensionality_dep.
  intros.
  rewrite H.
  lra.
Qed.

Import DecidableDec.

Fixpoint Rinfty_linear_combination_extend (l : list (R * Rinfty)) (r : R) (v : Rinfty) :=
  match l with
  | [] => [(r, v)]
  | (r0, v0) :: l0 =>
      if classic_dec (v = v0) then
        (r + r0, v) :: l0
      else
        (r0, v0) :: Rinfty_linear_combination_extend l0 r v
  end.

Fixpoint Rinfty_linear_combination_nodup (l : list (R * Rinfty)) :=
  match l with
  | [] => []
  | (r, v) :: l0 =>
      let l1 := Rinfty_linear_combination_nodup l0 in
      Rinfty_linear_combination_extend l1 r v
  end.

Lemma Rinfty_linear_combination_extend_map_snd_In l r v p :
  List.In p (map snd (Rinfty_linear_combination_extend l r v)) <->
    p = v \/ List.In p (map snd l).
Proof.
  induction l.
  { simpl.
    firstorder.
  }
  simpl. destruct a.
  simpl.
  destruct (classic_dec _).
  { subst. simpl.
    split; intros [|].
    + subst. tauto.
    + tauto.
    + subst. tauto.
    + destruct H.
      * tauto.
      * tauto.
  }
  simpl. rewrite IHl.
  tauto.
Qed.

Lemma Rinfty_linear_combination_extend_correct0 l r v :
  NoDup (map snd l) ->
  NoDup (map snd (Rinfty_linear_combination_extend l r v)).
Proof.
  intros.
  induction l.
  { simpl.
    repeat constructor.
    intuition.
  }
  simpl in H.
  inversion H; subst; clear H.
  specialize (IHl H3).
  simpl. destruct a.
  destruct (classic_dec _).
  - subst.
    simpl in *.
    constructor; assumption.
  - simpl in *.
    constructor; try assumption.
    intros ?.
    rewrite Rinfty_linear_combination_extend_map_snd_In in H.
    destruct H; auto.
Qed.

Lemma Rinfty_linear_combination_cons l r v :
  Rinfty_linear_combination ((r, v) :: l) =
    Rinfty_add (Rinfty_scale r v)
               (Rinfty_linear_combination l).
Proof.
  simpl.
  reflexivity.
Qed.

Lemma Rinfty_linear_combination_extend_correct1 l r v :
  Rinfty_linear_combination
    (Rinfty_linear_combination_extend l r v) =
    Rinfty_add (Rinfty_linear_combination l)
               (Rinfty_scale r v).
Proof.
  induction l.
  { simpl.
    apply functional_extensionality_dep.
    intros. lra.
  }
  unfold Rinfty_linear_combination_extend.
  fold Rinfty_linear_combination_extend.
  destruct a.
  destruct (classic_dec _).
  - subst. clear.
    simpl.
    apply functional_extensionality_dep.
    intros.
    lra.
  - rewrite !Rinfty_linear_combination_cons.
    rewrite IHl.
    rewrite Rinfty_add_assoc.
    reflexivity.
Qed.

Lemma Rinfty_linear_combination_nodup_correct l :
    NoDup (map snd (Rinfty_linear_combination_nodup l)) /\
    Rinfty_linear_combination (Rinfty_linear_combination_nodup l) = Rinfty_linear_combination l.
Proof.
  induction l.
  { simpl.
    repeat constructor.
  }
  destruct IHl.
  split.
  - simpl. destruct a.
    apply Rinfty_linear_combination_extend_correct0.
    assumption.
  - destruct a.
    rewrite Rinfty_linear_combination_cons.
    simpl Rinfty_linear_combination_nodup.
    rewrite Rinfty_linear_combination_extend_correct1.
    rewrite Rinfty_add_comm.
    rewrite H0. reflexivity.
Qed.

Lemma Rinfty_unit_vectors_lin_indep_lemma n l :
  Forall (In (Im Full_set Rinfty_unit_vector)) (map snd l) ->
  ~ List.In (Rinfty_unit_vector n) (map snd l) ->
  Rinfty_linear_combination l n = 0.
Proof.
  intros.
  induction l.
  { reflexivity. }
  destruct a.
  rewrite Rinfty_linear_combination_cons.
  unfold Rinfty_add.
  simpl in H. inversion H; subst; clear H.
  inversion H3; subst; clear H3. clear H.
  specialize (IHl H4).
  simpl in H0.
  rewrite IHl.
  - rewrite Rplus_0_r.
    simpl. unfold Rinfty_unit_vector.
    destruct (Nat.eq_dec _ _); try lra.
    subst. exfalso.
    apply H0.
    left. reflexivity.
  - intros ?.
    apply H0. right.
    assumption.
Qed.

Lemma Rinfty_unit_vectors_lin_indep :
  Rinfty_linearly_independent
    (Im Full_set Rinfty_unit_vector).
Proof.
  red. intros.
  induction l.
  { constructor.
  }
  inversion H; subst; clear H.
  inversion H4; subst; clear H4.
  rename x into n. clear H.
  assert (Rinfty_linear_combination (a :: l) n = fst a).
  { simpl. rewrite H2.
    unfold Rinfty_unit_vector.
    destruct (Nat.eq_dec _ _); try contradiction.
    clear e.
    simpl in H0.
    inversion H0; subst; clear H0.
    destruct a as [r a].
    simpl in H2, H4.
    subst. simpl.
    rewrite Rmult_1_r.
    apply Rinfty_unit_vectors_lin_indep_lemma in H4;
      try assumption.
    simpl in H4.
    rewrite H4.
    lra.
  }
  simpl.
  rewrite H1 in H.
  simpl in H.
  destruct a; simpl in H, H2; subst.
  constructor.
  { reflexivity. }
  rewrite Rinfty_linear_combination_cons_scale_zero in H1.
  2: reflexivity.
  inversion H0; subst; clear H0.
  apply IHl; assumption.
Qed.

Lemma Rinfty_scale_r p :
  Rinfty_scale 1 p = p.
Proof.
  apply functional_extensionality_dep.
  intros. simpl. lra.
Qed.

Lemma Rinfty_span_in_subspace U l :
  Rinfty_subspace U ->
  Forall (In U) (map snd l) ->
  In U (Rinfty_linear_combination l).
Proof.
  intros.
  induction l.
  { simpl.
    apply Rinfty_subspace_zero.
    assumption.
  }
  simpl in H0.
  inversion H0; subst; clear H0.
  specialize (IHl H4).
  destruct a.
  rewrite Rinfty_linear_combination_cons.
  simpl in H3.
  rewrite <- (Rinfty_scale_r (Rinfty_linear_combination _)).
  apply H; assumption.
Qed.

(* This is like [seq 0 n], but it calculates in a different order,
   very inefficient. The benefit is, that proofs with induction in [n]
   are a bit easier to carry out. *)
Fixpoint seqr (n : nat) : list nat :=
  match n with
  | O => []
  | S n => (seqr n) ++ [n]
  end.
Lemma seqr_spec (n : nat) : seqr n = seq 0 n.
Proof.
  induction n.
  { reflexivity. }
  simpl.
  rewrite IHn.
  simpl.
  rewrite cons_seq.
  rewrite seq_S.
  reflexivity.
Qed.

(* The "linear combination" is the important part here. *)
Definition Rn_projection (n : nat) (p : Rinfty) : Rinfty :=
  Rinfty_linear_combination (@map nat (R * Rinfty) (fun i => (p i, Rinfty_unit_vector i)) (seqr n)).

Lemma Rinfty_unit_vector_inj n m :
  Rinfty_unit_vector n = Rinfty_unit_vector m ->
  n = m.
Proof.
  intros.
  assert (Rinfty_unit_vector n n = 1).
  { unfold Rinfty_unit_vector.
    destruct (Nat.eq_dec _ _); congruence.
  }
  rewrite H in H0.
  unfold Rinfty_unit_vector in H0.
  destruct (Nat.eq_dec _ _); try congruence.
  lra.
Qed.

Lemma Rn_projection_recursion n p :
  Rn_projection (S n) p =
    Rinfty_add (Rn_projection n p)
               (Rinfty_scale (p n) (Rinfty_unit_vector n)).
Proof.
  apply functional_extensionality_dep.
  intros.
  unfold Rn_projection at 1.
  simpl seqr.
  rewrite map_app.
  rewrite <- Rinfty_linear_combination_add.
  simpl Rinfty_linear_combination at 2.
  unfold Rinfty_add.
  unfold Rinfty_scale.
  apply f_equal.
  lra.
Qed.

Lemma Rn_projection_subspace n p :
  In (Rn_ens n) (Rn_projection n p).
Proof.
  induction n; do 2 red; intros.
  { unfold Rn_projection.
    simpl. reflexivity.
  }
  rewrite Rn_projection_recursion.
  simpl.
  rewrite IHn; try lia.
  unfold Rinfty_unit_vector.
  destruct (Nat.eq_dec _ _); try lia; try lra.
Qed.

Lemma Rn_projection_projects_lemma n p x :
  (x < n)%nat ->
  Rn_projection n p x = p x.
Proof.
  intros.
  revert p x H.
  induction n.
  { lia. }
  intros.
  rewrite Rn_projection_recursion.
  red in H.
  inversion H; subst; clear H.
  { simpl.
    rewrite Rn_projection_subspace; try lia.
    unfold Rinfty_unit_vector.
    destruct (Nat.eq_dec _ _); try lia; try lra.
  }
  simpl.
  rewrite IHn; try lia.
  unfold Rinfty_unit_vector.
  destruct (Nat.eq_dec _ _); try lia; try lra.
Qed.

Lemma Rn_projection_projects n p :
  In (Rn_ens n) p ->
  Rn_projection n p = p.
Proof.
  revert p.
  intros.
  apply functional_extensionality_dep.
  intros.
  destruct (le_dec n x).
  { rewrite Rn_projection_subspace; try lia.
    unfold Rinfty_unit_vector.
    rewrite H; auto.
  }
  apply not_le in n0.
  unfold Rinfty_unit_vector.
  apply Rn_projection_projects_lemma.
  lia.
Qed.

Corollary Rn_projection_idempotent n p :
  Rn_projection n (Rn_projection n p) = Rn_projection n p.
Proof.
  apply Rn_projection_projects.
  apply Rn_projection_subspace.
Qed.

Lemma Rn_projection_cts (n : nat) : continuous (Rn_projection n).
Proof.
  induction n.
  { unfold Rn_projection.
    simpl.
    apply continuous_constant.
  }
  replace (Rn_projection (S n)) with
    (fun p => Rinfty_add (Rn_projection n p) (Rinfty_scale (p n) (Rinfty_unit_vector n))).
  2: {
    apply functional_extensionality.
    intros.
    symmetry.
    apply Rn_projection_recursion.
  }
  apply continuous_composition_2arg.
  1: assumption.
  2: apply Rinfty_add_cts.
  apply continuous_composition_2arg.
  2: apply continuous_constant.
  2: apply Rinfty_scale_cts.
  apply (product_space_proj_continuous nat (fun _ => RTop)).
Qed.

Lemma Rinfty_unit_vector_span (n : nat) :
  Rinfty_span (Im (fun m => m < n)%nat Rinfty_unit_vector) = Rn_ens n.
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - destruct H.
    subst.
    apply Rinfty_span_in_subspace.
    { apply Rn_ens_subspace. }
    red in H.
    eapply Forall_impl.
    2: eassumption.
    intros.
    inversion H0; subst; clear H0.
    intros ? ?.
    red in H1.
    unfold Rinfty_unit_vector.
    destruct (Nat.eq_dec x0 m).
    { subst. lia. }
    reflexivity.
  - exists (@map nat (R * Rinfty) (fun i => (x i, Rinfty_unit_vector i)) (seqr n)).
    { red.
      clear H.
      induction n.
      - constructor.
      - simpl.
        rewrite map_app.
        rewrite map_app.
        rewrite Forall_app.
        simpl in *.
        split.
        + eapply Forall_impl; try eassumption.
          intros.
          inversion H; subst; clear H.
          exists x0; auto.
          red. red in H0. lia.
        + constructor.
          2: constructor.
          exists n; try reflexivity.
          red. lia.
    }
    symmetry.
    apply Rn_projection_projects.
    assumption.
Qed.

Lemma Rn_space_std_basis (n : nat) :
  Rinfty_subspace_basis (Rn_ens n) (Im (fun m => m < n)%nat Rinfty_unit_vector).
Proof.
  split.
  - apply Rinfty_unit_vector_span.
  - eapply Rinfty_linearly_independent_subset.
    2: {
      apply Rinfty_unit_vectors_lin_indep.
    }
    intros ? ?.
    red. red in H.
    inversion H; subst; clear H.
    exists x0; auto with sets.
Qed.

(* TODO: Characterize that [Rn_ens n] is homeomorphic to n-fold
   repeated application of product to [RTop].
 *)

(* Takes an argument up to which index the vectors shall be evaluated.
   There is no compatible scalarproduct-structure on the whole of [Rinfty].

   This considers [p0] and [p1] as vectors of [Rn_ens n].
 *)
Definition Rinfty_scalarproduct (n : nat) (p0 p1 : Rinfty) : RTop :=
  fold_left Rplus (map (fun i => p0 i * p1 i) (seqr n)) 0.

Lemma Rinfty_scalarproduct_recursion n p0 p1 :
  Rinfty_scalarproduct (S n) p0 p1 =
    Rinfty_scalarproduct n p0 p1 + (p0 n * p1 n).
Proof.
  unfold Rinfty_scalarproduct.
  simpl.
  rewrite map_app.
  simpl.
  rewrite fold_left_app.
  simpl.
  reflexivity.
Qed.

Lemma Rinfty_scalarproduct_cts (n : nat) : continuous_2arg (Rinfty_scalarproduct n).
Proof.
  induction n.
  { unfold Rinfty_scalarproduct.
    simpl. red.
    apply continuous_constant.
  }
  replace (Rinfty_scalarproduct (S n)) with
    (fun p0 p1 => Rinfty_scalarproduct n p0 p1 + (p0 n * p1 n)).
  2: {
    apply functional_extensionality_dep.
    intros. simpl.
    apply functional_extensionality_dep.
    intros. symmetry.
    apply Rinfty_scalarproduct_recursion.
  }
  apply (@continuous_composition_2arg _ _ RTop).
  1: assumption.
  2: apply Rplus_continuous.
  apply (@continuous_composition_2arg _ _ RTop).
  - apply Rinfty_fst_proj_cts.
  - apply Rinfty_snd_proj_cts.
  - apply Rmult_continuous.
Qed.

Program Definition Rinfty_scalarproduct_self_nonneg (p : Rinfty) (n : nat) : nonnegreal :=
  {| nonneg := Rinfty_scalarproduct n p p; |}.
Next Obligation.
  unfold Rinfty_scalarproduct.
  induction n.
  { simpl. lra. }
  simpl in *.
  rewrite map_app.
  rewrite fold_left_app.
  simpl.
  apply Rplus_le_le_0_compat; try assumption.
  apply Rle_0_sqr.
Qed.

(* This definition and the following theorems up to
   [Rinfty_metrizable] are taken from Munkres, Theorem 20.5 on
   p.125. *)
Program Definition Rinfty_bounded_metric (p q : Rinfty) : R :=
  proj1_sig (sup (Im Full_set (fun n : nat => / (INR (S n))* Rmin (R_metric (p n) (q n)) 1)) _ _).
Next Obligation.
  exists 1. intros ? ?.
  inversion H; subst; clear H.
  rename x0 into n.
  clear H0.
  rewrite <- Rmult_1_r.
  assert (forall n, 0 < INR n + 1) as H.
  { clear n. intros.
    apply Rplus_le_lt_0_compat; try lra.
    apply pos_INR.
  }
  apply Rmult_le_compat.
  - destruct n; try lra.
    apply Rlt_le.
    apply Rinv_0_lt_compat.
    apply H.
  - apply Rmin_glb; try lra.
    apply Rge_le.
    apply metric_nonneg.
    apply R_metric_is_metric.
  - rewrite <- Rinv_1.
    apply Rle_Rinv; try rewrite Rinv_1; try lra.
    + destruct n; auto; lra.
    + destruct n; auto; try lra.
      pose proof (pos_INR (S n)).
      lra.
  - apply Rmin_r.
Qed.
Next Obligation.
  match goal with
  | |- exists _, Im _ ?a _ =>
      exists (a 0%nat)
  end.
  exists 0%nat.
  { constructor. }
  lra.
Qed.

Lemma pos_nat_INR (n : nat) :
  0 < / INR (S n).
Proof.
  apply Rinv_0_lt_compat.
  apply lt_0_INR.
  lia.
Qed.

Lemma Rinfty_bounded_metric_metric :
  metric Rinfty_bounded_metric.
Proof.
  constructor.
  - (* symmetry *)
    intros.
    unfold Rinfty_bounded_metric.
    destruct (sup _ _ _) as [d0].
    destruct (sup _ _ _) as [d1].
    simpl.
    apply (is_lub_u _ d0 d1 i).
    replace (fun n : nat => _) with
      (fun n : nat => / INR (S n) * Rmin (R_metric (y n) (x n)) 1); auto.
    apply functional_extensionality.
    intros.
    rewrite (metric_sym _ R_metric); auto.
    apply R_metric_is_metric.
  - intros. unfold Rinfty_bounded_metric.
    destruct (sup _ _ _) as [d0].
    destruct (sup _ _ _) as [d1].
    destruct (sup _ _ _) as [d2].
    simpl.
    apply i.
    intros w Hw.
    inversion Hw; subst; clear Hw.
    clear H.
    eapply Rle_trans with (r2 :=
                             ((/ INR (S x0) * Rmin (R_metric (x x0) (y x0)) 1) +
                                (/ INR (S x0) * Rmin (R_metric (y x0) (z x0)) 1))).
    + rewrite <- Rmult_plus_distr_l.
      apply Rmult_le_compat_l.
      { clear. pose proof (pos_nat_INR x0).
        auto with real.
      }
      pose proof (triangle_inequality _ _ R_metric_is_metric (x x0) (y x0) (z x0)).
      pose proof (metric_nonneg _ _ R_metric_is_metric (x x0) (y x0)).
      pose proof (metric_nonneg _ _ R_metric_is_metric (y x0) (z x0)).
      pose proof (metric_nonneg _ _ R_metric_is_metric (x x0) (z x0)).
      unfold Rmin.
      repeat destruct (Rle_dec _ _); try lra.
    + apply Rplus_le_compat.
      * apply i0.
        exists x0; auto with sets.
      * apply i1.
        exists x0; auto with sets.
  - (* [d x x = 0] *)
    intros. unfold Rinfty_bounded_metric.
    destruct (sup _ _ _) as [d].
    simpl.
    replace (Im Full_set _) with (Singleton 0) in i.
    2: {
      apply Extensionality_Ensembles; split; red; intros.
      - inversion H; subst; clear H.
        exists 0%nat; try constructor.
        simpl. rewrite Rinv_1.
        rewrite metric_zero.
        2: apply R_metric_is_metric.
        rewrite Rmin_left; lra.
      - inversion H; subst; clear H.
        clear H0. rewrite metric_zero.
        2: apply R_metric_is_metric.
        rewrite Rmin_left; try lra.
        rewrite Rmult_0_r.
        constructor.
    }
    apply (is_lub_u _ d _ i).
    lazy; intuition.
  - intros.
    unfold Rinfty_bounded_metric in H.
    destruct (sup _ _ _) in H.
    simpl in H. subst.
    apply functional_extensionality_dep; intros n.
    apply (metric_strict _ R_metric).
    { apply R_metric_is_metric. }
    assert (/ INR (S n) * Rmin (R_metric (x n) (y n)) 1 = 0).
    { apply Rle_antisym.
      - apply i.
        exists n; try constructor.
      - rewrite Rmult_comm.
        apply Rle_mult_inv_pos.
        2: apply lt_0_INR; lia.
        apply Rmin_glb; try lra.
        apply Rge_le.
        apply metric_nonneg.
        apply R_metric_is_metric.
    }
    apply Rmult_integral in H as [|].
    { exfalso.
      apply Rinv_neq_0_compat in H; auto.
      apply not_0_INR. lia.
    }
    unfold Rmin in H.
    destruct (Rle_dec _ _); try lra.
Qed.

Lemma open_neighborhood_basis_from_subbasis {X : TopologicalSpace}
      (SB : Family X) (x : X) (NB : Family X) :
  subbasis SB ->
  (forall N, In NB N -> open_neighborhood N x) ->
  (* maybe this assumption is a little too weak ... *)
  (forall S, In SB S -> In S x ->
        exists N, In NB N /\ Included N S) ->
  open_neighborhood_basis NB x.
Proof.
  intros.
  constructor; auto.
  intros.
  destruct H2.
  apply subbasis_cover with (SB := SB) (x := x) in H2
      as [A [HA [V [HV0 [HV1 HV2]]]]]; auto.
  destruct HV1 as [? HV1].
  (* it would be nice, if we could
     construct an element of [NB] that is included in
     [IndexedIntersection V]. *)
  admit.
Admitted.

Definition ProductTopology_subbasis_from_subbasis {A : Type}
           {X : A -> TopologicalSpace} (SB : forall a, Family (X a)) :
  Family (ProductTopology X) :=
  IndexedUnion
    (fun a => Im (SB a) (fun U => inverse_image (product_space_proj a) U)).

Lemma ProductTopology_subbasis_from_subbasis_correct {A : Type}
      (X : A -> TopologicalSpace) (SB : forall a, Family (X a)) :
  (forall a, subbasis (SB a)) ->
  subbasis (ProductTopology_subbasis_from_subbasis SB).
Proof.
Admitted.

Lemma sup_Rlt_split (f : nat -> R) HUbound HUnonempty r q N :
  q < r ->
  (forall n : nat, (n >= N)%nat -> f n <= q) ->
  (forall n : nat, (n < N)%nat -> f n < r) ->
  proj1_sig (sup (Im Full_set f) HUbound HUnonempty) < r.
Proof.
  intros.
Admitted.

Lemma Rinfty_bounded_metric_open_ball_open x r :
  open (open_ball Rinfty_bounded_metric x r).
Proof.
  apply open_char_neighborhood.
  destruct (classic (0 < r)).
  2: {
    intros.
    destruct H0.
    unshelve epose proof
             (metric_nonneg _ Rinfty_bounded_metric _ x x0);
      try lra.
    apply Rinfty_bounded_metric_metric.
  }
  intros y Hy.
  destruct Hy.
  pose (eps := if Rle_dec (Rinfty_bounded_metric x y) 0 then
                 r
               else
                 Rmin r (Rinfty_bounded_metric x y)).
  assert (0 < eps) as Heps.
  { unfold eps. destruct (Rle_dec _ _); try lra.
    unfold Rmin.
    destruct (Rle_dec _ _); try lra.
  }
  destruct (archimed_cor1 eps Heps) as [N [HN0 HN1]].
  pose (Vn := fun n : nat =>
              fun z : Rinfty =>
                y n - r < z n < y n + r).
  assert (forall n, open (Vn n)).
  { intros n.
    pose proof (R_interval_open (y n - r) (y n + r)).
    match goal with
    | H : open ?a |- open (Vn n) =>
        replace (Vn n) with
        (inverse_image
           (@product_space_proj nat (fun _ => RTop) n)
           a)
    end.
    { apply (product_space_proj_continuous nat (fun _ => RTop) n).
      apply R_interval_open.
    }
    apply Extensionality_Ensembles; split; red; intros.
    - destruct H2. destruct H2.
      do 2 red. assumption.
    - constructor. constructor.
      do 2 red in H2.
      assumption.
  }
  exists (IndexedIntersection
       (fun p : { n : nat | (n < S N)%nat } => Vn (proj1_sig p))).
  repeat split; try lra.
  { apply open_finite_indexed_intersection.
    * apply InfiniteTypes.finite_nat_initial_segment.
    * intros. apply H1.
  }
  destruct H2.
  unfold Vn in H2.
  unfold In in H2.
  unfold Rinfty_bounded_metric.
  apply sup_Rlt_split with (q := / INR N) (N := N).
  { destruct Rle_dec; try lra.
    - assumption.
    - unfold eps in HN0.
      apply Rlt_le_trans with (r2 := Rmin r (Rinfty_bounded_metric x y)); auto.
      apply Rmin_l.
  }
  - intros.
    (* use basic arithmetic. *)
    admit.
  - intros.
    (* use [H2] *)
    admit.
Admitted.

Lemma Rinfty_bounded_metric_metrizes :
  metrizes Rinfty Rinfty_bounded_metric.
Proof.
  red. intros.
  eapply open_neighborhood_basis_from_subbasis.
  { eapply ProductTopology_subbasis_from_subbasis_correct.
    intros.
    (* It'd simplify the second branch of the proof,
       if we'd choose the subbasis of open intervals here. *)
    apply Build_TopologicalSpace_from_subbasis_subbasis.
  }
  - intros.
    inversion H; subst; clear H.
    split.
    2: {
      do 2 red.
      constructor.
      rewrite metric_zero; try lra.
      apply Rinfty_bounded_metric_metric.
    }
    apply Rinfty_bounded_metric_open_ball_open.
  - intros.
    do 2 red in H.
    destruct H as [n F].
    destruct H. subst.
    destruct H0.
    inversion H; subst; clear H.
    all: destruct H0.
    + exists (open_ball Rinfty_bounded_metric x (/ INR (S n) * (x1 - x n))).
      split.
      * constructor.
        unfold product_space_proj in *.
        admit.
      * intros y Hy.
        destruct Hy as [Hy].
        constructor. constructor.
        unfold product_space_proj in *.
        admit.
    + exists (open_ball Rinfty_bounded_metric x (/ INR (S n) * (x n - x1))).
      split.
      * constructor.
        admit.
      * intros y Hy.
        destruct Hy as [Hy].
        constructor. constructor.
        unfold product_space_proj in *.
        admit.
Admitted.

Theorem Rinfty_metrizable : metrizable Rinfty.
Proof.
  exists Rinfty_bounded_metric.
  - apply Rinfty_bounded_metric_metric.
  - apply Rinfty_bounded_metric_metrizes.
Qed.

Definition Rinfty_euc_norm (n : nat) (p : Rinfty) : R :=
  Rsqrt (Rinfty_scalarproduct_self_nonneg p n).

Lemma Rinfty_euc_norm_positivity (p : Rinfty) (n : nat) :
  0 <= Rinfty_euc_norm n p.
Proof.
  unfold Rinfty_euc_norm.
  apply Rsqrt_positivity.
Qed.

Lemma Rsqr_zero (x : R) :
  Rsqr x = 0 ->
  x = 0.
Proof.
  apply Rsqr_0_uniq.
Qed.

Lemma Rsqrt_zero (x : nonnegreal) :
  nonneg x = 0 ->
  Rsqrt x = 0.
Proof.
  intros.
  unfold Rsqrt.
  destruct (Rsqrt_exists _ _).
  destruct a. induction x. simpl in *. subst.
  apply Rsqr_zero.
  symmetry. assumption.
Qed.

Lemma fold_right_Rplus_nonneg l :
  Forall (fun i => 0 <= i) l ->
  0 <= fold_right Rplus 0 l.
Proof.
  intros.
  induction H.
  - simpl. lra.
  - simpl. lra.
Qed.

Lemma fold_left_Rplus_nonneg_zero l :
  Forall (fun i => 0 <= i) l ->
  fold_left Rplus l 0 = 0 <-> Forall (fun i => i = 0) l.
Proof.
  rewrite fold_symmetric; try solve [intros; lra].
  intros.
  split; intros.
  - induction H.
    { constructor. }
    simpl in *.
    pose proof (fold_right_Rplus_nonneg _ H1).
    constructor.
    + lra.
    + apply IHForall.
      lra.
  - induction H0.
    { reflexivity. }
    simpl in *. subst.
    inversion H; subst; clear H.
    rewrite IHForall; auto.
    lra.
Qed.

Lemma map_Im_Included_impl {A B} l P Q (f : A -> B) :
  Included (Im P f) Q ->
  Forall P l ->
  Forall Q (map f l).
Proof.
  intros.
  induction l.
  { constructor. }
  simpl.
  inversion H0; subst; clear H0.
  constructor.
  - apply H.
    apply Im_def.
    assumption.
  - auto.
Qed.

Lemma map_Im_Included_Full_set {A B} l P (f : A -> B) :
  Included (Im Full_set f) P ->
  Forall P (map f l).
Proof.
  intros.
  apply map_Im_Included_impl with (Full_set);
    try assumption.
  rewrite Forall_forall.
  intros. constructor.
Qed.

Lemma Rinfty_scalarproduct_self_zero n p :
  Rinfty_scalarproduct n p p = 0 <->
  (forall m, (m < n)%nat -> p m = 0).
Proof.
  unfold Rinfty_scalarproduct.
  split.
  - intros.
    assert (Forall (fun i => 0 <= i) (map (fun i => p i * p i) (seqr n))).
    { apply map_Im_Included_Full_set.
      intros ? ?.
      inversion H1; subst; clear H1.
      apply Rle_0_sqr.
    }
    apply fold_left_Rplus_nonneg_zero in H;
      try assumption.
    assert (p m * p m = 0).
    { rewrite Forall_forall in H.
      apply H.
      apply in_map_iff.
      exists m; split; auto.
      rewrite seqr_spec.
      apply in_seq.
      lia.
    }
    apply Rmult_integral in H2.
    destruct H2; assumption.
  - intros; subst.
    induction n.
    { reflexivity. }
    simpl in *.
    rewrite map_app.
    rewrite fold_left_app.
    rewrite IHn.
    2: {
      intros.
      apply H.
      lia.
    }
    clear IHn.
    simpl.
    rewrite H; try lia; try lra.
Qed.

Lemma Rn_scalarproduct_self_zero n p :
  In (Rn_ens n) p ->
  Rinfty_scalarproduct n p p = 0 <->
  p = Rinfty_zero.
Proof.
  intros.
  rewrite Rinfty_scalarproduct_self_zero.
  do 2 red in H.
  split; intros.
  - apply functional_extensionality_dep.
    intros.
    specialize (H x).
    specialize (H0 x).
    destruct (le_gt_dec n x); intuition.
  - subst. reflexivity.
Qed.

Lemma Rinfty_euc_norm_is_zero_eq (p : Rinfty) n :
  Rinfty_euc_norm n p = 0 <->
  forall m, (m < n)%nat -> p m = 0.
Proof.
  rewrite <- Rinfty_scalarproduct_self_zero.
  unfold Rinfty_euc_norm.
  split; intros.
  - pose proof (Rsqrt_Rsqrt (Rinfty_scalarproduct_self_nonneg p n)).
    simpl in *.
    rewrite <- H0.
    rewrite H.
    lra.
  - apply Rsqrt_zero.
    assumption.
Qed.

Lemma Rn_norm_is_zero_eq n p :
  In (Rn_ens n) p ->
  Rinfty_euc_norm n p = 0 <->
  p = Rinfty_zero.
Proof.
  intros.
  rewrite Rinfty_euc_norm_is_zero_eq.
  do 2 red in H.
  split; intros.
  - apply functional_extensionality_dep.
    intros.
    specialize (H x).
    specialize (H0 x).
    destruct (le_gt_dec n x); intuition.
  - subst. reflexivity.
Qed.

Lemma Rinfty_scalarproduct_scale n p0 p1 r :
  Rinfty_scalarproduct n (Rinfty_scale r p0) p1 =
  r * Rinfty_scalarproduct n p0 p1.
Proof.
  unfold Rinfty_scalarproduct.
  induction n.
  { simpl. lra. }
  simpl in *.
  rewrite !map_app.
  rewrite !fold_left_app.
  simpl.
  rewrite IHn.
  lra.
Qed.

Lemma Rinfty_scalarproduct_sym n p0 p1 :
  Rinfty_scalarproduct n p0 p1 =
  Rinfty_scalarproduct n p1 p0.
Proof.
  unfold Rinfty_scalarproduct.
  induction n.
  { simpl. lra. }
  simpl in *.
  rewrite !map_app.
  rewrite !fold_left_app.
  simpl.
  rewrite IHn.
  lra.
Qed.

Lemma Rinfty_scalarproduct_add n p00 p01 p1 :
  Rinfty_scalarproduct n (Rinfty_add p00 p01) p1 =
  Rinfty_scalarproduct n p00 p1 +
  Rinfty_scalarproduct n p01 p1.
Proof.
  unfold Rinfty_scalarproduct.
  simpl.
  induction n.
  { simpl. lra. }
  simpl in *.
  rewrite !map_app.
  rewrite !fold_left_app.
  simpl.
  rewrite IHn.
  lra.
Qed.

Section Rsqrt_mult_Rabs_l.
  Program Let nonneg_mult_square x (y : nonnegreal) : nonnegreal :=
    {| nonneg := x² * y; |}.
  Next Obligation.
    destruct y as [y].
    simpl.
    apply Rmult_le_pos; try assumption.
    apply Rle_0_sqr.
  Qed.

  Lemma Rsqrt_uniq (x : nonnegreal) y :
    y * y = x ->
    0 <= y ->
    Rsqrt x = y.
  Proof.
    intros.
    unfold Rsqrt.
    destruct (Rsqrt_exists _ _).
    destruct a. unfold Rsqr in *.
    destruct (Req_dec x 0).
    { rewrite H3 in *.
      apply Rsqr_zero in H.
      symmetry in H2.
      apply Rsqr_zero in H2.
      congruence.
    }
    assert (0 < y).
    { destruct H0; try assumption.
      subst. lra.
    }
    assert (0 < x0).
    { destruct H1; try assumption.
      subst. lra.
    }
    clear H0 H1.
    assert ((y - x0)*(y + x0) = 0).
    { lra. }
    apply Rmult_integral in H0.
    destruct H0; lra.
  Qed.

  Corollary Rsqrt_proper (x : R) H0 H1 :
    Rsqrt {| nonneg := x; cond_nonneg := H0 |} =
      Rsqrt {| nonneg := x; cond_nonneg := H1 |}.
  Proof.
    unfold Rsqrt at 1.
    destruct (Rsqrt_exists _ _).
    destruct a.
    simpl in *.
    symmetry.
    apply Rsqrt_uniq; try assumption.
    simpl. unfold Rsqr in H2.
    congruence.
  Qed.

  Lemma Rsqrt_mult_Rabs_l x y :
    Rabs x * Rsqrt y = Rsqrt (nonneg_mult_square x y).
  Proof.
    symmetry.
    apply Rsqrt_uniq.
    - simpl.
      rewrite Rmult_assoc.
      rewrite (Rmult_comm (Rsqrt y)).
      rewrite Rmult_assoc.
      rewrite Rsqrt_Rsqrt.
      rewrite <- Rmult_assoc.
      rewrite Rsqr_abs.
      unfold Rsqr.
      reflexivity.
    - apply Rmult_le_pos.
      + apply Rabs_pos.
      + apply Rsqrt_positivity.
  Qed.
End Rsqrt_mult_Rabs_l.

Lemma Rsqrt_bijective x y (H0 : 0 <= x) (H1 : 0 <= y) :
  Rsqrt {| nonneg := x; cond_nonneg := H0 |} = Rsqrt {| nonneg := y; cond_nonneg := H1 |} <->
  x = y.
Proof.
  split.
  - intros.
    pose proof (Rsqrt_Rsqrt ({| nonneg := x; cond_nonneg := H0; |})).
    pose proof (Rsqrt_Rsqrt ({| nonneg := y; cond_nonneg := H1; |})).
    simpl in *.
    rewrite <- H2.
    rewrite H.
    assumption.
  - intros. subst.
    apply Rsqrt_proper.
Qed.

Lemma Rinfty_euc_norm_scale n p r :
  Rinfty_euc_norm n (Rinfty_scale r p) =
  Rabs r * Rinfty_euc_norm n p.
Proof.
  unfold Rinfty_euc_norm.
  rewrite Rsqrt_mult_Rabs_l.
  apply Rsqrt_bijective.
  unfold Rsqr.
  unfold Rinfty_scalarproduct_self_nonneg.
  unfold nonneg.
  rewrite Rmult_assoc.
  rewrite <- Rinfty_scalarproduct_scale.
  rewrite Rinfty_scalarproduct_scale.
  rewrite Rinfty_scalarproduct_sym.
  reflexivity.
Qed.

Lemma Rsqrt_monotonous r0 r1 H0 H1 :
  r0 <= r1 ->
  Rsqrt {| nonneg := r0; cond_nonneg := H0 |} <=
    Rsqrt {| nonneg := r1; cond_nonneg := H1 |}.
Proof.
  unfold Rsqrt.
  destruct Rsqrt_exists.
  destruct Rsqrt_exists.
  destruct a, a0.
  simpl in *. subst.
  intros.
  apply Rsqr_incr_0; try lra.
Qed.

Import RelationClasses.
Instance Rle_transitivity : Transitive Rle.
Proof.
  red; intros.
  eapply Rle_trans; eassumption.
Qed.

(*
Lemma Rsqrt_triang_ineq_helper r0 r1 r2 H0 H1 H2 :
  r0 <= r1 + r2 ->
  Rsqrt {| nonneg := r0; cond_nonneg := H0; |} <=
  Rsqrt {| nonneg := r1; cond_nonneg := H1; |} +
  Rsqrt {| nonneg := r2; cond_nonneg := H2; |}.
Proof.
  intros.
  etransitivity.
  { apply Rsqrt_monotonous; eassumption. }
  
  admit.
Admitted.
*)

Lemma Rinfty_scalarproduct_zero_l n p :
  Rinfty_scalarproduct n Rinfty_zero p = 0.
Proof.
  induction n.
  { reflexivity. }
  rewrite Rinfty_scalarproduct_recursion.
  rewrite IHn.
  unfold Rinfty_zero.
  lra.
Qed.

Corollary Rinfty_scalarproduct_zero_r n p :
  Rinfty_scalarproduct n p Rinfty_zero = 0.
Proof.
  rewrite Rinfty_scalarproduct_sym.
  apply Rinfty_scalarproduct_zero_l.
Qed.

Lemma Rinfty_scalarproduct_pos n p i :
  (i < n)%nat ->
  p i <> 0 ->
  0 < Rinfty_scalarproduct n p p.
Proof.
  intros.
  revert i H H0.
  induction n.
  { lia. }
  intros.
  rewrite Rinfty_scalarproduct_recursion.
  inversion H; subst; clear H.
  - apply Rplus_le_lt_0_compat.
    + apply Rinfty_scalarproduct_self_nonneg.
    + apply Rsqr_pos_lt.
      assumption.
  - destruct n.
    { lia. }
    apply Rplus_lt_le_0_compat.
    + apply IHn with (i := i); try lra; try lia.
    + apply Rle_0_sqr.
Qed.

Lemma Rsqr_Rsqrt p :
  Rsqr (Rsqrt p) = p.
Proof.
  apply Rsqrt_Rsqrt.
Qed.

Lemma Rinfty_scalarproduct_CauchySchwarz_lemma n p0 p1 i :
  (i < n)%nat ->
  p0 i <> 0 ->
  (/ Rsqr (Rinfty_euc_norm n p0)) *
    Rsqr (Rinfty_euc_norm n
                      (Rinfty_add
                         (Rinfty_scale (Rsqr (Rinfty_euc_norm n p0)) p1)
                         (Rinfty_scale (- Rinfty_scalarproduct n p1 p0) p0))) =
    Rsqr (Rinfty_euc_norm n p0) * Rsqr (Rinfty_euc_norm n p1) -
      Rsqr (Rabs (Rinfty_scalarproduct n p1 p0)).
Proof.
  intros.
  unfold Rinfty_euc_norm.
  rewrite !Rsqr_Rsqrt.
  rewrite <- Rsqr_abs.
  unfold Rinfty_scalarproduct_self_nonneg.
  unfold nonneg.
  rewrite !Rinfty_scalarproduct_add.
  rewrite !Rinfty_scalarproduct_scale.
  rewrite Rmult_plus_distr_l.
  rewrite <- Rmult_assoc at 1.
  rewrite Rinv_l.
  2: {
    pose proof (Rinfty_scalarproduct_pos n p0 i H H0).
    lra.
  }
  rewrite Rmult_1_l.
  rewrite !(Rinfty_scalarproduct_sym _ _ (Rinfty_add _ _)).
  rewrite !Rinfty_scalarproduct_add.
  rewrite !Rinfty_scalarproduct_scale.
  unfold Rsqr.
  rewrite (Rinfty_scalarproduct_sym n p1 p0) at 5.
  lra.
Qed.

Lemma Rinfty_scalarproduct_projection_left n m p0 p1 :
  (n <= m)%nat ->
  Rinfty_scalarproduct n p0 p1 =
    Rinfty_scalarproduct n (Rn_projection m p0) p1.
Proof.
  intros.
  induction n; try reflexivity.
  rewrite !Rinfty_scalarproduct_recursion.
  rewrite IHn; try lia.
  apply Rplus_eq_compat_l.
  rewrite !Rn_projection_projects_lemma; try lia.
  reflexivity.
Qed.

Corollary Rinfty_scalarproduct_projection n m o p0 p1 :
  (n <= m)%nat -> (n <= o)%nat ->
  Rinfty_scalarproduct n p0 p1 =
    Rinfty_scalarproduct n (Rn_projection m p0) (Rn_projection o p1).
Proof.
  intros.
  etransitivity.
  { apply (Rinfty_scalarproduct_projection_left n m).
    assumption.
  }
  rewrite Rinfty_scalarproduct_sym.
  rewrite (Rinfty_scalarproduct_sym n (Rn_projection _ _)).
  apply (Rinfty_scalarproduct_projection_left n o).
  assumption.
Qed.

Lemma Rinfty_zero_subspace n p :
  In (Rn_ens n) p ->
  (forall m, (m < n)%nat -> p m = 0) ->
  p = Rinfty_zero.
Proof.
  intros.
  apply functional_extensionality_dep.
  intros.
  do 2 red in H.
  unfold Rinfty_zero.
  destruct (le_gt_dec n x); auto.
Qed.

Lemma Rinfty_scalarproduct_CauchySchwarz n p0 p1 :
  (Rinfty_scalarproduct n p0 p1)² <= Rinfty_scalarproduct n p0 p0 * Rinfty_scalarproduct n p1 p1.
Proof.
  destruct (classic_dec (exists i, (i < n)%nat /\ p0 i <> 0)).
  2: {
    rewrite !(Rinfty_scalarproduct_projection_left n n p0); try lia.
    rewrite (Rinfty_zero_subspace n (Rn_projection _ _)).
    2: {
      apply Rn_projection_subspace.
    }
    2: {
      intros.
      apply NNPP.
      intros ?.
      apply n0.
      exists m. split; try assumption.
      rewrite Rn_projection_projects_lemma in H0; auto.
    }
    rewrite !Rinfty_scalarproduct_zero_l.
    unfold Rsqr.
    lra.
  }
  destruct e as [i [Hi0 Hi1]].
  pose proof (Rinfty_scalarproduct_CauchySchwarz_lemma n p0 p1 i Hi0 Hi1).
  simpl in *.
  unfold Rinfty_euc_norm in *.
  rewrite !Rsqr_Rsqrt in *.
  simpl in *.
  apply Rplus_le_reg_r with (r := - Rsqr (Rinfty_scalarproduct n p0 p1)).
  rewrite Rplus_opp_r.
  rewrite <- Rsqr_abs in H.
  rewrite (Rinfty_scalarproduct_sym n p0 p1).
  unfold Rminus in H.
  rewrite <- H.
  apply Rmult_le_pos.
  - left.
    apply Rinv_0_lt_compat.
    eapply Rinfty_scalarproduct_pos; eauto.
  - apply Rinfty_scalarproduct_self_nonneg.
Qed.

Lemma Rinfty_scalarproduct_add_r n p0 p1 p2 :
  Rinfty_scalarproduct n p0 (Rinfty_add p1 p2) =
    Rinfty_scalarproduct n p0 p1 + Rinfty_scalarproduct n p0 p2.
Proof.
  rewrite Rinfty_scalarproduct_sym.
  rewrite Rinfty_scalarproduct_add.
  rewrite !(Rinfty_scalarproduct_sym _ p0).
  reflexivity.
Qed.

(* A special case of bilinearity. *)
Lemma Rinfty_scalarproduct_add_both n p0 p1 p2 p3 :
  Rinfty_scalarproduct n (Rinfty_add p0 p1) (Rinfty_add p2 p3) =
    Rinfty_scalarproduct n p0 p2 + Rinfty_scalarproduct n p0 p3 +
      Rinfty_scalarproduct n p1 p2 + Rinfty_scalarproduct n p1 p3.
Proof.
  rewrite Rinfty_scalarproduct_add.
  rewrite !Rinfty_scalarproduct_add_r.
  lra.
Qed.

Lemma Rinfty_euc_norm_triang_ineq n p0 p1 :
  Rinfty_euc_norm n (Rinfty_add p0 p1) <=
  Rinfty_euc_norm n p0 + Rinfty_euc_norm n p1.
Proof.
  unfold Rinfty_euc_norm.
  apply Rsqr_incr_0.
  2: apply Rsqrt_positivity.
  2: {
    apply Rplus_le_le_0_compat;
    apply Rsqrt_positivity.
  }
  rewrite Rsqr_plus.
  rewrite !Rsqr_Rsqrt.
  unfold Rinfty_scalarproduct_self_nonneg at 1.
  unfold nonneg at 1.
  rewrite Rinfty_scalarproduct_add_both.
  simpl.
  rewrite !Rplus_assoc.
  apply Rplus_le_compat_l.
  rewrite <- Rplus_assoc.
  rewrite Rplus_comm.
  apply Rplus_le_compat_l.
  rewrite Rinfty_scalarproduct_sym.
  rewrite <- double.
  rewrite Rmult_assoc.
  apply Rmult_le_compat_l.
  1: lra.
  transitivity (Rabs (Rinfty_scalarproduct n p1 p0)).
  { apply Rle_abs.
  }
  apply Rsqr_incr_0.
  2: {
    apply Rabs_pos.
  }
  2: {
    apply Rmult_le_pos;
    apply Rsqrt_positivity.
  }
  rewrite <- Rsqr_abs.
  rewrite Rsqr_mult.
  rewrite !Rsqr_Rsqrt.
  rewrite Rinfty_scalarproduct_sym.
  apply Rinfty_scalarproduct_CauchySchwarz.
Qed.

Definition Rinfty_euc_metric (n : nat) (p0 p1 : Rinfty) : R :=
  Rinfty_euc_norm n (Rinfty_add p0 (Rinfty_scale (-1) p1)).

Lemma Rinfty_euc_metric_sym n p0 p1 :
  Rinfty_euc_metric n p0 p1 = Rinfty_euc_metric n p1 p0.
Proof.
  intros.
  pose proof (Rinfty_euc_norm_scale n (Rinfty_add p0 (Rinfty_scale (-1) p1)) (- (1))).
  rewrite Rabs_Ropp in H.
  rewrite Rabs_R1 in *.
  rewrite Rmult_1_l in H.
  unfold Rinfty_euc_metric.
  rewrite <- H.
  clear H.
  match goal with
  | |- Rinfty_euc_norm n ?a = Rinfty_euc_norm n ?b =>
    replace a with b; try reflexivity
  end.
  apply functional_extensionality_dep.
  intros. simpl.
  lra.
Qed.

Lemma Rinfty_euc_metric_triang_ineq n p0 p1 p2 :
  Rinfty_euc_metric n p0 p2 <=
  Rinfty_euc_metric n p0 p1 + Rinfty_euc_metric n p1 p2.
Proof.
  unfold Rinfty_euc_metric.
  replace (Rinfty_add p0 (Rinfty_scale _ p2)) with
      (Rinfty_add (Rinfty_add p0 (Rinfty_scale (-1) p1))
                  (Rinfty_add p1 (Rinfty_scale (-1) p2))).
  2: {
    apply functional_extensionality_dep.
    intros. simpl. lra.
  }
  apply Rinfty_euc_norm_triang_ineq.
Qed.

Lemma Rinfty_euc_metric_zero n p :
  Rinfty_euc_metric n p p = 0.
Proof.
  unfold Rinfty_euc_metric.
  apply Rinfty_euc_norm_is_zero_eq.
  intros. simpl. lra.
Qed.

(* [Rinfty_euc_metric] is a pseudometric, as [Rinfty_euc_norm] is a pseudonorm
   and [Rinfty_scalarproduct] is only semi-definite. *)

Lemma Rinfty_euc_metric_pseudostrict n p0 p1 :
  Rinfty_euc_metric n p0 p1 = 0 ->
  forall m, (m < n)%nat -> p0 m = p1 m.
Proof.
  intros.
  unfold Rinfty_euc_metric in H.
  rewrite Rinfty_euc_norm_is_zero_eq in H.
  specialize (H m H0).
  simpl in *. lra.
Qed.

Definition Rn_space (n : nat) : TopologicalSpace := SubspaceTopology (Rn_ens n).

Definition Rn_metric (n : nat) (p0 p1 : Rn_space n) : R :=
  Rinfty_euc_metric n (proj1_sig p0) (proj1_sig p1).

Theorem Rn_metric_metric (n : nat) : metric (Rn_metric n).
Proof.
  unfold Rn_metric.
  constructor.
  - intros. apply Rinfty_euc_metric_sym.
  - intros.
    apply Rinfty_euc_metric_triang_ineq.
  - intros.
    apply Rinfty_euc_metric_zero.
  - intros.
    destruct x, y.
    Require Import Program.Subset.
    apply subset_eq.
    simpl in *.
    apply functional_extensionality_dep.
    intros m.
    destruct (le_gt_dec n m).
    { rewrite i, i0; auto. }
    apply Rinfty_euc_metric_pseudostrict with (n := n); auto.
Qed.

(* Alternative proof that euclidean balls in ℝ^n are open w.r.t. the product topology:
   Prove that all norms on ℝ^n generate the same topology, then show
   that the ball w.r.t. the maximum norms (open hypercubes) are open in the product topology.
*)
Lemma Rn_metric_metrizes (n : nat) : metrizes (Rn_space n) (Rn_metric n).
Proof.
  admit.
Admitted.

(* Alternative proof: show that [Rinfty] is metrizable, then
   [Rn_space] is metrizable as a subspace. *)
Theorem Rn_metrizable (n : nat) :
  metrizable (Rn_space n).
Proof.
  exists (Rn_metric n).
  - apply Rn_metric_metric.
  - apply Rn_metric_metrizes.
Qed.

Definition metrically_bounded {X} (d : X -> X -> R) (S : Ensemble X) :=
  Inhabited S ->
  exists r x, Included S (open_ball d x r).

(* The Heine-Borel property for metric spaces. *)
Definition HeineBorel (X : TopologicalSpace) (d : X -> X -> R) :=
  forall S : Ensemble X,
    closed S /\ metrically_bounded d S -> compact (SubspaceTopology S).

Lemma net_limit_nbhd_basis
      {X : TopologicalSpace} {I : DirectedSet}
      (x : X) (n : Net I X) (NB : Family X) :
  open_neighborhood_basis NB x ->
  (forall U, In NB U ->
        for large i : DS_set I, In U (n i)) ->
  net_limit n x.
Proof.
  intros ? ? ? ? ?.
  destruct (open_neighborhood_basis_cond NB x H U (conj H1 H2))
           as [V [HV0 HV1]].
  specialize (H0 V HV0) as [i].
  exists i. auto.
Qed.

(* By giving this a name, we can [Search] for it. *)
Corollary metric_topology_neighborhood_basis_correct X d d_metric (x : X) :
  @open_neighborhood_basis
    (MetricTopology d d_metric)
    (metric_topology_neighborhood_basis d x)
    x.
Proof.
  apply Build_TopologicalSpace_from_open_neighborhood_bases_basis.
Qed.

Lemma Rinfty_bounded_metric_complete :
  complete Rinfty_bounded_metric Rinfty_bounded_metric_metric.
Proof.
  red. intros.
  (* Applying countable choice here *)
  Import ChoiceFacts.
  assert (FunctionalCountableChoice_on RTop) as Hc.
  { admit. }
  red in Hc.
  specialize (Hc (fun n r => @net_limit
                            nat_DS
                            (@MetricTopology R R_metric R_metric_is_metric)
                            (fun m : nat => x m n) r)) as [x0].
  - intros.
    pose proof (R_metric_complete (fun m => x m n)).
    apply H0. clear H0.
    red. intros.
    (* maybe [eps] in the following line has to be adapted. *)
    specialize (H eps H0) as [N].
    exists N. intros. specialize (H m n0 H1 H2).
    unfold Rinfty_bounded_metric in H.
    destruct (sup _ _ _).
    simpl in *.
    assert (/ (INR (S n)) * Rmin (R_metric (x m n) (x n0 n)) 1 < x0 + / INR (S n) * / INR (S n)).
    { destruct i.
      clear H4.
      match goal with
      | H : is_upper_bound (Im Full_set ?f) x0 |- _ =>
          unshelve epose proof (H (f n) _); clear H
      end.
      { apply Im_def. constructor. }
      rewrite !S_INR in *.
      simpl in H4. destruct n.
      { simpl. lra. }
      rewrite !S_INR in *.
      apply (Rle_lt_trans _ x0); auto.
      assert (0 < / (INR n + 1 + 1) * / (INR n + 1 + 1)); try lra.
      pose proof (pos_INR n).
      rewrite <- Rinv_mult_distr; try lra.
      apply Rinv_0_lt_compat.
      apply Rmult_lt_0_compat; lra.
    }
    (* this follows by multiplying [H3] on both sides with ... *)
    assert (Rmin (R_metric (x m n) (x n0 n)) 1 < INR (S n) * x0 + / INR (S n)).
    { admit. }
    clear H3.
    (* these need an additional assumption on [N] *)
    assert (R_metric (x m n) (x n0 n) < 1).
    { admit. }
    assert (INR (S n) * x0 + / INR (S n) < eps).
    { admit. }
    unfold Rmin in H4. destruct (Rle_dec _ _); lra.
  - exists x0.
    apply (@net_limit_nbhd_basis
             (@MetricTopology Rinfty _ _) nat_DS
             x0 x (metric_topology_neighborhood_basis
                     Rinfty_bounded_metric x0)).
    { apply metric_topology_neighborhood_basis_correct. }
    intros.
    inversion H1; subst; clear H1.
    unfold In, open_ball.
    simpl DS_set.
    admit.
Admitted.

Lemma Rinfty_bounded_metric_not_HeineBorel :
  ~ HeineBorel Rinfty Rinfty_bounded_metric.
Proof.
  intros ?.
  red in H.
  specialize (H (fun p => Rinfty_bounded_metric Rinfty_zero p <= 1)).
  (* construct a sequence in this set, which doesn't have a converging
     subsequence *)
  admit.
Admitted.

Corollary HeineBorel_not_impl_complete :
  exists X d H,
    metrizes X d /\ complete d H /\ ~ HeineBorel X d.
Proof.
  exists Rinfty, Rinfty_bounded_metric, Rinfty_bounded_metric_metric.
  split; [|split].
  - apply Rinfty_bounded_metric_metrizes.
  - apply Rinfty_bounded_metric_complete.
  - apply Rinfty_bounded_metric_not_HeineBorel.
Qed.

Lemma compact_Subspace (X : TopologicalSpace) (S : Ensemble (point_set X)) :
  compact (SubspaceTopology S) ->
  forall C : Family (point_set X),
    (forall U, In C U -> open U) ->
    FamilyUnion C = Full_set ->
    exists C',
      Finite C' /\ Included C' C /\ Included S (FamilyUnion C').
Proof.
  intros.
  specialize (H (Im C (inverse_image (subspace_inc _)))) as [C'].
  { intros.
    inversion H; subst; clear H.
    apply subspace_open_char.
    exists x. split; auto.
  }
  { apply Extensionality_Ensembles; split; red; intros.
    { constructor. }
    clear H.
    destruct x as [x].
    assert (In (FamilyUnion C) x).
    { rewrite H1. constructor. }
    destruct H.
    exists (inverse_image (subspace_inc S) S0).
    + apply Im_def. assumption.
    + constructor. simpl. assumption.
  }
  destruct H as [? []].
  (* [C'] is a finite cover of [S] using subsets of [S].
     But we actually want a finite cover of [S] using open sets of [X].
     This shall be constructed now.

     Note that [(fun U => In C' (subspace_set_inclusion U))] isn’t the
     right family, because then we lose finiteness.

     How can we do this without choice?
   *)
  admit.
Admitted.

Theorem metric_HeineBorel_converse (X : Type) (d : X -> X -> R) (H : metric d) :
  forall S : Ensemble (point_set (MetricTopology d H)),
    compact (SubspaceTopology S) ->
    closed S /\ metrically_bounded d S.
Proof.
  intros.
  split.
  - apply compact_closed.
    + apply metrizable_Hausdorff.
      exists d.
      * assumption.
      * apply MetricTopology_metrized.
    + assumption.
  - (* Construct the following family of open balls:
       For each x ∈ X include the ball of radius 1 in the family. *)
    pose proof (compact_Subspace _ _ H0).
    pose (C := (fun x : X => open_ball d x 1)).
    specialize (H1 (ImageFamily C)).
    destruct H1 as [C'].
    { intros.
      destruct H1; subst. unfold C.
      apply metric_space_open_ball_open; auto.
      apply MetricTopology_metrized.
    }
    { apply Extensionality_Ensembles; split; red; intros.
      { constructor. }
      clear H1.
      exists (C x).
      * exists x; try reflexivity. constructor.
      * constructor. rewrite metric_zero; try assumption.
        apply Rlt_0_1.
    }
    destruct H1 as [? [? ?]].
    unfold ImageFamily in H2.
    red. intros [x].
    assert (exists r, 0 < r /\
             forall y, In (FamilyUnion C') y ->
                  d x y < r).
    { clear H3 H4.
      induction H1.
      { exists 1. split; try lra; intros.
        destruct H1. contradiction.
      }
      destruct IHFinite as [r0].
      { intros ? ?.
        apply H2. left. assumption.
      }
      assert (In (Im Full_set C) x0).
      { apply H2.
        right. constructor.
      }
      inversion H5; subst; clear H5.
      clear H6.
      destruct H4.
      exists (r0 + (d x x1 + 2)).
      assert (d x x1 >= 0).
      { apply metric_nonneg.
        assumption.
      }
      split; try lra.
      intros. destruct H7.
      destruct H7.
      - unshelve epose proof (H5 x0 _); clear H5.
        { exists x2; auto. }
        lra.
      - inversion H7; subst; clear H7.
        destruct H8.
        assert (d x x1 >= 0).
        { apply metric_nonneg.
          assumption.
        }
        unshelve epose proof (triangle_inequality _ d _ x x1 x0); auto.
        lra.
    }
    destruct H5 as [r []].
    exists r, x.
    intros ? ?.
    apply H3 in H7.
    apply H6 in H7.
    constructor.
    auto.
Qed.

Lemma SingletonSpace_is_metrizable (X : TopologicalSpace) :
  (forall x y : point_set X, x = y) ->
  { d : _ -> _ -> R | metrizes X d /\ metric d }.
Proof.
  intros.
  exists (fun _ _ => 0). split.
  + constructor.
    * intros.
      destruct H0.
      constructor.
      -- replace (open_ball _ _ _) with (@Full_set (point_set X)).
         { apply open_full. }
         apply Extensionality_Ensembles; split; red; intros.
         2: { constructor. }
         clear H1.
         constructor.
         apply Rgt_lt. assumption.
      -- constructor. apply Rgt_lt. assumption.
    * intros.
      exists (open_ball (fun _ _ => 0) x 1). split.
      2: {
        red; intros. rewrite (H x0 x). apply H0.
      }
      constructor.
      apply Rlt_gt. apply Rlt_0_1.
  + constructor.
    * auto.
    * intros. rewrite Rplus_0_r. apply Rle_refl.
    * intros. reflexivity.
    * intros. apply H.
Defined.

(*
Lemma FiniteProduct_HeineBorel (n : nat) (X : Type) (d : X -> X -> R) (H : metric d) :
  metric_HeineBorel_prop X d H ->
  metric_HeineBorel_prop _ (FiniteProduct_metric n X d H) (FiniteProduct_metric_metric n X d H).
Proof.
  intros.
  red. intros.
Admitted.
*)

Theorem Rn_HeineBorel (n : nat) :
  HeineBorel (Rn_space n) (Rn_metric n).
Proof.
Admitted.

Corollary RTop_HeineBorel :
  HeineBorel RTop R_metric.
Proof.
Admitted.

(* Is the HeineBorel-property preserved by finite products? If yes,
then the proof of [HeineBorel] for ℝ^n can be deduced from the proof
of [HeineBorel] for ℝ, which’d make the whole stuff simpler. Depending
on the formalisation, we need to prove that [Rn_space (S n)] is
homeomorphic to [Rn_space n * RTop] first. *)

Definition Sphere (n : nat) : TopologicalSpace :=
  SubspaceTopology (inverse_image (subspace_inc (Rn_ens (S n))) (inverse_image (@Rinfty_euc_norm (S n)) (Singleton 1))).

Lemma Rinfty_euc_norm_cts (n : nat) : continuous (@Rinfty_euc_norm n) (Y := RTop).
Admitted.

Lemma Rn_has_zero (n : nat) :
  In (Rn_ens n) Rinfty_zero.
Proof.
  lazy. reflexivity.
Qed.

Theorem Sphere_compact (n : nat) : compact (Sphere n).
  apply Rn_HeineBorel.
  split.
  - (* closed *)
    apply continuous_closed.
    { apply subspace_inc_continuous. }
    apply (continuous_closed Rinfty RTop).
    + apply Rinfty_euc_norm_cts.
    + apply Hausdorff_impl_T1_sep.
      apply metrizable_Hausdorff.
      apply RTop_metrizable.
  - (* metrically bounded *)
    exists 2, (exist _ Rinfty_zero (Rn_has_zero _)).
    red; intros.
    destruct H. inversion H; subst; clear H.
    simpl. constructor.
    rewrite metric_sym.
    2: { apply Rn_metric_metric. }
    unfold Rn_metric.
    simpl.
    inversion H0; subst; clear H0.
    unfold Rinfty_euc_metric.
    destruct x.
    simpl in *. destruct H. inversion H; subst; clear H.
    replace (Rinfty_euc_norm _ _) with (Rinfty_euc_norm (S n) x).
    { lra. }
    apply f_equal.
    apply functional_extensionality_dep.
    intros. lra.
Qed.

(* TODO: Every S^n is (homeomorphic to) the one-point-compactification of ℝ^n.
*)

(* Claim: Each linear subspace of [Rinfty] is isomorphic to some ℝ^n or to
   [Rinfty] itself. *)

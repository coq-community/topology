(* Show that the CSB-theorem implies excluded-middle.
   Based on https://arxiv.org/abs/1904.09193 by Pierre Pradic and Chad E. Brown.
   Also noteworthy: https://mathoverflow.net/questions/225819/how-strong-is-cantor-bernstein-schr%C3%B6der
*)

From Coq Require Import
  FunctionalExtensionality
  Lia
  PeanoNat
  ProofIrrelevance
  ProofIrrelevanceFacts.
From ZornsLemma Require Import
  FiniteTypes
  FunctionProperties.
From Coq Require Import
  RelationClasses.

(* Definition 6 of the above paper *)
Definition OmniscientT (O : Type) : Prop :=
  forall p : O -> bool,
    (exists o : O, p o = false) \/ (forall o : O, p o = true).

(* This proof doesn't assume any axioms. *)
Example FiniteT_impl_OmniscientT (X : Type) :
  FiniteT X -> OmniscientT X.
Proof.
  intros.
  induction H; red; intros.
  - right. intros. contradiction.
  - specialize (IHFiniteT (fun x => p (Some x))) as [[o]|].
    + left. exists (Some o). assumption.
    + destruct (p None) eqn:?.
      * right. intros. destruct o; auto.
      * left. exists None. assumption.
  - specialize (IHFiniteT (fun x => p (f x))) as [[o]|].
    + left. exists (f o). assumption.
    + right. intros.
      destruct H0 as [g].
      rewrite <- (H2 o).
      apply H1.
Qed.

(* Lemma 7 of the above paper. *)
Lemma omniscient_dec (O A B : Type) (f : O -> A + B) :
  OmniscientT O -> surjective f ->
  inhabited A \/ ~ inhabited A.
Proof.
  intros.
  pose (p := fun x => match f x with inl _ => false | inr _ => true end).
  specialize (H p) as [[o]|].
  - left.
    unfold p in H.
    destruct (f o); auto; discriminate.
  - right. intros [a].
    specialize (H0 (inl a)) as [o].
    specialize (H o). unfold p in H.
    rewrite H0 in H. discriminate.
Qed.

(* The set of non-increasing sequences in [nat -> bool].
A one-point-compactification of the natural numbers. Note the
similarity to the ordinal [omega + 1], but that is probably not
necessary for the proof. *)
Definition N_infty :=
  { p : nat -> bool |
    forall n : nat, p n = true ->
             forall m : nat, m < n -> p m = true }.

(* We need something like functional extensionality on [N_infty] for the proofs to work.
  Actually we also need proof irrelevance. *)
Definition N_equiv (p q : N_infty) :=
  forall n, proj1_sig p n = proj1_sig q n.
Lemma N_infty_extensionality (p q : N_infty) :
  N_equiv p q ->
  p = q.
Proof.
  intros.
  destruct p, q.
  apply subset_eq_compat.
  apply functional_extensionality.
  auto.
Qed.
Global Instance N_equiv_Equivalence : Equivalence N_equiv.
Proof.
  unfold N_equiv.
  split; red; intros.
  - reflexivity.
  - symmetry; auto.
  - transitivity (proj1_sig y n); auto.
Qed.

Program Definition omga : N_infty :=
  exist _ (fun _ => true) _.

Program Definition nat_inj : nat -> N_infty :=
  fun n =>
    exist _ (fun m => m <? n) _.
Next Obligation.
  apply Nat.ltb_lt.
  apply Nat.ltb_lt in H.
  transitivity n0; assumption.
Qed.

Fact nat_inj_inj : injective nat_inj.
Proof.
  red; intros.
  unfold nat_inj in *.
  apply proj1_sig_eq in H.
  simpl in *.
  pose (Hx := (fun m => m <? x) x = (fun m => m <? y) x).
  pose (Hy := (fun m => m <? x) y = (fun m => m <? y) y).
  assert Hx.
  { red. rewrite H. reflexivity. }
  assert Hy.
  { red. rewrite H. reflexivity. }
  simpl in *. red in H0, H1.
  rewrite Nat.ltb_irrefl in *.
  symmetry in H0.
  apply Nat.ltb_ge in H0.
  apply Nat.ltb_ge in H1.
  apply Nat.le_antisymm; assumption.
Qed.

(* The successor function on N_infty. *)
Program Definition S_infty (p : N_infty) : N_infty :=
  exist _
    (fun n =>
       match n with
       | O => true
       | S n' => (proj1_sig p) n'
       end)
    _.
Next Obligation.
  induction H0.
  - induction m.
    + reflexivity.
    + pose (proj2_sig p). simpl in *.
      apply e with _ m in H; auto.
  - induction m.
    + reflexivity.
    + apply (proj2_sig p) with _ m in H; auto.
      rewrite Nat.le_succ_l in H0.
      transitivity (S m); auto.
Qed.

(* Lemma 9 first part. *)
Lemma S_infty_inj' : forall p q,
    N_equiv (S_infty p) (S_infty q) ->
    N_equiv p q.
Proof.
  intros. red; intros.
  assert ((proj1_sig (S_infty p)) (S n) = (proj1_sig (S_infty q)) (S n)).
  { rewrite H. reflexivity. }
  simpl in *.
  assumption.
Qed.

Lemma S_infty_inj : injective S_infty.
Proof.
  red; intros.
  apply N_infty_extensionality.
  apply S_infty_inj'.
  rewrite H.
  reflexivity.
Qed.

(* Lemma 9 second part. *)
Lemma S_infty_nonzero : forall p : N_infty, S_infty p <> (nat_inj 0).
Proof.
  intros.
  intro H.
  assert ((proj1_sig (S_infty p)) 0 = (proj1_sig (nat_inj 0)) 0).
  { rewrite H. reflexivity. }
  simpl in *.
  rewrite Nat.ltb_irrefl in H0.
  discriminate.
Qed.

Lemma N_infty_false_minimal : forall p : N_infty,
    forall n : nat,
      (proj1_sig p) n = false ->
      { n' : nat | (proj1_sig p) n' = false /\
                 forall k, k < n' -> (proj1_sig p) k = true }.
Proof.
  intros.
  induction n.
  - exists 0; intuition.
    inversion H0.
  - destruct (proj1_sig p n) eqn:?.
    + exists (S n); intuition.
      destruct (Nat.eq_dec k n).
      * subst. assumption.
      * apply (proj2_sig p n); auto.
        rewrite Nat.lt_succ_r in H0.
        induction H0; try contradiction.
        rewrite Nat.lt_succ_r. assumption.
    + apply IHn. reflexivity.
Qed.

Lemma N_infty_false_le : forall p : N_infty,
    forall n : nat,
      (proj1_sig p) n = false ->
      forall m : nat,
        n <= m ->
        (proj1_sig p) m = false.
Proof.
  intros.
  destruct (proj1_sig p m) eqn:?; auto.
  exfalso.
  apply (proj2_sig p m) with n in Heqb.
  - rewrite Heqb in H; discriminate.
  - induction H0.
    + rewrite Heqb in H; discriminate.
    + apply Nat.lt_lt_succ_r.
      apply IHle.
      apply (proj2_sig p (S m)); auto.
Qed.

Lemma N_infty_false_eq_nat_inj' : forall p : N_infty,
    forall n : nat,
      (proj1_sig p) n = false ->
      { n' : nat | N_equiv p (nat_inj n') }.
Proof.
  intros.
  destruct (N_infty_false_minimal p n H) as [n' []].
  exists n'.
  red. intros.
  simpl.
  destruct (n0 <? n') eqn:?.
  - apply H1. apply Nat.ltb_lt. assumption.
  - apply N_infty_false_le with n'; auto.
    apply Nat.ltb_ge in Heqb.
    assumption.
Qed.

Lemma N_infty_false_eq_nat_inj : forall p : N_infty,
    forall n : nat,
      (proj1_sig p) n = false ->
      { n' | p = nat_inj n' }.
Proof.
  intros.
  destruct (N_infty_false_eq_nat_inj' _ _ H) as [n'].
  exists n'. auto using N_infty_extensionality.
Qed.

(* Lemma 10. An induction principle for decidable predicates. *)
Lemma N_infty_ind_dec' : forall Q : N_infty -> bool,
    (forall p : N_infty, N_equiv p omga -> Q p = true) ->
    (forall (p : N_infty) (n : nat), N_equiv p (nat_inj n) -> Q p = true) ->
    (forall p : N_infty, Q p = true).
Proof.
  intros.
  destruct (Q p) eqn:?; auto.
  exfalso.
  assert (forall n : nat, (proj1_sig p) n = true).
  { intros.
    destruct (proj1_sig p n) eqn:?; auto.
    exfalso.
    destruct (N_infty_false_eq_nat_inj' _ _ Heqb0) as [n'].
    subst. rewrite H0 with _ n' in Heqb; intuition.
  }
  rewrite H in Heqb; try discriminate.
  red; intros.
  rewrite H1. reflexivity.
Qed.

Lemma N_infty_ind_dec : forall Q : N_infty -> bool,
    (Q omga = true) ->
    (forall n : nat, Q (nat_inj n) = true) ->
    (forall p : N_infty, Q p = true).
Proof.
  intros.
  apply N_infty_ind_dec'; auto; intros.
  - apply N_infty_extensionality in H1.
    rewrite H1. apply H.
  - apply N_infty_extensionality in H1.
    rewrite H1. apply H0.
Qed.

(* Returns true, iff [f k = true] for all [k <= n] *)
Fixpoint nat_bounded_forall (f : nat -> bool) (n : nat) : bool :=
  match n with
  | O => f n
  | S n' => andb (f (S n')) (nat_bounded_forall f n')
  end.

Lemma nat_bounded_forall_lt (f : nat -> bool) (n m : nat) :
  nat_bounded_forall f n = true ->
  m < n ->
  nat_bounded_forall f m = true.
Proof.
  intros.
  induction n.
  { inversion H0. }
  simpl in *.
  apply andb_prop in H.
  intuition.
  inversion H0; subst; auto.
Qed.

Lemma ltb_0_r (n : nat) :
  n <? 0 = false.
Proof.
  induction n; auto.
Qed.

Lemma nat_bounded_forall_char (f : nat -> bool) (n : nat) :
  f n = false ->
  (forall k : nat, k < n -> f k = true) ->
  forall n' : nat,
    nat_bounded_forall f n' = (n' <? n).
Proof.
  intros.
  induction n'.
  - simpl.
    destruct (0 <? n) eqn:?.
    + apply H0.
      apply Nat.ltb_lt.
      assumption.
    + destruct n.
      * assumption.
      * exfalso.
        apply Nat.ltb_ge in Heqb.
        inversion Heqb.
  - simpl in *.
    destruct (S n' <? n) eqn:?.
    + assert (n' <? n = true).
      { rewrite Nat.ltb_lt.
        rewrite Nat.ltb_lt in Heqb.
        apply Nat.lt_succ_l.
        assumption.
      }
      rewrite IHn'.
      rewrite H1 in IHn'.
      rewrite H0; auto.
      apply Nat.ltb_lt. assumption.
    + destruct (n' <? n) eqn:?.
      * rewrite IHn'.
        rewrite Bool.andb_comm; simpl.
        assert (S n' = n).
        { rewrite Nat.ltb_lt in Heqb0.
          rewrite Nat.ltb_ge in Heqb.
          rewrite Nat.le_succ_r in Heqb.
          destruct Heqb; auto.
          apply lt_not_le in Heqb0.
          contradiction.
        }
        rewrite H1. assumption.
      * rewrite IHn'.
        rewrite Bool.andb_comm; simpl; reflexivity.
Qed.

Lemma nat_bounded_forall_true (f : nat -> bool) (n : nat) :
  nat_bounded_forall f n = true ->
  f n = true.
Proof.
  intros.
  induction n.
  - simpl in *. assumption.
  - simpl in *.
    apply andb_prop in H.
    destruct H. assumption.
Qed.

Lemma nat_bounded_forall_char' (f : nat -> bool) (n : nat) :
  nat_bounded_forall f n = false ->
  (forall k : nat, k < n -> nat_bounded_forall f k = true) ->
  forall n' : nat,
    nat_bounded_forall f n' = (n' <? n).
Proof.
  intros.
  induction n.
  - simpl in *.
    apply nat_bounded_forall_char; auto.
    intros. inversion H1.
  - simpl in *.
    rewrite Bool.andb_false_iff in H.
    destruct H.
    + apply nat_bounded_forall_char; auto.
      intros. specialize (H0 _ H1).
      apply nat_bounded_forall_true.
      assumption.
    + intuition.
      destruct (n' <? S n) eqn:?.
      * apply H0. apply Nat.ltb_lt. assumption.
      * assert (forall k, k < n -> nat_bounded_forall f k = true).
        { intros. apply H0. auto. }
        intuition.
        rewrite H3.
        destruct (n' <? n) eqn:?; auto.
        exfalso.
        rewrite Nat.ltb_lt in Heqb0.
        rewrite Nat.ltb_ge in Heqb.
        rewrite Nat.le_succ_l in Heqb.
        apply Nat.lt_asymm in Heqb0.
        contradiction.
Qed.

Lemma nat_bounded_forall_edge_false (f : nat -> bool) (n : nat) :
  nat_bounded_forall f n = false ->
  (forall k, k < n -> nat_bounded_forall f k = true) ->
  f n = false.
Proof.
  intros.
  induction n; simpl in *.
  { assumption. }
  rewrite Bool.andb_false_iff in H.
  destruct H; intuition.
  exfalso.
  specialize (H0 n).
  rewrite H0 in H; intuition.
Qed.

Program Definition N_infty_epsilon (Q : N_infty -> bool) : N_infty :=
  exist
    _ (nat_bounded_forall (fun k => Q (nat_inj k))) _.
Next Obligation.
  apply (nat_bounded_forall_lt _ n); assumption.
Qed.

(* Theorem 11. Note that there's a typo in the paper in the statement
  of the theorem. They wrote [p : N_infty -> bool] instead of [p : N_infty].
*)
Theorem N_infty_epsilon_selection' :
  forall Q : N_infty -> bool,
    (forall p : N_infty, N_equiv (N_infty_epsilon Q) p ->
                         Q p = true) ->
    (forall n p, N_equiv (nat_inj n) p -> Q (nat_inj n) = Q p) ->
    forall p : N_infty, Q p = true.
Proof.
  intros Q ?H.
  assert (forall n, proj1_sig (N_infty_epsilon Q) n = true).
  { intros.
    destruct (proj1_sig (N_infty_epsilon Q) n) eqn:?; auto.
    exfalso.
    destruct (N_infty_false_minimal _ _ Heqb) as [n' [? ?]].
    assert (N_equiv (N_infty_epsilon Q) (nat_inj n')).
    { red. intros. simpl in *.
      apply nat_bounded_forall_char'; auto.
    }
    specialize (H _ H2).
    simpl in *.
    assert (Q (nat_inj n') = false).
    { apply nat_bounded_forall_edge_false in H0; auto. }
    rewrite H in H3.
    discriminate H3.
  }
  assert (N_equiv (N_infty_epsilon Q) omga).
  { auto. }
  intros ?H.
  apply N_infty_ind_dec'.
  { intros. apply H. red; intros.
    rewrite H0. rewrite H3.
    reflexivity.
  }
  intros.
  destruct (Q (nat_inj n)) eqn:?.
  - rewrite <- Heqb. symmetry. apply H2.
    red; intros; symmetry; apply H3.
  - exfalso.
    specialize (H0 n).
    simpl in *.
    apply nat_bounded_forall_true in H0.
    rewrite H0 in Heqb.
    discriminate Heqb.
Qed.

Theorem N_infty_epsilon_selection :
  forall Q : N_infty -> bool,
    Q (N_infty_epsilon Q) = true ->
    forall p : N_infty, Q p = true.
Proof.
  intros Q ?H.
  apply N_infty_epsilon_selection'.
  - intros. apply N_infty_extensionality in H0.
    rewrite H0 in H. assumption.
  - intros.
    apply N_infty_extensionality in H0. subst. reflexivity.
Qed.

(* Corollary 12 *)
Corollary N_infty_omniscient' :
  forall Q : N_infty -> bool,
    (forall p q, N_equiv p q -> Q p = Q q) ->
    (exists p : N_infty, Q p = false) \/ (forall p : N_infty, Q p = true).
Proof.
  intros Q Hproper.
  destruct (Q (N_infty_epsilon Q)) eqn:?.
  - right. apply N_infty_epsilon_selection'.
    + intros ? H. apply Hproper in H. rewrite <- H. assumption.
    + intros ? ? H. apply Hproper in H. assumption.
  - intros. left. exists (N_infty_epsilon Q). assumption.
Qed.

Lemma omniscient_dec' (A B : Type) (f : N_infty -> A + B) :
  (forall p q, N_equiv p q -> f p = f q) ->
  surjective f ->
  inhabited A \/ ~ inhabited A.
Proof.
  intros Hproper.
  pose (p := fun x => match f x with inl _ => false | inr _ => true end).
  destruct (N_infty_omniscient' p).
  - intros.
    unfold p.
    apply Hproper in H. rewrite H. reflexivity.
  - left.
    unfold p in *. destruct H as [o].
    destruct (f o); auto. discriminate.
  - right. intros [a].
    specialize (H0 (inl a)) as [o].
    specialize (H o). unfold p in *.
    rewrite H0 in H. discriminate.
Qed.

Corollary N_infty_omniscient : OmniscientT N_infty.
Proof.
  red; intros Q.
  apply N_infty_omniscient'.
  intros. apply N_infty_extensionality in H. subst. reflexivity.
Qed.

Section CSB_Reverse.
  Variable CSB : forall (X Y : Type) (f : X -> Y) (g : Y -> X),
    injective f -> injective g -> exists h : X -> Y, bijective h.

  (** only depends on [proof_irrelevance] and [functional_extensionality_dep] *)
  Theorem  CSB_impl_LEM : forall P : Prop, P \/ ~P.
  Proof.
    intros.
    pose (A := { x : bool | x = false /\ P }).
    pose (f := fun x : N_infty => @inr A _ x).
    pose (g := fun x : A + N_infty =>
                 match x with
                 | inl _ => nat_inj 0
                 | inr x => S_infty x
                 end).
    specialize (CSB _ _ f g) as [h].
    { (* injective f *)
      red; intros.
      inversion H; auto.
    }
    { (* injective g *)
      red; intros.
      destruct x, y.
      - simpl in *.
        destruct a, a0.
        destruct a, a0.
        subst.
        pose (proof_irrelevance _ p p0).
        subst. reflexivity.
      - simpl in *.
        symmetry in H.
        contradict H.
        apply S_infty_nonzero.
      - simpl in *.
        contradict H.
        apply S_infty_nonzero.
      - simpl in *.
        apply S_infty_inj in H.
        subst. reflexivity.
    }
    destruct H.
    destruct (omniscient_dec _ _ _ h N_infty_omniscient H0).
    - left. destruct H1. destruct H1. destruct a.
      assumption.
    - right. intros ?H.
      contradict H1.
      constructor.
      exists false.
      auto.
  Qed.
End CSB_Reverse.

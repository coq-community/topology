From Coq Require Import Program.Subset.
From Topology Require Export TopologicalSpaces.
From Topology Require Import Completeness MetricSpaces SeparatednessAxioms
                             WeakTopology.

Section Subspace.

Context {X:TopologicalSpace}.
Variable A:Ensemble X.

Definition SubspaceTopology : TopologicalSpace :=
  WeakTopology1 (proj1_sig (P:=fun x:X => In A x)).

Definition subspace_inc :
  SubspaceTopology -> X :=
  proj1_sig (P:=fun x:X => In A x).

Lemma subspace_inc_continuous:
  @continuous SubspaceTopology X (@proj1_sig _ _).
Proof.
apply weak_topology1_makes_continuous_func.
Qed.

Lemma subspace_continuous_char (Y : TopologicalSpace)
      (f : Y -> SubspaceTopology) :
  continuous f <->
  continuous (compose subspace_inc f).
Proof.
  apply weak_topology1_continuous_char.
Qed.

Lemma subspace_open_char: forall U:Ensemble {x: X | In A x},
  @open SubspaceTopology U <-> exists V:Ensemble X,
  open V /\ U = inverse_image subspace_inc V.
Proof.
apply weak_topology1_topology.
Qed.

Lemma subspace_closed_char: forall U:Ensemble {x: X | In A x},
  @closed SubspaceTopology U <-> exists V:Ensemble X,
  closed V /\ U = inverse_image subspace_inc V.
Proof.
apply weak_topology1_topology_closed.
Qed.

Lemma subspace_closure U :
  closure U = inverse_image subspace_inc (closure (Im U subspace_inc)).
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - constructor.
    apply continuous_closure.
    { apply subspace_inc_continuous. }
    apply Im_def.
    assumption.
  - destruct H.
    unfold closure in H.
    constructor. intros.
    destruct H0. destruct H0.
    rewrite subspace_closed_char in H0.
    destruct H0 as [V []].
    subst. constructor.
    destruct H.
    apply H. repeat split; try assumption.
    intros ? ?. inversion H2; subst; clear H2.
    apply H1. assumption.
Qed.

End Subspace.

(* Every set is dense in its closure. *)
Lemma dense_in_closure {X:TopologicalSpace} (A : Ensemble X) :
  dense (inverse_image (subspace_inc (closure A)) A).
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  { constructor. }
  destruct x.
  rewrite subspace_closure.
  constructor. simpl.
  rewrite inverse_image_image_surjective_locally.
  { assumption. }
  intros.
  unshelve eexists (exist _ y _).
  2: { reflexivity. }
  apply closure_inflationary.
  assumption.
Qed.

(* If the subspace [F] is closed in [X], then its [subspace_inc] is a
   closed map. *)
Lemma subspace_inc_takes_closed_to_closed
  (X : TopologicalSpace) (F:Ensemble X) :
  closed F ->
  forall G:Ensemble (SubspaceTopology F),
  closed G -> closed (Im G (subspace_inc F)).
Proof.
intros.
red in H0.
rewrite subspace_open_char in H0.
destruct H0 as [U []].
replace (Im G (subspace_inc F)) with
  (Intersection F (Complement U)).
{ apply closed_intersection2; trivial.
  red. now rewrite Complement_Complement. }
apply Extensionality_Ensembles; split; red; intros.
- destruct H2.
  exists (exist _ x H2); trivial.
  apply NNPP. intro.
  change (In (Complement G) (exist (In F) x H2)) in H4.
  rewrite H1 in H4.
  now destruct H4.
- destruct H2 as [[y]].
  subst y0.
  constructor; trivial.
  intro.
  absurd (In (Complement G) (exist _ y i)).
  + now intro.
  + now rewrite H1.
Qed.

Instance T0_space_hereditary {X:TopologicalSpace} `(T0_space X) (A : Ensemble X) :
  T0_space (SubspaceTopology A).
Proof.
  constructor. intros.
  destruct (T0_sep (proj1_sig x) (proj1_sig y))
           as [[U [? []]]|[U [? []]]].
  { intros ?. apply subset_eq in H1. tauto. }
  - left. exists (inverse_image (subspace_inc A) U).
    repeat split.
    + apply subspace_inc_continuous; assumption.
    + assumption.
    + intros ?. destruct H4. tauto.
  - right. exists (inverse_image (subspace_inc A) U).
    repeat split.
    + apply subspace_inc_continuous; assumption.
    + intros ?. destruct H4. tauto.
    + assumption.
Qed.

Instance T1_space_hereditary {X:TopologicalSpace} `(T1_space X) (A : Ensemble X) :
  T1_space (SubspaceTopology A).
Proof.
  constructor.
  intros.
  rewrite subspace_closed_char.
  exists (Singleton (proj1_sig x)).
  split.
  - apply T1_sep.
  - extensionality_ensembles_inv.
    + constructor. constructor.
    + apply subset_eq in H2 as [].
      constructor.
Qed.

Instance Hausdorff_hereditary {X:TopologicalSpace} `(Hausdorff X) (A : Ensemble X) :
  Hausdorff (SubspaceTopology A).
Proof.
  constructor.
  intros.
  destruct (hausdorff (proj1_sig x) (proj1_sig y))
           as [U [V [? [? [? []]]]]].
  { intros ?. apply subset_eq in H1. tauto. }
  exists (inverse_image (subspace_inc A) U),
    (inverse_image (subspace_inc A) V).
  repeat split.
  - apply subspace_inc_continuous; assumption.
  - apply subspace_inc_continuous; assumption.
  - assumption.
  - assumption.
  - rewrite <- inverse_image_intersection.
    rewrite H5.
    apply inverse_image_empty.
Qed.

Instance T3_space_hereditary {X:TopologicalSpace} `(T3_space X)
         (A : Ensemble X) :
  T3_space (SubspaceTopology A).
Proof.
  split.
  { apply T1_space_hereditary. apply H. }
  intros.
  rewrite subspace_closed_char in H0.
  destruct H0 as [D []].
  subst.
  assert (~ In D (proj1_sig x)).
  { intros ?. apply H1. constructor. assumption. }
  clear H1.
  destruct (T3_sep (proj1_sig x) D)
    as [U [V [? [? [? []]]]]];
    try assumption.
  exists (inverse_image (subspace_inc _) U).
  exists (inverse_image (subspace_inc _) V).
  repeat split.
  - apply subspace_inc_continuous; assumption.
  - apply subspace_inc_continuous; assumption.
  - assumption.
  - destruct H7. apply H5. assumption.
  - rewrite <- inverse_image_intersection.
    rewrite H6. apply inverse_image_empty.
Qed.


(* Side note: only [metric_zero] was important here. As long as [metrizes _ _] holds,
   this proof could go through for non-metrizable spaces.
*)
Lemma metric_restriction_metrizes_subspace {X:TopologicalSpace} (d:X->X->R) A :
  metrizes X d -> metric d ->
  metrizes (SubspaceTopology A) (fun x y => d (proj1_sig x) (proj1_sig y)).
Proof.
  intros.
  constructor.
  - intros. inversion_clear H1.
    split.
    + rewrite subspace_open_char.
      exists (open_ball X d (proj1_sig x) r).
      split.
      { apply metric_space_open_ball_open; assumption. }
      extensionality_ensembles_inv;
        repeat constructor; assumption.
    + constructor.
      rewrite metric_zero; auto.
  - intros.
    destruct H1.
    rewrite subspace_open_char in H1.
    destruct H1 as [U0 []]. subst.
    destruct H2.
    destruct (open_neighborhood_basis_cond
                _ (proj1_sig x) (H (proj1_sig x)) U0)
             as [V0 []].
    { split; assumption. }
    inversion H3; subst; clear H3.
    exists (open_ball _ (fun x y => d (proj1_sig x) (proj1_sig y)) x r).
    repeat split; try assumption.
    apply H4. constructor.
    destruct H3.
    assumption.
Qed.

Instance metrizable_hereditary {X:TopologicalSpace} `(metrizable X) (A : Ensemble X) :
  metrizable (SubspaceTopology A).
Proof.
  destruct H as [d ?Hd ?Hd].
  exists (fun x y => d (proj1_sig x) (proj1_sig y)).
  - apply d_restriction_metric. assumption.
  - apply metric_restriction_metrizes_subspace;
      assumption.
Qed.

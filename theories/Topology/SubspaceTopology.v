Require Export TopologicalSpaces.
Require Import WeakTopology.

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

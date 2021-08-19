Require Export TopologicalSpaces.
Require Import WeakTopology.

Section Subspace.

Variable X:TopologicalSpace.
Variable A:Ensemble (point_set X).

Definition SubspaceTopology : TopologicalSpace :=
  WeakTopology1 (proj1_sig (P:=fun x:point_set X => In A x)).

Definition subspace_inc : point_set SubspaceTopology ->
  point_set X :=
  proj1_sig (P:=fun x:point_set X => In A x).

Lemma subspace_inc_continuous:
  continuous subspace_inc.
Proof.
apply weak_topology1_makes_continuous_func.
Qed.

Lemma subspace_open_char: forall U:Ensemble {x:point_set X | In A x},
  @open SubspaceTopology U <-> exists V:Ensemble (point_set X),
  open V /\ U = inverse_image subspace_inc V.
Proof.
apply weak_topology1_topology.
Qed.

End Subspace.

Arguments SubspaceTopology {X}.
Arguments subspace_inc {X}.

(* If the subspace [F] is closed in [X], then its [subspace_inc] is a
   closed map. *)
Lemma subspace_inc_takes_closed_to_closed
  (X : TopologicalSpace) (F:Ensemble (point_set X)) :
  closed F ->
  forall G:Ensemble (point_set (SubspaceTopology F)),
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

Require Export TopologicalSpaces.
Require Export Subbases.
Require Export Continuity.
Require Export Nets.
From ZornsLemma Require Export InverseImage.
From ZornsLemma Require Import FiniteIntersections.

(* Also called "initial topology". Its construction is dual
   (in the categorical sense) to the construction of the strong topology. *)

Section WeakTopology.

Variable X:Type.
Variable A:Type.
Variable Y:A->TopologicalSpace.
Variable f:forall a:A, X->point_set (Y a).

Inductive weak_topology_subbasis : Family X :=
  | intro_fa_inv_image: forall (a:A) (V:Ensemble (point_set (Y a))),
    open V -> In weak_topology_subbasis (inverse_image (f a) V).

Definition WeakTopology : TopologicalSpace :=
  Build_TopologicalSpace_from_subbasis X weak_topology_subbasis.

Lemma weak_topology_makes_continuous_funcs:
  forall a:A, continuous (f a) (X:=WeakTopology).
Proof.
intro.
red; intros.
pose proof (Build_TopologicalSpace_from_subbasis_subbasis
  _ weak_topology_subbasis).
apply H0.
constructor; trivial.
Qed.

Lemma weak_topology_is_weakest: forall (T':Family X)
  (H1:_) (H2:_) (H3:_),
  (forall a:A, continuous (f a)
     (X := Build_TopologicalSpace X T' H1 H2 H3)) ->
  forall U:Ensemble X, @open WeakTopology U -> T' U.
Proof.
intros.
destruct H0.
apply H1.
intros.
apply H0 in H4.
induction H4.
- exact H3.
- destruct H4.
  apply H; trivial.
- apply H2; trivial.
Qed.

Lemma weak_topology_continuous_char (W : TopologicalSpace)
      (g : (point_set W) -> (point_set (WeakTopology))) :
      continuous g <-> (forall a, continuous (compose (f a) g)).
Proof.
split.
- intros.
  unfold compose. apply continuous_composition.
  + apply weak_topology_makes_continuous_funcs.
  + assumption.
- intros.
  apply continuous_subbasis with weak_topology_subbasis.
  { apply Build_TopologicalSpace_from_subbasis_subbasis. }
  intros. induction H0.
  rewrite <- inverse_image_composition.
  apply H. assumption.
Qed.

Section WeakTopology_and_Nets.

Variable I:DirectedSet.
Hypothesis I_nonempty: inhabited (DS_set I).
Variable x:Net I WeakTopology.
Variable x0:X.

Lemma net_limit_in_weak_topology_impl_net_limit_in_projections :
  net_limit x x0 ->
  forall a:A, net_limit (fun i:DS_set I => (f a) (x i)) ((f a) x0).
Proof.
intros.
apply continuous_func_preserves_net_limits; trivial.
apply continuous_func_continuous_everywhere.
apply weak_topology_makes_continuous_funcs.
Qed.

Lemma net_limit_in_projections_impl_net_limit_in_weak_topology :
  (forall a:A, net_limit (fun i:DS_set I => (f a) (x i))
                         ((f a) x0)) ->
  net_limit x x0.
Proof.
intros.
red; intros.
assert (@open_basis WeakTopology
        (finite_intersections weak_topology_subbasis)).
{ apply Build_TopologicalSpace_from_open_basis_basis. }
destruct (open_basis_cover _ H2 x0 U) as [V [? [? ?]]]; trivial.
assert (for large i:DS_set I, In V (x i)).
{ clear H4.
  induction H3.
  - destruct I_nonempty.
    exists X0; constructor.
  - destruct H3.
    destruct H5.
    apply eventually_impl_base with (fun i:DS_set I => In V (f a (x i))).
    + intros.
      constructor; trivial.
    + apply H; trivial.
  - apply eventually_impl_base with
        (fun i:DS_set I => In U0 (x i) /\ In V (x i)).
    + intros.
      destruct H6.
      constructor; trivial.
    + destruct H5.
      apply eventually_and;
        (apply IHfinite_intersections || apply IHfinite_intersections0);
        trivial.
}
refine (eventually_impl_base _ _ _ H6).
intro; apply H4.
Qed.

End WeakTopology_and_Nets.

End WeakTopology.

Arguments WeakTopology {X} {A} {Y}.
Arguments weak_topology_subbasis {X} {A} {Y}.

Require Import ClassicalChoice.

Section WeakTopology1.

Variable X:Type.
Variable Y:TopologicalSpace.
Variable f:X->point_set Y.

Definition WeakTopology1 := WeakTopology (True_rect f).

Lemma weak_topology1_makes_continuous_func:
  continuous f (X:=WeakTopology1).
Proof.
exact (weak_topology_makes_continuous_funcs _ _ _ (True_rect f) I).
Qed.

Lemma weak_topology1_topology:
  forall U:Ensemble X, @open WeakTopology1 U <->
  exists V:Ensemble (point_set Y), open V /\ U = inverse_image f V.
Proof.
split.
2: {
  intros.
  destruct H as [V []].
  subst.
  apply weak_topology1_makes_continuous_func.
  assumption.
}
intros.
red in H.
simpl in H.
destruct H.
assert (forall U:Ensemble X,
  In (finite_intersections (weak_topology_subbasis (True_rect f))) U ->
  exists V:Ensemble (point_set Y), open V /\ U = inverse_image f V).
{ intros.
  induction H0.
  - exists Full_set.
    split.
    + apply open_full.
    + symmetry. apply inverse_image_full.
  - destruct H0.
    destruct a.
    simpl.
    exists V.
    split; trivial.
  - destruct IHfinite_intersections as [V1 [? ?]].
    destruct IHfinite_intersections0 as [V2 [? ?]].
    exists (Intersection V1 V2).
    split.
    + auto with topology.
    + rewrite H3; rewrite H5.
      rewrite inverse_image_intersection.
      trivial.
}
destruct (choice (fun (U:{U:Ensemble X | In F U}) (V:Ensemble (point_set Y))
  => open V /\ proj1_sig U = inverse_image f V)) as [choice_fun].
{ intros.
  destruct x as [U].
  simpl.
  apply H0; auto with sets.
}
exists (IndexedUnion choice_fun).
split.
{ apply open_indexed_union.
  apply H1.
}
apply Extensionality_Ensembles; split; red; intros.
- destruct H2.
  constructor.
  exists (exist _ S H2).
  pose proof (H1 (exist _ S H2)).
  destruct H4.
  simpl in H5.
  rewrite H5 in H3.
  destruct H3.
  exact H3.
- destruct H2.
  inversion H2.
  pose proof (H1 a).
  destruct H5.
  destruct a as [U].
  exists U; trivial.
  simpl in H6.
  rewrite H6.
  constructor.
  exact H3.
Qed.

Lemma weak_topology1_topology_closed:
  forall U:Ensemble X, @closed WeakTopology1 U <->
  exists V:Ensemble (point_set Y), closed V /\ U = inverse_image f V.
Proof.
unfold closed.
split.
- intros. unfold closed in *.
  rewrite weak_topology1_topology in H.
  destruct H as [V []].
  exists (Complement V).
  rewrite inverse_image_complement.
  rewrite <- H0.
  rewrite !Complement_Complement.
  auto.
- intros. destruct H as [V []].
  subst. apply continuous_closed; try assumption.
  apply weak_topology1_makes_continuous_func.
Qed.

End WeakTopology1.

Arguments WeakTopology1 {X} {Y}.

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
Variable f:forall a:A, X->Y a.

Inductive weak_topology_subbasis : Family X :=
  | intro_fa_inv_image: forall (a:A) (V:Ensemble (Y a)),
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
      (g : W -> WeakTopology) :
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

Section WeakTopology1.

Variable X:Type.
Variable Y:TopologicalSpace.
Variable f:X->Y.

Definition WeakTopology1 := WeakTopology (True_rect f).

Lemma weak_topology1_makes_continuous_func:
  continuous f (X:=WeakTopology1).
Proof.
exact (weak_topology_makes_continuous_funcs _ _ _ (True_rect f) I).
Qed.

Lemma weak_topology1_topology:
  forall U:Ensemble X, @open WeakTopology1 U <->
  exists V:Ensemble Y, open V /\ U = inverse_image f V.
Proof.
split.
2: {
  intros.
  destruct H as [V []].
  subst.
  apply weak_topology1_makes_continuous_func.
  assumption.
}

intros HU.
exists (FamilyUnion
     (fun V : Ensemble Y =>
        open V /\ Included (inverse_image f V) U)).
split.
{ apply open_family_union.
  intros S [HS0 HS1].
  assumption.
}
apply Extensionality_Ensembles; split; red.
- assert (forall U:Ensemble X,
    In (finite_intersections (weak_topology_subbasis (True_rect f))) U ->
    exists V:Ensemble Y, open V /\ U = inverse_image f V).
  { clear U HU.
    intros U HU.
    induction HU.
    - exists Full_set.
      split.
      + apply open_full.
      + symmetry. apply inverse_image_full.
    - destruct H.
      destruct a.
      simpl.
      exists V.
      split; trivial.
    - destruct IHHU as [V1 [? ?]].
      destruct IHHU0 as [V2 [? ?]].
      exists (Intersection V1 V2).
      split.
      + auto with topology.
      + subst.
        symmetry.
        apply inverse_image_intersection.
  }
  intros x HUx.
  constructor.
  destruct HU.
  destruct HUx.
  specialize (H0 S H1).
  specialize (H S H0) as [V []].
  subst. destruct H2.
  exists V; auto.
  split; auto.
  intros y Hy.
  exists (inverse_image f V); auto.
- intros x HVx.
  destruct HVx.
  inversion H; subst; clear H.
  destruct H0.
  apply H0. constructor. assumption.
Qed.

Lemma weak_topology1_topology_closed:
  forall U:Ensemble X, @closed WeakTopology1 U <->
  exists V:Ensemble Y, closed V /\ U = inverse_image f V.
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

Lemma weak_topology1_continuous_char (Z : TopologicalSpace)
      (g : Z -> WeakTopology1) :
  continuous g <->
  continuous (compose f g).
Proof.
  replace f with (True_rect f I).
  2: { reflexivity. }
  unfold WeakTopology1.
  rewrite weak_topology_continuous_char.
  split; intros; auto.
  destruct a. assumption.
Qed.

End WeakTopology1.

Arguments WeakTopology1 {X} {Y}.

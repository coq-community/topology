From ZornsLemma Require Import Powerset_facts.
From ZornsLemma Require Export Filters.
From Topology Require Export TopologicalSpaces Neighborhoods Continuity.

Program Definition neighborhood_filter {X:TopologicalSpace} (x0:point_set X) :
  Filter X :=
  {| filter_family := [N : _ | neighborhood N x0 ] |}.
Next Obligation.
intros.
destruct H as [[U [[]]]], H0 as [[V [[]]]].
constructor.
exists (Intersection U V); split.
- constructor; auto with topology sets.
- red; intros. destruct H5; constructor; auto.
Qed.
Next Obligation.
intros.
destruct H as [[U [[]]]].
red. constructor.
exists U; repeat split; trivial.
auto with sets.
Qed.
Next Obligation.
constructor.
exists Full_set; repeat split; auto with sets topology.
Qed.
Next Obligation.
red; intro.
destruct H as [[U [[]]]].
apply H1 in H0.
destruct H0.
Qed.

Definition filter_limit {X:TopologicalSpace} (F:Filter X)
  (x0:point_set X) : Prop :=
  Included (filter_family (neighborhood_filter x0))
           (filter_family F).

Definition filter_cluster_point {X:TopologicalSpace}
  (F:Filter X) (x0:point_set X) : Prop :=
  forall S:Ensemble X, In (filter_family F) S ->
  In (closure S) x0.

Lemma filter_limit_is_cluster_point:
  forall {X:TopologicalSpace} (F:Filter X) (x0:point_set X),
  filter_limit F x0 -> filter_cluster_point F x0.
Proof.
intros.
red; intros.
apply meets_every_open_neighborhood_impl_closure.
intros.
assert (In (filter_family F) U).
{ apply H.
  simpl.
  constructor.
  exists U; repeat split; auto with sets.
}
assert (In (filter_family F) (Intersection S U)).
{ apply filter_intersection; trivial. }
apply NNPP; red; intro.
assert (Intersection S U = Empty_set).
{ apply Extensionality_Ensembles; split; red; intros.
  - contradiction H5.
    exists x; trivial.
  - destruct H6.
}
rewrite H6 in H4.
contradiction (filter_empty _ F).
Qed.

Lemma ultrafilter_cluster_point_is_limit: forall {X:TopologicalSpace}
  (F:Filter X) (x0:point_set X),
  filter_cluster_point F x0 -> ultrafilter F ->
  filter_limit F x0.
Proof.
intros.
red.
red; intros N ?.
destruct H1.
destruct H1 as [U [[]]].
cut (In (filter_family F) U).
{ intros; apply filter_upward_closed with U; trivial. }
clear N H3.
apply NNPP; intro.
assert (In (filter_family F) (Complement U)).
{ pose proof (H0 U).
  tauto.
}
pose proof (H _ H4).
rewrite closure_fixes_closed in H5.
- contradiction H5; trivial.
- red; rewrite Complement_Complement; trivial.
Qed.

Lemma closure_impl_filter_limit: forall {X:TopologicalSpace}
  (S:Ensemble X) (x0:point_set X),
  In (closure S) x0 ->
  exists F:Filter X,
    In (filter_family F) S /\ filter_limit F x0.
Proof.
intros.
assert (Inhabited S).
{ destruct (closure_impl_meets_every_open_neighborhood _ _ _ H
    Full_set).
  - apply open_full.
  - constructor.
  - destruct H0.
    exists x; trivial.
}
unshelve refine (let H1:=_ in let H2:=_ in let H3:=_ in
  let Sfilt := Build_Filter_from_basis (Singleton S)
  H1 H2 H3 in _).
- exists S; constructor.
- red; intro.
  inversion H2.
  rewrite H3 in H0.
  destruct H0.
  destruct H0.
- intros.
  destruct H3.
  destruct H4.
  exists S; split; auto with sets.
- unshelve refine (let H4:=_ in
    ex_intro _ (filter_sum (neighborhood_filter x0) Sfilt H4) _).
  + intros.
    simpl in H4.
    destruct H4 as [[U [[]]]].
    simpl in H5.
    destruct H5 as [[T0 [[]]]].
    destruct (closure_impl_meets_every_open_neighborhood
      _ _ _ H U); trivial.
    destruct H8.
    exists x; constructor; auto.
  + split.
    * simpl.
      constructor.
      exists S.
      split; auto with sets.
      exists ( (Full_set, S) ).
      -- constructor; split.
         ++ constructor.
            exists Full_set; repeat split.
            apply open_full.
         ++ constructor.
            exists S; split; auto with sets.
      -- symmetry. apply Intersection_Full_set.
    * red; red; intros U ?.
      constructor.
      exists U.
      split; auto with sets.
      exists ( (U, Full_set) ).
      -- constructor.
         split; trivial.
         constructor.
         exists S; split; auto with sets.
      -- rewrite Intersection_commutative. symmetry.
         apply Intersection_Full_set.
Qed.

Lemma continuous_function_preserves_filter_limits:
  forall (X Y:TopologicalSpace) (f:point_set X -> point_set Y)
    (x:point_set X) (F:Filter X),
  filter_limit F x -> continuous_at f x ->
  filter_limit (filter_direct_image f F) (f x).
Proof.
intros.
red; intros.
intros V ?.
destruct H1.
constructor.
cut (In (filter_family (neighborhood_filter x))
  (inverse_image f V)).
{ apply H. }
constructor.
apply H0; trivial.
Qed.

Lemma func_preserving_filter_limits_is_continuous:
  forall (X Y:TopologicalSpace) (f:point_set X -> point_set Y)
    (x:point_set X),
  (forall F:Filter X, filter_limit F x ->
                     filter_limit (filter_direct_image f F) (f x)) ->
  continuous_at f x.
Proof.
intros.
assert (filter_limit (filter_direct_image f (neighborhood_filter x))
  (f x)).
{ apply H.
  red; auto with sets.
}
red; intros V ?.
assert (In (filter_family (filter_direct_image f (neighborhood_filter x)))
  V).
{ apply H0.
  constructor.
  trivial.
}
destruct H2.
destruct H2.
trivial.
Qed.

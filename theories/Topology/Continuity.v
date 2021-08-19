Require Export TopologicalSpaces.
Require Export Neighborhoods.
From ZornsLemma Require Export InverseImage.
Require Export OpenBases.
Require Export NeighborhoodBases.
Require Export Subbases.

Section continuity.

Variable X Y:TopologicalSpace.
Variable f:X -> Y.

Definition continuous : Prop :=
  forall V:Ensemble Y, open V ->
  open (inverse_image f V).

Definition continuous_at (x:X) : Prop :=
  forall V:Ensemble Y,
  neighborhood V (f x) -> neighborhood (inverse_image f V) x.

Lemma continuous_at_open_neighborhoods:
  forall x:X,
  (forall V:Ensemble Y,
  open_neighborhood V (f x) -> neighborhood (inverse_image f V) x) ->
  continuous_at x.
Proof.
intros.
red; intros.
destruct H0 as [V' [? ?]].
pose proof (H V' H0).
destruct H2 as [U' [? ?]].
exists U'; split; trivial.
apply (inverse_image_increasing f) in H1; auto with sets.
Qed.

Lemma pointwise_continuity :
  (forall x:point_set X, continuous_at x) -> continuous.
Proof.
intros.
red; intros.
replace (inverse_image f V) with (interior (inverse_image f V)).
{ apply interior_open. }
apply Extensionality_Ensembles; split.
{ apply interior_deflationary. }
red; intros.
destruct H1.
assert (neighborhood V (f x)).
{ exists V; repeat split; auto with sets. }
pose proof (H x V H2).
destruct H3 as [U].
destruct H3.
destruct H3.
assert (Included U (interior (inverse_image f V))).
{ apply interior_maximal; trivial. }
auto.
Qed.

Lemma continuous_func_continuous_everywhere:
  continuous -> forall x:point_set X, continuous_at x.
Proof.
intros.
apply continuous_at_open_neighborhoods.
intros.
apply open_neighborhood_is_neighborhood.
destruct H0; split; try constructor; auto.
Qed.

Lemma continuous_at_neighborhood_basis:
  forall (x:X) (NB:Family Y),
  neighborhood_basis NB (f x) ->
  (forall V:Ensemble Y,
  In NB V -> neighborhood (inverse_image f V) x) ->
  continuous_at x.
Proof.
intros.
red; intros.
destruct H.
apply neighborhood_basis_cond in H1.
destruct H1 as [N [? ?]].
pose proof (H0 N H).
destruct H2 as [U [? ?]].
exists U; split; trivial.
assert (Included (inverse_image f N) (inverse_image f V));
  auto with sets.
Qed.

Lemma continuous_open_basis:
  forall (B:Family Y), open_basis B ->
  (forall V:Ensemble Y,
    In B V -> open (inverse_image f V)) -> continuous.
Proof.
intros.
apply pointwise_continuity.
intro.
pose proof (open_basis_to_open_neighborhood_basis B (f x) H).
apply open_neighborhood_basis_is_neighborhood_basis in H1.
apply (continuous_at_neighborhood_basis _ _ H1).
intros.
destruct H2 as [[? ?]].
apply open_neighborhood_is_neighborhood.
split; try constructor; auto.
Qed.

Lemma continuous_subbasis:
  forall (SB:Family Y), subbasis SB ->
  (forall V:Ensemble Y,
     In SB V -> open (inverse_image f V)) -> continuous.
Proof.
intros.
apply (continuous_open_basis _
  (finite_intersections_of_subbasis_form_open_basis _ _ H)).
intros.
destruct H1.
destruct H1 as [A [? [V' []]]].
rewrite H3.
rewrite inverse_image_indexed_intersection.
apply open_finite_indexed_intersection; trivial.
intros.
apply H0.
apply H2.
Qed.

Lemma continuous_closed :
  continuous <-> forall U, closed U -> closed (inverse_image f U).
Proof.
  split.
  - intros. red.
    rewrite <- inverse_image_complement.
    apply H. assumption.
  - intros.
    red. intros.
    apply closed_complement_open.
    rewrite <- inverse_image_complement.
    apply H. red. rewrite Complement_Complement.
    assumption.
Qed.

Lemma continuous_interior :
  continuous <->
  forall A, Included (inverse_image f (interior A))
                (interior (inverse_image f A)).
Proof.
split.
- intros. red; intros.
  assert (open (inverse_image f (interior A))).
  { apply H. apply interior_open. }
  apply (interior_maximal _ _ H1).
  + intros ? ?.
    destruct H2. constructor.
    apply interior_deflationary. assumption.
  + assumption.
- intros. red; intros.
  specialize (H V).
  rewrite interior_fixes_open in H; auto.
  assert (inverse_image f V = interior (inverse_image f V)).
  { apply Extensionality_Ensembles. split.
    - assumption.
    - apply interior_deflationary.
  }
  rewrite H1.
  apply interior_open.
Qed.

Lemma continuous_closure :
  continuous <->
  (forall A, Included (Im (closure A) f)
                 (closure (Im A f))).
Proof.
rewrite continuous_closed.
split.
- intros.
  remember (inverse_image f (closure (Im A f))) as B.
  assert (closed B).
  { subst B. apply H. apply closure_closed. }
  assert (Included (closure A) B).
  { subst B. apply closure_minimal; auto.
    intros ? ?.
    constructor. apply closure_inflationary.
    exists x; auto.
  }
  intros ? ?.
  destruct H2; subst.
  apply H1 in H2.
  destruct H2.
  assumption.
- intros.
  assert (inverse_image f U = closure (inverse_image f U)).
  2: { rewrite H1. apply closure_closed. }
  apply Extensionality_Ensembles; split.
  { apply closure_inflationary. }
  specialize (H (inverse_image f U)).
  assert (Included (Im (closure (inverse_image f U)) f) U).
  + apply (Inclusion_is_transitive _ _ (closure (Im (inverse_image f U) f)));
      auto.
    apply closure_fixes_closed in H0.
    rewrite <- H0 at 2.
    apply closure_increasing.
    apply image_inverse_image_included.
  + apply (inverse_image_increasing f) in H1.
    apply (Inclusion_is_transitive
             _ _ (inverse_image f (Im (closure (inverse_image f U)) f)));
      auto.
    apply inverse_image_image_included.
Qed.

End continuity.

Arguments continuous {X} {Y}.
Arguments continuous_at {X} {Y}.

Lemma continuous_composition_at: forall {X Y Z:TopologicalSpace}
  (f:Y -> Z) (g:X -> Y)
  (x:X),
  continuous_at f (g x) -> continuous_at g x ->
  continuous_at (fun x:X => f (g x)) x.
Proof.
intros.
red; intros.
rewrite inverse_image_composition.
auto.
Qed.

Lemma continuous_composition: forall {X Y Z:TopologicalSpace}
  (f:Y -> Z) (g:X -> Y),
  continuous f -> continuous g ->
  continuous (fun x:X => f (g x)).
Proof.
intros.
red; intros.
rewrite inverse_image_composition.
auto.
Qed.

Lemma continuous_identity: forall (X:TopologicalSpace),
  continuous (fun x:X => x).
Proof.
intros.
red; intros.
rewrite inverse_image_id.
assumption.
Qed.

Lemma continuous_constant: forall (X Y:TopologicalSpace)
  (y0:Y), continuous (fun x:X => y0).
Proof.
intros.
pose (f := fun _:X => y0).
fold f.
red; intros.
destruct (classic (In V y0)).
- replace (inverse_image f V) with (@Full_set X).
  { apply open_full. }
  apply Extensionality_Ensembles; split; red; intros.
  + constructor; trivial.
  + constructor.
- replace (inverse_image f V) with (@Empty_set X).
  { apply open_empty. }
  apply Extensionality_Ensembles; split; auto with sets;
    red; intros.
  destruct H1.
  contradiction H0.
Qed.

Lemma continuous_at_is_local: forall (X Y:TopologicalSpace)
  (x0:X) (f g:X -> Y)
  (N:Ensemble X),
  neighborhood N x0 -> (forall x:point_set X, In N x -> f x = g x) ->
  continuous_at f x0 -> continuous_at g x0.
Proof.
intros.
red; intros.
destruct H as [U1 [[]]].
rewrite <- H0 in H2.
2: { auto. }
apply H1 in H2.
destruct H2 as [U2 [[]]].
exists (Intersection U1 U2).
repeat split; trivial.
- apply open_intersection2; trivial.
- destruct H7.
  rewrite <- H0.
  + apply H6 in H8.
    destruct H8; trivial.
  + auto.
Qed.

Lemma dense_image_surjective {X Y : TopologicalSpace} {f : X -> point_set Y}
  (S : Ensemble X) :
  continuous f ->
  surjective f ->
  dense S ->
  dense (Im S f).
Proof.
intros.
apply Extensionality_Ensembles.
split; red; intros; constructor.
intros U [[? H4]].
destruct (H0 x) as [x0 H5].
assert (In (closure S) x0) as H6 by now rewrite H1.
destruct H6.
rewrite <- H5.
apply in_inverse_image, H6.
repeat split.
- red.
  rewrite <- inverse_image_complement.
  auto.
- apply H4.
  now econstructor; trivial.
Qed.

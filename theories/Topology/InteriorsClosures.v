From ZornsLemma Require Import
  EnsemblesTactics
  Powerset_facts.
From Topology Require Export
  TopologicalSpaces.

Section interior_closure.

Context {X:TopologicalSpace}.
Variable S:Ensemble X.

Definition interior := FamilyUnion
  [ U:Ensemble X | open U /\ Included U S ].
Definition closure := FamilyIntersection
  [ F:Ensemble X | closed F /\ Included S F ].

Lemma interior_open : open interior.
Proof.
apply open_family_union.
intros.
now destruct H as [[]].
Qed.

Lemma interior_deflationary : Included interior S.
Proof.
red; intros.
destruct H.
destruct H as [[]]; auto with sets.
Qed.

Lemma interior_fixes_open: open S -> interior = S.
Proof.
intros.
apply Extensionality_Ensembles; split.
- apply interior_deflationary.
- red; intros.
  exists S; trivial.
  constructor.
  auto with sets.
Qed.

Lemma interior_maximal: forall U:Ensemble X,
  open U -> Included U S -> Included U interior.
Proof.
intros.
red; intros.
exists U; trivial.
constructor; split; trivial.
Qed.

Lemma closure_closed : closed closure.
Proof.
apply closed_family_intersection.
intros.
destruct H as [[]]; trivial.
Qed.

Lemma closure_inflationary : Included S closure.
Proof.
red.
intros.
constructor.
intros ? H0.
destruct H0 as [[]].
auto with sets.
Qed.

Lemma closure_fixes_closed : closed S -> closure = S.
Proof.
intro.
apply Extensionality_Ensembles.
split.
- red.
  intros.
  destruct H0.
  apply H0; split; auto with sets.
- apply closure_inflationary.
Qed.

Lemma closure_minimal: forall F:Ensemble X,
  closed F -> Included S F -> Included closure F.
Proof.
intros.
red.
intros.
destruct H1.
apply H1.
constructor; split; trivial.
Qed.

End interior_closure.

Lemma closure_empty {X:TopologicalSpace} :
  closure (@Empty_set X) = Empty_set.
Proof.
  apply closure_fixes_closed.
  apply closed_empty.
Qed.

Section interior_closure_relations.

Definition idempotent {T:Type} (f:T->T) := forall x, f (f x) = f x.

Hint Unfold idempotent : closure.

Variable X:TopologicalSpace.

Lemma interior_idempotent : idempotent (@interior X).
Proof.
intro.
apply Extensionality_Ensembles.
split.
- apply interior_deflationary.
- red. intros.
  econstructor; [ | eassumption ].
  constructor.
  split.
  + apply interior_open.
  + intro.
    exact id.
Qed.

Lemma closure_idempotent : idempotent (@closure X).
Proof.
intro.
apply Extensionality_Ensembles.
split.
- red. intros.
  destruct H.
  apply H.
  constructor.
  split.
  + apply closure_closed.
  + red.
    now intros.
- apply closure_inflationary.
Qed.

Lemma interior_increasing: forall S T:Ensemble X,
  Included S T -> Included (interior S) (interior T).
Proof.
intros.
apply interior_maximal.
- apply interior_open.
- assert (Included (interior S) S) by
    apply interior_deflationary.
  auto with sets.
Qed.

Lemma interior_intersection: forall S T:Ensemble X,
  interior (Intersection S T) =
  Intersection (interior S) (interior T).
Proof.
intros.
apply Extensionality_Ensembles. split.
- assert (Included (interior (Intersection S T)) (interior S)).
  { apply interior_increasing.
    auto with sets. }
  assert (Included (interior (Intersection S T)) (interior T)).
  { apply interior_increasing.
    auto with sets. }
  auto with sets.
- apply interior_maximal.
  + apply open_intersection2; apply interior_open.
  + pose proof (interior_deflationary S).
    pose proof (interior_deflationary T).
    red. intros x H1.
    constructor;
      [ apply H | apply H0];
      now destruct H1.
Qed.

Lemma interior_union: forall S T:Ensemble X,
  Included (Union (interior S) (interior T))
           (interior (Union S T)).
Proof.
intros.
apply interior_maximal.
- apply open_union2; apply interior_open.
- pose proof (interior_deflationary S).
  pose proof (interior_deflationary T).
  auto with sets.
Qed.

Lemma complement_inclusion: forall {Y:Type} (S T:Ensemble Y),
  Included S T -> Included (Complement T) (Complement S).
Proof.
intros.
red. intros.
intro.
contradiction H0.
auto with sets.
Qed.

Lemma interior_complement: forall S:Ensemble X,
  interior (Complement S) = Complement (closure S).
Proof.
intros.
apply Extensionality_Ensembles; split.
- rewrite <- Complement_Complement with (A:=interior (Complement S)).
  apply complement_inclusion.
  apply closure_minimal.
  + red.
    rewrite Complement_Complement.
    apply interior_open.
  + pattern S at 1.
    rewrite <- Complement_Complement with (A:=S).
    apply complement_inclusion.
    apply interior_deflationary.
- apply interior_maximal.
  + apply closure_closed.
  + apply complement_inclusion.
    apply closure_inflationary.
Qed.

Lemma closure_increasing: forall S T:Ensemble X,
  Included S T -> Included (closure S) (closure T).
Proof.
intros.
apply closure_minimal.
- apply closure_closed.
- pose proof (closure_inflationary T).
  auto with sets.
Qed.

Lemma closure_full :
  closure (@Full_set X) = Full_set.
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  { constructor. }
  apply closure_inflationary.
  assumption.
Qed.

Lemma closure_complement: forall S:Ensemble X,
  closure (Complement S) = Complement (interior S).
Proof.
intros.
pose proof (interior_complement (Complement S)).
rewrite Complement_Complement in H.
now rewrite H, Complement_Complement.
Qed.

Lemma closure_union: forall S T:Ensemble X,
  closure (Union S T) = Union (closure S) (closure T).
Proof.
intros.
apply Extensionality_Ensembles; split.
- apply closure_minimal.
  + apply closed_union2; apply closure_closed.
  + pose proof (closure_inflationary S).
    pose proof (closure_inflationary T).
    auto with sets.
- assert (Included (closure S) (closure (Union S T))).
  { apply closure_increasing; auto with sets. }
  assert (Included (closure T) (closure (Union S T))).
  { apply closure_increasing; auto with sets. }
  auto with sets.
Qed.

Lemma closure_intersection: forall S T:Ensemble X,
  Included (closure (Intersection S T))
           (Intersection (closure S) (closure T)).
Proof.
intros.
assert (Included (closure (Intersection S T)) (closure S)).
{ apply closure_increasing; auto with sets. }
assert (Included (closure (Intersection S T)) (closure T)).
{ apply closure_increasing; auto with sets. }
auto with sets.
Qed.

Lemma closure_interior_idempotent:
  idempotent (fun S => closure (@interior X S)).
Proof.
intro.
extensionality_ensembles;
apply H;
constructor;
split;
try apply closure_closed.
- apply interior_deflationary.
- red.
  intros.
  constructor.
  intros.
  destruct H1.
  destruct H1.
  apply H2.
  econstructor; [ | eassumption].
  constructor.
  split.
  + apply interior_open.
  + apply closure_inflationary.
Qed.

Lemma interior_closure_idempotent:
  idempotent (fun S => interior (@closure X S)).
Proof.
intro.
extensionality_ensembles;
  destruct H.
- eapply interior_maximal; try eassumption.
  eapply Inclusion_is_transitive; [ eassumption | ].
  red.
  intros.
  destruct H2 as [? H2].
  apply H2.
  constructor.
  split.
  + apply closure_closed.
  + apply interior_deflationary.
- econstructor; [ | eassumption ].
  constructor.
  split; try eassumption.
  eapply Inclusion_is_transitive.
  + eapply interior_maximal; eassumption.
  + apply closure_inflationary.
Qed.

Lemma meets_every_open_neighborhood_impl_closure:
  forall (S:Ensemble X) (x:X),
  (forall U:Ensemble X, open U -> In U x ->
                                Inhabited (Intersection S U)) ->
  In (closure S) x.
Proof.
intros.
apply NNPP; intro.
pose proof (H (Complement (closure S))).
destruct H1.
- apply closure_closed.
- assumption.
- destruct H1.
  contradiction H2.
  now apply closure_inflationary.
Qed.

Lemma closure_impl_meets_every_open_neighborhood:
  forall (S:Ensemble X) (x:X),
  In (closure S) x ->
  forall U:Ensemble X, open U -> In U x ->
    Inhabited (Intersection S U).
Proof.
intros.
apply NNPP; intro.
assert (Included (closure S) (Complement U)).
{ apply closure_minimal.
  - unfold closed.
    now rewrite Complement_Complement.
  - red; intros.
    intro.
    contradiction H2.
    exists x0; constructor; trivial. }
contradict H1.
now apply H3.
Qed.

Definition dense (S:Ensemble X) : Prop :=
  closure S = Full_set.

Corollary dense_full :
  dense (@Full_set X).
Proof.
  apply closure_full.
Qed.

Lemma dense_meets_every_nonempty_open:
  forall S:Ensemble X, dense S ->
    forall U:Ensemble X, open U -> Inhabited U ->
    Inhabited (Intersection S U).
Proof.
intros.
destruct H1.
apply closure_impl_meets_every_open_neighborhood with x; trivial.
rewrite H; constructor.
Qed.

Lemma meets_every_nonempty_open_impl_dense:
  forall S:Ensemble X,
  (forall U:Ensemble X, open U -> Inhabited U ->
   Inhabited (Intersection S U)) ->
  dense S.
Proof.
intros.
extensionality_ensembles.
- constructor.
- apply meets_every_open_neighborhood_impl_closure.
  intros.
  apply H; trivial.
  now exists x.
Qed.

End interior_closure_relations.

Arguments interior_increasing {X}.
Arguments interior_intersection {X}.
Arguments interior_union {X}.
Arguments interior_complement {X}.
Arguments closure_increasing {X}.
Arguments closure_complement {X}.
Arguments closure_union {X}.
Arguments closure_intersection {X}.
Arguments dense {X}.

Section Build_from_closure.

Variable X:Type.
Variable cl : Ensemble X -> Ensemble X.
Hypothesis cl_inflationary: forall S:Ensemble X,
  Included S (cl S).
Hypothesis cl_respects_union: forall S1 S2:Ensemble X,
  cl (Union S1 S2) = Union (cl S1) (cl S2).
Hypothesis cl_empty: cl Empty_set = Empty_set.
Hypothesis cl_idempotent: forall S:Ensemble X,
  cl (cl S) = cl S.

Lemma cl_increasing: forall S1 S2:Ensemble X,
  Included S1 S2 -> Included (cl S1) (cl S2).
Proof.
intros.
replace S2 with (Union S1 S2).
- rewrite cl_respects_union.
  auto with sets.
- extensionality_ensembles;
    auto with sets.
Qed.

Definition Build_TopologicalSpace_from_closure_operator : TopologicalSpace.
refine (Build_TopologicalSpace_from_closed_sets
  (fun F => cl F = F) _ _ _).
- apply cl_empty.
- intros.
  rewrite cl_respects_union; congruence.
- intros.
  extensionality_ensembles.
  + constructor. intros.
    rewrite <- (H S H1).
    apply cl_increasing with (FamilyIntersection F); trivial.
    red. intros.
    destruct H2.
    apply H2; trivial.
  + apply cl_inflationary.
    now constructor.
Defined.

Lemma Build_TopologicalSpace_from_closure_operator_closure:
  forall S:Ensemble (point_set Build_TopologicalSpace_from_closure_operator),
    closure S = cl S.
Proof.
intros.
apply Extensionality_Ensembles; split.
- apply closure_minimal.
  + apply <- Build_TopologicalSpace_from_closed_sets_closed.
    apply cl_idempotent.
  + trivial.
- replace (closure S) with (cl (closure S)).
  + apply cl_increasing.
    apply (closure_inflationary S).
  + pose proof (closure_closed S).
    apply -> Build_TopologicalSpace_from_closed_sets_closed in H.
    exact H.
Qed.

End Build_from_closure.

Arguments Build_TopologicalSpace_from_closure_operator {X}.

Section Build_from_interior.

Variable X:Type.
Variable int : Ensemble X -> Ensemble X.
Hypothesis int_deflationary: forall S:Ensemble X,
  Included (int S) S.
Hypothesis int_respects_intersection: forall S1 S2:Ensemble X,
  int (Intersection S1 S2) = Intersection (int S1) (int S2).
Hypothesis int_full: int Full_set = Full_set.
Hypothesis int_idempotent: forall S:Ensemble X,
  int (int S) = int S.

Lemma int_increasing: forall S1 S2:Ensemble X,
  Included S1 S2 -> Included (int S1) (int S2).
Proof.
intros.
replace S1 with (Intersection S1 S2).
- rewrite int_respects_intersection.
  auto with sets.
- extensionality_ensembles; auto with sets.
Qed.

Lemma intersection_family_union : forall (S:Ensemble X) (F:Ensemble (Ensemble X)),
  In F S -> Intersection S (FamilyUnion F) = S.
Proof.
intros.
extensionality_ensembles; trivial.
constructor; trivial.
econstructor; eassumption.
Qed.

Lemma int_family_union: forall (S:Ensemble X) (F:Ensemble (Ensemble X)),
  In F S ->
  Included (int S) (int (FamilyUnion F)).
Proof.
intros.
replace (int S) with (Intersection (int S) (int (FamilyUnion F))).
- auto with sets.
- rewrite <- int_respects_intersection.
  f_equal.
  now apply intersection_family_union.
Qed.

Definition Build_TopologicalSpace_from_interior_operator : TopologicalSpace.
apply Build_TopologicalSpace with (point_set:=X) (open:=fun F => int F = F);
  intros.
- extensionality_ensembles.
  + now apply int_deflationary.
  + eapply int_family_union; [ eassumption | ].
    now rewrite H.
- rewrite <- H, <- H0 at 2.
  apply int_respects_intersection.
- assumption.
Defined.

Lemma Build_TopologicalSpace_from_interior_operator_interior:
  forall S:Ensemble (point_set Build_TopologicalSpace_from_interior_operator),
    interior S = int S.
Proof.
intros.
apply Extensionality_Ensembles; split.
- red.
  intros.
  destruct H.
  destruct H.
  destruct H.
  simpl in *.
  eapply int_increasing;
    [ | erewrite H ];
    eassumption.
- red.
  intros.
  econstructor; [ | eassumption ].
  constructor.
  split.
  + apply int_idempotent.
  + apply int_deflationary.
Qed.

End Build_from_interior.

Arguments Build_TopologicalSpace_from_interior_operator {X}.

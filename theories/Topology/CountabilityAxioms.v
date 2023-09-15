From Coq Require Import
  ClassicalChoice
  Description
  Program.Subset.
From Topology Require Export
  NeighborhoodBases
  Nets
  SubspaceTopology.
From ZornsLemma Require Export
  CardinalsEns
  CountableTypes.
From ZornsLemma Require Import
  Classical_Wf
  DecidableDec
  FiniteIntersections.
From Coq Require Import
  RelationClasses.

Global Set Asymmetric Patterns.

Definition first_countable (X:TopologicalSpace) : Prop :=
  forall x:point_set X, exists NBx:Family X,
    neighborhood_basis NBx x /\ Countable NBx.

Lemma first_countable_open_neighborhood_bases:
  forall X:TopologicalSpace, first_countable X ->
    forall x:point_set X, exists NBx:Family X,
      open_neighborhood_basis NBx x /\ Countable NBx.
Proof.
intros.
destruct (H x) as [NBx [? ?]].
exists (@Im (Ensemble X) (Ensemble X) NBx (@interior X)).
split.
- constructor; intros.
  + destruct H2.
    split; rewrite H3.
    * apply interior_open.
    * now apply neighborhood_interior, H0.
  + destruct H0.
    destruct (neighborhood_basis_cond U) as [N].
    * now apply open_neighborhood_is_neighborhood.
    * destruct H0.
      exists (interior N).
      split.
      ** now exists N.
      ** pose proof (interior_deflationary N).
         auto with sets.
- now apply countable_img.
Qed.

Lemma first_countable_sequence_closure:
  forall (X:TopologicalSpace) (S:Ensemble X) (x:point_set X),
  first_countable X -> In (closure S) x ->
  exists y:Net nat_DS X, (forall n:nat, In S (y n)) /\
                         net_limit y x.
Proof.
intros.
destruct (first_countable_open_neighborhood_bases _ H x) as [NB []].
destruct H2 as [g].
pose (U (n:nat) := IndexedIntersection
  (fun x: {x:{x:Ensemble X | In NB x} | (g x < n)%nat} =>
     proj1_sig (proj1_sig x))).
assert (forall n:nat, open (U n)).
{ intros.
  apply open_finite_indexed_intersection.
- apply inj_finite with _ (fun x:{x:{x:Ensemble X | In NB x}
                             | (g x < n)%nat} =>
    exist (fun m:nat => (m<n)%nat) (g (proj1_sig x)) (proj2_sig x)).
  + apply finite_nat_initial_segment.
  + intros [[x0 P] p] [[y0 Q] q] ?.
    simpl in H3.
    apply subset_eq, subset_eq. simpl.
    injection H3; intros.
    apply H2 in H4.
    now injection H4.
  + intros; apply classic.
- intros.
  destruct a as [[x0]].
  now apply H1.
}
destruct (choice (fun (n:nat) (x:point_set X) => In (U n) x /\
                                                 In S x)) as [y].
- intros n.
  destruct (closure_impl_meets_every_open_neighborhood _ _ _ H0 (U n))
    as [y]; trivial.
  + constructor; trivial.
    destruct a as [[x0]].
    simpl.
    now apply H1.
  + exists y.
    destruct H4.
    now split.
- exists y.
  split.
  + apply H4.
  + red; intros V ? ?.
    destruct H1.
    destruct (open_neighborhood_basis_cond V) as [W []].
    * now split.
    * pose (a := (exist _ W H1 : {x:Ensemble X|In NB x})).
      exists (Datatypes.S (g a)).
      intros.
      simpl in j.
      simpl in H8.
      apply H7.
      assert (Included (U j) W).
    { red; intros.
      destruct H9.
      exact (H9 (exist _ a H8)). }
      apply H9, H4.
Qed.

(** in a first-countable space, a set is closed if it contains all its
  limits of sequences. *)
Corollary first_countable_sequence_closed
  {X : TopologicalSpace} (S : Ensemble X) :
  first_countable X ->
  (forall (x : Net nat_DS X) (x0 : X),
      (forall n : nat, In S (x n)) ->
      net_limit x x0 -> In S x0) ->
  closed S.
Proof.
  intros.
  replace S with (closure S).
  { apply closure_closed. }
  apply Extensionality_Ensembles; split; red.
  2: apply closure_inflationary.
  intros x Hx.
  apply first_countable_sequence_closure in Hx;
    auto.
  clear H.
  destruct Hx as [x0 [Hx0 Hx1]].
  eapply H0; eauto.
Qed.

Definition separable (X : TopologicalSpace) : Prop :=
  exists S : Ensemble X,
    Countable S /\ dense S.

Definition open_cover {X : TopologicalSpace} (F : Family X) : Prop :=
  (forall U, In F U -> open U) /\ (FamilyUnion F = Full_set).

(* [FS] is a subcover of [F] *)
Definition subcover {X : Type} (FS F : Family X) : Prop :=
  Included FS F /\ Included (FamilyUnion F) (FamilyUnion FS).

(** we consistently write "Lindelof" instead of "Lindelöf" to
    accomodate those people who do not have a letter "ö" handy on their
    keyboards. *)
Definition Lindelof (X : TopologicalSpace) : Prop :=
  forall cover:Family X,
    open_cover cover ->
    exists scover:Family X,
      subcover scover cover /\ Countable scover.

Definition second_countable (X:TopologicalSpace) : Prop :=
  exists B : Family X,
    open_basis B /\ Countable B.

Lemma second_countable_impl_first_countable:
  forall X:TopologicalSpace, second_countable X -> first_countable X.
Proof.
intros.
destruct H as [B []].
red; intros.
exists [ U:Ensemble X | In B U /\ In U x ]; split.
- apply open_neighborhood_basis_is_neighborhood_basis.
  apply open_basis_to_open_neighborhood_basis; trivial.
- apply countable_downward_closed with B; trivial.
  red; intros.
  now destruct H1 as [[? ?]].
Qed.

Lemma second_countable_subbasis:
  forall (X:TopologicalSpace) (SB : Family X),
    subbasis SB -> Countable SB ->
    second_countable X.
Proof.
  intros.
  eexists; split.
  { apply finite_intersections_of_subbasis_form_open_basis.
    eassumption.
  }
  apply finite_intersections_countable.
  assumption.
Qed.

Lemma second_countable_impl_separable:
  forall X:TopologicalSpace, second_countable X -> separable X.
Proof.
intros.
destruct H as [B []].
destruct (choice (fun (U:{U:Ensemble X | In B U /\ Inhabited U})
  (x:point_set X) => In (proj1_sig U) x)) as [choice_fun].
- intros.
  destruct x as [U [? ?]].
  simpl.
  destruct i0.
  now exists x.
- exists (Im Full_set choice_fun); split.
  + apply countable_img.
    red.
    match goal with |- CountableT ?S =>
      pose (g := fun (x:S) =>
        match x return {U:Ensemble X | In B U} with
        | exist (exist U (conj i _)) _ => exist _ U i
        end)
    end.
    apply inj_countable with g; trivial.
    red; intros x y H2.
    unfold g in H2.
    destruct x as [[U [? ?]]].
    destruct y as [[V [? ?]]].
    apply subset_eq, subset_eq.
    now injection H2.
  + apply meets_every_nonempty_open_impl_dense.
    intros.
    destruct H3, H.
    destruct (open_basis_cover x U) as [V [? [? ?]]]; trivial.
    assert (In B V /\ Inhabited V).
    { split; trivial.
      exists x; trivial.
    }
    exists (choice_fun (exist _ V H6)).
    constructor.
    * pose proof (H1 (exist _ V H6)).
      simpl in H7.
      exists (exist _ V H6).
      ** constructor.
      ** reflexivity.
    * apply H4.
      now pose proof (H1 (exist _ V H6)).
Qed.

Lemma weight_second_countable_char (X : TopologicalSpace) :
  second_countable X <->
    (forall Y (kappa : Ensemble Y),
        weight X kappa -> le_cardinal_ens kappa (@Full_set nat)).
Proof.
split.
- intros [B [HBbasis HBcount]] **.
  apply least_cardinal_ext_to_subset in H.
  destruct H as [C [[HCbasis HCmin] HCcard]].
  eapply le_cardinal_ens_Proper_l; eauto.
  clear Y kappa HCcard.
  specialize (HCmin B HBbasis).
  apply Countable_as_le_cardinal_ens in HBcount.
  eapply le_cardinal_ens_transitive; eauto.
- intros.
  destruct (weight_exists X) as [kappa [[B [HB0 HB1]]]].
  red in HB0.
  exists B; split; auto.
  apply Countable_as_le_cardinal_ens.
  apply H.
  split.
  + exists B; split; auto. reflexivity.
  + intros.
    specialize (H0 Y V H1).
    clear H1.
    apply eq_cardinal_ens_sym in HB1.
    eapply le_cardinal_ens_Proper_l; eauto.
Qed.

(* As defined in the “Encyclopedia of General Topology”.
   A cardinality [kappa] is a candidate for the Lindelöf degree of [X],
   if for every open cover [cover] of [X] there is a subcover of
   cardinality at most [kappa].
 *)
Definition Lindelof_degree_candidate (X : TopologicalSpace)
  {Y : Type} (kappa : Ensemble Y) : Prop :=
  forall cover : Family X,
    open_cover cover ->
    exists scover, subcover scover cover /\
                le_cardinal_ens scover kappa.

Lemma Lindelof_degree_candidate_upwards_closed
  (X : TopologicalSpace) :
  forall {Y0 Y1 : Type} (kappa : Ensemble Y0)
    (lambda : Ensemble Y1),
    Lindelof_degree_candidate X kappa ->
    le_cardinal_ens kappa lambda ->
    Lindelof_degree_candidate X lambda.
Proof.
  intros.
  red. intros.
  specialize (H cover H1).
  destruct H as [scover []].
  exists scover. split; try assumption.
  eapply le_cardinal_ens_transitive; eauto.
Qed.

(* As defined in the “Encyclopedia of General Topology” *)
(* The minimal "Lindelöf_degree_candidate" *)
Definition Lindelof_degree (X : TopologicalSpace) {Y : Type} (kappa : Ensemble Y) : Prop :=
  least_cardinal (@Lindelof_degree_candidate X) kappa.

Lemma Lindelof_degree_Lindelof_char (X : TopologicalSpace) :
  Lindelof X <-> Lindelof_degree_candidate X (@Full_set nat).
Proof.
unfold Lindelof, Lindelof_degree_candidate.
split.
- intros ? cover Hcover.
  specialize (H cover Hcover) as [scover [? ?]].
  exists scover.
  split; try assumption.
  apply Countable_as_le_cardinal_ens.
  assumption.
- intros ? cover Hcover.
  specialize (H cover Hcover) as [scover []].
  exists scover.
  repeat split; try apply H.
  apply Countable_as_le_cardinal_ens.
  assumption.
Qed.

Lemma Lindelof_Lemma_technical:
  (* given a topological space [X], a basis [B] on [X] *)
  forall (X:TopologicalSpace) (B:Family X),
    open_basis B ->
    (* and an open cover [C] of [X] *)
    forall C:Family X,
      open_cover C ->
      (* there exists a subcover [V] of cardinality
         less than the cardinality of [B]. *)
      exists V:Family X,
        subcover V C /\
          le_cardinal_ens V B.
Proof.
intros.
pose (basis_elts_contained_in_cover_elt :=
  [ U:Ensemble X | In B U /\ Inhabited U /\
    exists V:Ensemble X, In C V /\ Included U V ]).
destruct (choice (fun (U:{U | In basis_elts_contained_in_cover_elt U})
  (V:Ensemble X) => In C V /\ Included (proj1_sig U) V))
  as [choice_fun Hcf].
{ intros.
  destruct x.
  simpl.
  now destruct i as [[? [? ?]]].
}
exists (Im Full_set choice_fun).
repeat split.
- red; intros.
  destruct_ensembles_in.
  subst.
  apply Hcf.
- intros x Hx.
  destruct Hx.
  destruct (open_basis_cover B H x S) as [V [? []]]; trivial.
  { now apply H0. }
  unshelve eexists (choice_fun (exist _ V _)).
  { constructor.
    repeat split; trivial.
    - now exists x.
    - exists S; now split.
  }
  + apply Im_def.
    constructor.
  + apply Hcf. simpl.
    assumption.
- eapply le_cardinal_ens_transitive.
  { apply le_cardinal_ens_Im. }
  eapply le_cardinal_ens_Proper_l.
  { apply eq_cardinal_ens_sym.
    apply eq_cardinal_ens_sig.
  }
  apply le_cardinal_ens_Included.
  firstorder.
Qed.

Corollary Lindelof_Lemma_technical' (X : TopologicalSpace)
  (B : Family X) :
  open_basis B ->
  Lindelof_degree_candidate X B.
Proof.
  intros HB.
  intros C HC.
  apply Lindelof_Lemma_technical; auto.
Qed.

(* The Lindelöf degree of a space is less (or equal) to its weight. *)
Theorem Lindelof_Lemma (X : TopologicalSpace) {Y0 Y1 : Type}
  (kappa : Ensemble Y0) (lambda : Ensemble Y1) :
  Lindelof_degree X kappa ->
  weight X lambda ->
  le_cardinal_ens kappa lambda.
Proof.
  intros [?Hkappa0 ?Hkappa0].
  intros H.
  apply least_cardinal_ext_to_subset in H.
  destruct H as [B [[?HB0 ?HB0] ?Hlambda]].
  eapply le_cardinal_ens_Proper_r; eauto.
  clear Y1 lambda Hlambda.
  apply Hkappa1.
  clear Y0 kappa Hkappa0 Hkappa1.
  apply Lindelof_Lemma_technical'; auto.
Qed.

Lemma Lindelof_degree_exists (X : TopologicalSpace) :
  exists (Y : Type) (kappa : Ensemble Y), Lindelof_degree X kappa.
Proof.
  unfold Lindelof_degree.
  apply least_cardinal_exists with (X := Ensemble X) (U := @open X).
  apply Lindelof_Lemma_technical'.
  firstorder.
Qed.

Lemma second_countable_impl_Lindelof:
  forall X:TopologicalSpace, second_countable X -> Lindelof X.
Proof.
intros.
rewrite weight_second_countable_char in H.
apply Lindelof_degree_Lindelof_char.
destruct (Lindelof_degree_exists X) as [Y0 [kappa ?Hk]].
destruct (weight_exists X) as [lambda ?Hl].
pose proof (Lindelof_Lemma X kappa lambda Hk Hl).
specialize (H (Ensemble X) lambda Hl).
eapply Lindelof_degree_candidate_upwards_closed.
2: eapply H.
eapply Lindelof_degree_candidate_upwards_closed.
2: eapply H0.
apply Hk.
Qed.

Definition Hereditary_Lindelof_degree (X : TopologicalSpace) {Y : Type} (kappa : Ensemble Y) : Prop :=
  least_cardinal
    (fun Y U =>
       forall A : Ensemble X,
         Lindelof_degree_candidate (SubspaceTopology A) U) kappa.

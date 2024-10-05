From ZornsLemma Require Import
  Cardinals
  DecidableDec
  FiniteIntersections
  Proj1SigInjective.
From Topology Require Export
  TopologicalSpaces.
From Topology Require Import
  Homeomorphisms
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

(* Corresponds to Lemma 16.1 in Munkres. *)
Lemma subspace_basis (B : Family X) :
  open_basis B ->
  open_basis (Im B (inverse_image subspace_inc)).
Proof.
  intros.
  constructor.
  - intros.
    inversion H0; subst; clear H0.
    apply subspace_inc_continuous.
    apply H. assumption.
  - intros.
    rewrite subspace_open_char in H0.
    destruct H0 as [V []]. subst.
    pose proof (open_basis_cover B H (proj1_sig x) V H0).
    destruct H2 as [V0 [? []]].
    { destruct H1. assumption. }
    exists (inverse_image subspace_inc V0).
    repeat split.
    + eexists V0; auto.
    + apply H3. apply H5.
    + apply H4.
Qed.

Lemma subspace_subbasis (B : Family X) :
  subbasis B ->
  subbasis (Im B (fun Bx => inverse_image subspace_inc Bx)).
Proof.
  intros. constructor.
  - intros.
    inversion H0; subst; clear H0.
    apply subspace_inc_continuous.
    apply subbasis_elements in H1; assumption.
  - intros U x HUx HU.
    rewrite subspace_open_char in HU.
    destruct HU as [V [HV HUV]].
    subst.
    inversion HUx; subst; clear HUx.
    apply subbasis_cover with (SB := B) (x := subspace_inc x)
      in HV as [W [HWx [HWfin HWV]]]; auto.
    exists (inverse_image subspace_inc W); repeat split; auto.
    + apply finite_intersections_Im_inverse_image.
      assumption.
    + destruct H1. auto.
Qed.

(** the weight of a subspace never exceeds the weight of the ambient
    space *)
Corollary subspace_weight_le_space {Y0 Y1 : Type} (kappa : Ensemble Y0)
  (lambda : Ensemble Y1) :
  weight X kappa -> weight SubspaceTopology lambda ->
  le_cardinal_ens lambda kappa.
Proof.
  intros HX HS.
  destruct HX as [[BX [HBX0 HBX1]] HBX2].
  destruct HS as [[BS [HBS0 HBS1]] HBS2].
  apply le_cardinal_ens_transitive
    with (V := (Im BX (inverse_image subspace_inc))).
  - apply HBS2.
    eexists; split.
    2: reflexivity.
    apply subspace_basis. assumption.
  - eapply le_cardinal_ens_Proper_r; eauto.
    apply le_cardinal_ens_Im.
Qed.

End Subspace.

Lemma subspace_full_homeo (X : TopologicalSpace) :
  homeomorphic
    (SubspaceTopology (@Full_set X)) X.
Proof.
  exists (subspace_inc Full_set).
  constructor.
  { apply subspace_inc_continuous. }
  exists (fun x => exist _ x (Full_intro X x)).
  split; [|split].
  - apply subspace_continuous_char. apply continuous_identity.
  - intros ?. apply Subset.subset_eq. reflexivity.
  - reflexivity.
Qed.

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

Section PastingLemma.
  Context {X Y : TopologicalSpace} {A B : Ensemble X}
    (f : SubspaceTopology A -> Y) (g : SubspaceTopology B -> Y)
    (HAB : Union A B = Full_set).

  Let Union_Full_set (x : X) (HA : ~ In A x) : In B x.
    assert (In Full_set x) as Hx by auto with sets.
    rewrite <- HAB in Hx.
    destruct Hx; intuition.
  Qed.

  Definition pasting_lemma_fn (x : X) : Y :=
    match classic_dec (In A x) with
    | left Hx => f (exist A x Hx)
    | right HA =>
        g (exist B x (Union_Full_set x HA))
    end.

  Lemma pasting_lemma_fn_left (x : X) (Hx : In A x) :
    pasting_lemma_fn x = f (exist A x Hx).
  Proof using Type.
    unfold pasting_lemma_fn.
    destruct (classic_dec _); try contradiction.
    destruct (proof_irrelevance _ Hx i); reflexivity.
  Qed.

  Lemma pasting_lemma_fn_right (x : X) (Hx0 : ~ In A x) (Hx1 : In B x) :
    pasting_lemma_fn x = g (exist B x Hx1).
  Proof using Type.
    unfold pasting_lemma_fn.
    destruct (classic_dec _); try contradiction.
    destruct (proof_irrelevance _ (Union_Full_set _ n) Hx1); reflexivity.
  Qed.

  Lemma pasting_lemma_fn_eq_inverse_image
    (Hfg : forall (x : X) H0 H1, f (exist _ x H0) = g (exist _ x H1))
    (U : Ensemble Y) :
    inverse_image pasting_lemma_fn U =
      Union (Im (inverse_image f U) (subspace_inc _))
            (Im (inverse_image g U) (subspace_inc _)).
  Proof using Type.
   apply Extensionality_Ensembles; split; red.
   - intros x Hx.
     inversion Hx; subst; clear Hx.
     unfold pasting_lemma_fn in H.
     destruct (classic_dec _).
     + left.
       exists (exist _ x i).
       * constructor. assumption.
       * reflexivity.
     + right.
       eexists (exist _ x _).
       * constructor. eassumption.
       * reflexivity.
   - intros x Hx. constructor.
     destruct Hx as [x Hx|x Hx].
     + inversion Hx; subst; clear Hx.
       destruct H.
       destruct x0 as [x Hx].
       simpl.
       erewrite pasting_lemma_fn_left; eauto.
     + inversion Hx; subst; clear Hx.
       destruct H.
       destruct x0 as [x Hx].
       simpl.
       destruct (classic (In A x)).
       { unshelve erewrite pasting_lemma_fn_left; eauto.
         erewrite Hfg; eauto.
       }
       erewrite pasting_lemma_fn_right; eauto.
  Qed.

  (* Corresponds to 18.3 in Munkres. Two continuous functions [f], [g], defined on
     closed subspaces [A], [B] of a space [X] which cover [X], can be combined to
     a continuous function [pasting_lemma_fn] defined on the whole space [X].
   *)
  Lemma pasting_lemma_cts  :
    (forall x : X, forall H0 H1, f (exist _ x H0) = g (exist _ x H1)) ->
    closed A -> closed B ->
    continuous f -> continuous g ->
    continuous pasting_lemma_fn.
  Proof using Type.
   intros Hfg HA HB Hf Hg.
   apply continuous_closed.
   intros U HU.
   rewrite pasting_lemma_fn_eq_inverse_image; auto.
   apply closed_union2.
   - apply subspace_inc_takes_closed_to_closed.
     + assumption.
     + apply continuous_closed; assumption.
   - apply subspace_inc_takes_closed_to_closed.
     + assumption.
     + apply continuous_closed; assumption.
  Qed.
End PastingLemma.

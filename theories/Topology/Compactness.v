From ZornsLemma Require Import EnsemblesTactics Powerset_facts.
Require Export TopologicalSpaces Nets FilterLimits Homeomorphisms SeparatednessAxioms SubspaceTopology.
Require Import FiltersAndNets ClassicalChoice.
Set Asymmetric Patterns.

Definition compact (X:TopologicalSpace) :=
  forall C:Family X,
    (forall U:Ensemble X, In C U -> open U) ->
    FamilyUnion C = Full_set ->
    exists C':Family X,
      Finite C' /\ Included C' C /\
      FamilyUnion C' = Full_set.

Lemma compactness_on_indexed_covers:
  forall (X:TopologicalSpace) (A:Type) (C:IndexedFamily A X),
    compact X ->
    (forall a:A, open (C a)) -> IndexedUnion C = Full_set ->
  exists A':Ensemble A, Finite A' /\
    IndexedUnion (fun a':{a':A | In A' a'} => C (proj1_sig a')) = Full_set.
Proof.
intros.
pose (cover := ImageFamily C).
destruct (H cover) as [subcover].
- intros.
  destruct H2.
  rewrite H3; apply H0.
- unfold cover.
  now rewrite <- indexed_to_family_union.
- destruct H2 as [? []].
  destruct (finite_choice _ _
    (fun (U:{U:Ensemble X | In subcover U}) (a:A) =>
        proj1_sig U = C a)) as [choice_fun].
  + now apply Finite_ens_type.
  + destruct x as [U].
    simpl.
    apply H3 in i.
    destruct i.
    now exists x.
  + exists (Im Full_set choice_fun).
    split.
    * apply FiniteT_img.
      ** now apply Finite_ens_type.
      ** intros; apply classic.
    * extensionality_ensembles.
      ** constructor.
      ** assert (In Full_set x) by constructor.
         rewrite <- H4 in H6.
          destruct H6.
          assert (In (Im Full_set choice_fun) (choice_fun (exist _ S H6))).
        { exists (exist _ S H6); constructor. }
          exists (exist _ (choice_fun (exist _ S H6)) H8).
          simpl.
          now rewrite <- H5.
Qed.

Lemma compact_finite_nonempty_closed_intersection:
  forall X:TopologicalSpace, compact X ->
  forall F:Family X,
    (forall G:Ensemble X, In F G -> closed G) ->
    (forall F':Family X, Finite F' -> Included F' F ->
     Inhabited (FamilyIntersection F')) ->
    Inhabited (FamilyIntersection F).
Proof.
intros.
apply NNPP; red; intro.
pose (C := [ U:Ensemble X | In F (Complement U) ]).
unshelve refine (let H3:=(H C _ _) in _).
- intros.
  destruct H3.
  apply H0 in H3.
  now apply closed_complement_open.
- extensionality_ensembles.
  + constructor.
  + apply NNPP; red; intro.
    contradiction H2.
    exists x.
    constructor.
    intros.
    apply NNPP; red; intro.
    contradiction H3.
    exists (Complement S).
    * constructor.
      now rewrite Complement_Complement.
    * assumption.
- destruct H3 as [C' [? [? ?]]].
  pose (F' := [G : Ensemble X | In C' (Complement G)]).
  unshelve refine (let H6 := (H1 F' _ _) in _).
  + assert (F' = Im C' Complement).
  { apply Extensionality_Ensembles; split; red; intros;
      destruct H6.
    - exists (Complement x); trivial.
      now rewrite Complement_Complement.
    - constructor.
      now rewrite H7, Complement_Complement. }
    rewrite H6.
    now apply finite_image.
  + red; intros.
    destruct H6.
    apply H4 in H6.
    destruct H6.
    now rewrite Complement_Complement in H6.
  + destruct H6 as [x0].
    destruct H6.
    assert (In (FamilyUnion C') x).
  { rewrite H5. constructor. }
    destruct H7.
    assert (In (Complement S) x).
  { apply H6.
    constructor.
    now rewrite Complement_Complement. }
    contradiction H9.
Qed.

Lemma finite_nonempty_closed_intersection_impl_compact:
  forall X:TopologicalSpace,
  (forall F:Family X,
    (forall G:Ensemble X, In F G -> closed G) ->
    (forall F':Family X, Finite F' -> Included F' F ->
     Inhabited (FamilyIntersection F')) ->
    Inhabited (FamilyIntersection F)) ->
  compact X.
Proof.
intros.
red; intros.
apply NNPP; red; intro.
pose (F := [ G:Ensemble X | In C (Complement G) ]).
unshelve refine (let H3 := (H F _ _) in _).
- intros.
  destruct H3.
  now apply H0.
- intros.
  apply NNPP; red; intro.
  contradiction H2.
  exists [ U:Ensemble X | In F' (Complement U) ].
  repeat split.
  + assert ([U:Ensemble X | In F' (Complement U)] =
      Im F' Complement).
    * extensionality_ensembles.
      ** econstructor.
         *** eassumption.
         *** now rewrite Complement_Complement.
      ** constructor.
         now rewrite H7, Complement_Complement.
    *  rewrite H6.
       now apply finite_image.
  + red; intros.
    destruct H6.
    apply H4 in H6.
    destruct H6.
    now rewrite Complement_Complement in H6.
  + extensionality_ensembles.
    * constructor.
    * apply NNPP; red; intro.
      contradiction H5.
      exists x.
      constructor.
      intros.
      apply NNPP; red; intro.
      contradiction H6.
      exists (Complement S).
      ** constructor.
         rewrite Complement_Complement; trivial.
      ** exact H8.
- destruct H3.
  assert (In (FamilyUnion C) x).
{ rewrite H1. constructor. }
  destruct H4.
  assert (In (Complement S) x).
{ destruct H3.
  apply H3.
  constructor.
  now rewrite Complement_Complement. }
  contradiction H6.
Qed.

Lemma compact_impl_filter_cluster_point:
  forall X:TopologicalSpace, compact X ->
    forall F:Filter X, exists x0:point_set X,
    filter_cluster_point F x0.
Proof.
intros.
pose proof (compact_finite_nonempty_closed_intersection
  _ H [ G:Ensemble X | In (filter_family F) G /\
                                   closed G ]) as [x0].
- intros.
  destruct H0 as [[]]; trivial.
- intros.
  assert (closed (FamilyIntersection F')).
{ apply closed_family_intersection.
  intros.
  apply H1 in H2.
  now destruct H2, H2. }
  assert (In (filter_family F) (FamilyIntersection F')).
{ clear H2.
  induction H0.
  - rewrite empty_family_intersection.
    apply filter_full.
  - replace (FamilyIntersection (Add A x)) with
      (Intersection (FamilyIntersection A) x).
    + apply filter_intersection.
      * apply IHFinite.
        auto with sets.
      * assert (In (Add A x) x).
      { right. constructor. }
        apply H1 in H3.
        now destruct H3, H3.
    + extensionality_ensembles.
      * constructor.
        intros.
        destruct H5.
        ** now apply H3.
        ** now destruct H5.
      * repeat constructor; intros; apply H3; auto with sets. }

  apply NNPP; intro.
  contradiction (filter_empty _ F).
  replace (@Empty_set X) with (FamilyIntersection F'); trivial.
  extensionality_ensembles.
  contradiction H4.
  exists x.
  now constructor.
- exists x0.
  red; intros.
  destruct H0.
  apply H0.
  constructor.
  split.
  + apply filter_upward_closed with S; trivial.
    apply closure_inflationary.
  + apply closure_closed.
Qed.

Lemma filter_cluster_point_impl_compact:
  forall X:TopologicalSpace,
    (forall F:Filter X, exists x0:point_set X,
      filter_cluster_point F x0) -> compact X.
Proof.
intros.
apply finite_nonempty_closed_intersection_impl_compact.
intros.
unshelve refine (let H2:=_ in let filt := Build_Filter_from_subbasis F H2 in _).
- intros.
  rewrite indexed_to_family_intersection.
  apply H1.
  + apply FiniteT_img; trivial.
    intros.
    apply classic.
  + red; intros.
    destruct H4.
    rewrite H5; apply H3.
- assert (filter_subbasis filt F) by apply filter_from_subbasis_subbasis.
  destruct (H filt) as [x0].
  exists x0.
  constructor; intros.
  assert (closed S) by now apply H0.
  assert (In (filter_family filt) S).
{ eapply filter_subbasis_elements; eassumption. }
  pose proof (H4 _ H7).
  now rewrite closure_fixes_closed in H8.
Qed.

Lemma ultrafilter_limit_impl_compact:
  forall X:TopologicalSpace,
    (forall U:Filter X, ultrafilter U ->
      exists x0:point_set X, filter_limit U x0) -> compact X.
Proof.
intros.
apply filter_cluster_point_impl_compact.
intros.
destruct (ultrafilter_extension F) as [U].
destruct H0.
destruct (H _ H1) as [x0].
exists x0.
red; intros.
apply filter_limit_is_cluster_point in H2.
apply H0 in H3.
now apply H2.
Qed.

Lemma compact_impl_net_cluster_point:
  forall X:TopologicalSpace, compact X ->
    forall (I:DirectedSet) (x:Net I X), inhabited (DS_set I) ->
    exists x0:point_set X, net_cluster_point x x0.
Proof.
intros.
destruct (compact_impl_filter_cluster_point
  _ H (tail_filter x H0)) as [x0].
exists x0.
apply tail_filter_cluster_point_impl_net_cluster_point with H0.
apply H1.
Qed.

Lemma net_cluster_point_impl_compact: forall X:TopologicalSpace,
  (forall (I:DirectedSet) (x:Net I X), inhabited (DS_set I) ->
    exists x0:point_set X, net_cluster_point x x0) ->
  compact X.
Proof.
intros.
apply filter_cluster_point_impl_compact.
intros.
destruct (H _ (filter_to_net _ F)) as [x0].
- cut (inhabited X).
  + intro.
    destruct H0 as [x].
    exists.
    simpl.
    apply Build_filter_to_net_DS_set with Full_set x.
    * apply filter_full.
    * constructor.
  + apply NNPP; intro.
    contradiction (filter_empty _ F).
    replace (@Empty_set X) with (@Full_set X).
    * apply filter_full.
    * extensionality_ensembles.
      contradiction H0.
      now constructor.
- exists x0.
  now apply filter_to_net_cluster_point_impl_filter_cluster_point.
Qed.

Lemma compact_closed: forall (X:TopologicalSpace)
  (S:Ensemble X), Hausdorff X ->
  compact (SubspaceTopology S) -> closed S.
Proof.
intros.
destruct (classic (Inhabited S)).
- replace S with (closure S).
  { apply closure_closed. }
  apply Extensionality_Ensembles; split; red; intros.
  2: {
    apply closure_inflationary. assumption.
  }
  destruct (net_limits_determine_topology _ _ H2) as [I0 [y []]].
  pose (yS (i:DS_set I0) := exist (fun x:X => In S x) (y i) (H3 i)).
  assert (inhabited (point_set (SubspaceTopology S))).
{ destruct H1.
  constructor.
  now exists x0. }
  assert (inhabited (DS_set I0)) as HinhI0.
{ red in H4.
  destruct (H4 Full_set) as [i0]; auto with topology.
  constructor. }
  pose proof (compact_impl_net_cluster_point
    (SubspaceTopology S) H0 _ yS HinhI0).
  destruct H6 as [[x0]].
  apply net_cluster_point_impl_subnet_converges in H6.
  + destruct H6 as [J [y' []]].
    destruct H6.
    assert (net_limit (fun j:DS_set J => y (h j)) x0).
  { apply continuous_func_preserves_net_limits with
    (f:=subspace_inc S) (Y:=X) in H7.
    - assumption.
    - apply continuous_func_continuous_everywhere, subspace_inc_continuous. }
    assert (net_limit (fun j:DS_set J => y (h j)) x).
  { apply subnet_limit with I0 y; trivial.
    now constructor. }
    assert (x = x0).
  { eapply Hausdorff_impl_net_limit_unique; eassumption. }
    now subst.
  + destruct (H4 Full_set).
    * apply open_full.
    * constructor.
    * now constructor.
- red.
  rewrite (not_inhabited_empty _ H1).
  rewrite Complement_Empty_set.
  apply open_full.
Qed.

Lemma closed_compact: forall (X:TopologicalSpace) (S:Ensemble X),
  compact X -> closed S -> compact (SubspaceTopology S).
Proof.
intros.
apply net_cluster_point_impl_compact.
intros.
destruct (compact_impl_net_cluster_point _ H
  _ (fun i:DS_set I => subspace_inc _ (x i))) as [x0]; trivial.
assert (In S x0).
{ rewrite <- (closure_fixes_closed S); trivial.
  eapply net_cluster_point_in_closure;
[ | eassumption ].
  destruct H1 as [i0].
  exists i0.
  intros.
  now destruct (x j). }
exists (exist _ x0 H3).
red; intros.
red; intros.
rewrite subspace_open_char in H4.
destruct H4 as [V []].
rewrite H6 in H5.
destruct H5.
simpl in H5.
destruct (H2 V H4 H5 i) as [j []]; trivial.
exists j; split; trivial.
rewrite H6.
now constructor.
Qed.

Lemma compact_image: forall {X Y:TopologicalSpace}
  (f:point_set X->Y),
  compact X -> continuous f -> surjective f -> compact Y.
Proof.
intros.
red; intros.
pose (B := fun U:{U:Ensemble Y | In C U} =>
           inverse_image f (proj1_sig U)).
destruct (compactness_on_indexed_covers _ _ B H) as [subcover].
- destruct a as [U].
  now apply H0, H2.
- extensionality_ensembles.
  + constructor.
  + assert (In (FamilyUnion C) (f x)).
  { rewrite H3; constructor. }
    inversion_clear H4 as [V].
    exists (exist _ V H5).
    now constructor.
- exists (Im subcover (@proj1_sig _ (fun U:Ensemble Y => In C U))).
  destruct H4.
  repeat split.
  + now apply finite_image.
  + intros V ?.
    destruct H6 as [[U]].
    now subst.
  + apply Extensionality_Ensembles; split; red; intros y ?.
  { constructor. }
    destruct (H1 y) as [x].
    assert (In (IndexedUnion
      (fun a':{a' | In subcover a'} => B (proj1_sig a'))) x).
  { rewrite H5; constructor. }
    destruct H8 as [[[U]]].
    exists U.
    * now exists (exist _ U i).
    * destruct H8.
      now subst.
Qed.

Lemma compact_Hausdorff_impl_normal_sep: forall X:TopologicalSpace,
  compact X -> Hausdorff X -> normal_sep X.
Proof.
intros.
assert (T3_sep X).
{ destruct (choice (fun (xy:{xy:X * X |
                    let (x,y):=xy in x <> y})
    (UV:Ensemble X * Ensemble X) =>
    match xy with | exist (x,y) i =>
      let (U,V):=UV in
    open U /\ open V /\ In U x /\ In V y /\ Intersection U V = Empty_set
    end)) as
  [choice_fun].
- destruct x as [[x y] i].
  destruct (H0 _ _ i) as [U [V]].
  now exists (U, V).
- pose (choice_fun_U := fun (x y:X)
    (Hineq:x<>y) => fst (choice_fun (exist _ (x,y) Hineq))).
  pose (choice_fun_V := fun (x y:X)
    (Hineq:x<>y) => snd (choice_fun (exist _ (x,y) Hineq))).
  assert (forall (x y:X) (Hineq:x<>y),
    open (choice_fun_U x y Hineq) /\
    open (choice_fun_V x y Hineq) /\
    In (choice_fun_U x y Hineq) x /\
    In (choice_fun_V x y Hineq) y /\
    Intersection (choice_fun_U x y Hineq) (choice_fun_V x y Hineq) = Empty_set).
{ intros.
  unfold choice_fun_U; unfold choice_fun_V.
  pose proof (H1 (exist _ (x,y) Hineq)).
  now destruct (choice_fun (exist _ (x,y) Hineq)). }
  clearbody choice_fun_U choice_fun_V; clear choice_fun H1.
  split.
  + now apply Hausdorff_impl_T1_sep.
  + intros.
    pose proof (closed_compact _ _ H H1).
    assert (forall y:point_set X, In F y -> x <> y).
  { intros. congruence. }
    pose (cover := fun (y:point_set (SubspaceTopology F)) =>
      let (y,i):=y in inverse_image (subspace_inc F)
                         (choice_fun_V x y (H5 y i))).
    destruct (compactness_on_indexed_covers _ _ cover H4) as [subcover].
    * destruct a as [y i].
      apply subspace_inc_continuous, H2.
    * apply Extensionality_Ensembles; split; red; intros y ?.
      ** constructor.
      ** exists y.
         destruct y as [y i].
         simpl.
         constructor.
         simpl.
         apply H2.
    * destruct H6.
      exists (IndexedIntersection
        (fun y:{y:point_set (SubspaceTopology F) | In subcover y} =>
          let (y,_):=y in let (y,i):=y in choice_fun_U x y (H5 y i))).
      exists (IndexedUnion
        (fun y:{y:point_set (SubspaceTopology F) | In subcover y} =>
          let (y,_):=y in let (y,i):=y in choice_fun_V x y (H5 y i))).
      repeat split.
      ** apply open_finite_indexed_intersection.
         *** now apply Finite_ens_type.
         *** destruct a as [[y]].
             apply H2.
      ** apply open_indexed_union.
         destruct a as [[y]].
         apply H2.
      ** destruct a as [[y]].
         apply H2.
      ** red; intros y ?.
         assert (In (IndexedUnion
           (fun y:{y:point_set (SubspaceTopology F) | In subcover y} =>
             cover (proj1_sig y))) (exist _ y H8)).
       { rewrite H7. constructor. }
         remember (exist (In F) y H8) as ysig.
         destruct H9 as [[y']].
         rewrite Heqysig in H9; clear x0 Heqysig.
         simpl in H9.
         destruct y' as [y'].
         simpl in H9.
         destruct H9.
         simpl in H9.
         now exists (exist _ (exist _ y' i0) i).
      ** apply Extensionality_Ensembles; split; auto with sets; red; intros y ?.
         destruct H8.
         destruct H8.
         destruct H9.
         pose proof (H8 a).
         destruct a as [[y]].
         replace (@Empty_set X) with
           (Intersection (choice_fun_U x y (H5 y i))
                         (choice_fun_V x y (H5 y i))).
         *** now constructor.
         *** apply H2. }
destruct (choice (fun (xF:{p:X * Ensemble X |
                        let (x,F):=p in closed F /\ ~ In F x})
  (UV:Ensemble X * Ensemble X) =>
  let (p,i):=xF in let (x,F):=p in
  let (U,V):=UV in
  open U /\ open V /\ In U x /\ Included F V /\
  Intersection U V = Empty_set)) as [choice_fun].
- destruct x as [[x F] []].
  destruct H1.
  destruct (H4 x F H2 H3) as [U [V]].
  now exists (U, V).
- pose (choice_fun_U := fun (x:X) (F:Ensemble X)
    (HC:closed F) (Hni:~ In F x) =>
    fst (choice_fun (exist _ (x,F) (conj HC Hni)))).
  pose (choice_fun_V := fun (x:X) (F:Ensemble X)
    (HC:closed F) (Hni:~ In F x) =>
    snd (choice_fun (exist _ (x,F) (conj HC Hni)))).
  assert (forall (x:X) (F:Ensemble X)
    (HC:closed F) (Hni:~ In F x),
    open (choice_fun_U x F HC Hni) /\
    open (choice_fun_V x F HC Hni) /\
    In (choice_fun_U x F HC Hni) x /\
    Included F (choice_fun_V x F HC Hni) /\
    Intersection (choice_fun_U x F HC Hni) (choice_fun_V x F HC Hni) =
       Empty_set).
  + intros.
    pose proof (H2 (exist _ (x,F) (conj HC Hni))).
    unfold choice_fun_U, choice_fun_V.
    now destruct (choice_fun (exist _ (x,F) (conj HC Hni))).
  + clearbody choice_fun_U choice_fun_V; clear choice_fun H2.
    split.
    * apply H1.
    * intros.
      pose proof (closed_compact _ _ H H2).
      assert (forall x:point_set X, In F x -> ~ In G x).
    { intros.
      intro.
      absurd (In Empty_set x).
      - easy.
      - now rewrite <- H5. }

      pose (cover := fun x:point_set (SubspaceTopology F) =>
        let (x,i):=x in inverse_image (subspace_inc F)
                         (choice_fun_U x G H4 (H7 x i))).
      destruct (compactness_on_indexed_covers _ _ cover H6) as [subcover].
      ** destruct a as [x i].
         apply subspace_inc_continuous, H3.
      ** apply Extensionality_Ensembles; split; red; intros.
         *** constructor.
         *** exists x.
             destruct x.
             simpl cover.
             constructor.
             simpl.
             apply H3.
      ** destruct H8.
         exists (IndexedUnion
           (fun x:{x:point_set (SubspaceTopology F) | In subcover x} =>
              let (x,i):=proj1_sig x in choice_fun_U x G H4 (H7 x i))).
         exists (IndexedIntersection
           (fun x:{x:point_set (SubspaceTopology F) | In subcover x} =>
              let (x,i):=proj1_sig x in choice_fun_V x G H4 (H7 x i))).
         repeat split.
         *** apply open_indexed_union.
             destruct a as [[x]].
             simpl.
             apply H3.
         *** apply open_finite_indexed_intersection.
             **** apply Finite_ens_type; trivial.
             **** destruct a as [[x]].
                  simpl.
                  apply H3.
         *** intros x ?.
             assert (In (@Full_set (point_set (SubspaceTopology F))) (exist _ x H10))
               by constructor.
             rewrite <- H9 in H11.
             remember (exist _ x H10) as xsig.
             destruct H11.
             destruct a as [x'].
             destruct x' as [x'].
             rewrite Heqxsig in H11; clear x0 Heqxsig.
             simpl in H11.
             destruct H11.
             now exists (exist _ (exist _ x' i0) i).
         *** destruct a as [x'].
             simpl.
             destruct x' as [x'].
             assert (Included G (choice_fun_V x' G H4 (H7 x' i0))) by apply H3.
             auto.
         *** extensionality_ensembles.
             specialize H11 with a.
             destruct a as [[x']].
             simpl in H11, H10.
             replace (@Empty_set X) with (Intersection
               (choice_fun_U x' G H4 (H7 x' i))
               (choice_fun_V x' G H4 (H7 x' i))) by apply H3.
             now constructor.
Qed.

Lemma topological_property_compact :
  topological_property compact.
Proof.
  intros X Y f [g Hcont_f Hcont_g Hgf Hfg] Hcomp F H eq.
  destruct (Hcomp (inverse_image (inverse_image g) F)) as [F' [H1 [H2 H3]]].
  - intros.
    rewrite <- (inverse_image_id_comp Hgf).
    apply Hcont_f, H.
    now destruct H0.
  - erewrite <- inverse_image_full,
             <- (inverse_image_id_comp Hgf (FamilyUnion _)).
    f_equal.
    now rewrite <- (inverse_image_family_union F Hgf),
               inverse_image_id_comp.
  - exists (inverse_image (inverse_image f) F').
    split; [|split].
    + apply inverse_image_finite; trivial.
      intro y.
      exists (g y).
      now rewrite Hfg.
    + intros S [Hin].
      destruct (H2 _ Hin) as [H0].
      now rewrite inverse_image_id_comp in H0.
    + rewrite <- (inverse_image_family_union _ Hfg Hgf), H3.
      apply inverse_image_full.
Qed.

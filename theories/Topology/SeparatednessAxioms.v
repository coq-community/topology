From Coq Require Import
  Morphisms
  Program.Subset
  RelationClasses.
From Topology Require Export
  Nets.
From Topology Require Import
  Homeomorphisms
  SubspaceTopology.

Definition T0_sep (X:TopologicalSpace) : Prop :=
  forall x y:X, x <> y ->
  (exists U:Ensemble X, open U /\ In U x /\ ~ In U y) \/
  (exists U:Ensemble X, open U /\ ~ In U x /\ In U y).

Lemma topological_property_T0_sep : topological_property T0_sep.
Proof.
  apply Build_topological_property.
  intros X Y f Hcont_f g Hcont_g Hfg Hsep x y neq.
  destruct (Hsep (g x) (g y)) as [[U [Hopen [Hin H']]] | [U [Hopen [H' Hin]]]];
  [ shelve | left | right ];
    exists (inverse_image g U);
    repeat split;
    try apply Hcont_g;
    assumption + (intros [?]; contradiction).
  Unshelve.
  intro contra.
  eapply f_equal in contra.
  rewrite (proj2 Hfg), (proj2 Hfg) in contra.
  contradiction.
Qed.

(** the [T0_sep] property is hereditary *)
Lemma T0_sep_Subspace {X : TopologicalSpace} (A : Ensemble X) :
  T0_sep X -> T0_sep (SubspaceTopology A).
Proof.
  intros HX [x Hx] [y Hy] Hxy.
  specialize (HX x y) as
    [[U [HU0 [HU1 HU2]]]|[U [HU0 [HU1 HU2]]]];
    [|left|right].
  { intros ?. subst.
    destruct (PI.proof_irrelevance _ Hx Hy).
    contradiction.
  }
  all: exists (inverse_image (subspace_inc A) U);
         (split; [|split]).
  1, 4: apply subspace_inc_continuous;
    assumption.
  1, 4: constructor; simpl; assumption.
  1, 2: intros [H0]; simpl in H0; auto.
Qed.

Definition T1_sep (X:TopologicalSpace) : Prop :=
  forall x:X, closed (Singleton x).

Lemma topological_property_T1_sep : topological_property T1_sep.
Proof.
  apply Build_topological_property.
  intros X Y f Hcont_f g Hcont_g Hfg Hsep x.
  rewrite <- (proj1 (injective_inverse_image_Singleton g)).
  2: {
    apply invertible_impl_bijective.
    exists f. apply inverse_map_sym, Hfg.
  }
  apply continuous_closed.
  { apply Hcont_g. }
  apply Hsep.
Qed.

(** the [T1_sep] property is hereditary *)
Lemma T1_sep_Subspace {X : TopologicalSpace} (A : Ensemble X) :
  T1_sep X -> T1_sep (SubspaceTopology A).
Proof.
  intros HX [x Hx].
  apply subspace_closed_char.
  specialize (HX x).
  exists (Singleton x).
  split; auto.
  apply Extensionality_Ensembles; split.
  - intros y Hy.
    destruct Hy.
    constructor. simpl.
    constructor.
  - intros [y Hy] [Hy0].
    simpl in Hy0. destruct Hy0.
    destruct (PI.proof_irrelevance _ Hx Hy).
    constructor.
Qed.

Definition Hausdorff (X:TopologicalSpace) : Prop :=
  forall x y:X, x <> y ->
    exists U:Ensemble X,
    exists V:Ensemble X,
  open U /\ open V /\ In U x /\ In V y /\
  Intersection U V = Empty_set.
Definition T2_sep := Hausdorff.

Definition topological_property_Hausdorff :
  topological_property Hausdorff.
Proof.
  apply Build_topological_property.
  intros X Y f Hcont_f g Hcont_g Hfg Hhaus x y neq.
  destruct (Hhaus (g x) (g y)) as [U [V [HopenU [HopenV [HinU [HinV eq]]]]]].
  { intro contra.
    eapply f_equal in contra.
    now rewrite (proj2 Hfg), (proj2 Hfg) in contra.
  }
  exists (inverse_image g U), (inverse_image g V).
  repeat split;
    try apply Hcont_g;
    trivial.
  erewrite <- inverse_image_intersection, <- inverse_image_empty.
  now f_equal.
Qed.

(** the [Hausdorff] property is hereditary *)
Lemma Hausdorff_Subspace {X : TopologicalSpace} (A : Ensemble X) :
  Hausdorff X ->
  Hausdorff (SubspaceTopology A).
Proof.
  intros HX.
  intros [x Hx] [y Hy] H.
  specialize (HX x y) as [U [V [HU [HV [HUx [HVx HUV]]]]]].
  { intros ?. subst. apply H.
    apply subset_eq. reflexivity.
  }
  exists (inverse_image (subspace_inc _) U).
  exists (inverse_image (subspace_inc _) V).
  repeat split.
  1,2: apply subspace_inc_continuous.
  all: try assumption.
  extensionality_ensembles.
  assert (In Empty_set (subspace_inc A x0)).
  { rewrite <- HUV.
    split; assumption.
  }
  contradiction.
Qed.

Definition T3_sep (X:TopologicalSpace) : Prop :=
  T1_sep X /\
  forall (x:X) (F:Ensemble X),
  closed F -> ~ In F x -> exists U:Ensemble X,
                          exists V:Ensemble X,
        open U /\ open V /\ In U x /\ Included F V /\
        Intersection U V = Empty_set.

Lemma topological_property_T3_sep : topological_property T3_sep.
Proof.
  apply topological_property_and.
  { apply topological_property_T1_sep. }
  apply proper_sym_impl_iff.
  { typeclasses eauto. }
  intros X Y HXY H.
  destruct HXY as [f [Hcont_f [g [Hcont_g Hfg]]]].
  intros y F Hcl Hn.
  specialize (H (g y) (inverse_image f F)) as [U [V [HopenU [HopenV [HinU [Hincl eq]]]]]].
  { now apply continuous_closed. }
  { intros [contra].
    now rewrite (proj2 Hfg) in contra.
  }
  exists (inverse_image g U), (inverse_image g V).
  repeat split;
    try apply Hcont_g;
    trivial.
  - apply Hincl.
    constructor.
    now rewrite (proj2 Hfg).
  - erewrite <- inverse_image_intersection, <- inverse_image_empty.
    now f_equal.
Qed.

(** the [T3_sep] property is hereditary *)
Lemma T3_sep_Subspace {X : TopologicalSpace} (A : Ensemble X) :
  T3_sep X -> T3_sep (SubspaceTopology A).
Proof.
  intros [HX0 HX1].
  split.
  { apply T1_sep_Subspace. assumption. }
  intros [x Hx] F HF HFx.
  apply subspace_closed_char in HF as [G [HG HG0]].
  subst.
  assert (~ In G x) as HGx.
  { intros HGx. apply HFx.
    constructor. simpl.
    assumption.
  }
  clear HFx.
  specialize (HX1 x G HG HGx) as [U [V [HU [HV [HUx [HVG HUV]]]]]].
  exists (inverse_image (subspace_inc A) U),
    (inverse_image (subspace_inc A) V).
  repeat split.
  - apply subspace_inc_continuous; assumption.
  - apply subspace_inc_continuous; assumption.
  - simpl. assumption.
  - apply HVG. destruct H. assumption.
  - rewrite <- inverse_image_intersection.
    rewrite HUV.
    apply inverse_image_empty.
Qed.

Definition normal_sep (X:TopologicalSpace) : Prop :=
  T1_sep X /\
  forall (F G:Ensemble X),
  closed F -> closed G -> Intersection F G = Empty_set ->
  exists U:Ensemble X, exists V:Ensemble X,
  open U /\ open V /\ Included F U /\ Included G V /\
  Intersection U V = Empty_set.
Definition T4_sep := normal_sep.

Lemma topological_property_T4_sep : topological_property T4_sep.
Proof.
  apply topological_property_and.
  { apply topological_property_T1_sep. }
  apply proper_sym_impl_iff.
  { typeclasses eauto. }
  intros X Y HXY H.
  intros F G HF_closed HG_closed HFG.
  destruct HXY as [f [Hcont_f [g [Hcont_g Hfg]]]].
  specialize (H (inverse_image f F) (inverse_image f G))
    as [U [V [HU_open [HV_open [HFU [HGV HUV]]]]]].
  { now apply continuous_closed. }
  { now apply continuous_closed. }
  { erewrite <- inverse_image_intersection, <- inverse_image_empty.
    now f_equal.
  }
  exists (inverse_image g U), (inverse_image g V).
  repeat split;
    try apply Hcont_g;
    trivial.
  - apply HFU. constructor.
    now rewrite (proj2 Hfg).
  - apply HGV. constructor.
    now rewrite (proj2 Hfg).
  - erewrite <- inverse_image_intersection, <- inverse_image_empty.
    now f_equal.
Qed.

Lemma T1_sep_impl_T0_sep: forall X:TopologicalSpace,
  T1_sep X -> T0_sep X.
Proof.
intros.
red. intros.
left.
exists (Complement (Singleton y)).
repeat split.
- apply H.
- intro.
  destruct H1.
  now contradiction H0.
- intro.
  apply H1.
  constructor.
Qed.

Lemma Hausdorff_impl_T1_sep: forall X:TopologicalSpace,
  Hausdorff X -> T1_sep X.
Proof.
intros X H x.
replace (Singleton x) with (closure (Singleton x)).
{ apply closure_closed. }
extensionality_ensembles;
  [ | now apply closure_inflationary ].
replace x0 with x.
{ constructor. }
apply NNPP.
intro.
pose proof (H x x0 H1).
destruct H2 as [U [V [? [? [? [? ?]]]]]].
assert (In (interior (Complement (Singleton x))) x0).
{ exists V; trivial.
  constructor; split; trivial.
  red; intros.
  intro.
  destruct H8.
  eapply Noone_in_empty.
  erewrite <- H6.
  econstructor;
    eassumption. }
rewrite interior_complement in H7.
now contradiction H7.
Qed.

Lemma T3_sep_impl_Hausdorff: forall X:TopologicalSpace,
  T3_sep X -> Hausdorff X.
Proof.
intros.
destruct H.
red; intros.
pose proof (H0 x (Singleton y)).
match type of H2 with | ?A -> ?B -> ?C => assert C end.
- apply H2.
  + apply H.
  + intro.
    now destruct H3.
- destruct H3 as [U [V [? [? [? [? ?]]]]]].
  exists U, V.
  auto 6 with sets.
Qed.

Lemma normal_sep_impl_T3_sep: forall X:TopologicalSpace,
  normal_sep X -> T3_sep X.
Proof.
intros.
destruct H.
split; trivial.
intros.
pose proof (H0 (Singleton x) F).
match type of H3 with | ?A -> ?B -> ?C -> ?D => assert D end.
- apply H3; trivial.
  now extensionality_ensembles.
- destruct H4 as [U [V [? [? [? [? ?]]]]]].
  exists U, V.
  auto with sets.
Qed.

Section Hausdorff_and_nets.

Lemma Hausdorff_impl_net_limit_unique:
  forall {X:TopologicalSpace} {I:DirectedSet} (x:Net I X),
    Hausdorff X -> uniqueness (net_limit x).
Proof.
intros.
red; intros x1 x2 ? ?.
apply NNPP.
intro.
destruct (H x1 x2) as [U [V [? [? [? [? ?]]]]]]; trivial.
destruct (H0 U H3 H5) as [i].
destruct (H1 V H4 H6) as [j].
destruct (DS_join_cond i j) as [k [? ?]].
assert (In (Intersection U V) (x k)).
{ constructor.
  - now apply H8.
  - now apply H9. }
rewrite H7 in H12.
destruct H12.
Qed.

Lemma Hausdorff_impl_net_limit_is_unique_cluster_point:
  forall {X:TopologicalSpace} {I:DirectedSet} (x:Net I X)
    (x0:X), Hausdorff X -> net_limit x x0 ->
    forall y:X, net_cluster_point x y -> y = x0.
Proof.
intros.
destruct (net_cluster_point_impl_subnet_converges _ _ x y H1) as
  [J [x' [? ?]]].
- destruct (H0 Full_set).
  + apply open_full.
  + constructor.
  + now exists.
- assert (net_limit x' x0) by
    now apply subnet_limit with _ x.
  now apply Hausdorff_impl_net_limit_unique with x'.
Qed.

Lemma net_limit_is_unique_cluster_point_impl_Hausdorff:
  forall (X:TopologicalSpace),
  (forall (I:DirectedSet) (x:Net I X) (x0 y:X),
  net_limit x x0 -> net_cluster_point x y ->
  y = x0) -> Hausdorff X.
Proof.
intros.
red; intros.
assert (~ net_cluster_point (neighborhood_net _ x) y).
{ intro.
  contradiction H0.
  symmetry.
  apply H with _ (neighborhood_net _ x); trivial.
  apply neighborhood_net_limit. }
apply not_all_ex_not in H1.
destruct H1 as [V].
apply imply_to_and in H1.
destruct H1.
apply imply_to_and in H2.
destruct H2.
apply not_all_ex_not in H3.
destruct H3 as [[U]].
exists U, V.
repeat split; trivial.
extensionality_ensembles.
contradiction H3.
exists (intro_neighborhood_net_DS X x U x0 o i H4).
split; trivial.
simpl.
auto with sets.
Qed.

Lemma net_limit_uniqueness_impl_Hausdorff:
  forall X:TopologicalSpace,
  (forall (I:DirectedSet) (x:Net I X), uniqueness (net_limit x)) ->
  Hausdorff X.
Proof.
intros.
apply net_limit_is_unique_cluster_point_impl_Hausdorff.
intros.
pose proof (net_cluster_point_impl_subnet_converges _ _ _ _ H1).
destruct H2 as [J [x' [? ?]]].
- destruct (H0 Full_set).
  + apply open_full.
  + constructor.
  + now exists.
- assert (net_limit x' x0) by
    now apply subnet_limit with _ x.
  now apply H with _ x'.
Qed.

End Hausdorff_and_nets.

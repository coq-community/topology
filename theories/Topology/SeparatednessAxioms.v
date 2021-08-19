From Coq Require Import Program.Subset.
From Topology Require Export Nets.
From Topology Require Import Homeomorphisms SubspaceTopology.
From ZornsLemma Require Import EnsemblesTactics.

Class T0_space (X:TopologicalSpace) : Prop :=
  { T0_sep :
      forall x y:point_set X,
        x <> y ->
        (exists U:Ensemble (point_set X), open U /\ In U x /\ ~ In U y) \/
        (exists U:Ensemble (point_set X), open U /\ ~ In U x /\ In U y);
  }.

Lemma topological_property_T0_space : topological_property T0_space.
Proof.
  intros X Y f [g Hcont_f Hcont_g Hgf Hfg] Hsep.
  constructor. intros x y neq.
  destruct (T0_sep (g x) (g y)) as [[U [Hopen [Hin H']]] | [U [Hopen [H' Hin]]]];
  [ shelve | left | right ];
    exists (inverse_image g U);
    repeat split;
    try apply Hcont_g;
    assumption + (intros [?]; contradiction).
  Unshelve.
  intro contra.
  eapply f_equal in contra.
  rewrite Hfg, Hfg in contra.
  contradiction.
Qed.

Class T1_space (X:TopologicalSpace) : Prop :=
  { T1_sep :
      forall x:point_set X, closed (Singleton x);
  }.

Lemma topological_property_T1_space : topological_property T1_space.
Proof.
  intros X Y f [g Hcont_f Hcont_g Hgf Hfg] Hsep.
  constructor. intros x.
  replace (Singleton x) with (inverse_image g (Singleton (g x))).
  - red.
    rewrite <- inverse_image_complement.
    apply Hcont_g.
    apply Hsep.
  - extensionality_ensembles_inv.
    + eapply f_equal in H1.
      rewrite Hfg, Hfg in H1.
      subst.
      constructor.
    + subst.
      constructor.
      constructor.
Qed.

Class Hausdorff (X:TopologicalSpace) : Prop :=
  { hausdorff :
      forall x y:point_set X,
        x <> y ->
        exists U:Ensemble (point_set X),
        exists V:Ensemble (point_set X),
          open U /\ open V /\ In U x /\ In V y /\
          Intersection U V = Empty_set;
  }.
Definition T2_space := Hausdorff.

Definition topological_property_Hausdorff :
  topological_property Hausdorff.
Proof.
  intros X Y f [g Hcont_f Hcont_g Hgf Hfg] Hhaus.
  constructor. intros x y neq.
  destruct (hausdorff (g x) (g y)) as [U [V [HopenU [HopenV [HinU [HinV eq]]]]]].
  - intro contra.
    eapply f_equal in contra.
    now rewrite Hfg, Hfg in contra.
  - exists (inverse_image g U), (inverse_image g V).
    repeat split;
      try apply Hcont_g;
      trivial.
    erewrite <- inverse_image_intersection, <- inverse_image_empty.
    now f_equal.
Qed.

Class T3_space (X:TopologicalSpace) : Prop :=
  { T3_space_is_T1_space :> T1_space X;
    T3_sep :
      forall (x:point_set X) (F:Ensemble (point_set X)),
        closed F -> ~ In F x -> exists U:Ensemble (point_set X),
          exists V:Ensemble (point_set X),
            open U /\ open V /\ In U x /\ Included F V /\
            Intersection U V = Empty_set;
  }.

Lemma topological_property_T3_space : topological_property T3_space.
Proof.
  intros X Y f Hf [HT1 H].
  split.
  - eapply topological_property_T1_space.
    + exact Hf.
    + assumption.
  - destruct Hf as [g Hcont_f Hcont_g Hgf Hfg].
    intros y F Hcl Hn.
    destruct (H (g y) (inverse_image f F)) as [U [V [HopenU [HopenV [HinU [Hincl eq]]]]]].
    + red.
      rewrite <- inverse_image_complement.
      now apply Hcont_f.
    + intros [contra].
      now rewrite Hfg in contra.
    + exists (inverse_image g U), (inverse_image g V).
      repeat split;
        try apply Hcont_g;
        trivial.
     * apply Hincl.
       constructor.
       now rewrite Hfg.
     * erewrite <- inverse_image_intersection, <- inverse_image_empty.
       now f_equal.
Qed.

Class normal_space (X:TopologicalSpace) : Prop :=
  { normal_space_is_T1_space :> T1_space X;
    normal_sep :
      forall (F G:Ensemble (point_set X)),
        closed F -> closed G -> Intersection F G = Empty_set ->
        exists U:Ensemble (point_set X), exists V:Ensemble (point_set X),
            open U /\ open V /\ Included F U /\ Included G V /\
            Intersection U V = Empty_set;
  }.
Definition T4_space := normal_space.

Lemma topological_property_normal_space : topological_property normal_space.
Proof.
  intros X Y f Hf [HT1 H].
  split.
  - eapply topological_property_T1_space.
    + exact Hf.
    + assumption.
  - destruct Hf as [g Hcont_f Hcont_g Hgf Hfg].
    intros F G HclF HclG Hn.
    destruct (H (inverse_image f F) (inverse_image f G))
      as [U [V [HopenU [HopenV [HinclU [HinclV eq]]]]]].
    + now apply continuous_closed.
    + now apply continuous_closed.
    + rewrite <- inverse_image_intersection.
      rewrite Hn. apply inverse_image_empty.
    + exists (inverse_image g U), (inverse_image g V).
      repeat split;
        try apply Hcont_g;
        trivial.
      * apply HinclU.
        constructor.
        now rewrite Hfg.
      * apply HinclV.
        constructor.
        now rewrite Hfg.
      * erewrite <- inverse_image_intersection, <- inverse_image_empty.
        now f_equal.
Qed.

Instance T1_space_is_T0_space {X} `(H:T1_space X) : T0_space X.
Proof.
intros.
constructor. intros.
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

Instance Hausdorff_is_T1_space {X:TopologicalSpace} `(H:Hausdorff X) : T1_space X.
Proof.
constructor. intros x.
replace (Singleton x) with (closure (Singleton x)).
{ apply closure_closed. }
extensionality_ensembles;
  [ | now apply closure_inflationary ].
replace x0 with x.
{ constructor. }
apply NNPP.
intro.
pose proof (hausdorff x x0 H1).
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

Instance T3_space_is_Hausdorff {X:TopologicalSpace} `(T3_space X) : Hausdorff X.
Proof.
constructor. intros.
pose proof (T3_sep x (Singleton y)).
match type of H1 with | ?A -> ?B -> ?C => assert C end.
- apply H1.
  + apply H.
  + intro.
    now destruct H2.
- destruct H2 as [U [V [? [? [? [? ?]]]]]].
  exists U, V.
  auto 6 with sets.
Qed.

Instance normal_space_is_T3_space {X:TopologicalSpace} `(normal_space X) : T3_space X.
Proof.
split; [apply H|].
intros.
pose proof (normal_sep (Singleton x) F).
match type of H2 with | ?A -> ?B -> ?C -> ?D => assert D end.
- apply H2; trivial.
  + apply T1_sep.
  + extensionality_ensembles_inv. subst. contradiction.
- destruct H3 as [U [V [? [? [? [? ?]]]]]].
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
destruct (hausdorff x1 x2) as [U [V [? [? [? [? ?]]]]]]; trivial.
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
    (x0:point_set X), Hausdorff X -> net_limit x x0 ->
    forall y:point_set X, net_cluster_point x y -> y = x0.
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
  (forall (I:DirectedSet) (x:Net I X) (x0 y:point_set X),
  net_limit x x0 -> net_cluster_point x y ->
  y = x0) -> Hausdorff X.
Proof.
intros.
constructor; intros.
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
extensionality_ensembles_inv.
contradiction H3.
exists (intro_neighborhood_net_DS X x U x0 o i H5).
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

Lemma Hausdorff_Subspace {X : TopologicalSpace} (A : Ensemble X) :
  Hausdorff X ->
  Hausdorff (SubspaceTopology A).
Proof.
  intros HX.
  constructor.
  intros [x Hx] [y Hy] H.
  specialize (hausdorff x y) as [U [V [HU [HV [HUx [HVx HUV]]]]]].
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

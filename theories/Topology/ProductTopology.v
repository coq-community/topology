From Topology Require Export TopologicalSpaces WeakTopology FilterLimits Compactness.
From Coq Require Import FunctionalExtensionality.
From ZornsLemma Require Import DependentTypeChoice EnsembleProduct FiniteIntersections.

Section product_topology.

Variable A:Type.
Variable X:forall a:A, TopologicalSpace.

Definition product_space_point_set : Type :=
  forall a:A, X a.
Definition product_space_proj (a:A) :
  product_space_point_set -> X a :=
  fun (x:product_space_point_set) => x a.

Definition ProductTopology : TopologicalSpace :=
  WeakTopology product_space_proj.

Lemma product_space_proj_continuous: forall a:A,
  continuous (product_space_proj a) (X:=ProductTopology).
Proof.
apply weak_topology_makes_continuous_funcs.
Qed.

Lemma product_net_limit: forall (I:DirectedSet)
  (x:Net I ProductTopology) (x0:ProductTopology),
  inhabited (DS_set I) ->
  (forall a:A, net_limit (fun i:DS_set I => x i a) (x0 a)) ->
  net_limit x x0.
Proof.
intros.
now apply net_limit_in_projections_impl_net_limit_in_weak_topology.
Qed.

Lemma product_filter_limit:
  forall (F:Filter ProductTopology)
    (x0:ProductTopology),
  (forall a:A, filter_limit (filter_direct_image
                     (product_space_proj a) F) (x0 a)) ->
  filter_limit F x0.
Proof.
intros.
assert (subbasis
  (weak_topology_subbasis product_space_proj)
  (X:=ProductTopology)) by
  apply Build_TopologicalSpace_from_subbasis_subbasis.
red. intros.
red. intros U ?.
destruct H1.
destruct H1 as [U' []].
cut (In (filter_family F) U').
- intro.
  apply filter_upward_closed with U'; trivial.
- destruct H1.
  destruct (subbasis_cover _ _ H0 _ _ H3 H1) as
    [B [? [V [? []]]]].
  cut (In (filter_family F) (IndexedIntersection V)).
  + intro.
    eapply filter_upward_closed;
      eassumption.
  + apply filter_finite_indexed_intersection;
      trivial.
    intro b.
    pose proof (H5 b).
    inversion H8.
    apply H.
    constructor.
    apply open_neighborhood_is_neighborhood.
    constructor; trivial.
    destruct H6.
    pose proof (H6 b).
    rewrite <- H9 in H11.
    now destruct H11.
Qed.

Theorem TychonoffProductTheorem:
  (forall a:A, compact (X a)) -> compact ProductTopology.
Proof.
intro.
apply ultrafilter_limit_impl_compact.
intros.
destruct (choice_on_dependent_type (fun (a:A) (x:X a) =>
  filter_limit (filter_direct_image (product_space_proj a) U) x))
  as [choice_fun].
- intro.
  destruct (compact_impl_filter_cluster_point _ (H a)
    (filter_direct_image (product_space_proj a) U)) as [xa].
  exists xa.
  apply ultrafilter_cluster_point_is_limit; trivial.
  red. intros.
  now destruct (H0 (inverse_image (product_space_proj a) S));
    [left | right];
    constructor;
    [ | rewrite inverse_image_complement ].
- exists choice_fun.
  now apply product_filter_limit.
Qed.

End product_topology.

Arguments ProductTopology {A}.
Arguments product_space_proj {A} {X}.

Lemma product_map_continuous: forall {A:Type}
  (X:TopologicalSpace) (Y:A->TopologicalSpace)
  (f:forall a:A, X -> Y a) (x:X),
  (forall a:A, continuous_at (f a) x) ->
  continuous_at (fun x:X => (fun a:A => f a x)) x
    (Y:=ProductTopology Y).
Proof.
intros.
apply func_preserving_net_limits_is_continuous.
intros.
apply product_net_limit.
- destruct (H0 Full_set) as [i].
  + apply open_full.
  + constructor.
  + now exists.
- intros.
  now apply continuous_func_preserves_net_limits.
Qed.

Section product_topology2.

(* we provide a version of the product topology on [X] and [Y]
   whose underlying set is [point_set X * point_set Y], for
   more convenience as compared with the general definition *)
Variable X Y:TopologicalSpace.

Inductive twoT := | twoT_1 | twoT_2.
Let prod2_fun (i:twoT) := match i with
  | twoT_1 => X | twoT_2 => Y end.
Let prod2 := ProductTopology prod2_fun.

Let prod2_conv1 (p:prod2) : X * Y :=
  (p twoT_1, p twoT_2).
Let prod2_conv2 (p : X * Y) : prod2 :=
  let (x,y):=p in fun i:twoT => match i with
    | twoT_1 => x | twoT_2 => y
  end.

Lemma prod2_comp1: forall p:prod2,
  prod2_conv2 (prod2_conv1 p) = p.
Proof.
intros.
extensionality i.
now destruct i.
Qed.

Lemma prod2_comp2: forall p:X * Y,
  prod2_conv1 (prod2_conv2 p) = p.
Proof.
now intros [? ?].
Qed.

Let prod2_proj := fun i:twoT =>
  match i return (X * Y -> (prod2_fun i)) with
  | twoT_1 => @fst X Y
  | twoT_2 => @snd X Y
  end.

Definition ProductTopology2 : TopologicalSpace :=
  WeakTopology prod2_proj.

Lemma prod2_conv1_cont: continuous prod2_conv1 (Y:=ProductTopology2).
Proof.
apply pointwise_continuity.
intros p.
apply func_preserving_net_limits_is_continuous.
intros.
apply net_limit_in_projections_impl_net_limit_in_weak_topology.
- destruct (H Full_set).
  + apply open_full.
  + constructor.
  + exact (inhabits x0).
- destruct a;
    simpl.
  + now apply net_limit_in_weak_topology_impl_net_limit_in_projections
      with (a:=twoT_1) in H.
  + now apply net_limit_in_weak_topology_impl_net_limit_in_projections
      with (a:=twoT_2) in H.
Qed.

Lemma prod2_conv2_cont: continuous prod2_conv2 (X:=ProductTopology2).
Proof.
apply pointwise_continuity.
destruct x as [x y].
apply func_preserving_net_limits_is_continuous.
intros.
apply net_limit_in_projections_impl_net_limit_in_weak_topology.
- destruct (H Full_set).
  + apply open_full.
  + constructor.
  + exact (inhabits x1).
- destruct a.
  + unfold product_space_proj.
    simpl.
    replace (fun i => prod2_conv2 (x0 i) twoT_1) with
      (fun i => fst (x0 i)).
    * now apply net_limit_in_weak_topology_impl_net_limit_in_projections
        with (a:=twoT_1) in H.
    * extensionality i.
      now destruct (x0 i).
  + unfold product_space_proj.
    simpl.
    replace (fun i:DS_set I => prod2_conv2 (x0 i) twoT_2) with
      (fun i:DS_set I => snd (x0 i)).
    * now apply net_limit_in_weak_topology_impl_net_limit_in_projections
        with (a:=twoT_2) in H.
    * extensionality i.
      now destruct (x0 i).
Qed.

Lemma product2_fst_continuous:
  continuous (@fst X Y)
    (X:=ProductTopology2).
Proof.
exact (weak_topology_makes_continuous_funcs
  _ _ _ prod2_proj twoT_1).
Qed.

Lemma product2_snd_continuous:
  continuous (@snd X Y)
    (X:=ProductTopology2).
Proof.
exact (weak_topology_makes_continuous_funcs
  _ _ _ prod2_proj twoT_2).
Qed.

Lemma product2_map_continuous_at: forall (W:TopologicalSpace)
  (f:W -> X) (g:W -> Y) (w:W),
  continuous_at f w -> continuous_at g w ->
  continuous_at (fun w:W => (f w, g w)) w (Y:=ProductTopology2).
Proof.
intros.
replace (fun w:W => (f w, g w)) with
  (fun w:W => prod2_conv1
             (fun i:twoT =>
                match i with
                | twoT_1 => f w
                | twoT_2 => g w end)).
- apply (@continuous_composition_at W prod2 ProductTopology2
    prod2_conv1
    (fun w:W =>
       fun i:twoT => match i with
           | twoT_1 => f w | twoT_2 => g w end)).
  + apply continuous_func_continuous_everywhere.
    apply prod2_conv1_cont.
  + apply product_map_continuous.
    now destruct a.
- now extensionality w0.
Qed.

Corollary product2_map_continuous: forall (W:TopologicalSpace)
  (f:W -> X) (g:W -> Y),
  continuous f -> continuous g ->
  continuous (fun w:W => (f w, g w))
  (Y:=ProductTopology2).
Proof.
  intros.
  apply pointwise_continuity.
  intros.
  apply product2_map_continuous_at.
  - apply continuous_func_continuous_everywhere.
    assumption.
  - apply continuous_func_continuous_everywhere.
    assumption.
Qed.

Inductive ProductTopology2_basis :
  Family ProductTopology2 :=
| intro_product2_basis_elt:
  forall (U:Ensemble X)
         (V:Ensemble Y),
  open U -> open V ->
  In ProductTopology2_basis (EnsembleProduct U V).

Lemma ProductTopology2_basis_is_basis:
  open_basis ProductTopology2_basis.
Proof.
assert (open_basis (finite_intersections (weak_topology_subbasis prod2_proj))
  (X:=ProductTopology2)) by apply
  Build_TopologicalSpace_from_open_basis_basis.
apply eq_ind with (1:=H).
apply Extensionality_Ensembles; split; red; intros U ?.
- induction H0.
  + rewrite <- EnsembleProduct_Full.
    constructor; apply open_full.
  + destruct H0.
    destruct a.
    * simpl.
      rewrite inverse_image_fst.
      constructor; auto with topology.
    * simpl.
      rewrite inverse_image_snd.
      constructor; auto with topology.
  + destruct IHfinite_intersections as [U1 V1].
    destruct IHfinite_intersections0 as [U2 V2].
    rewrite EnsembleProduct_Intersection.
    constructor; auto with topology.
- destruct H0.
  rewrite EnsembleProduct_proj.
  constructor 3.
  + constructor.
    replace (@fst X Y) with (prod2_proj twoT_1); auto.
    constructor. assumption.
  + constructor.
    replace (@snd X Y) with (prod2_proj twoT_2); auto.
    constructor. assumption.
Qed.

End product_topology2.

Section two_arg_convenience_results.

Variable X Y Z:TopologicalSpace.
Variable f:X -> Y -> Z.

Definition continuous_2arg :=
  continuous (fun p:X * Y =>
                f (fst p) (snd p))
  (X:=ProductTopology2 X Y).
Definition continuous_at_2arg (x:X) (y:Y) :=
  continuous_at (fun p:X * Y =>
                 f (fst p) (snd p))  (x, y)
  (X:=ProductTopology2 X Y).

Lemma continuous_2arg_func_continuous_everywhere:
  continuous_2arg -> forall (x:X) (y:Y),
                       continuous_at_2arg x y.
Proof.
intros.
now apply continuous_func_continuous_everywhere.
Qed.

Lemma pointwise_continuity_2arg:
  (forall (x:X) (y:Y),
   continuous_at_2arg x y) -> continuous_2arg.
Proof.
intros.
apply pointwise_continuity.
intros [? ?].
apply H.
Qed.

End two_arg_convenience_results.

Arguments continuous_2arg {X} {Y} {Z}.
Arguments continuous_at_2arg {X} {Y} {Z}.

Lemma continuous_composition_at_2arg:
  forall (W X Y Z:TopologicalSpace)
    (f:X -> Y -> Z) (g:W -> X) (h:W -> Y)
    (w:W),
  continuous_at_2arg f (g w) (h w) ->
  continuous_at g w -> continuous_at h w ->
  continuous_at (fun w:W => f (g w) (h w)) w.
Proof.
intros.
red in H.
apply (continuous_composition_at
  (fun p:ProductTopology2 X Y =>
      f (fst p) (snd p))
  (fun w:W => (g w, h w))); trivial.
now apply product2_map_continuous_at.
Qed.

Corollary continuous_composition_2arg:
  forall {U X Y Z : TopologicalSpace} (f : U -> X) (g : U -> Y) (h : X -> Y -> Z),
    continuous f -> continuous g -> continuous_2arg h ->
    continuous (fun p => h (f p) (g p)).
Proof.
  intros.
  apply pointwise_continuity.
  intros.
  apply continuous_composition_at_2arg.
  - apply continuous_2arg_func_continuous_everywhere.
    assumption.
  - apply continuous_func_continuous_everywhere.
    assumption.
  - apply continuous_func_continuous_everywhere.
    assumption.
Qed.

Lemma EnsembleProduct_open {X Y : TopologicalSpace} (U : Ensemble X) (V : Ensemble Y) :
open U -> open V -> @open (@ProductTopology2 X Y) (EnsembleProduct U V).
Proof.
intros.
apply ProductTopology2_basis_is_basis.
constructor; assumption.
Qed.

Instance Hausdorff_ProductTopology2 {X Y : TopologicalSpace} :
  Hausdorff X -> Hausdorff Y ->
  Hausdorff (ProductTopology2 X Y).
Proof.
  intros HX HY.
  constructor.
  intros [x0 y0] [x1 y1] Hxy.
  pose proof (hausdorff x0 x1) as Hxx.
  pose proof (hausdorff y0 y1) as Hyy.
  (* Is there some "symmetry" that can be used, so the proof doesn't
     contain redundant parts? *)
  destruct (classic (x0 = x1)) as [|Hx].
  { subst.
    assert (y0 <> y1) as Hy by congruence.
    clear Hxy.
    specialize (Hyy Hy) as [U [V [HU [HV [HU0 [HV0 HUV]]]]]].
    exists (EnsembleProduct Full_set U), (EnsembleProduct Full_set V).
    repeat split; auto using EnsembleProduct_open, open_full.
    simpl.
    rewrite EnsembleProduct_Intersection.
    rewrite Powerset_facts.Intersection_Full_set.
    rewrite HUV.
    apply EnsembleProduct_Empty_r.
  }
  clear Hxy.
  specialize (Hxx Hx) as [U [V [HU [HV [HU0 [HV0 HUV]]]]]].
  exists (EnsembleProduct U Full_set), (EnsembleProduct V Full_set).
  repeat split; auto using EnsembleProduct_open, open_full.
  simpl.
  rewrite EnsembleProduct_Intersection.
  rewrite Powerset_facts.Intersection_Full_set.
  rewrite HUV.
  apply EnsembleProduct_Empty_l.
Qed.

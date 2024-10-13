From ZornsLemma Require Export
  Relation_Definitions_Implicit.
From ZornsLemma Require Import
  EnsemblesTactics
  Finite_sets.
From Topology Require Export
  Compactness
  SeparatednessAxioms
  Subbases.

(** ** Order theory *)
Lemma order_flip {X : Type} (R : relation X) :
  order R -> order (flip R).
Proof.
  intros HR. split; unfold flip.
  - intros ?; apply HR.
  - intros ? ? ? ? ?.
    apply (ord_trans HR z y x); assumption.
  - intros ? ? ? ?.
    apply (ord_antisym HR x y); assumption.
Qed.

(* a finite set in a total order is empty or has a least element. *)
Lemma order_total_finite_minimal_ens {X : Type} (R : relation X)
  (HR : order R) (HR_total : forall x y, R x y \/ R y x)
  (B : Ensemble X) (HBfin : Finite B) :
  B = Empty_set \/
    exists b : X, In B b /\ forall b0 : X, In B b0 -> R b b0.
Proof.
  induction HBfin.
  { left. reflexivity. }
  destruct IHHBfin as [|IHHBfin].
  { subst A. rewrite !Empty_set_zero'.
    right. exists x. split.
    { constructor. }
    intros b0 Hb0. destruct Hb0.
    apply (ord_refl HR x).
  }
  destruct IHHBfin as [b0 [Hb0 Hb1]].
  right. specialize (HR_total x b0) as [|].
  - exists x. split.
    { right; constructor. }
    intros y Hy. destruct Hy as [y Hy|].
    + specialize (Hb1 y Hy).
      apply (ord_trans HR _ b0); assumption.
    + destruct H1. apply (ord_refl HR).
  - exists b0. split.
    { left; assumption. }
    intros y Hy. destruct Hy as [y Hy|].
    + apply (Hb1 y Hy).
    + destruct H1. assumption.
Qed.

(** * Order Topology *)
Section OrderTopology.

Context {X:Type}.
Variable R:relation X.
Hypothesis R_ord: order R.

Definition lower_open_ray (x : X) : Ensemble X :=
  [ y : X | R y x /\ y <> x ].

Definition upper_open_ray (x : X) : Ensemble X :=
  [ y : X | R x y /\ y <> x ].

Inductive order_topology_subbasis : Family X :=
  | intro_lower_ray: forall x:X,
    In order_topology_subbasis (lower_open_ray x)
  | intro_upper_ray: forall x:X,
    In order_topology_subbasis (upper_open_ray x).

Definition OrderTopology : TopologicalSpace :=
  Build_TopologicalSpace_from_subbasis X order_topology_subbasis.

Lemma lower_upper_open_ray_disjoint (x : X) :
  Disjoint (lower_open_ray x) (upper_open_ray x).
Proof.
  constructor. intros y Hy.
  destruct Hy as [y [[Hy1 Hy2]] [[Hy3 Hy4]]].
  pose proof (ord_antisym R_ord y x Hy1 Hy3).
  auto.
Qed.

End OrderTopology.

(** The topology of [X] coincides with the order-topology defined
  by [R]. *)
Definition orders_top (X : TopologicalSpace) (R : relation X) : Prop :=
  subbasis (order_topology_subbasis R).

Fact OrderTopology_orders_top {X : Type} (R : relation X) :
  orders_top (OrderTopology R) R.
Proof.
  apply Build_TopologicalSpace_from_subbasis_subbasis.
Qed.

(** The relation [flip R] induces the same topology *)
Lemma order_topology_subbasis_flip {X : Type} (R : relation X) :
  order_topology_subbasis (flip R) =
    order_topology_subbasis R.
Proof.
  apply Extensionality_Ensembles; split.
  - intros I HI. destruct HI as [x|x]; constructor.
  - intros I HI. destruct HI as [x|x].
    + apply (intro_upper_ray (flip R)).
    + apply (intro_lower_ray (flip R)).
Qed.

Corollary orders_top_flip (X : TopologicalSpace) (R : relation X) :
  orders_top X R -> orders_top X (flip R).
Proof.
  unfold orders_top.
  rewrite order_topology_subbasis_flip.
  tauto.
Qed.

Section OrderTopology.
Context {X : TopologicalSpace}
  {R : relation X} (R_ord : order R) (HR : orders_top X R).

Lemma lower_open_ray_open (x : X) :
  open (lower_open_ray R x).
Proof.
  eapply subbasis_elements.
  1: apply HR.
  constructor.
Qed.

Lemma upper_open_ray_open (x : X) :
  open (upper_open_ray R x).
Proof.
  eapply subbasis_elements.
  1: apply HR.
  constructor.
Qed.

Section if_total_order.

Hypothesis R_total: forall x y:X, R x y \/ R y x.

Lemma lower_closed_ray_closed: forall x:X,
  closed [ y:X | R y x ].
Proof.
intro.
red.
match goal with |- open ?U => replace U with (interior U) end.
{ apply interior_open. }
apply Extensionality_Ensembles; split.
{ apply interior_deflationary. }
intros y ?.
red in H.
red in H.
assert (R x y).
{ destruct (R_total x y); trivial.
  now contradiction H. }
exists (upper_open_ray R x);
  constructor; split; trivial.
- apply upper_open_ray_open.
- red. intros z ?.
  destruct H1.
  destruct H1.
  intro.
  destruct H3.
  contradiction H2.
  now apply (ord_antisym R_ord).
- intro.
  contradiction H.
  constructor.
  now subst.
Qed.

Lemma upper_closed_ray_closed: forall x:X,
  closed [y:X | R x y].
Proof.
intro.
red.
match goal with |- open ?U => replace U with (interior U) end.
{ apply interior_open. }
apply Extensionality_Ensembles; split.
{ apply interior_deflationary. }
intros y ?.
red in H.
red in H.
assert (R y x).
{ destruct (R_total x y); trivial.
  now contradiction H. }
exists (lower_open_ray R x);
  constructor; split; trivial.
- apply lower_open_ray_open.
- red; intros z ?.
  destruct H1.
  destruct H1.
  intro.
  destruct H3.
  contradiction H2.
  now apply (ord_antisym R_ord).
- intro.
  contradiction H.
  constructor.
  now subst.
Qed.

Lemma order_topology_Hausdorff: Hausdorff X.
Proof.
red.
match goal with |- forall x y : point_set X, ?P =>
  cut (forall x y: X, R x y -> P)
end; intros.
- destruct (R_total x y).
  { exact (H x y H1 H0). }
  assert (y <> x) by auto.
  destruct (H y x H1 H2) as [V [U [? [? [? []]]]]].
  exists U, V.
  repeat split; trivial.
  transitivity (Intersection V U); trivial.
  now extensionality_ensembles.
- destruct (classic (exists z:X, R x z /\ R z y /\ z <> x /\ z <> y)).
  + destruct H1 as [z [? [? []]]].
    exists (lower_open_ray R z), (upper_open_ray R z).
    repeat split; auto.
    * apply lower_open_ray_open.
    * apply upper_open_ray_open.
    * apply Disjoint_Intersection.
      apply lower_upper_open_ray_disjoint, R_ord.
  + exists (lower_open_ray R y), (upper_open_ray R x).
    repeat split; auto.
    * apply lower_open_ray_open.
    * apply upper_open_ray_open.
    * extensionality_ensembles.
      destruct H2, H3.
      contradiction H1.
      exists x0.
      now repeat split.
Qed.

End if_total_order.

End OrderTopology.

(** ** Extreme Value Theorem *)
(** Every compact set in a total order has a minimal element.
  The approach is taken from Munkres, Theorem 27.4 *)
Lemma extreme_value_theorem_ens_lower {X : TopologicalSpace} (R : relation X)
  (A : Ensemble X) (HR : order R) (HR_total : forall x y, R x y \/ R y x) :
  orders_top X R -> Inhabited A -> compact (SubspaceTopology A) ->
  exists c : X, In A c /\ forall x : X, In A x -> R c x.
Proof.
  intros HX HA_inh HA.
  rewrite compact_SubspaceTopology_char in HA.
  (* [A] is only covered by those open rays, iff it has no minimal element. *)
  specialize (HA (Im A (upper_open_ray R))).
  unshelve epose proof (HA _) as HA.
  { intros U HU. apply Im_inv in HU. destruct HU as [a [Ha HU]];
      subst U. apply upper_open_ray_open, HX.
  }
  clear HX.
  (* assume [A] has no minimal element *)
  apply NNPP; intros Hc.
  (* use that to prove the assumption in [HA] *)
  unshelve epose proof (HA _) as HA.
  { intros a Ha.
    apply NNPP. intros Ha0.
    contradict Hc. exists a; split; auto.
    intros b Hb; apply NNPP; intros Hb0.
    contradict Ha0. exists (upper_open_ray R b).
    { apply Im_def; assumption. }
    constructor. specialize (HR_total a b) as [|]; [contradiction|].
    split; auto. intros ?; subst b. contradiction.
  }
  clear Hc.
  destruct HA as [C [HC_fin [HC_imA HAC]]].
  (* destruct [HC_fin] and [HC_imA] *)
  destruct (finite_in_image _ _ _ HC_fin HC_imA)
    as [B [HB_fin [HBC HBA]]].
  subst C. clear HC_fin HC_imA.
  (* [A] is not relevant anymore *)
  assert (Inhabited B) as HB_inh.
  { destruct HA_inh as [a Ha].
    apply HAC in Ha. destruct Ha as [S a HS HSb].
    destruct HS as [b Hb]. exists b; exact Hb.
  }
  pose proof (HB := Inclusion_is_transitive _ _ _ _ HBA HAC).
  clear A HA_inh HAC HBA.
  (* since [B] is finite, it has a least element (or is empty) *)
  pose proof (order_total_finite_minimal_ens R HR HR_total B HB_fin)
    as [HB_empty|HB_min];
    clear HR_total HB_fin.
  { subst. destruct HB_inh; contradiction. }
  clear HB_inh.
  destruct HB_min as [b [HBb Hb_min]].
  specialize (HB b HBb).
  destruct HB as [S b HS HSb].
  destruct HS as [b0 HBb0 S HS]. subst S.
  destruct HSb as [[Hbb0 Hbb1]].
  specialize (Hb_min b0 HBb0).
  contradict Hbb1. apply (ord_antisym HR); assumption.
Qed.

Lemma extreme_value_theorem_ens {X : TopologicalSpace} (R : relation X)
  (A : Ensemble X) (HR : order R) (HR_total : forall x y, R x y \/ R y x) :
  orders_top X R -> Inhabited A -> compact (SubspaceTopology A) ->
  exists c d : X, In A c /\ In A d /\ forall x : X, In A x -> R c x /\ R x d.
Proof.
  intros HX HA_inh HA.
  cut ((exists c : X, In A c /\ forall x : X, In A x -> R c x) /\
         exists d : X, In A d /\ forall x : X, In A x -> R x d).
  { firstorder. }
  split.
  - apply extreme_value_theorem_ens_lower; assumption.
  - apply extreme_value_theorem_ens_lower with (R := flip R); auto.
    + apply order_flip, HR.
    + clear HX HA_inh HA; firstorder.
    + apply orders_top_flip, HX.
Qed.

(** Corresponds to Munkres, Theorem 27.4 *)
Theorem extreme_value_theorem
  {X Y : TopologicalSpace} (R : relation Y)
  (HY : orders_top Y R) (HR : order R) (HR_total : forall x y, R x y \/ R y x)
  (f : X -> Y) (Hf : continuous f)
  (HX : compact X) (HX_inh : inhabited X) :
  exists c d : X, forall x : X, R (f c) (f x) /\ R (f x) (f d).
Proof.
  unshelve epose proof (compact_image_ens f Full_set Hf _).
  { eapply topological_property_compact; eauto.
    apply subspace_full_homeo.
  }
  apply (@extreme_value_theorem_ens Y R) in H;
    auto.
  2: {
    destruct HX_inh as [x]; exists (f x); apply Im_def; constructor.
  }
  destruct H as [c0 [d0 [Hc0 [Hd0 Hcd]]]].
  apply Im_inv in Hc0, Hd0.
  destruct Hc0 as [c [_ Hc0]].
  destruct Hd0 as [d [_ Hd0]].
  subst c0 d0. exists c, d. intros x.
  apply Hcd. apply Im_def. constructor.
Qed.

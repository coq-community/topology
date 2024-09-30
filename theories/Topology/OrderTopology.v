From Topology Require Export
  SeparatednessAxioms
  Subbases.
From ZornsLemma Require Export Relation_Definitions_Implicit.
From ZornsLemma Require Import EnsemblesTactics.

Section OrderTopology.

Context {X:Type}.
Variable R:relation X.
Hypothesis R_ord: order R.

Definition lower_open_ray (x : X) : Ensemble X :=
  [ y : X | R y x /\ y <> x ].

Definition upper_open_ray (x : X) : Ensemble X :=
  [ y : X | R x y /\ y <> x ].

Inductive order_topology_subbasis : Family X :=
  | intro_lower_interval: forall x:X,
    In order_topology_subbasis (lower_open_ray x)
  | intro_upper_interval: forall x:X,
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

Lemma lower_closed_interval_closed: forall x:X,
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

Lemma upper_closed_interval_closed: forall x:X,
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

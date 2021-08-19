Require Export Subbases SeparatednessAxioms.
From ZornsLemma Require Export Relation_Definitions_Implicit.
From ZornsLemma Require Import EnsemblesTactics.

Section OrderTopology.

Variable X:Type.
Variable R:relation X.
Hypothesis R_ord: order R.

Inductive order_topology_subbasis : Family X :=
  | intro_lower_interval: forall x:X,
    In order_topology_subbasis [ y:X | R y x /\ y <> x ]
  | intro_upper_interval: forall x:X,
    In order_topology_subbasis [ y:X | R x y /\ y <> x].

Definition OrderTopology : TopologicalSpace :=
  Build_TopologicalSpace_from_subbasis X order_topology_subbasis.

Section if_total_order.

Hypothesis R_total: forall x y:X, R x y \/ R y x.

Lemma lower_closed_interval_closed: forall x:X,
  closed [ y:X | R y x ] (X:=OrderTopology).
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
exists [z:X | R x z /\ z <> x];
  constructor; split; trivial.
- apply (Build_TopologicalSpace_from_subbasis_subbasis
    _ order_topology_subbasis).
  constructor.
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
  closed [y:X | R x y] (X:=OrderTopology).
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
exists ([z:X | R z x /\ z <> x]);
  constructor; split; trivial.
- apply (Build_TopologicalSpace_from_subbasis_subbasis
    _ order_topology_subbasis).
  constructor.
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

Instance order_topology_Hausdorff: Hausdorff OrderTopology.
Proof.
constructor.
match goal with |- forall x y:point_set OrderTopology, ?P =>
  cut (forall x y:point_set OrderTopology, R x y -> P)
  end;
  intros.
- destruct (R_total x y).
  { exact (H x y H1 H0). }
  assert (y <> x) by auto.
  destruct (H y x H1 H2) as [V [U [? [? [? []]]]]].
  exists U, V.
  repeat split; trivial.
  transitivity (Intersection V U); trivial.
  now extensionality_ensembles.
- pose proof (Build_TopologicalSpace_from_subbasis_subbasis
    _ order_topology_subbasis).
  destruct (classic (exists z:X, R x z /\ R z y /\ z <> x /\ z <> y)).
  + destruct H2 as [z [? [? []]]].
    exists ([w:X | R w z /\ w <> z]),
           ([w:X | R z w /\ w <> z]).
    repeat split; auto.
    * apply H1.
      constructor.
    * apply H1.
      constructor.
    * extensionality_ensembles.
      destruct H6, H7.
      contradiction H8.
      now apply (ord_antisym R_ord).
  + exists ([w:X | R w y /\ w <> y]),
           ([w:X | R x w /\ w <> x]).
    repeat split; auto.
    * apply H1.
      constructor.
    * apply H1.
      constructor.
    * extensionality_ensembles.
      destruct H3, H4.
      contradiction H2.
      exists x0.
      now repeat split.
Qed.

End if_total_order.

End OrderTopology.

Arguments OrderTopology {X}.

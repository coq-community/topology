From ZornsLemma Require Import InverseImage Powerset_facts Quotients.
Require Export QuotientTopology.

Section AdjunctionSpace.

Context {X : TopologicalSpace}.
Variable S : Ensemble X.

Definition SpaceAdjunction : relation X := fun x y => x = y \/ (In S x /\ In S y).
Definition AdjunctionSpace := QuotientTopology SpaceAdjunction.

Lemma SpaceAdjunction_equivalence: equivalence SpaceAdjunction.
Proof.
split; red; intros; unfold SpaceAdjunction in *.
- now left.
- destruct H, H0; subst;
    now left + right.
- destruct H, H;
    now left + right.
Qed.

Hint Resolve equiv_class_self : topology.
Hint Resolve SpaceAdjunction_equivalence : topology.

Lemma SpaceAdjunction_equiv_class_S (x : X):
  In S x -> equiv_class SpaceAdjunction x = S.
Proof.
intro.
extensionality_ensembles.
- destruct H0, H0;
    now subst.
- constructor.
  now right.
Qed.

Lemma SpaceAdjunction_equiv_class_Singleton (x : X):
  ~ In S x -> equiv_class SpaceAdjunction x = Singleton x.
Proof.
intros.
extensionality_ensembles.
- destruct H0;
    now subst.
- auto with topology.
Qed.

Lemma SpaceAdjunction_equiv_class_cases (x : X):
  ~ In S x /\ equiv_class SpaceAdjunction x = Singleton x \/
  In S x.
Proof.
destruct (classic (In S x)).
- now right.
- left.
  split; trivial.
  now rewrite SpaceAdjunction_equiv_class_Singleton.
Qed.

Lemma SpaceAdjunction_equiv_class_Singleton_eq (x y : X):
  equiv_class SpaceAdjunction x = Singleton y ->
  S <> Singleton y ->
  x = y.
Proof.
intros.
destruct (SpaceAdjunction_equiv_class_cases x) as [[? ?] | ?].
- rewrite H in H2.
  now apply Singleton_injective.
- now rewrite SpaceAdjunction_equiv_class_S in H.
Qed.

Lemma SpaceAdjunction_quotient_projection_injective (x y : X):
  ~ In S x ->
  quotient_projection SpaceAdjunction x = quotient_projection SpaceAdjunction y ->
  x = y.
Proof.
intros.
apply quotient_projection_minimally_collapses_R in H0;
  auto with topology.
now destruct H0.
Qed.

End AdjunctionSpace.

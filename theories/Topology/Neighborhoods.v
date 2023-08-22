Require Export TopologicalSpaces Ensembles InteriorsClosures.
From ZornsLemma Require Import EnsemblesImplicit.

Definition open_neighborhood {X:TopologicalSpace}
  (U:Ensemble X) (x:X) :=
  open U /\ In U x.

Global Hint Unfold open_neighborhood : topology.

Definition neighborhood {X:TopologicalSpace}
  (N:Ensemble X) (x:X) :=
  exists U:Ensemble X,
    open_neighborhood U x /\ Included U N.

Lemma open_neighborhood_is_neighborhood: forall {X:TopologicalSpace}
  (U:Ensemble X) (x:X),
  open_neighborhood U x -> neighborhood U x.
Proof.
intros.
exists U.
auto with sets.
Qed.

Lemma neighborhood_interior: forall {X:TopologicalSpace}
  (N:Ensemble X) (x:X),
  neighborhood N x -> In (interior N) x.
Proof.
intros.
destruct H as [U].
destruct H.
destruct H.
assert (Included U (interior N)) by
  now apply interior_maximal.
auto with sets.
Qed.

Lemma interior_neighborhood: forall {X:TopologicalSpace}
  (N:Ensemble X) (x:X),
  In (interior N) x -> neighborhood N x.
Proof.
intros.
exists (interior N).
repeat split; trivial.
- apply interior_open.
- apply interior_deflationary.
Qed.

Lemma neighborhood_upward_closed
  {X : TopologicalSpace} (x : X) (U V : Ensemble X) :
  Included U V ->
  neighborhood U x ->
  neighborhood V x.
Proof.
  intros HUV [W []]. exists W; auto.
  split; auto.
  transitivity U; auto.
Qed.

Lemma open_char_neighborhood: forall {X:TopologicalSpace} (U : Ensemble X),
    open U <-> forall x, In U x -> neighborhood U x.
Proof.
  split.
  - intros.
    exists U. auto with relations topology.
  - intros.
    assert (U = FamilyUnion (fun V => open V /\ Included V U)).
    2: {
      rewrite H0.
      apply open_family_union.
      intuition.
      destruct H1.
      assumption.
    }
    apply Extensionality_Ensembles.
    split; red; intros; intuition.
    + specialize (H _ H0). destruct H.
      destruct H as [[? ?] ?].
      exists x0; auto.
      constructor; auto.
    + destruct H0.
      destruct H0.
      intuition.
Qed.

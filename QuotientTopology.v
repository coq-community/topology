From ZornsLemma Require Import InverseImage Families Quotients.
From Coq Require Export Ensembles.
Require Export TopologicalSpaces.
Require Import InverseImageLemmas Continuity Connectedness.

Definition QuotientTopology {X : TopologicalSpace} (R : Relation (point_set X)) :
  TopologicalSpace.
apply (Build_TopologicalSpace _ (inverse_image (inverse_image (quotient_projection R)) open));
  rewrite inverse_image_fun;
  intros.
- rewrite inverse_image_family_union_fun.
  apply open_family_union.
  intros S [H1 [H2 H3]].
  rewrite H3.
  now apply H.
- rewrite inverse_image_intersection.
  now apply open_intersection2.
- rewrite inverse_image_full_set.
  apply open_full.
Defined.

Lemma quotient_projection_continuous {X : TopologicalSpace} (R : Relation (point_set X)) :
  @continuous X (QuotientTopology R) (quotient_projection R).
Proof.
now intros ? [?].
Qed.

Lemma quotient_projection_open_iff {X : TopologicalSpace} (R : Relation (point_set X))
  (U : Ensemble (point_set (QuotientTopology R))) :
  open (inverse_image (quotient_projection R) U) <-> open U.
Proof.
split.
- intro.
  now constructor.
- apply quotient_projection_continuous.
Qed.

Lemma quotient_topology_final {X : TopologicalSpace} (R : Relation (point_set X))
  (open' : Family (quotient R))
  (H1 : forall F : Family (quotient R), (forall S, In F S -> open' S) -> open' (FamilyUnion F))
  (H2 : forall U V, open' U -> open' V -> open' (Intersection U V))
  (H3 : open' Full_set) :
  @continuous X (Build_TopologicalSpace (quotient R) open' H1 H2 H3) (quotient_projection R) ->
  Included open' (@open (QuotientTopology R)).
Proof.
intros H ? ?.
constructor.
now apply H.
Qed.

Lemma quotient_connected {X : TopologicalSpace} (R : Relation (point_set X)) :
  connected X -> connected (QuotientTopology R).
Proof.
intros H U [[H1] [H2]].
destruct (H (inverse_image (quotient_projection R) U));
[ (split; trivial; red;
  now rewrite <- inverse_image_complement) | | ];
[ left | right ];
  apply Extensionality_Ensembles;
  split; red; intros;
  easy + destruct (quotient_projection_surjective x);
[ contradict H3 |];
  rewrite <- H4, in_inverse_image;
  simpl;
  now rewrite H0.
Qed.
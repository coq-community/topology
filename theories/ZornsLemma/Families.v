From Coq Require Import Classical_Prop.
From Coq Require Import Classical_sets.
From ZornsLemma Require Export EnsemblesSpec EnsemblesTactics.
From ZornsLemma Require Import Image ImageImplicit.
From ZornsLemma Require Import EnsemblesImplicit.
From Coq Require Export Ensembles.
Set Implicit Arguments.

Section Families.

Variable T:Type.
Definition Family := Ensemble (Ensemble T).
Variable F:Family.

Inductive FamilyUnion: Ensemble T :=
  | family_union_intro: forall (S:Ensemble T) (x:T),
    In F S -> In S x -> In FamilyUnion x.

Inductive FamilyIntersection: Ensemble T :=
  | family_intersection_intro: forall x:T,
    (forall S:Ensemble T, In F S -> In S x) ->
    In FamilyIntersection x.

End Families.

Section FamilyFacts.

Variable T:Type.

Lemma empty_family_union: FamilyUnion (@Empty_set (Ensemble T)) =
                          Empty_set.
Proof.
apply Extensionality_Ensembles.
unfold Same_set.
unfold Included.
intuition.
- destruct H.
  contradiction H.
- contradiction H.
Qed.

Lemma empty_family_intersection:
  FamilyIntersection (@Empty_set (Ensemble T)) = Full_set.
Proof.
apply Extensionality_Ensembles.
unfold Same_set.
unfold Included.
intuition.
constructor.
intros.
contradiction H0.
Qed.

(* unions and intersections of subfamilies *)

Lemma subfamily_union: forall F G:Family T, Included F G ->
  Included (FamilyUnion F) (FamilyUnion G).
Proof.
unfold Included.
intros.
destruct H0.
apply family_union_intro with S.
- apply H.
  assumption.
- assumption.
Qed.

Lemma subfamily_intersection: forall F G:Family T, Included F G ->
  Included (FamilyIntersection G) (FamilyIntersection F).
Proof.
unfold Included.
intros.
constructor.
destruct H0.
intros.
apply H0.
apply H.
assumption.
Qed.

Lemma Complement_FamilyIntersection: forall F:Family T,
    Complement (FamilyIntersection F) =
    FamilyUnion [ S:Ensemble T |
                  In F (Complement S)].
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
- apply NNPP.
  red; intro.
  red in H; red in H.
  contradict H.
  constructor. intros.
  apply NNPP.
  red; intro.
  contradict H0.
  exists (Complement S).
  + constructor. rewrite Complement_Complement. assumption.
  + assumption.
- destruct H.
  red; red; intro.
  destruct H1.
  destruct H.
  pose proof (H1 _ H).
  contradiction.
Qed.

Lemma Complement_FamilyUnion: forall F:Family T,
    Complement (FamilyUnion F) =
    FamilyIntersection [ S:Ensemble T |
                         In F (Complement S) ].
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
- constructor. intros.
  destruct H0.
  apply NNPP. red; intro.
  red in H; red in H. contradict H.
  exists (Complement S); assumption.
- red; red. intro.
  destruct H.
  destruct H0.
  specialize (H (Complement S)).
  apply H.
  2: { assumption. }
  constructor. rewrite Complement_Complement.
  assumption.
Qed.

Lemma union_as_family_union (U V : Ensemble T) :
  Union U V = FamilyUnion (Couple U V).
Proof.
  extensionality_ensembles_inv; subst.
  - exists U; firstorder.
  - exists V; firstorder.
  - left. assumption.
  - right. assumption.
Qed.

Lemma family_union_singleton
  (S : Ensemble T) :
  FamilyUnion (Singleton S) = S.
Proof.
now extensionality_ensembles;
  try econstructor.
Qed.
End FamilyFacts.

Lemma image_family_union (X Y : Type) (F : Family X) (f : X -> Y) :
  Im (FamilyUnion F) f = FamilyUnion (Im F (fun U => Im U f)).
Proof.
apply Extensionality_Ensembles; split; red; intros.
- inversion_clear H. subst.
  inversion_clear H0.
  exists (Im S f).
  { exists S; auto. }
  apply Im_def.
  assumption.
- inversion_clear H.
  inversion_clear H0.
  subst.
  inversion_clear H1.
  subst.
  apply Im_def.
  exists x0; auto.
Qed.

Lemma family_intersection_add {X : Type} (F : Family X) (U : Ensemble X) :
  FamilyIntersection (Add F U) = Intersection (FamilyIntersection F) U.
Proof.
apply Extensionality_Ensembles; split; red; intros; constructor.
- constructor. destruct H.
  intros. apply H. left. assumption.
- destruct H. apply H. right. reflexivity.
- intros. destruct H. destruct H.
  destruct H0.
  + apply H. assumption.
  + inversion H0; subst; clear H0.
    assumption.
Qed.

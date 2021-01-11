Require Import Classical_Prop.
Require Import Classical_sets.
Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Export EnsemblesSpec.

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
- constructor.
- constructor.
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
End FamilyFacts.

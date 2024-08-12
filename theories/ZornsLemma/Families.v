From Coq Require Import
  Morphisms.
From ZornsLemma Require Export
  EnsemblesTactics.
From ZornsLemma Require Import
  EnsemblesImplicit
  Image
  ImageImplicit.
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

#[export]
Instance FamilyUnion_Proper {X : Type} :
  Proper (Same_set ==> Same_set) (@FamilyUnion X).
Proof.
  intros F0 F1 HF.
  split; intros x Hx; destruct Hx as [S x HFS HSx];
    exists S; firstorder.
Qed.

#[export]
Instance FamilyIntersection_Proper {X : Type} :
  Proper (Same_set ==> Same_set) (@FamilyIntersection X).
Proof.
  intros F0 F1 HF.
  split; intros _ [x Hx]; constructor; intros S HS;
    apply Hx, HF, HS.
Qed.

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
    FamilyUnion (Im F Complement).
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
  + apply Im_def. assumption.
  + assumption.
- destruct H.
  inversion H; subst; clear H.
  intros ?.
  destruct H.
  firstorder.
Qed.

Lemma Complement_FamilyUnion: forall F:Family T,
    Complement (FamilyUnion F) =
    FamilyIntersection (Im F Complement).
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
- constructor. intros S HS.
  destruct HS as [U HU S]. subst.
  intros HUx. apply H.
  exists U; auto.
- destruct H as [x Hx].
  intros Hx0.
  destruct Hx0.
  specialize (Hx (Complement S)).
  apply Hx; auto.
  apply Im_def.
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

Lemma intersection_as_family_intersection
  (U V : Ensemble T) :
  Intersection U V = FamilyIntersection (Couple U V).
Proof.
  apply Extensionality_Ensembles; split; red.
  - intros _ [x Hx0 Hx1]. constructor.
    intros _ [|]; assumption.
  - intros _ [x Hx].
    split; apply Hx; clear Hx; constructor.
Qed.

Lemma family_union_singleton
  (S : Ensemble T) :
  FamilyUnion (Singleton S) = S.
Proof.
now extensionality_ensembles;
  try econstructor.
Qed.

Lemma family_intersection_singleton (S : Ensemble T) :
  FamilyIntersection (Singleton S) = S.
Proof.
  apply Extensionality_Ensembles; split.
  - intros _ [x Hx].
    apply Hx. constructor.
  - intros x Hx.
    constructor. intros U HU.
    destruct HU; assumption.
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

Lemma family_union_add {X : Type} (F : Family X) (U : Ensemble X) :
  FamilyUnion (Add F U) = Union (FamilyUnion F) U.
Proof.
  apply Extensionality_Ensembles; split; red.
  - intros x Hx.
    destruct Hx as [A x HA Hx].
    destruct HA as [A HA|A HA].
    + left. exists A; auto.
    + destruct HA. right. assumption.
  - intros x Hx.
    destruct Hx as [x Hx|x Hx].
    + destruct Hx as [A x HA Hx].
      exists A; auto. left; auto.
    + exists U; auto. right. constructor.
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

Lemma family_union_union {X : Type} (F G : Family X) :
  FamilyUnion (Union F G) =
    Union (FamilyUnion F) (FamilyUnion G).
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - inversion H; subst; clear H.
    destruct H0; [left|right]; exists x0; auto.
  - destruct H, H; exists S; auto; [left|right]; auto.
Qed.

Lemma family_union_empty_sets (X : Type) (F : Family X) :
  (forall U, In F U -> U = Empty_set) <->
  FamilyUnion F = Empty_set.
Proof.
split.
- intros. extensionality_ensembles.
  rewrite <- (H S); auto.
- intros. extensionality_ensembles.
  rewrite <- H. exists U; assumption.
Qed.

Lemma FamilyUnion_In_Included {X : Type}
  (F : Family X) (U : Ensemble X) :
  In F U -> Included U (FamilyUnion F).
Proof.
  intros HU x Hx.
  exists U; assumption.
Qed.

Lemma FamilyIntersection_In_Included {X : Type}
  (F : Family X) (U : Ensemble X) :
  In F U -> Included (FamilyIntersection F) U.
Proof.
  intros HU x Hx.
  destruct Hx. apply H, HU.
Qed.

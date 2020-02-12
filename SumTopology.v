Require Export TopologicalSpaces.
Require Import StrongTopology EnsembleTactic.

Section SumTopology.

Variable A:Type.
Variable X:forall a:A, TopologicalSpace.

Inductive sum_space_point_set : Type :=
  sum_space_point_set_intro (a : A) : point_set (X a) -> sum_space_point_set.

Definition SumTopology : TopologicalSpace :=
  StrongTopology sum_space_point_set_intro.

End SumTopology.

Arguments sum_space_point_set {A}.
Arguments sum_space_point_set_intro {A}.

Lemma sum_topology_open_full_set_component {A : Type} (X : forall a, TopologicalSpace) :
  forall a, @open (SumTopology A X) (Im Full_set (sum_space_point_set_intro X a)).
Proof.
intros a1 a2.
destruct (classic (a1 = a2)).
- subst.
  replace (inverse_image (sum_space_point_set_intro X a2) (Im Full_set (sum_space_point_set_intro X a2))) with
          (@Full_set (point_set (X a2))).
  + apply open_full.
  + extensionality_ensembles;
      repeat econstructor.
- replace (inverse_image (sum_space_point_set_intro X a2) (Im Full_set (sum_space_point_set_intro X a1))) with
          (@Empty_set (point_set (X a2))).
  + apply open_empty.
  + extensionality_ensembles_inv.
    subst.
    injection H2 as H2.
    now subst.
Qed.

Lemma sum_topology_closed_full_set_component {A : Type} (X : forall a, TopologicalSpace) :
  forall a, @closed (SumTopology A X) (Im Full_set (sum_space_point_set_intro X a)).
Proof.
intros a1 a2.
destruct (classic (a1 = a2)).
- subst.
  replace (inverse_image (sum_space_point_set_intro X a2)
     (@Complement (point_set (SumTopology A X))
        (Im Full_set (sum_space_point_set_intro X a2)))) with
          (@Empty_set (point_set (X a2))).
  + apply open_empty.
  + extensionality_ensembles_inv.
    destruct H0.
    repeat econstructor.
- replace (inverse_image (sum_space_point_set_intro X a2)
     (@Complement (point_set (SumTopology A X))
        (Im Full_set (sum_space_point_set_intro X a1)))) with
          (@Full_set (point_set (X a2))).
  + apply open_full.
  + extensionality_ensembles_inv;
      repeat econstructor.
    intro.
    inversion H0.
    injection H3 as H3.
    now subst.
Qed.

Lemma sum_topology_inj_image_open {A : Type} (X : forall a, TopologicalSpace) (a : A) (S : Ensemble (point_set (X a))) :
  open S <-> @open (SumTopology A X) (Im S (sum_space_point_set_intro X a)).
Proof.
split; intros.
- intro a'.
  destruct (classic (a = a')).
  + subst.
    replace (inverse_image (sum_space_point_set_intro X a') (Im S (sum_space_point_set_intro X a'))) with S;
      trivial.
    extensionality_ensembles_inv.
    * now repeat econstructor.
    * injection H2 as H2.
      apply inj_pair2 in H2.
      now subst.
  + replace (inverse_image (sum_space_point_set_intro X a') (Im S (sum_space_point_set_intro X a))) with
            (@Empty_set (point_set (X a'))).
    * apply open_empty.
    * extensionality_ensembles_inv.
      injection H3 as H3.
      now subst.
- replace S with (inverse_image (sum_space_point_set_intro X a) (Im S (sum_space_point_set_intro X a))).
  + apply H.
  + extensionality_ensembles_inv.
    * injection H2 as H2.
      apply inj_pair2 in H2.
      now subst.
    * now repeat econstructor.
Qed.


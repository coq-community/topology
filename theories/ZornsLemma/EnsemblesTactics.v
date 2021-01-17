From ZornsLemma Require Import EnsemblesImplicit.

Ltac destruct_ensembles_in :=
 match goal with
   | [H : Ensembles.In _ _ |- _] => destruct H
 end.

Ltac extensionality_ensembles :=
  apply Extensionality_Ensembles;
  split; red; intros;
    repeat destruct_ensembles_in.

Ltac inversion_ensembles_in :=
 match goal with
   | [H : Ensembles.In _ _ |- _] => inversion H; clear H
 end.

Ltac extensionality_ensembles_inv :=
  apply Extensionality_Ensembles;
  split; red; intros;
    repeat inversion_ensembles_in.

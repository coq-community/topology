Require Export ImageImplicit.
Require Import EnsemblesImplicit.
Require Import FunctionProperties.

Lemma option_Full_set_Im (X : Type) :
  Full_set = Add (Im Full_set (@Some X)) None.
Proof.
apply Extensionality_Ensembles; split; red; intros.
2: { constructor. }
destruct x.
- left. exists x; constructor.
- right. constructor.
Qed.

Lemma Im_Full_set_surj {X Y : Type} (f : X -> Y) :
  surjective f ->
  Full_set = Im Full_set f.
Proof.
intros. apply Extensionality_Ensembles; split; red; intros.
2: { constructor. }
destruct (H x) as [y].
subst. apply Im_def.
constructor.
Qed.

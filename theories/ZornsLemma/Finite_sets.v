From Coq Require Import Classical.
From Coq Require Export Finite_sets.
From ZornsLemma Require Import EnsemblesImplicit FiniteImplicit.

(* This is like a choice property for finite sets. And [P] is about pairs, so
   that's the meaning of the name. It is similar to
   [FiniteTypes.finite_choice]. *)
Lemma finite_ens_pair_choice {X Y : Type} (U : Ensemble X)
      (P : X -> Y -> Prop) :
  Finite U ->
  (forall x, In U x -> exists y, P x y) ->
  exists V : Ensemble Y,
    Finite V /\
      (forall x, In U x -> exists y, In V y /\ P x y) /\
      (forall y, In V y -> exists x, In U x /\ P x y).
Proof.
  intros U_fin U_ex.
  induction U_fin as [|U ? ? x].
  { (* U = Empty_set *)
    exists Empty_set. repeat split;
      intros; try contradiction.
    constructor.
  }
  (* U = Add _ _ *)
  specialize IHU_fin as [V0 [H0 [H1 H2]]].
  { intros. apply U_ex. left. assumption. }
  specialize (U_ex x) as [y].
  { right. reflexivity. }
  destruct (classic (In V0 y)).
  - (* In V0 y *)
    exists V0. repeat split; intros; auto.
    + destruct H5.
      { apply H1; auto. }
      exists y. inversion H5; subst; clear H5.
      auto.
    + destruct (H2 y0 H5) as [x0 []];
        exists x0; split; auto with sets.
  - (* ~ In V0 y *)
    exists (Add V0 y). repeat split; intros; auto.
    + constructor; auto.
    + destruct H5 as [x0|x0].
      * destruct (H1 x0 H5) as [y0 []].
        exists y0; split; auto with sets.
      * inversion H5; subst; clear H5.
        exists y; auto with sets.
    + destruct H5 as [y0|y0].
      * destruct (H2 y0 H5) as [x0 []].
        exists x0; split; auto with sets.
      * inversion H5; subst; clear H5.
        exists x; auto with sets.
Qed.

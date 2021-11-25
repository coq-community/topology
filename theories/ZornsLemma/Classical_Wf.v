From Coq Require Import Classical.
From Coq Require Export Ensembles.
From ZornsLemma Require Import EnsemblesImplicit.
From Coq Require Export Relation_Definitions.
From ZornsLemma Require Import Relation_Definitions_Implicit.
From ZornsLemma Require Import EnsemblesSpec.

Section MinimalElements.

Variable T:Type.
Variable R:relation T.

(* R is well-founded if and only if every nonempty subset of
   T has a minimal element *)

Definition minimal_element_property : Prop :=
  forall S:Ensemble T, Inhabited S -> exists x:T, In S x /\
    forall y:T, In S y -> ~ R y x.

Lemma WF_implies_MEP: well_founded R -> minimal_element_property.
Proof.
unfold well_founded.
unfold minimal_element_property.
intros WF S Hinh.
destruct Hinh.
revert x H.
apply (@well_founded_ind T R WF
 (fun x:T =>
  In S x -> exists y:T, In S y /\ (forall z:T, In S z -> ~ R z y))).
intros.
case (classic (forall y:T, In S y -> ~ R y x)).
- exists x.
  split.
  + assumption.
  + assumption.
- intro.
  apply not_all_ex_not in H1.
  destruct H1.
  apply imply_to_and in H1.
  destruct H1.
  apply H with x0.
  + apply NNPP.
    assumption.
  + assumption.
Qed.

(* Prop. 2.1 from n-lab page "well-founded relation" 2021-11-21
   This is why the [minimal_element_property] is way too strong for
   constructive reasoning.
   This proof can even be performed in a topos. See the n-lab for this. *)
Lemma MEP_inh_impl_LEM :
  minimal_element_property ->
  (exists x y, R y x) ->
  (forall P : Prop, P \/ ~ P).
Proof.
  intros ? ? Q.
  destruct H0 as [x [y Hxy]].
  pose (P := Union (Singleton x) (fun a => R y x /\ Q)).
  specialize (H P).
  destruct H as [x0].
  { exists x. left. constructor. }
  destruct H.
  destruct H.
  2: {
    left.
    apply H.
  }
  inversion H; subst; clear H.
  right.
  intros ?.
  unshelve eapply (H0 _ _ Hxy).
  right. split; assumption.
Qed.

(* This fact holds constructively. *)
Lemma MEP_implies_WF: minimal_element_property -> well_founded R.
Proof.
intros MEP. red. intros.
constructor. intros.
unshelve epose proof (MEP_inh_impl_LEM MEP _) as LEM.
{ eauto. }
destruct (LEM (Acc R y)) as [|]; try assumption.
exfalso.
assert (Inhabited [x:T | ~ Acc R x]) as HInh.
{ exists y.
  constructor; assumption.
}
apply MEP in HInh as [? [[?] ?]].
contradict H1.
constructor.
intros.
destruct (LEM (Acc R y0)) as [|]; try assumption.
exfalso.
apply H2 with y0.
- constructor; assumption.
- assumption.
Qed.

End MinimalElements.

Require Import ClassicalChoice.

Section DecreasingSequences.

(* R is well-founded if and only if there is no infinite strictly
   decreasing sequence of elements of T *)

Variable T:Type.
Variable R:relation T.

Definition decreasing_sequence_property :=
  forall a:nat->T, exists n:nat, ~ R (a (S n)) (a n).

Lemma WF_implies_DSP: well_founded R -> decreasing_sequence_property.
Proof.
unfold decreasing_sequence_property.
intros WF a.
remember (a 0) as a0.
revert a0 a Heqa0.
apply (well_founded_ind WF (fun x:T =>
  forall a:nat->T, x = a 0 -> exists n:nat, ~ R (a (S n)) (a n))).
intros.
case (classic (R (a 1) (a 0))).
- intro.
  pose (b := fun n:nat => a (S n)).
  assert (exists n:nat, ~ R (b (S n)) (b n)).
  { apply H with (a 1).
    - rewrite H0.
      assumption.
    - trivial.
  }
  destruct H2.
  exists (S x0).
  unfold b in H2.
  assumption.
- exists 0.
  assumption.
Qed.

Lemma DSP_implies_WF: decreasing_sequence_property -> well_founded R.
Proof.
unfold decreasing_sequence_property.
intro DSP.
apply MEP_implies_WF.
unfold minimal_element_property.
intro S0.
intros.
apply NNPP.
intuition.
assert (forall x:T, In S0 x -> exists y:T, In S0 y /\ R y x).
{ intros.
  apply NNPP.
  intuition.
  assert (forall y:T, ~(In S0 y /\ R y x)).
  { apply not_ex_all_not. assumption. }
  apply H0.
  exists x.
  split.
  - assumption.
  - intros.
    apply H3 with y.
    tauto.
}
pose (S_type := {x:T | In S0 x}).
assert (exists f:S_type -> S_type, forall x:S_type,
  R (proj1_sig (f x)) (proj1_sig x)).
{ apply choice with (R:=fun x y:S_type => R (proj1_sig y) (proj1_sig x)).
  intro.
  destruct x.
  simpl.
  pose proof (H1 x i).
  destruct H2 as [? [? ?]].
  exists (exist (fun x:T => In S0 x) x0 H2).
  simpl. assumption.
}
destruct H2 as [f Hf].
destruct H.
pose (b := nat_rect (fun n:nat => S_type)
  (exist (fun x:T => In S0 x) x H)
  (fun (n:nat) (x:S_type) => f x)).
simpl in b.
pose (a := fun n:nat => (proj1_sig (b n))).
assert (forall n:nat, R (a (S n)) (a n)).
{ unfold a.
  intro.
  simpl.
  apply Hf.
}
contradict DSP.
apply ex_not_not_all.
exists a.
apply all_not_not_ex.
auto.
Qed.

End DecreasingSequences.

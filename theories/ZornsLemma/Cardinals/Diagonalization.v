(** Proves that the powerset of a set has larger cardinality than the
  set itself, in different statements. Uses this to show that the
  order of cardinals is unbounded. *)
From ZornsLemma Require Import
  Cardinals.Cardinals
  Cardinals.CardinalsEns
  FunctionProperties
  FunctionPropertiesEns
  Powerset_facts.

Lemma Prop_contradiction_neq (P Q : Prop) (HP : P) :
  ~ (P /\ Q) ->
  P <> Q.
Proof.
  intros ? ?. subst.
  tauto.
Qed.

Lemma P_neq_not_P: forall (P:Prop), P <> ~P.
Proof.
unfold not; intros.
assert (~P).
{ unfold not; intro.
  assert (P->False).
  { rewrite <- H.
    assumption.
  }
  tauto.
}
assert P.
{ rewrite H.
  assumption.
}
contradiction.
Qed.

Lemma cantor_diag: forall (X:Type) (f:X->(X->bool)),
  ~ surjective f.
Proof.
intros.
red; intro.
pose (g := fun x:X => negb (f x x)).
pose proof (H g).
destruct H0.
assert (f x x = g x).
{ rewrite H0.
  reflexivity.
}
unfold g in H1.
destruct (f x x).
- discriminate H1.
- discriminate H1.
Qed.

Lemma cantor_diag2: forall (X:Type) (f:X->(X->Prop)),
  ~ surjective f.
Proof.
unfold not; intros.
pose (g := fun x:X => ~ f x x).
pose proof (H g).
destruct H0.
assert (f x x = g x).
{ rewrite H0.
  reflexivity.
}
unfold g in H1.
contradiction P_neq_not_P with (f x x).
Qed.

Lemma cardinals_unbounded: forall kappa:Type,
  lt_cardinal kappa (Ensemble kappa).
Proof.
intros ?.
split.
- exists Singleton.
  red; intros.
  apply Powerset_facts.Singleton_injective.
  assumption.
- intros [f Hf].
  apply (cantor_diag2 _ f).
  apply invertible_impl_bijective.
  apply Hf.
Qed.

Lemma cantor_diag2_ens {X : Type} (U : Ensemble X)
  (f : X -> (Ensemble X)) :
  ~ surjective_ens f U (fun V : Ensemble X => Included V U).
Proof.
  intros Hf.
  pose (g := (fun x : X => In U x /\ ~ In (f x) x) : Ensemble X).
  pose proof (Hf g) as [x [Hx Hxg]].
  { intros x [Hx _]. apply Hx. }
  assert (f x x = g x).
  { rewrite Hxg. reflexivity. }
  unfold g in H.
  unfold In in H.
  destruct (classic (f x x)).
  - apply (Prop_contradiction_neq
             (f x x) (U x /\ ~ f x x)); tauto.
  - apply (Prop_contradiction_neq
             (U x /\ ~ f x x) (f x x)); try tauto.
    congruence.
Qed.

Lemma cardinals_unbounded_ens {X : Type} (U : Ensemble X) :
  lt_cardinal_ens
    U (fun V : Ensemble X => Included V U).
Proof.
  split.
  - right. exists Singleton. split.
    + intros x Hx y Hy.
      inversion Hy; subst; clear Hy.
      assumption.
    + intros x0 x1 Hx0 Hx1 Hx.
      apply Singleton_injective in Hx.
      assumption.
  - intros H.
    apply eq_cardinal_ens_sym in H.
    destruct H as [[H _]|[f Hf]].
    + apply (H Empty_set).
    + destruct Hf as [Hf0 [Hf1 Hf2]].
      apply (cantor_diag2_ens U f).
      assumption.
Qed.

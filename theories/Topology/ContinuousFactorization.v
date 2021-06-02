From ZornsLemma Require Import EnsemblesTactics.
Require Export TopologicalSpaces Continuity SubspaceTopology.

Section continuous_factorization.

Variable X Y:TopologicalSpace.
Variable f:point_set X -> point_set Y.
Variable S:Ensemble (point_set Y).
Hypothesis f_cont: continuous f.
Hypothesis f_img: forall x:point_set X, In S (f x).

Definition continuous_factorization :
  point_set X -> point_set (SubspaceTopology S) :=
  fun x:point_set X => exist _ (f x) (f_img x).

Lemma factorization_is_continuous:
  continuous continuous_factorization.
Proof.
red.
intros.
rewrite subspace_open_char in H.
destruct H as [V' []].
subst V.
rewrite <- inverse_image_composition.
simpl.
replace (inverse_image (fun x:point_set X => f x) V')
        with (inverse_image f V').
- now apply f_cont.
- extensionality_ensembles; now constructor.
Qed.

End continuous_factorization.

Arguments continuous_factorization {X} {Y}.

Section continuous_surj_factorization.

Variable X Y:TopologicalSpace.
Variable f:point_set X -> point_set Y.
Hypothesis f_cont: continuous f.

Definition continuous_surj_factorization :
  point_set X -> point_set (SubspaceTopology (Im Full_set f)).
apply continuous_factorization with f.
intros.
exists x; constructor.
Defined.

Lemma continuous_surj_factorization_is_surjective:
  surjective continuous_surj_factorization.
Proof.
intro.
destruct y.
destruct i.
exists x.
unfold continuous_surj_factorization, continuous_factorization.
subst.
f_equal.
f_equal.
apply proof_irrelevance.
Qed.

Lemma continuous_surj_factorization_is_continuous:
  continuous continuous_surj_factorization.
Proof.
now apply factorization_is_continuous.
Qed.

End continuous_surj_factorization.

Arguments continuous_surj_factorization {X} {Y}.

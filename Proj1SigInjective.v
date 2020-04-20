Require Import ProofIrrelevance.

Lemma proj1_sig_injective: forall {A:Type} (P:A->Prop)
  (a1 a2:{x:A | P x}), proj1_sig a1 = proj1_sig a2 -> a1 = a2.
Proof.
intros.
destruct a1, a2.
now apply subset_eq_compat.
Qed.

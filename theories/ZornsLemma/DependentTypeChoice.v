From Coq Require Import ClassicalChoice.

Set Asymmetric Patterns.

Lemma choice_on_dependent_type {A : Type} {B : A -> Type}
  (R : forall a, B a -> Prop) :
  (forall a, exists b, R a b) ->
  exists f:(forall a, B a), forall a, R a (f a).
Proof.
intros.
destruct (choice (fun a (b:{a:A & B a}) =>
  match b with existT a' b0 => a=a' /\ R a' b0 end))
as [choice_fun].
- intro a.
  destruct (H a) as [b].
  now exists (existT _ a b).
- assert (forall a, {b : B a | R a b}) as f0.
  + intro.
    pose proof (H0 a).
    destruct (choice_fun a) as [a' b], H1, H1.
    now exists b.
  + exists (fun a:A => proj1_sig (f0 a)).
    intro.
    now destruct (f0 a) as [b].
Qed.

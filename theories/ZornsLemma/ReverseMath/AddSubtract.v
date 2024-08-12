(* “This is why we can’t have nice things.” *)
From Coq Require Import
  Morphisms
  Setoid.
From ZornsLemma Require Import
  EnsemblesImplicit.

#[export]
Instance In_Same_set_Proper {Z : Type} :
  Proper (Same_set ==> eq ==> iff) (@In Z).
Proof.
  red; red; intros; red; intros;
  split; intros;
    match goal with
    | H : Same_set _ _ |- _ =>
      apply H
    end;
    subst; assumption.
Qed.

(** This fact encodes, that if we have [In U x] and want to replace [U]
  with [Add (Subtract U x) x] we need (in general) the law of
  excluded middle. Or we find some constructive way to satisfy the
  hypotheses encoded here (that we can decide equality for [x]).

  For this reason, certain theorems about [cardinal] and similar
  predicates can only be proven for types with decidable equality.

  For finite combinatorics this should not be a hindrance, since many
  notions of finite-ness imply decidable equality.
 *)
Fact Add_Subtract_discouraging {X : Type} U (x : X) :
  Same_set U (Add (Subtract U x) x) <->
  In U x /\ forall y : X, In U y -> x = y \/ x <> y.
Proof.
  split.
  - intros HU.
    split.
    { rewrite HU; right; constructor. }
    intros y Hy.
    rewrite HU in Hy.
    destruct Hy as [y Hy|y Hy]; [right|left].
    + destruct Hy as [_ Hy].
      intros ?. subst. apply Hy. constructor.
    + destruct Hy. reflexivity.
  - intros [Hx HU].
    split; red.
    + intros y Hy.
      specialize (HU y Hy) as [|].
      * subst. right. constructor.
      * left. split; [assumption|].
        intros Hq; destruct Hq; contradiction.
    + intros y Hy.
      destruct Hy as [y Hy|y Hy];
        destruct Hy; assumption.
Qed.

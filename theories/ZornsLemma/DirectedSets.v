From Coq Require Export Relation_Definitions.
From ZornsLemma Require Import Relation_Definitions_Implicit.
From Coq Require Import Classical.
From Coq Require Import Arith.
From Coq Require Import Lia.

Record DirectedSet := {
  DS_set :> Type;
  DS_ord : relation DS_set;
  DS_ord_cond : preorder DS_ord;
  DS_join_cond : forall i j:DS_set, exists k:DS_set,
    DS_ord i k /\ DS_ord j k
}.

Arguments DS_ord {d}.
Arguments DS_ord_cond {d}.
Arguments DS_join_cond {d}.

Section for_large.

Context {I : DirectedSet}.

Definition eventually (P : I -> Prop) : Prop :=
  exists i : I, forall j : I,
  DS_ord i j -> P j.

Lemma eventually_and: forall (P Q : I -> Prop),
  eventually P -> eventually Q ->
  eventually (fun i : I => P i /\ Q i).
Proof.
intros.
destruct H, H0.
destruct (DS_join_cond x x0) as [? [? ?]].
exists x1.
intros; split;
[ apply H | apply H0 ];
  apply preord_trans with x1;
  trivial;
  apply DS_ord_cond.
Qed.

Lemma eventually_impl_base: forall (P Q : I -> Prop),
  (forall i : I, P i -> Q i) ->
  eventually P -> eventually Q.
Proof.
intros.
destruct H0.
exists x.
intros.
auto.
Qed.

Lemma eventually_impl: forall (P Q : I -> Prop),
  eventually P -> eventually (fun i : I => P i -> Q i) ->
  eventually Q.
Proof.
intros.
apply eventually_impl_base with (P := fun (i : I) =>
  P i /\ (P i -> Q i)).
- tauto.
- now apply eventually_and.
Qed.

Definition exists_arbitrarily_large (P : I -> Prop) :=
  forall i : I, exists j : I,
  DS_ord i j /\ P j.

Lemma exists_arbitrarily_large_all (P : I -> Prop) :
  (forall i : I, P i) ->
  exists_arbitrarily_large P.
Proof.
  intros HP i.
  exists i; split; auto.
  apply DS_ord_cond.
Qed.

Lemma not_eal_eventually_not: forall (P : I -> Prop),
  ~ exists_arbitrarily_large P ->
  eventually (fun i : I => ~ P i).
Proof.
intros.
apply not_all_ex_not in H.
destruct H as [i].
exists i.
intros.
intro.
contradiction H.
exists j; split; trivial.
Qed.

Lemma not_eventually_eal_not: forall (P : I -> Prop),
  ~ eventually P ->
  exists_arbitrarily_large (fun i : I => ~ P i).
Proof.
intros.
red; intros.
apply NNPP; intro.
contradiction H.
exists i.
intros.
apply NNPP; intro.
contradiction H0.
now exists j.
Qed.

End for_large.

Notation "'for' 'large' i : I , p" :=
  (eventually (fun i:I => p))
  (at level 200, i ident, right associativity).

Notation "'exists' 'arbitrarily' 'large' i : I , p" :=
  (exists_arbitrarily_large (fun i:I => p))
  (at level 200, i ident, right associativity).

Section nat_DS.

Definition nat_DS : DirectedSet.
refine (Build_DirectedSet nat le _ _).
- constructor; red; lia.
- intros.
  case (lt_eq_lt_dec i j).
  + intro s.
    exists j.
    destruct s; lia.
  + exists i; auto with arith.
Defined.

End nat_DS.

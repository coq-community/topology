Require Import WellOrders.

(* Define a the usual order on [well_order] and show that this order has all (strict!) joins.
I.e. we need [forall E : Ensemble well_order, exists W : well_order, forall W' : well_order, (forall i, In E i -> i < W') -> W <= W'].
*)

Record WO :=
  { WO_T : Type;
    WO_R : relation WO_T;
    WO_WO : well_order WO_R;
  }.

Coercion WO_T : WO >-> Sortclass.
Require Import FunctionProperties.

Definition WO_le (alpha beta : WO) : Prop :=
  exists f : alpha -> beta,
    injective f /\ forall x y : alpha, WO_R alpha x y -> WO_R beta (f x) (f y).
Require Import RelationClasses.
Require Import Basics.

Instance WO_le_refl : PreOrder WO_le.
Proof.
constructor; red; intros.
- exists id. split.
  + red. intros. assumption.
  + intros. assumption.
- destruct H as [f [? ?]].
  destruct H0 as [g [? ?]].
  exists (compose g f). split.
  + apply injective_compose; assumption.
  + intros.
    apply H2.
    apply H1.
    assumption.
Qed.

Definition WO_lt (alpha beta : WO) : Prop :=
  WO_le alpha beta /\ ~ WO_le beta alpha.
Lemma WO_lt_irreflexive : forall a, WO_lt a a -> False.
Proof.
  intros.
  destruct H.
  contradiction.
Qed.

Definition WO_eq (alpha beta : WO) : Prop :=
  WO_le alpha beta /\ WO_le beta alpha.

Instance WO_eq_equiv : Equivalence WO_eq.
Proof.
  split; red; intros.
  - split; apply WO_le_refl.
  - destruct H; split; assumption.
  - destruct H, H0.
    split.
    + transitivity y; assumption.
    + transitivity y; assumption.
Qed.

Require Import SetoidChoice.

Definition WO_repr_fn_ex : exists f : WO -> WO,
    forall W : WO, WO_eq W (f W) /\ forall W', WO_eq W W' -> (f W) = (f W').
Proof.
  apply representative_choice.
  apply WO_eq_equiv.
Defined.

Require Import Epsilon.

Definition WO_repr_fn_sig : { f : WO -> WO | _ } :=
  constructive_indefinite_description _ WO_repr_fn_ex.

Definition WO_repr_fn : WO -> WO :=
  proj1_sig WO_repr_fn_sig.

Definition WO_repr_fn_correct0 :
  forall W, WO_eq W (WO_repr_fn W).
Proof.
  intros.
  pose proof (proj2_sig WO_repr_fn_sig W).
  destruct H.
  apply H.
Qed.

Definition WO_repr_fn_correct1 :
  forall W W', WO_eq W W' -> (WO_repr_fn W) = (WO_repr_fn W').
Proof.
  intros.
  pose proof (proj2_sig WO_repr_fn_sig W).
  apply H0.
  assumption.
Qed.

Require Import Cardinals.

Definition WO_reprs := { W : WO | exists W', W = WO_repr_fn W' }.
Coercion WO_cardinality (W : WO) : Cardinal := cardinality (WO_T W).
Coercion WO_reprs_cardinality (W : WO_reprs) : Cardinal := proj1_sig W.

Axiom WO_lt_wf : well_founded WO_lt.
Axiom WO_lt_tso : total_strict_order WO_lt.

Lemma WO_repr_fn_lt x y :
  WO_lt (WO_repr_fn x) (WO_repr_fn y) <->
  WO_lt x y.
Proof.
  intros.
Admitted.

Program Definition WO_next (E : WO -> Prop) : WO :=
  {| WO_T := { W : WO | exists W', W = WO_repr_fn W' /\ In E W' } |}.
Proof.
Next Obligation.
  red; intros x y.
  destruct x as [x], y as [y].
  apply (WO_lt x y).
Defined.
Next Obligation.
  split.
  - red; intros x.
    destruct x as [x' [x [? ?]]].
    subst.
    induction (WO_lt_wf x) as [? ? IH].
    constructor. intros y ?.
    destruct y as [y' [y [? ?]]].
    subst.
    simpl in *.
    apply IH.
    apply WO_repr_fn_lt.
    assumption.
  - red; intros.
    destruct x as [x' [x [? ?]]], y as [y' [y [? ?]]].
    subst. simpl.
    destruct (WO_lt_tso x y) as [|[|]].
    + left. apply WO_repr_fn_lt. assumption.
    + right; left. subst.
      replace i0 with i.
      2: { apply proof_irrelevance. }
      reflexivity.
    + right; right. apply WO_repr_fn_lt. assumption.
Qed.

Definition downward_closed {A : Type} (E : A -> Prop) (R : A -> A -> Prop) :=
  (forall x y, R x y -> In E y -> In E x).

(* If [E] is downwards closed, then the ordinal described by [E] is
   larger than all its elements. *)
Lemma WO_next_lt (E : WO -> Prop) :
  downward_closed E WO_le ->
  forall W, In E W -> WO_lt W (WO_next E).
Proof.
  intros.
Admitted.

Definition WO_hartogs (X : Cardinal) : WO := WO_next (fun W => le_cardinal W X).

(* A cardinal [X] is smaller than an ordinal [W] if all well-orders on [X] are smaller than [W] *)
Lemma lt_cardinal_WO (X : Cardinal) (W : WO) :
  (forall WO : WO, WO_T WO = (match X with cardinality T => T end) -> WO_lt WO W) <->
  lt_cardinal X W.
Proof.
Admitted.

Theorem hartogs (X : Cardinal) :
  lt_cardinal X (WO_hartogs X).
Proof.
  unfold WO_hartogs.
  apply lt_cardinal_WO.
  intros.
  induction X.
  subst.
  apply WO_next_lt.
  - red; intros.
    unfold In in *.
    apply le_cardinal_preorder with y.
    2: { assumption. }
    destruct H as [f [? ?]].
    exists f. assumption.
  - unfold In.
    exists id. red; intros; assumption.
Qed.

(* show that the hartogs number is the least upper bound. *)
Theorem hartogs' (X : Cardinal) (W : WO) :
  lt_cardinal X W ->
  WO_le (WO_hartogs X) W.
Proof.
Admitted.

Definition omega1 := WO_hartogs (cardinality nat).

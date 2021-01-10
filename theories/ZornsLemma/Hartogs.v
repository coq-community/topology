Require Import WellOrders.

(* Reproduce the major theorems of Ordinals.v and construct Hartog numbers. *)

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

Instance WO_le_PreOrder : PreOrder WO_le.
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

Instance WO_lt_StrictOrder : StrictOrder WO_lt.
Proof.
  split; red; intros.
  - red; intros. intro. destruct H. contradiction.
  - destruct H, H0.
    split.
    + transitivity y; assumption.
    + intro. apply H1. transitivity z; assumption.
Qed.

Definition WO_eq (alpha beta : WO) : Prop :=
  WO_le alpha beta /\ WO_le beta alpha.

Instance WO_eq_equiv : Equivalence WO_eq.
Proof.
  split; red; intros.
  - split; reflexivity.
  - destruct H; split; assumption.
  - destruct H, H0.
    split.
    + transitivity y; assumption.
    + transitivity y; assumption.
Qed.

Require Import SetoidChoice.
Require Import Epsilon.
Require Import ProofIrrelevanceFacts.
Import ProofIrrelevance.
Import ProofIrrelevanceTheory.
(*
Require Import Ordinals.

Definition Ordinal_repr_ex : exists f : Ordinal -> Ordinal,
    forall ord : Ordinal, ord == (f ord) /\ forall ord', ord == ord' -> (f ord) = (f ord').
Proof.
  apply representative_choice.
  apply ord_eq_Equivalence.
Defined.


Definition Ordinal_repr_sig : { f : Ordinal -> Ordinal | _ } :=
  constructive_indefinite_description _ Ordinal_repr_ex.

Definition Ordinal_repr : Ordinal -> Ordinal :=
  proj1_sig Ordinal_repr_sig.

Lemma Ordinal_repr_correct0 :
  forall o, o == (Ordinal_repr o).
Proof.
  intros.
  pose proof (proj2_sig Ordinal_repr_sig o) as [? ?].
  assumption.
Qed.

Lemma Ordinal_repr_correct1 :
  forall o p, o == p -> Ordinal_repr o = Ordinal_repr p.
Proof.
  intros.
  pose proof (proj2_sig Ordinal_repr_sig o) as [? ?].
  apply H1. assumption.
Qed.

Definition Ordinal_reprs := { o : Ordinal | exists o', o = Ordinal_repr o' }.
Definition Ordinal_reprs_lt : Ordinal_reprs -> Ordinal_reprs -> Prop.
  intros x y.
  destruct x as [x'], y as [y'].
  apply constructive_indefinite_description in e.
  apply constructive_indefinite_description in e0.
  destruct e as [x], e0 as [y].
  subst.
  exact (ord_lt x y).
Defined.

Lemma Ordinal_repr_lt o p :
  ord_lt o p <-> ord_lt (Ordinal_repr o) (Ordinal_repr p).
Proof.
  split; intros.
  - pose proof (Ordinal_repr_correct0 o).
    pose proof (Ordinal_repr_correct0 p).
    destruct H0, H1.
    apply ord_le_lt_trans with o; try assumption.
    apply ord_lt_le_trans with p; assumption.
  - pose proof (Ordinal_repr_correct0 o).
    pose proof (Ordinal_repr_correct0 p).
    destruct H0, H1.
    apply ord_le_lt_trans with (Ordinal_repr o); try assumption.
    apply ord_lt_le_trans with (Ordinal_repr p); assumption.
Qed.

Lemma Ordinal_reprs_lt_correct (o p : Ordinal) :
  Ordinal_reprs_lt
    (exist _ (Ordinal_repr o) (ex_intro _ o eq_refl))
    (exist _ (Ordinal_repr p) (ex_intro _ p eq_refl)) <->
  ord_lt o p.
Proof.
  split.
  - intros.
    simpl in *.
    destruct (constructive_indefinite_description _).
    destruct (constructive_indefinite_description _).
    pose proof (Ordinal_repr_correct0 o).
    pose proof (Ordinal_repr_correct0 p).
    pose proof (Ordinal_repr_correct0 x).
    pose proof (Ordinal_repr_correct0 x0).
    rewrite e in H0.
    rewrite e0 in H1.
    destruct H0, H1, H2, H3.
    apply ord_le_lt_trans with (Ordinal_repr x); try assumption.
    apply ord_lt_le_trans with (Ordinal_repr x0); try assumption.
    apply ord_lt_le_trans with x0; try assumption.
    apply ord_le_lt_trans with x; assumption.
  - intros.
    simpl.
    destruct (constructive_indefinite_description _).
    destruct (constructive_indefinite_description _).
    pose proof (Ordinal_repr_correct0 o).
    pose proof (Ordinal_repr_correct0 p).
    pose proof (Ordinal_repr_correct0 x).
    pose proof (Ordinal_repr_correct0 x0).
    rewrite e in H0.
    rewrite e0 in H1.
    destruct H0, H1, H2, H3.
    apply ord_le_lt_trans with (Ordinal_repr x); try assumption.
    apply ord_lt_le_trans with (Ordinal_repr x0); try assumption.
    apply ord_le_lt_trans with o; try assumption.
    apply ord_lt_le_trans with p; assumption.
Qed.

Program Definition Ordinal_reprs_WO : WO :=
  {| WO_T := Ordinal_reprs;
     WO_R := Ordinal_reprs_lt; |}.
Proof.
Next Obligation.
split.
- red. intros [x' [x ?]]. subst.
  pose proof (ordinals_well_founded x).
  induction H.
  constructor. intros [y' [y ?]] ?. subst.
  apply H0.
  apply Ordinal_reprs_lt_correct in H1.
  assumption.
- red; intros.
  destruct x as [x' [x]], y as [y' [y]].
  subst.
  rewrite ?Ordinal_reprs_lt_correct.
  destruct (ord_total_order x y) as [|[|]]; try tauto.
  right; left.
  apply Ordinal_repr_correct1 in H.
  apply subset_eq_compat.
  assumption.
Qed.
*)

Definition WO_repr_fn_ex : exists f : WO -> WO,
    forall W : WO, WO_eq W (f W) /\ forall W', WO_eq W W' -> (f W) = (f W').
Proof.
  apply representative_choice.
  apply WO_eq_equiv.
Defined.

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

Definition WO_reprs := { W : WO | exists W', W = WO_repr_fn W' }.
Definition WO_reprs_lt : WO_reprs -> WO_reprs -> Prop.
  intros x y.
  destruct x as [x'], y as [y'].
  apply constructive_indefinite_description in e.
  apply constructive_indefinite_description in e0.
  destruct e as [x], e0 as [y].
  subst. exact (WO_lt x y).
Defined.

Lemma WO_reprs_lt_correct (W V : WO) :
  WO_reprs_lt
    (exist _ (WO_repr_fn W) (ex_intro _ W eq_refl))
    (exist _ (WO_repr_fn V) (ex_intro _ V eq_refl)) <->
  WO_lt W V.
Proof.
  split.
  - intros. simpl in *.
    destruct (constructive_indefinite_description _) as [W'].
    destruct (constructive_indefinite_description _) as [V'].
    pose proof (WO_repr_fn_correct0 W).
    pose proof (WO_repr_fn_correct0 V).
    pose proof (WO_repr_fn_correct0 W').
    pose proof (WO_repr_fn_correct0 V').
    destruct H, H0, H1, H2, H3.
    split.
    + transitivity (WO_repr_fn W); try assumption.
      rewrite e. transitivity W'; try assumption.
      transitivity V'; try assumption.
      transitivity (WO_repr_fn V'); try assumption.
      rewrite <- e0. assumption.
    + intro. contradict H4.
      transitivity (WO_repr_fn V'); try assumption.
      rewrite <- e0. transitivity V; try assumption.
      transitivity W; try assumption.
      transitivity (WO_repr_fn W); try assumption.
      rewrite e. assumption.
  - intros. simpl.
    destruct (constructive_indefinite_description _) as [W'].
    destruct (constructive_indefinite_description _) as [V'].
    pose proof (WO_repr_fn_correct0 W).
    pose proof (WO_repr_fn_correct0 V).
    pose proof (WO_repr_fn_correct0 W').
    pose proof (WO_repr_fn_correct0 V').
    destruct H, H0, H1, H2, H3.
    split.
    + transitivity (WO_repr_fn W'); try assumption.
      rewrite <- e. transitivity W; try assumption.
      transitivity V; try assumption.
      transitivity (WO_repr_fn V); try assumption.
      rewrite e0. assumption.
    + intro. contradict H4.
      transitivity (WO_repr_fn V); try assumption.
      rewrite e0. transitivity V'; try assumption.
      transitivity W'; try assumption.
      transitivity (WO_repr_fn W'); try assumption.
      rewrite <- e. assumption.
Qed.

(* Successor ordinal. Append [None] as new maximal element. *)
Program Definition WO_succ (W : WO) : WO :=
  {| WO_T := option (WO_T W);
     WO_R u v :=
       match u with
       | None => False
       | Some u' =>
         match v with
         | None => True
         | Some v' => WO_R W u' v'
         end
       end; |}.
Next Obligation.
  pose proof (WO_WO W).
  destruct H.
  split.
  - red. intros a.
    destruct a.
    + specialize (wo_well_founded w).
      induction wo_well_founded.
      constructor. intros. destruct y.
      * apply H0. assumption.
      * contradiction.
    + constructor. intros.
      destruct y.
      2: { contradiction. }
      specialize (wo_well_founded w).
      induction wo_well_founded.
      constructor. intros.
      destruct y.
      * apply H1. assumption.
      * contradiction.
  - red; intros.
    destruct x, y; auto.
    specialize (wo_total_strict_order w w0) as [|[|]]; subst; auto.
Qed.

Lemma WO_succ_le (W : WO) :
  WO_le W (WO_succ W).
Proof.
  exists (fun x => Some x). split.
  - (* injectivity *)
    red; intros. inversion H; subst; clear H. reflexivity.
  - (* order preservation *)
    intros.
    simpl.
    assumption.
Qed.

Lemma wf_no_infinite_descending_chain
      {X : Type} {R : relation X} (wf : well_founded R)
      (f : X -> X) : inhabited X -> (forall x, R (f x) x) -> False.
Proof.
  intros.
  red in wf.
  destruct H as [x].
  induction x using (well_founded_ind wf).
  apply (H (f x)).
  auto.
Qed.

Lemma wf_no_infinite_descending_sequence
      {X : Type} {R : relation X} (wf : well_founded R)
      (f : nat -> X) : (forall n, R (f (S n)) (f n)) -> False.
Proof.
  intros.
  (* restrict [R] etc. to the image of f *)
  pose (X' := { x : X & { n : nat | x = f n }}).
  pose (R' := fun x y : X' => R (projT1 x) (projT1 y)).
  assert (well_founded R') as wf'.
  { red. intros [x].
    specialize (wf x).
    induction wf.
    constructor. intros [y].
    intros.
    unfold R' in H2. simpl in *.
    specialize (H1 y).
    intuition.
  }
  unshelve epose (f' := (fun x : X' => existT _ (f (S (proj1_sig (projT2 x)))) _) : X' -> X').
  { simpl. eexists. reflexivity. }
  apply (wf_no_infinite_descending_chain wf' f').
  - constructor. red. exists (f 0). eexists. reflexivity.
  - intros.
    red. destruct x. simpl. destruct s. simpl. subst.
    apply H.
Qed.

Lemma WO_succ_not_le (W : WO) :
  ~ WO_le (WO_succ W) W.
Proof.
  intro.
  destruct H as [f [? ?]].
  pose (f' := fix f' n := match n with O => f None | S n' => f (Some (f' n')) end).
  destruct (WO_WO W).
  apply (wf_no_infinite_descending_sequence wo_well_founded f').
  intros.
  induction n.
  - simpl. apply H0. simpl. apply I.
  - simpl. apply H0. simpl in *. assumption.
Qed.

Corollary WO_succ_lt (W : WO) :
  WO_lt W (WO_succ W).
Proof.
  split.
  - apply WO_succ_le.
  - apply WO_succ_not_le.
Qed.

Axiom WO_lt_wf : well_founded WO_lt.
Axiom WO_lt_tso : forall W V : WO,
    WO_lt W V \/ WO_eq W V \/ WO_lt V W.

Program Definition WO_reprs_WO : WO :=
  {| WO_T := WO_reprs;
     WO_R := WO_reprs_lt; |}.
Next Obligation.
split.
- red. intros [x' [x ?]]. subst.
  pose proof (WO_lt_wf x).
  induction H.
  constructor. intros [y' [y ?]] ?. subst.
  apply H0. apply WO_reprs_lt_correct in H1.
  assumption.
- red; intros [x' [x]] [y' [y]]. subst.
  rewrite ?WO_reprs_lt_correct.
  destruct (WO_lt_tso x y) as [|[|]]; try tauto.
  right; left.
  apply WO_repr_fn_correct1 in H.
  apply subset_eq_compat.
  assumption.
Qed.

(* Define the supremum of a family of ordinals.
   It’s carrier are those ordinals that are less than some element in [W].
*)
Program Definition WO_sup {I : Type} (W : I -> WO) : WO :=
  {| WO_T := { w : WO_reprs | exists i : I, WO_le (proj1_sig w) (W i) };
     WO_R w v := WO_reprs_lt (proj1_sig w) (proj1_sig v);
  |}.
Next Obligation.
  split.
  - red. intros [[x' [x]] [i ?]]. subst.
    simpl in *.
    pose proof (WO_lt_wf x).
    generalize dependent i.
    induction H.
    constructor. intros [[y' [y]] [j ?]] ?. subst.
    simpl in *.
    apply WO_reprs_lt_correct in H1.
    eapply (H0 y); try assumption.
  - red. intros [[x' [x]] [i]] [[y' [y]] [j]]. subst.
    simpl in *.
    destruct (WO_lt_tso x y) as [|[|]].
    + left. apply WO_reprs_lt_correct. assumption.
    + right; left.
      apply subset_eq_compat.
      apply subset_eq_compat.
      apply WO_repr_fn_correct1.
      assumption.
    + right; right. apply WO_reprs_lt_correct. assumption.
Qed.

Lemma WO_sup_le {I : Type} (W : I -> WO) (i : I) :
  WO_le (W i) (WO_sup W).
Proof.
Admitted.

Lemma WO_sup_0 {I : Type} (W : I -> WO) (W_upper_bound : WO) :
  (forall i, WO_le (W i) W_upper_bound) ->
  WO_le (WO_sup W) W_upper_bound.
Proof.
Admitted.

Theorem WO_sup_char {I : Type} (W : I -> WO) (W_sup : WO) :
  (forall W', (forall i, WO_le (W i) W') -> WO_le W_sup W') ->
  WO_eq W_sup (WO_sup W).
Proof.
Admitted.

(* Prove that [WO_sup] has the properties we expect of a supremum.

  Also show that every ordinal is either a limit or a successor ordinal.
*)

(*
Program Definition Ordinals_to_WO (ord : Ordinal) : WO :=
  {| WO_T := { ord' : Ordinal_reprs | ord' < ord }; |}.
Next Obligation.
  red; intros.
  destruct X, X0.
  exact (Ordinal_reprs_lt x x0).
Defined.
Next Obligation.
  split.
  - red. intros x.
    destruct x as [x].
    constructor. intros [[y]] ?.

Theorem Ordinals_eq_WO :
  WO_eq Ordinal_reprs_WO WO_reprs_WO.
Proof.
  split.
  - red.
    unshelve eexists.
    { intros.
      destruct X.
      apply constructive_indefinite_description in e.
      destruct e.
    unfold Ordinal_reprs_WO at 2. simpl.
    unfold WO_reprs at 2.
Admitted.
*)

Require Import Cardinals.

Coercion WO_cardinality (W : WO) : Cardinal := cardinality (WO_T W).
Coercion WO_reprs_cardinality (W : WO_reprs) : Cardinal := proj1_sig W.

Lemma WO_repr_fn_lt x y :
  WO_lt (WO_repr_fn x) (WO_repr_fn y) <->
  WO_lt x y.
Proof.
  intros; split; intros.
  - pose proof (WO_repr_fn_correct0 x).
    pose proof (WO_repr_fn_correct0 y).
    destruct H, H0, H1.
    split.
    + transitivity (WO_repr_fn x); try assumption.
      transitivity (WO_repr_fn y); assumption.
    + intro. contradict H2.
      transitivity y; try assumption.
      transitivity x; assumption.
  - pose proof (WO_repr_fn_correct0 x).
    pose proof (WO_repr_fn_correct0 y).
    destruct H, H0, H1.
    split.
    + transitivity x; try assumption.
      transitivity y; assumption.
    + intro. contradict H2.
      transitivity (WO_repr_fn x); try assumption.
      transitivity (WO_repr_fn y); assumption.
Qed.

Definition downward_closed {A : Type} (E : A -> Prop) (R : A -> A -> Prop) :=
  (forall x y, R x y -> In E y -> In E x).

(*
Lemma WO_self_embed (W : WO) :
  exists f : W -> WO_reprs,
*)

(* An ordinal is equivalent to the set of all ordinals strictly less than itself.
Lemma WO_self_embed (W : WO) :
  WO_eq W (WO_sup (fun W' => WO_lt W' W)).
Proof.
  split.
  - 
*)

Definition WO_ensemble_sup (E : Ensemble WO) : WO :=
  WO_sup (fun x : { w : WO | In E w } => proj1_sig x).

(* For every ordinal [W] there is a function [f] from the cardinal of [W] to an initial segment of the type of ordinals [WO] which is order preserving, injective. And the least (strict) upper bound of this initial segment is exactly [WO_eq] to [W] *)

Definition WO_hartogs (X : Cardinal) : WO := WO_ensemble_sup (fun W => le_cardinal W X).

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
  (*
  apply WO_next_lt.
  - red; intros.
    unfold In in *.
    apply le_cardinal_preorder with y.
    2: { assumption. }
    destruct H as [f [? ?]].
    exists f. assumption.
  - unfold In.
    exists id. red; intros; assumption.
*)
Admitted.

(* show that the hartogs number is the least upper bound. *)
Theorem hartogs' (X : Cardinal) (W : WO) :
  lt_cardinal X W ->
  WO_le (WO_hartogs X) W.
Proof.
Admitted.

Definition omega1 := WO_hartogs (cardinality nat).

(** Some general theory about strict orders, i.e. the irreflexive
    relations corresponding to partial orders. *)

From Coq Require Import Relation_Definitions.
From Coq Require Import Description SetoidClass.
From Coq Require Import FunctionalExtensionality.
From ZornsLemma Require Import Classical_Wf EnsemblesImplicit Image
     InverseImage Families.
Require Import FiniteTypes.
From Coq Require Import RelationClasses.

(** * Definitions of properties *)
Class Connected {X} (R : relation X) :=
  connected : forall x0 x1, ~ R x0 x1 -> ~ R x1 x0 -> x0 = x1.

Class TotalStrictOrder {X} (R : relation X) :=
  total_strict_order : forall x0 x1, R x0 x1 \/ x0 = x1 \/ R x1 x0.

(** Usually [StronglyConnected] would be defined using a (thight)
   apartness relation.
 *)
Class StronglyConnected {X} (R : relation X) :=
  strongly_connected : forall x0 x1, x0 <> x1 -> R x0 x1 \/ R x1 x0.

Section relations.
  Context {X : Type} (R : relation X).
  Context `{HRtrans : Transitive X R}.
  Context `{HRirrefl : Irreflexive X R}.
  Context `{HRasymm : Asymmetric X R}.

  (** ** Variations on total relations *)
  Lemma Connected_impl_TotalStrictOrder_dec `{Connected X R} :
    (forall x0 x1, R x0 x1 \/ ~ R x0 x1) ->
    TotalStrictOrder R.
  Proof using Type.
    intros Hdec x0 x1.
    destruct (Hdec x0 x1); auto.
    destruct (Hdec x1 x0); auto.
  Qed.

  Global Instance Connected_impl_TotalStrictOrder `{Connected X R} :
    TotalStrictOrder R.
  Proof using Type.
    apply Connected_impl_TotalStrictOrder_dec; auto.
    intros ? ?. apply classic.
  Qed.

  Global Instance TotalStrictOrder_impl_Connected `{TotalStrictOrder X R} :
    Connected R.
  Proof using Type.
    intros x0 x1 **.
    destruct (H x0 x1) as [|[|]]; tauto.
  Qed.

  (** Given decidable equality and a decidable order, the two notions
      are equivalent. *)
  Lemma StronglyConnected_Connected_dec `{StronglyConnected X R} :
    (forall x0 x1 : X, x0 = x1 \/ x0 <> x1) ->
    Connected R.
  Proof using Type.
    red in H.
    intros eqdec_p. red.
    intros.
    destruct (eqdec_p x0 x1); auto.
    apply H in H2.
    tauto.
  Qed.

  Lemma Connected_StronglyConnected_dec `{Connected X R} :
    (forall x0 x1, R x0 x1 \/ ~ R x0 x1) ->
    StronglyConnected R.
  Proof using Type.
    red.
    intros dec_rel **.
    destruct (dec_rel x0 x1); try tauto.
    destruct (dec_rel x1 x0); try tauto.
    contradict H.
    auto.
  Qed.

  (** using classical logic, they are equivalent. *)
  Global Instance StronglyConnected_Connected `{StronglyConnected X R} :
    Connected R.
  Proof using Type.
    apply StronglyConnected_Connected_dec.
    intros ? ?. apply classic.
  Qed.

  Global Instance Connected_StronglyConnected `{HRconn : Connected X R} :
    StronglyConnected R.
  Proof using Type.
    apply Connected_StronglyConnected_dec.
    intros ? ?. apply classic.
  Qed.

  Context `{HRconn : Connected X R}.

  (** A set of incomparable elements is called an antichain. *)
  Definition antichain (U : Ensemble X) :=
    forall x y, In U x -> In U y -> ~ R x y.

  (** If a relation is connected, then each antichain is a subsingleton. |*)
  Lemma Connected_impl_antichain_subsingleton U :
    antichain U ->
    forall x0 x1, In U x0 -> In U x1 -> x0 = x1.
  Proof using HRconn.
    auto.
  Qed.

  Lemma Connected_Classical_le_dec x0 x1 :
    (forall x0 x1, R x0 x1 \/ ~ R x0 x1) ->
    ~ R x0 x1 -> R x1 x0 \/ x0 = x1.
  Proof using HRconn.
    intros dec_rel **.
    destruct (dec_rel x1 x0); auto.
  Qed.

  Lemma Connected_Classical_le x0 x1 :
    ~ R x0 x1 -> R x1 x0 \/ x0 = x1.
  Proof using HRconn.
    apply Connected_Classical_le_dec.
    intros ? ?. apply classic.
  Qed.

  (** If for a relation each antichain is a subsingleton and it is
     irreflexive, then it is connected. *)
  Lemma Irreflexive_antichain_subsingleton_impl_Connected :
    (forall U : Ensemble X,
        antichain U ->
        forall x0 x1, In U x0 -> In U x1 -> x0 = x1) ->
    Connected R.
  Proof using HRirrefl.
    intros Ha x0 x1 ? ?.
    specialize (Ha (Couple x0 x1)).
    apply Ha; clear Ha.
    2: left.
    2: right.
    intros ? ? ? ?.
    destruct H1, H2; try assumption.
    all: apply irreflexivity.
  Qed.

  (** ** Downwards closed sets and initial segments
    and their relation with transitivity. *)
  Class DownwardsClosed (U : Ensemble X) :=
    downwards_closed : forall x, In U x -> forall y, R y x -> In U y.

  (** A simple way of constructing downwards closed sets. *)
  Definition downwards_closure (U : Ensemble X) :=
    Union U (fun x => exists y, In U y /\ R x y).

  Global Instance downwards_closure_DownwardsClosed U :
    DownwardsClosed (downwards_closure U).
  Proof using HRtrans.
    clear HRirrefl HRconn HRasymm.
    intros x Hx y Hy.
    destruct Hx as [|x [z [Hz0 Hz1]]].
    - (* [In U x] *)
      right; firstorder.
    - right. exists z. split; auto.
      transitivity x; auto.
  Qed.

  (** Another way how downwards closed sets arise. *)
  Definition initial_segment (x : X) : Ensemble X :=
    fun t : X => R t x.

  (** Note that care is taken to avoid using [HRtrans]. *)
  Fact Transitive_initial_segment_downwards_closed :
    Transitive R <->
      forall x : X, DownwardsClosed (initial_segment x).
  Proof using X R.
    clear HRtrans.
    firstorder.
  Qed.

  Global Instance initial_segment_downwards_closed (x : X) :
    DownwardsClosed (initial_segment x).
  Proof using HRtrans.
    apply Transitive_initial_segment_downwards_closed.
    assumption.
  Qed.

  Definition closed_initial_segment (x : X) :=
    (fun y => ~ R x y).

  Global Instance closed_initial_segment_DownwardsClosed (x : X) :
    DownwardsClosed (closed_initial_segment x).
  Proof using HRtrans.
    intros y Hxy z Hz Hzx.
    apply Hxy.
    transitivity z; auto.
  Qed.

  Lemma closed_initial_segment_irreflexive :
    Irreflexive R <->
      forall x : X, In (closed_initial_segment x) x.
  Proof using Type.
    clear HRirrefl.
    firstorder.
  Qed.

  (** ** Successors, minimal and maximal elements *)
  Definition succeeded_by (x0 x1 : X) : Prop :=
    R x0 x1 /\
    forall x2 : X,
      R x0 x2 ->
      ~ R x2 x1.

  Definition maximal_element (x : X) : Prop :=
    forall y : X, ~ R x y.

  Definition minimal_element_ens (U : Ensemble X) (x : X) :=
    In U x /\
      forall y : X, In U y -> ~ R y x.

  (* characterize [succeeded_by] using [minimal_element_ens] *)
  Lemma succeeded_by_char_minimal (x0 x1 : X) :
    succeeded_by x0 x1 =
      minimal_element_ens (fun y => R x0 y) x1.
  Proof using Type.
    unfold succeeded_by, minimal_element_ens.
    unfold In.
    reflexivity.
  Qed.

  (** the predecessor is unique in connected orders. *)
  Lemma succeeded_by_pred_unique x0 x1 y :
    succeeded_by x0 y ->
    succeeded_by x1 y ->
    x0 = x1.
  Proof.
    intros [H00 H01] [H10 H11].
    apply connected.
    - intros H2.
      apply H01 in H10; auto.
    - intros H2.
      apply H11 in H00; auto.
  Qed.

  Lemma minimal_element_property_char_minimal :
    minimal_element_property X R =
      forall S, Inhabited S -> exists x, minimal_element_ens S x.
  Proof using Type.
    reflexivity.
  Qed.

  Lemma minimal_element_ens_unique U x0 x1 :
    minimal_element_ens U x0 ->
    minimal_element_ens U x1 ->
    x0 = x1.
  Proof using HRconn.
    intros [H00 H01] [H10 H11].
    specialize (H01 x1 H10).
    specialize (H11 x0 H00).
    apply connected; auto.
  Qed.

  (** ** Bounds and suprema *)
  Definition is_strict_upper_bound (U : Ensemble X) (x : X) :=
    forall y, In U y -> R y x.

  Definition is_upper_bound (U : Ensemble X) (x : X) :=
    forall y, In U y -> ~ R x y.

  Definition supremum (U : Ensemble X) (x : X) :=
    minimal_element_ens (is_upper_bound U) x.

  Lemma connected_supremum_unique U x0 x1 `{Connected X R} :
    supremum U x0 ->
    supremum U x1 ->
    x0 = x1.
  Proof using Type.
    intros [Hx0b Hx0s] [Hx1b Hx1s].
    apply Hx0s in Hx1b.
    apply Hx1s in Hx0b.
    apply connected; auto.
  Qed.

  Lemma upper_bound_Included U V x :
    Included U V ->
    is_upper_bound V x ->
    is_upper_bound U x.
  Proof using Type.
    clear HRasymm HRconn.
    firstorder.
  Qed.

  Lemma supremum_Included U V supU supV :
    Included U V ->
    supremum U supU ->
    supremum V supV ->
    ~ R supV supU.
  Proof using Type.
    intros HUV HsupU HsupV.
    apply HsupU. clear HsupU.
    apply (upper_bound_Included U V supV);
      auto.
    apply HsupV.
  Qed.

  Lemma downwards_closure_upper_bound U x :
    is_upper_bound (downwards_closure U) x <->
    is_upper_bound U x.
  Proof using HRtrans.
    split.
    - intros Hx y Hy.
      apply Hx.
      left. assumption.
    - intros Hx _ [y Hy|y [z Hz]].
      + firstorder.
      + intros ?.
        firstorder.
  Qed.

  Lemma downwards_closure_strict_upper_bound U x :
    is_strict_upper_bound (downwards_closure U) x <->
    is_strict_upper_bound U x.
  Proof using HRtrans.
    split.
    - intros Hx y Hy.
      apply Hx.
      left. assumption.
    - intros Hx _ [y Hy|y [z Hz]].
      + firstorder.
      + transitivity z; firstorder.
  Qed.

  Lemma downwards_closure_supremum U x :
    supremum (downwards_closure U) x <->
      supremum U x.
  Proof using HRtrans.
    unfold supremum.
    unfold minimal_element_ens.
    unfold In.
    split; intros [Hx0 Hx1]; split.
    - rewrite downwards_closure_upper_bound in Hx0;
        auto.
    - intros y.
      specialize (Hx1 y).
      rewrite downwards_closure_upper_bound in Hx1; auto.
    - rewrite downwards_closure_upper_bound; auto.
    - intros y.
      rewrite downwards_closure_upper_bound; auto.
  Qed.

  Lemma is_strict_upper_bound_is_upper_bound U (x : X) `{HR : Asymmetric X R} :
    is_strict_upper_bound U x ->
    is_upper_bound U x.
  Proof using Type.
    unfold is_strict_upper_bound, is_upper_bound.
    intros ** ?.
    apply H in H0.
    apply asymmetry in H0; auto.
  Qed.

  (** something greater than the supremum of [U] is certainly not in
     [U] *)
  Lemma compare_supremum_not_In U x supU :
    supremum U supU ->
    R supU x ->
    ~ In U x.
  Proof.
    intros Hsup HR Hx.
    apply Hsup in Hx.
    contradiction.
  Qed.

  (** in particular, the successor of the supremum (if it exists) is not
     in [U]. *)
  Corollary supremum_successor_not_In U succ supU :
    supremum U supU ->
    succeeded_by supU succ ->
    ~ In U succ.
  Proof.
    intros Hsup Hsucc.
    apply (compare_supremum_not_In U succ supU); auto.
    apply Hsucc.
  Qed.

  Lemma succeeded_by_order_equiv_dec x0 x1 y0 y1 :
    (forall x0 x1, R x0 x1 \/ ~ R x0 x1) ->
    succeeded_by x0 x1 ->
    succeeded_by y0 y1 ->
    R x0 y0 <-> R x1 y1.
  Proof using HRconn HRtrans.
    intros Hdec [Hx0 Hx1] [Hy0 Hy1].
    split; intros HR.
    - specialize (Hx1 _ HR).
      apply Connected_Classical_le_dec in Hx1 as [|];
        try typeclasses eauto; subst; auto.
      transitivity y0; auto.
    - destruct (Hdec x0 y0) as [|H2]; auto; exfalso.
      apply Connected_Classical_le_dec in H2 as [|];
        try typeclasses eauto; subst; auto.
      + apply Hy1 in H.
        contradict H.
        transitivity x1; auto.
      + apply Hy1 in HR; auto.
  Qed.

  Lemma succeeded_by_order_equiv x0 x1 y0 y1 :
    succeeded_by x0 x1 ->
    succeeded_by y0 y1 ->
    R x0 y0 <-> R x1 y1.
  Proof using HRconn HRtrans.
    apply succeeded_by_order_equiv_dec.
    intros ? ?. apply classic.
  Qed.

  (** if the supremum of a set [U] is a successor of some element, then
     the supremum is in [U] *)
  Lemma supremum_is_successor_implies_In_dec U supU pred :
    supremum U supU ->
    succeeded_by pred supU ->
    ~ ~ In U supU.
  Proof using HRconn.
    intros Hsup Hsucc.
    intros HsupU.
    assert (is_upper_bound U pred).
    { intros x Hx.
      red in Hsucc.
      intros HRx.
      apply Hsucc in HRx.
      pose proof Hx as Hx0.
      apply Hsup in Hx0.
      pose proof (connected _ _ HRx Hx0).
      subst.
      contradiction.
    }
    apply Hsup in H.
    apply H.
    apply Hsucc.
  Qed.

  Lemma supremum_is_successor_implies_In U supU pred :
    supremum U supU ->
    succeeded_by pred supU ->
    In U supU.
  Proof using HRconn.
    intros.
    apply NNPP.
    eapply supremum_is_successor_implies_In_dec;
      eauto.
  Qed.

  (** if the supremum is a strict upper bound, then it does not have an immediate predecessor.
      In the theory of well-orders, such elements are called "limit". *)
  Lemma supremum_strict_upper_bound_is_limit U sup :
    supremum U sup ->
    is_strict_upper_bound U sup ->
    ~ (exists y : X, succeeded_by y sup).
  Proof using HRconn HRirrefl.
    intros Hsup Hbound [pred Hsucc].
    apply supremum_is_successor_implies_In with (U := U) in Hsucc;
      auto.
    apply Hbound in Hsucc.
    apply irreflexivity in Hsucc.
    assumption.
  Qed.

  Lemma closed_initial_segment_supremum (x : X) :
    supremum (closed_initial_segment x) x.
  Proof using HRirrefl.
    split.
    - intros y Hy.
      assumption.
    - intros.
      intros ?.
      apply (H x); auto.
      apply HRirrefl.
  Qed.
End relations.

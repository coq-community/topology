From Coq Require Import Relation_Definitions.
From Coq Require Import Description SetoidClass.
From Coq Require Import FunctionalExtensionality.
From ZornsLemma Require Import Classical_Wf EnsemblesImplicit Image
     InverseImage Families.
From ZornsLemma Require Import FiniteTypes StrictOrders.
From Coq Require Import RelationClasses Program.Subset.

Class Injective {X Y} (f : X -> Y) :=
  injective_class : Image.injective f.

Global Instance proj1_sig_Injective {X P} :
  Injective (@proj1_sig X P).
Proof.
  red. red. apply subset_eq.
Qed.

(** ** A helper from set theory *)
Lemma Ensemble_neq {X : Type} (U V : Ensemble X) :
  U <> V ->
  (exists x, In U x /\ ~ In V x) \/
    (exists x, ~ In U x /\ In V x).
Proof.
  intros.
  apply NNPP.
  intros ?.
  apply H.
  apply Extensionality_Ensembles.
  apply not_or_and in H0 as [].
  pose proof (not_ex_all_not _ _ H0).
  pose proof (not_ex_all_not _ _ H1).
  clear H0 H1.
  simpl in *.
  split; red; intros; specialize (H2 x); specialize (H3 x); tauto.
Qed.

(** * Some additional helpers from logic and set theory *)
Lemma Same_set_iff_In {X} (U V : Ensemble X) :
  (forall x, In U x <-> In V x) <-> Same_set U V.
Proof.
  firstorder.
Qed.

Lemma exists_iff_Proper {X} (P Q : X -> Prop) :
  (forall x, P x <-> Q x) ->
  ((exists x, P x) <-> (exists x, Q x)).
Proof.
  firstorder.
Qed.

Lemma exists_unique_proper {A : Type} (P Q : A -> Prop) :
  (forall a, P a <-> Q a) ->
  (exists! a, P a) <-> (exists! a, Q a).
Proof.
  firstorder.
Qed.

(** * General theory of relations *)

(** ** Mappings between relations *)
Class RelationPreserve {T0 T1} (R0 : relation T0) (R1 : relation T1)
      (f : T0 -> T1) :=
  relation_preserve : forall x y : T0, R0 x y -> R1 (f x) (f y).
Class RelationReflect {T0 T1} (R0 : relation T0) (R1 : relation T1)
      (f : T0 -> T1) :=
  relation_reflect : forall x y : T0, R1 (f x) (f y) -> R0 x y.

Global Instance RelationPreserve_compose {T0 T1 T2 R0} R1 {R2} f g
       `{RelationPreserve T0 T1 R0 R1 f}
       `{RelationPreserve T1 T2 R1 R2 g} :
  RelationPreserve R0 R2 (compose g f).
Proof.
  red. intros.
  apply H0.
  apply H.
  assumption.
Qed.

Global Instance RelationReflect_compose {T0 T1 T2 R0} R1 {R2} f g
       `{RelationReflect T0 T1 R0 R1 f}
       `{RelationReflect T1 T2 R1 R2 g} :
  RelationReflect R0 R2 (compose g f).
Proof.
  red. intros.
  apply H0 in H1.
  apply H in H1.
  assumption.
Qed.

(** Most definitions of simulation I found omit [sim_reflects],
   but it is a useful property for [simulation_initial_segment] and
   [simulation_compose].

   For (strongly connected) orders, we can recover [sim_reflects] from
   [sim_preserves] by a lemma [RelationPreserve_Reflects_Order].
   And using classical logic every [Connected] order is
   [StronglyConnected], and using classical logic every [WellOrder] is
   [Connected] so every simulation of well-orders has
   [RelationReflect].
*)
Class Simulation {X Y : Type} (R0 : relation X) (R1 : relation Y)
      (f : X -> Y) :=
  { sim_preserves :> RelationPreserve R0 R1 f;
    sim_reflects :> RelationReflect R0 R1 f;
    (* i.e. the image of [f] is downwards closed. *)
    simulation : (forall x t, R1 t (f x) -> exists y, t = f y);
  }.

(**
Restate the [simulation] condition. But we use the def. above instead
of the "conceptual def." below, because it is easier to work with,
since then we don’t have to deal with the inductive def. of [Im].
 *)
Global Instance Simulation_Im_downwards_closed {X Y R0 R1} {f : X -> Y}
     `{Simulation _ _ R0 R1 f} :
  DownwardsClosed R1 (Im Full_set f).
Proof.
  lazy. intros.
  inversion H0; subst; clear H0.
  apply simulation in H1 as [x1].
  subst. apply Im_def. constructor.
Qed.

Lemma simulation_initial_segment {X Y : Type} R0 R1 (f : X -> Y)
      `{Simulation _ _ R0 R1 f} :
  forall x : X,
  Same_set (Im (initial_segment R0 x) f) (initial_segment R1 (f x)).
Proof.
  intros.
  split; red; intros ? Hin.
  - inversion Hin; subst; clear Hin.
    lazy. apply relation_preserve.
    assumption.
  - lazy in Hin.
    pose proof Hin as Hin0.
    apply simulation in Hin0 as [].
    subst.
    apply Im_def.
    apply H.
    assumption.
Qed.

Global Instance Simulation_identity {X R} : Simulation R R (@id X).
Proof.
  constructor; lazy; eauto.
Qed.

Global Instance Simulation_compose {T0 T1 T2 R0 R1 R2} f g
       `{Simulation T0 T1 R0 R1 f}
       `{Simulation T1 T2 R1 R2 g} :
  Simulation R0 R2 (compose g f).
Proof.
  constructor; try typeclasses eauto.
  intros. unfold compose in *.
  pose proof H1.
  apply simulation in H2 as [z].
  subst.
  apply H0 in H1.
  apply simulation in H1 as [y].
  subst.
  exists y. reflexivity.
Qed.

Lemma RelationPreserve_inverse {T0 T1 R0 R1} f g :
  (forall x : T0, g (f x) = x) ->
  (forall x : T1, f (g x) = x) ->
  RelationPreserve R0 R1 f ->
  RelationReflect R1 R0 g.
Proof.
  intros.
  intros ? ?.
  rewrite <- (H0 x) at 2.
  rewrite <- (H0 y) at 2.
  apply H1.
Qed.

Lemma RelationReflect_inverse {T0 T1 R0 R1} f g :
  (forall x : T0, g (f x) = x) ->
  (forall x : T1, f (g x) = x) ->
  RelationReflect R0 R1 f ->
  RelationPreserve R1 R0 g.
Proof.
  intros.
  intros ? ?.
  rewrite <- (H0 x) at 1.
  rewrite <- (H0 y) at 1.
  apply H1.
Qed.

Lemma Simulation_inverse {T0 T1 R0 R1} f g :
  (forall x : T0, g (f x) = x) ->
  (forall x : T1, f (g x) = x) ->
  Simulation R0 R1 f ->
  Simulation R1 R0 g.
Proof.
  intros.
  constructor.
  - eapply RelationReflect_inverse; eauto.
    typeclasses eauto.
  - eapply RelationPreserve_inverse; eauto.
    typeclasses eauto.
  - intros. exists (f t). congruence.
Qed.

(** * Beginning of Order Theory *)
Global Instance Irrefl_Trans_impl_Asymmetric {X R} `{Irreflexive X R} `{Transitive X R} :
  Asymmetric R.
Proof.
  red. intros.
  apply (H x).
  transitivity y;
    assumption.
Qed.

Corollary RelationPreserve_irrefl_inverse_image_antichain {X Y : Type}
          R0 R1 (f : X -> Y)
          `{Irreflexive Y R1} `{RelationPreserve _ _ R0 R1 f} :
  forall y : Y,
    antichain R0 (inverse_image f (Singleton y)).
Proof.
  intros.
  intros x0 x1 ? ? ?.
  inversion H1; subst; clear H1.
  inversion H2; subst; clear H2.
  inversion H1; subst; clear H1.
  inversion H4; subst; clear H4.
  apply relation_preserve in H3.
  rewrite H2 in H3.
  apply (H (f x0)).
  assumption.
Qed.

Global Instance RelationPreserve_Reflects_Order {X Y R0 R1 f}
         `{HR1i : Irreflexive _ R1} `{HR1a : Asymmetric _ R1}
         `{HR0c : StronglyConnected _ R0}
         `{RelationPreserve X Y R0 R1 f} :
  RelationReflect R0 R1 f.
Proof.
  red. intros.
  destruct (HR0c x y); auto.
  - intros ?. subst.
    apply irreflexivity in H0.
    assumption.
  - exfalso.
    apply (@asymmetry _ R1 _ (f x) (f y));
      try assumption.
    apply H.
    assumption.
Qed.

Global Instance RelationPreserve_Connected_Irreflexive_Inj
       {X Y R0 R1 f}
       `{Connected X R0} `{Irreflexive Y R1}
       `{RelationPreserve _ _ R0 R1 f} :
  Injective f.
Proof.
  intros ? ? ?.
  apply connected.
  all: apply (RelationPreserve_irrefl_inverse_image_antichain
                _ _ f (f x)).
  all: constructor; rewrite H2; constructor.
Qed.

(** If the maximal element of [R1] is in the image of [f] then [f] is surjective. *)
Lemma Simulation_surjective_dec {T0 R0 T1 R1} (f : T0 -> T1) `{Simulation _ _ R0 R1 f}
      `{StronglyConnected _ R1} x :
  (forall y0 y1 : T1, y0 = y1 \/ y0 <> y1) ->
  maximal_element R1 (f x) ->
  surjective f.
Proof.
  intros eqdec_p **.
  intros ?.
  red in H1.
  red in H0.
  specialize (H1 y).
  destruct (eqdec_p (f x) y).
  { subst. eauto. }
  specialize (H0 (f x) y H2) as [|];
    try contradiction.
  apply simulation in H0.
  destruct H0 as [x0];
    exists x0; symmetry; assumption.
Qed.

Lemma Simulation_surjective {T0 R0 T1 R1} (f : T0 -> T1) `{Simulation _ _ R0 R1 f}
      `{StronglyConnected _ R1} x :
  maximal_element R1 (f x) ->
  surjective f.
Proof.
  eapply Simulation_surjective_dec; eauto.
  intros ? ?. apply classic.
Qed.

Class WeaklyExtensional {X : Type} (R : relation X) :=
  weakly_extensional : forall x y,
      Same_set (initial_segment R x) (initial_segment R y) -> x = y.

(** Introduce well-founded relations and their basic properties, by
    recalling/restating them from the standard library. *)
Class WellFounded {X : Type} (R : relation X) :=
  well_founded : well_founded R.

Definition well_founded_ind {X : Type} (R : relation X)
           `{H : WellFounded X R} (P : X -> Prop)
           (H0 : forall x : X, (forall y, R y x -> P y) -> P x) :
  forall x : X, P x :=
  Wf.well_founded_ind well_founded P H0.

Definition well_founded_induction {X : Type} (R : relation X)
           `{H : WellFounded X R} (P : X -> Set)
           (H0 : forall x : X, (forall y, R y x -> P y) -> P x) :
  forall x : X, P x :=
  Wf.well_founded_induction well_founded P H0.

Definition well_founded_rect {X : Type} (R : relation X)
           `{H : WellFounded X R} (P : X -> Type)
           (H0 : forall x : X, (forall y, R y x -> P y) -> P x) :
  forall x : X, P x :=
  Wf.well_founded_induction_type well_founded P H0.

(** Prop. 2.5 from n-lab page "well-founded relation" 2021-11-21 *)
Lemma simulation_uniqueness {X Y : Type} R0 R1 (f g : X -> Y)
      `{WellFounded X R0} `{WeaklyExtensional Y R1}
      `{Simulation _ _ R0 R1 f} `{Simulation _ _ R0 R1 g} :
  (forall x, f x = g x).
Proof.
  apply (well_founded_induction R0).
  intros.
  apply H0.
  erewrite <- !simulation_initial_segment; try eassumption.
  unfold initial_segment.
  split; red; intros ? Ha;
    inversion Ha; subst; clear Ha;
    [rewrite H3 | rewrite <- H3];
    try assumption; apply Im_def;
    assumption.
Qed.

(**
Prop. 2.3 from n-lab page "well-founded relation" 2021-11-21
Any subset [A] of a well-order [R] that has no minimal element
(i.e. below each element [a] of [A] there is another element [b])
is empty.
 *)
Lemma well_founded_no_minimal_element_impl_empty
      {X : Type} (R : relation X) `{H : WellFounded X R}:
  forall A : Ensemble X,
    (forall a, In A a -> exists b, In A b /\ R b a) ->
    (forall x, ~ In A x).
Proof.
  intros ? ?.
  apply (well_founded_ind R (fun u => ~ In A u /\
                                     (forall x, R x u -> ~ In A x))).
  intros.
  simpl.
  split.
  - intros ?.
    specialize (H0 x H2) as [y []].
    specialize (H1 y H3) as [].
    contradiction.
  - intros.
    apply H1.
    assumption.
Qed.

Global Instance wf_irrefl {X R} `{H : WellFounded X R} : Irreflexive R.
Proof.
  lazy.
  intros ? ?.
  unshelve eapply (well_founded_no_minimal_element_impl_empty
                     R (Singleton x) _ x).
  2: now constructor.
  intros.
  exists x. firstorder.
  inversion H1; subst; clear H1.
  assumption.
Qed.

Global Instance wf_asymm {X : Type} (R : relation X)
       `{H : WellFounded X R} : Asymmetric R.
Proof.
  lazy.
  intros ? ? ? ?.
  unshelve eapply (well_founded_no_minimal_element_impl_empty
                     R (Couple x y) _ x).
  2: now left.
  intros.
  destruct H2.
  - exists y; auto with sets.
  - exists x; auto with sets.
Qed.

(** A well-founded set has no infinite descending sequences. *)
Lemma wf_no_inf_desc_seq {X : Type} (R : relation X)
      `{H : WellFounded X R} :
  ~ (exists a : nat -> X, forall n, R (a (S n)) (a n)).
Proof.
  intros [a].
  unshelve eapply (well_founded_no_minimal_element_impl_empty
                     R (Im Full_set a) _ (a 0)).
  2: {
    apply Im_def.
    constructor.
  }
  intros.
  inversion H1; subst; clear H1.
  exists (a (S x)).
  split.
  - apply Im_def.
    constructor.
  - apply H0.
Qed.

(** * Well Orders *)
Class WellOrder {X} (R : relation X) :=
  { wo_WF :> WellFounded R;
    wo_trans :> Transitive R;
    wo_wext :> WeaklyExtensional R;
  }.

Global Existing Instance wo_WF.
Global Existing Instance wo_trans.
Global Existing Instance wo_wext.

(** ** Constructions *)
(** *** The (external) successor *)
(** Adjoins a "top" (rightmost) element to a relation. *)
Definition rel_adjoin_top {X} (R : relation X) : relation (option X) :=
  fun x y =>
    match x, y with
    | None, _ => False
    | Some _, None => True
    | Some a, Some b => R a b
    end.

Global Instance rel_adjoin_top_WellFounded {X R} `{WellFounded X R} :
  WellFounded (rel_adjoin_top R).
Proof.
  assert (forall w, Acc (rel_adjoin_top R) (Some w)).
  { intros.
    specialize (H w).
    induction H.
    constructor. intros.
    destruct y; try contradiction.
    apply H0. assumption.
  }
  do 2 red. intros [|]; auto.
  constructor.
  intros [|]; try contradiction.
  auto.
Defined.

Global Instance rel_adjoin_top_Transitive {X R} `{Transitive X R} :
  Transitive (rel_adjoin_top R).
Proof.
  intros [|] [|] [|]; auto; try contradiction.
  simpl.
  apply transitivity.
Qed.

Global Instance rel_adjoin_top_Irreflexive {X R} `{Irreflexive X R} :
  Irreflexive (rel_adjoin_top R).
Proof.
  intros [|]; lazy; auto.
  apply H.
Qed.

Global Instance rel_adjoin_top_WeaklyExtensional {X R} `{Irreflexive X R} `{WeaklyExtensional X R} :
  WeaklyExtensional (rel_adjoin_top R).
Proof.
  intros [|] [|]; auto; try contradiction.
  - (* Some _ = Some _ *)
    intros.
    assert (x = x0); try congruence.
    apply weakly_extensional.
    assert (forall w w0,
               Included (initial_segment (rel_adjoin_top R) (Some w))
                        (initial_segment (rel_adjoin_top R) (Some w0)) ->
               Included (initial_segment R w)
                        (initial_segment R w0)) as HL.
    { clear.
      unfold Included, In, initial_segment.
      intros.
      specialize (H (Some x)).
      apply H. assumption.
    }
    split; apply HL; apply H1.
  - (* Some _ = None *)
    intros.
    assert (rel_adjoin_top R (Some x) (Some x)).
    { apply H1. lazy. auto. }
    exfalso.
    apply (@irreflexivity _ R _ x).
    assumption.
  - (* None = Some _ *)
    intros.
    assert (rel_adjoin_top R (Some x) (Some x)).
    { apply H1. lazy. auto. }
    exfalso.
    apply (@irreflexivity _ R _ x).
    assumption.
Qed.

Global Instance rel_adjoin_top_StronglyConnected {X R}
       `{HS : StronglyConnected X R} :
  StronglyConnected (rel_adjoin_top R).
Proof.
  intros [|] [|]; simpl; try tauto.
  intros. apply HS. congruence.
Qed.

Global Instance rel_adjoin_top_WellOrder {X} (R : relation X) `{WellOrder X R} :
  WellOrder (rel_adjoin_top R).
Proof.
  constructor.
  - apply rel_adjoin_top_WellFounded.
  - apply rel_adjoin_top_Transitive.
  - apply rel_adjoin_top_WeaklyExtensional.
Qed.

Global Instance well_order_successor_Some_Simulation {T} R `{W : WellOrder T R} :
  Simulation R (rel_adjoin_top R) Some.
Proof.
  split.
  1, 2: red; intros; assumption.
  intros.
  destruct t; try contradiction.
  eauto.
Qed.

(** The (unique) maximal element of [rel_adjoin_top R] is [None]. *)
Lemma rel_adjoin_top_maximal_element {T} (R : relation T) :
  maximal_element (rel_adjoin_top R) None.
Proof.
  red. intros [|]; auto.
Qed.

Lemma rel_adjoin_top_maximal_element_None {T} (R : relation T) x :
  maximal_element (rel_adjoin_top R) x -> x = None.
Proof.
  intros. red in H.
  destruct x; auto.
  specialize (H None).
  lazy in H. contradiction.
Qed.

(** *** Lexicographic Product *)
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Relation_Operators.

(** only here for compatibility reasons. If support for coq v8.15 and lower is dropped,
the next three definitions and lemmas can be removed. *)
Definition slexprod {A B} (leA : relation A) (leB : relation B) p1 p2 :=
  lexprod _ _ leA (fun _ => leB)
    (existT (fun _ => B) (fst p1) (snd p1)) (existT (fun _ => B) (fst p2) (snd p2)).

Definition left_slex {A B} (leA : relation A) (leB : relation B) a0 a1 b0 b1 :
  leA a0 a1 ->
  @slexprod A B leA leB (a0, b0) (a1, b1).
Proof.
  intros.
  unfold slexprod.
  constructor.
  assumption.
Qed.

Definition right_slex {A B} (leA : relation A) (leB : relation B) a b0 b1 :
  leB b0 b1 ->
  @slexprod A B leA leB (a, b0) (a, b1).
Proof.
  intros.
  red.
  apply right_lex.
  assumption.
Qed.

Global Instance slexprod_Transitive {A B leA leB}
       `{Transitive A leA} `{Transitive B leB} :
  Transitive (slexprod leA leB).
Proof.
  red. intros.
  revert z H2.
  unfold slexprod in *.
  remember (existT (fun _ => B) (fst x) (snd x)) as xx.
  remember (existT (fun _ => B) (fst y) (snd y)) as yy.
  revert x y Heqxx Heqyy.
  induction H1.
  - intros.
    inversion H2; subst; clear H2.
    + apply left_slex.
      transitivity x'; assumption.
    + apply left_slex. assumption.
  - intros.
    inversion H2; subst; clear H2.
    + apply left_slex. assumption.
    + apply right_slex.
      transitivity y'; assumption.
Qed.

Global Instance slexprod_WeaklyExtensional {A B leA leB}
       `{HA0 : WeaklyExtensional A leA} `{HB0 : WeaklyExtensional B leB}
       `{HA1 : Irreflexive A leA} `{HB1 : Irreflexive B leB} :
  WeaklyExtensional (slexprod leA leB).
Proof.
  red; intros [] [] Heq.
  assert (~ leA a a0) as Haa0.
  2: assert (~ leA a0 a) as Ha0a.
  1, 2: intros ?.
  1: assert (slexprod leA leB (a, b) (a0, b0)) as Hl
      by (apply left_slex; assumption).
  2: assert (slexprod leA leB (a0, b0) (a, b)) as Hl
      by (apply left_slex; assumption).
  1, 2: apply Heq in Hl.
  1, 2: inversion Hl; subst; clear Hl.
  all: try match goal with
           | H : _ ?a ?a |- False =>
               apply irreflexivity in H; assumption
           end.
  assert (a0 = a).
  { apply weakly_extensional.
    split; lazy; intros.
    - assert (slexprod leA leB (x, b) (a0, b0)) as Hl.
      { apply left_slex. assumption. }
      apply Heq in Hl.
      inversion Hl; subst; clear Hl; try assumption.
      contradiction.
    - assert (slexprod leA leB (x, b) (a, b)) as Hl.
      { apply left_slex. assumption. }
      apply Heq in Hl.
      inversion Hl; subst; clear Hl; try assumption.
      contradiction.
  }
  subst.
  assert (b0 = b).
  { apply weakly_extensional.
    split; lazy; intros.
    - assert (slexprod leA leB (a, x) (a, b0)) as Hl.
      { apply right_slex; assumption. }
      apply Heq in Hl.
      inversion Hl; subst; clear Hl; try assumption.
      exfalso. auto using irreflexivity.
    - assert (slexprod leA leB (a, x) (a, b)) as Hl.
      { apply right_slex; assumption. }
      apply Heq in Hl.
      inversion Hl; subst; clear Hl; try assumption.
      exfalso. auto using irreflexivity.
  }
  congruence.
Qed.

(** re-using the proof from the stdlib of coq v8.16 *)
Theorem wf_slexprod {A B} leA leB:
  WellFounded leA -> WellFounded leB -> WellFounded (@slexprod A B leA leB).
Proof.
  intros. unfold slexprod.
  red. red. intros ?.
  assert (forall A B (R : B -> B -> Prop) (f : A -> B),
           forall x:A, Acc R (f x) -> Acc (fun x y : A => R (f x) (f y)) x)
           as Acc_inverse_image.
  2: {
    apply Acc_inverse_image. apply wf_lexprod; auto.
  }
  clear.
  intros.
  remember (f x) as y.
  revert x Heqy.
  induction H as [y _ IHAcc]; intros x H.
  apply Acc_intro; intros y0 H1.
  apply (IHAcc (f y0)); try trivial.
  rewrite H; trivial.
Qed.

Global Instance slexprod_WellFounded {A B leA leB}
       `{wfA : WellFounded A leA} `{wfB : WellFounded B leB} :
  WellFounded (slexprod leA leB).
Proof.
  apply wf_slexprod; auto.
Defined.

(** the following fact is not actually necessary *)
Global Instance slexprod_WellOrder {A B} R0 R1 `{WellOrder A R0} `{WellOrder B R1} :
  WellOrder (slexprod R0 R1).
Proof.
  constructor; typeclasses eauto.
Qed.

(** ** Well orders are connected
Assuming classical logic. For this we needed that the
lexicographic product of two well-orders is again well-ordered.
*)
Global Instance WellOrder_Connected_Classical {W R}
       `{HR : WellOrder W R} : Connected R.
Proof.
  pose (fun p => ~ R (fst p) (snd p) /\
                ~ R (snd p) (fst p) /\
                (fst p) <> (snd p)) as A.
  cut (~ Inhabited A).
  { intros Hinh x0 x1 ? ?.
    apply NNPP.
    intros ?.
    apply Hinh.
    exists (x0, x1).
    lazy. tauto.
  }
  intros Hinh.
  apply (WF_implies_MEP _ (slexprod R R)) in Hinh as [[a b] [[HRab []] Hab]].
  2: now apply slexprod_WellFounded.
  simpl in *.
  assert (forall x, R x b -> R x a).
  { intros x Hxb.
    assert (~ R a x).
    { intros ?.
      apply HRab.
      transitivity x; assumption.
    }
    apply NNPP.
    intros ?.
    apply (Hab (a, x)).
    2: apply right_slex; assumption.
    repeat split; simpl; auto.
    intros ?. subst.
    contradiction.
  }
  pose (fun a' => (R a' a \/ a' = a) /\
                 (forall x, R x b -> R x a'))
    as B.
  assert (Inhabited B) as HBinh.
  { exists a.
    split; try assumption.
    right. reflexivity.
  }
  apply (WF_implies_MEP _ R) in HBinh as [a' [[Ha'0 Ha'1] Ha'2]].
  2: apply HR.
  cut (a' = b).
  { intros. subst. firstorder. }
  apply weakly_extensional.
  split; red.
  2: assumption.
  lazy. intros x ?.
  assert (R x a).
  { destruct Ha'0; subst; try assumption.
    transitivity a'; assumption.
  }
  assert (~ R b x).
  { intros ?.
    assert (R b a').
    { transitivity x; assumption. }
    unfold B in Ha'2.
    lazy in Ha'2.
    clear B.
    specialize (Ha'2 x).
    apply Ha'2; try assumption.
    split; auto.
    intros.
    transitivity b; assumption.
  }
  apply NNPP.
  intros ?.
  assert (~ In A (x, b)) as Hneg.
  { intros ?.
    apply (Hab (x, b)).
    { assumption. }
    constructor. assumption.
  }
  contradict Hneg.
  repeat split; simpl; try assumption.
  intros ?.
  subst.
  contradiction.
Qed.

(** *** Corollaries *)
Global Instance WO_Simulation_injective {X Y : Type} R0 R1 (f : X -> Y)
       `{WellOrder X R0} `{WellOrder Y R1}
      `{Simulation  _ _ R0 R1 f} :
  Injective f.
Proof.
  typeclasses eauto.
Qed.

Corollary WO_Simulation_unique {X Y R0 R1}
          `{WellOrder X R0} `{WellOrder Y R1} f g
      `{Simulation X Y R0 R1 f} `{Simulation X Y R0 R1 g} :
  forall x, f x = g x.
Proof.
  eapply simulation_uniqueness; typeclasses eauto.
Qed.

(** Every simulation from a WO to itself is the identity. *)
Corollary WO_Simulation_id {T R}
          `{WellOrder T R} (f : T -> T) `{Simulation _ _ R R f} :
  forall x, f x = x.
Proof.
  apply WO_Simulation_unique.
  - assumption.
  - apply Simulation_identity.
Qed.

(** Every simulation from a WO to its successor is [Some] *)
Corollary well_order_successor_Some {T} R `{W : WellOrder T R} f :
  Simulation R (rel_adjoin_top R) f ->
  forall x, f x = Some x.
Proof.
  intros.
  apply WO_Simulation_unique;
    typeclasses eauto.
Qed.

(** ** The Order of Well-Orders
One well-order is "less than" another, if there is a simulation
between them (going in the right direction). This induces a preorder.
*)
Definition le_well_order {T0 T1} R0 R1
           `{WellOrder T0 R0} `{WellOrder T1 R1} :=
  exists f, Simulation R0 R1 f.

(** This is the "isomorphism" relation for well-orders. *)
Definition eq_well_order {T0 T1} R0 R1
           `{WellOrder T0 R0} `{WellOrder T1 R1} :=
  le_well_order R0 R1 /\ le_well_order R1 R0.

Lemma eq_well_order_symmetric {T0 T1} R0 R1 `{WellOrder T0 R0} `{WellOrder T1 R1} :
  eq_well_order R0 R1 -> eq_well_order R1 R0.
Proof.
  unfold eq_well_order.
  tauto.
Qed.

Corollary le_well_order_transitive {T0 T1 T2} R0 R1 R2
          `{WellOrder T0 R0} `{WellOrder T1 R1} `{WellOrder T2 R2} :
  le_well_order R0 R1 ->
  le_well_order R1 R2 ->
  le_well_order R0 R2.
Proof.
  intros [f] [g].
  exists (compose g f).
  typeclasses eauto.
Qed.

Corollary eq_well_order_transitive {T0 T1 T2} R0 R1 R2
          `{WellOrder T0 R0} `{WellOrder T1 R1} `{WellOrder T2 R2} :
  eq_well_order R0 R1 ->
  eq_well_order R1 R2 ->
  eq_well_order R0 R2.
Proof.
  unfold eq_well_order.
  intros [] [].
  split; eapply (le_well_order_transitive _ R1);
    assumption.
Qed.

Lemma eq_well_order_Simulation_surjective {T0 T1 R0 R1}
      `{WellOrder T0 R0} `{WellOrder T1 R1} f :
  Simulation R0 R1 f ->
  surjective f ->
  eq_well_order R0 R1.
Proof.
  intros.
  assert (invertible f) as [g].
  { apply bijective_impl_invertible; split; try assumption.
    eapply WO_Simulation_injective; try typeclasses eauto.
  }
  split.
  { exists f; assumption. }
  exists g.
  apply (Simulation_inverse f g); auto.
Qed.

Lemma eq_well_order_Simulation_surjective_inv {T0 T1 R0 R1}
      `{WellOrder T0 R0} `{WellOrder T1 R1} f :
  eq_well_order R0 R1 ->
  Simulation R0 R1 f ->
  surjective f.
Proof.
  intros [] ?.
  apply invertible_impl_bijective.
  destruct H2 as [g].
  exists g.
  - apply WO_Simulation_id.
    eapply Simulation_compose; eauto.
  - apply WO_Simulation_id.
    eapply Simulation_compose; eauto.
Qed.

Definition lt_well_order {T0 T1} R0 R1
           `{WellOrder T0 R0} `{WellOrder T1 R1} :=
  exists f, Simulation R0 R1 f /\ ~ surjective f.

Corollary lt_well_order_transitive {T0 T1 T2} R0 R1 R2
          `{WellOrder T0 R0} `{WellOrder T1 R1} `{WellOrder T2 R2} :
  lt_well_order R0 R1 ->
  lt_well_order R1 R2 ->
  lt_well_order R0 R2.
Proof.
  intros [f []] [g []].
  exists (compose g f).
  split; [typeclasses eauto|].
  intros ?.
  eauto using surjective_compose_conv.
Qed.

Corollary lt_well_order_trans_le_lt {T0 T1 T2} R0 R1 R2
          `{WellOrder T0 R0} `{WellOrder T1 R1} `{WellOrder T2 R2} :
  le_well_order R0 R1 ->
  lt_well_order R1 R2 ->
  lt_well_order R0 R2.
Proof.
  intros [f] [g []].
  exists (compose g f).
  split; [typeclasses eauto|].
  intros ?.
  eauto using surjective_compose_conv.
Qed.

Corollary lt_well_order_trans_lt_le {T0 T1 T2} R0 R1 R2
          `{WellOrder T0 R0} `{WellOrder T1 R1} `{WellOrder T2 R2} :
  lt_well_order R0 R1 ->
  le_well_order R1 R2 ->
  lt_well_order R0 R2.
Proof.
  intros [f [Hfsim Hfnsurj]] [g].
  exists (compose g f).
  split; [typeclasses eauto|].
  intros Hgsurj.
  apply Hfnsurj.
  red. intros.
  specialize (Hgsurj (g y)) as [x Hx].
  exists x. unfold compose in Hx.
  eapply WO_Simulation_injective in Hx;
    eauto; typeclasses eauto.
Qed.

Lemma lt_well_order_impl_not_le {T0 T1 R0 R1} `{W0 : WellOrder T0 R0} `{W1 : WellOrder T1 R1} :
  lt_well_order R0 R1 ->
  ~ le_well_order R1 R0.
Proof.
  intros.
  intros ?.
  destruct H as [f []].
  contradict H1.
  apply eq_well_order_Simulation_surjective_inv;
    auto.
  split; auto.
  exists f; auto.
Qed.

Lemma lt_well_order_impl_le_succ {T0 T1 R0 R1}
      `{WellOrder T0 R0} `{WellOrder T1 R1} :
  lt_well_order R0 R1 ->
  le_well_order (rel_adjoin_top R0) R1.
Proof.
  intros [f [Hf0 Hf1]].
  assert (exists t1,
             ~ In (Im Full_set f) t1 /\
               (forall t1', ~ In (Im Full_set f) t1' -> ~ R1 t1' t1))
         as [t1 [Ht00 Ht01]].
  { apply WF_implies_MEP; try apply H0.
    apply not_all_ex_not in Hf1.
    destruct Hf1 as [t1 Ht1].
    exists t1.
    intros H_IM.
    apply Ht1.
    apply Im_inv in H_IM.
    firstorder.
  }
  exists (fun x => match x with Some x => f x | None => t1 end).
  assert (forall t, R1 (f t) t1).
  { intros.
    apply NNPP. intros ?.
    apply Ht00.
    unshelve eapply Simulation_Im_downwards_closed.
    { exact (f t). }
    { apply Im_def. constructor. }
    unshelve edestruct (@strongly_connected _ R1 _ t1 (f t));
      auto; try contradiction.
    intros ?.
    subst.
    contradict Ht00.
    apply Im_def. constructor.
  }
  constructor.
  + red. intros [] []; auto.
    * lazy.
      apply relation_preserve.
    * lazy. contradiction.
    * lazy. contradiction.
  + intros [] []; lazy; auto.
    * apply relation_reflect.
    * intros.
      apply (@irreflexivity _ R1 _ t1).
      transitivity (f t); auto.
    * apply irreflexivity.
  + intros [x|] ? Htx.
    * apply simulation in Htx as [y].
      subst. exists (Some y). auto.
    * apply NNPP; intros Htz.
      apply (Ht01 t).
      2: assumption.
      intros Hti.
      inversion Hti; subst; clear Hti.
      apply Htz.
      exists (Some x); auto.
Qed.

(** ** More constructions *)

(** *** Inverse Image *)
Require Import Wellfounded.Inverse_Image.

Section rel_induce_preim.
  (** given a relation of [Y] and a map [X -> Y], we can induce a
  relation on [X], which is well-behaved. *)
  Context {X Y : Type}.
  Variable (R : relation Y) (f : X -> Y).

  Definition rel_induce_preim :=
    fun x0 x1 => R (f x0) (f x1).

  Global Instance rel_induce_preim_WellFounded `{WellFounded Y R} :
    WellFounded rel_induce_preim.
  Proof.
    lazy.
    apply wf_inverse_image.
    assumption.
  Defined.

  Global Instance rel_induce_preim_Transitive `{Transitive Y R} :
    Transitive rel_induce_preim.
  Proof.
    intros ? ? ?.
    unfold rel_induce_preim.
    apply transitivity.
  Qed.

  Global Instance rel_induce_preim_WeaklyExtensional `{WeaklyExtensional Y R} `{Injective _ _ f}
         `{Simulation _ _ rel_induce_preim R f} :
    WeaklyExtensional rel_induce_preim.
  Proof.
    intros ? ? ?.
    apply H0.
    apply weakly_extensional.
    lazy. lazy in H2.
    intuition.
    - pose proof H2.
      apply simulation in H2 as [x1]; subst.
      auto.
    - pose proof H2.
      apply simulation in H2 as [x1]; subst.
      auto.
  Qed.

  (** If the image of [f] is downwards closed, then [f] is a [Simulation]. *)
  Lemma rel_induce_preim_Simulation :
    (forall x y, R y (f x) -> exists x0, y = f x0) ->
    Simulation rel_induce_preim R f.
  Proof.
    intros. split; lazy; auto.
  Qed.

  Local Lemma invertible_impl_Injective :
    invertible f -> Injective f.
  Proof.
    intros.
    apply invertible_impl_bijective.
    assumption.
  Qed.

  Local Lemma invertible_impl_down_closed_Im :
    invertible f ->
    forall x y,
      R y (f x) ->
      exists x0, y = f x0.
  Proof.
    intros [g]. intros.
    exists (g y).
    congruence.
  Qed.

  Lemma rel_induce_preim_WellOrder `{HR : WellOrder Y R} (Hi : invertible f) :
    WellOrder rel_induce_preim.
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - assert (Injective f).
      { apply invertible_impl_Injective.
        auto.
      }
      unshelve eapply rel_induce_preim_WeaklyExtensional.
      apply rel_induce_preim_Simulation.
      apply invertible_impl_down_closed_Im.
      assumption.
  Qed.

  (** Of course, for invertible [f], the inverse map is also a
      [Simulation] and is an equivalence of relations. *)
  Lemma rel_induce_preim_eq_well_order
        `{HR : WellOrder Y R} (Hi : invertible f) :
    @eq_well_order Y X R
     rel_induce_preim HR (rel_induce_preim_WellOrder Hi).
  Proof.
    destruct Hi as [g Hg0 Hg1].
    split; [exists g|exists f].
    2: apply rel_induce_preim_Simulation; auto.
    2: eauto using invertible_impl_down_closed_Im.
    eapply Simulation_inverse; eauto.
    apply rel_induce_preim_Simulation; auto.
    eauto using invertible_impl_down_closed_Im.
  Qed.
End rel_induce_preim.

(* *** Restriction to a subset *)
Definition rel_restriction {T} (R : relation T) (U : Ensemble T) :
  relation { x | In U x } :=
  rel_induce_preim R (@proj1_sig T U).

Global Instance  rel_restriction_WeaklyExtensional {T R U}
       `{HRirr : Irreflexive T R} `{HRconn : Connected T R} :
  WeaklyExtensional (rel_restriction R U).
Proof.
  intros [x Hx] [y Hy] Heq.
  cut (x = y).
  { intros; subst.
    apply subset_eq.
    reflexivity.
  }
  apply connected.
  - intros Hxy.
    destruct Heq as [_ Heq].
    specialize (Heq (exist _ x Hx) Hxy).
    apply HRirr in Heq.
    assumption.
  - intros Hyx.
    destruct Heq as [Heq _].
    specialize (Heq (exist _ y Hy) Hyx).
    apply HRirr in Heq.
    assumption.
Qed.

Global Instance rel_restriction_WeaklyExtensional2 {T R U}
      `{WeaklyExtensional T R} `{DownwardsClosed _ R U} :
  WeaklyExtensional (rel_restriction R U).
Proof.
  intros HU.
  apply rel_induce_preim_WeaklyExtensional;
    try typeclasses eauto.
  constructor; lazy; auto.
  intros [x] t Htx.
  unshelve eexists (exist _ t _); auto.
  apply (downwards_closed R x); auto.
Qed.

Global Instance rel_restriction_WellOrder {T R U} `{WellOrder T R} :
  WellOrder (rel_restriction R U).
Proof.
  constructor.
  - typeclasses eauto.
  - typeclasses eauto.
  - unshelve eapply rel_restriction_WeaklyExtensional.
Qed.

(** ** Successors, minimal and maximal elements *)
(* Classical fact. Interesting: Proving this seems difficult
constructively "inside" a well-order, but the order-structure of
well-founded relations has this property, even
constructively. (because there is no maximal well-order, and because
we can always construct the successor well-order.) In this way,
constructive well-founded relations have "bad" successor
functions/relations. *)
Fact well_founded_has_succ_or_is_max {X} R `{WellFounded X R} x :
  (exists y, succeeded_by R x y) \/ maximal_element R x.
Proof.
  destruct (classic (exists y, succeeded_by R x y)); try tauto.
  right. red; intros y ?.
  destruct (WF_implies_MEP) with (R := R) (S := (fun y => R x y)); eauto.
  now exists y.
Qed.

Fact well_founded_bounded_has_succ {X} R `{WellFounded X R} x y :
  R x y ->
  (exists z, succeeded_by R x z).
Proof.
  intros Hxy.
  destruct (well_founded_has_succ_or_is_max R x) as [|Hmax]; auto.
  apply Hmax in Hxy.
  contradiction.
Qed.

(**
With classical logic:
Every strictly-bounded downwards-closed subset of a well-order arises as
the initial segment of some element.
*)
Lemma WO_bounded_downwards_closed_is_initial_segment {X R} `{WellOrder X R} U x
      `{DownwardsClosed _ R U} :
  is_strict_upper_bound R U x ->
  exists x0,
    Same_set U (initial_segment R x0).
Proof.
  intros.
  pose (fun y => Included U (initial_segment R y)) as A.
  assert (Inhabited A) as HA.
  { exists x.
    apply H1.
  }
  apply WF_implies_MEP with (R := R) in HA as [x0 []].
  2: apply H.
  exists x0.
  split; try assumption.
  red; intros.
  do 2 red in H4.
  assert (~ In A x1).
  { intros ?.
    apply H3 in H5.
    auto.
  }
  unfold In, A in H5.
  assert (exists u, In U u /\ ~ R u x1) as [u [Hu0 Hu1]].
  { unfold Included in H5.
    apply not_all_ex_not in H5.
    destruct H5 as [u]; exists u.
    apply imply_to_and in H5.
    assumption.
  }
  destruct (classic (u = x1)).
  { subst. assumption. }
  assert (R x1 u).
  { unshelve epose proof (@strongly_connected _ R _ x1 u) as [|].
    all: auto; try contradiction.
  }
  apply H0 in H7; auto.
Qed.

Lemma wo_bounded_supremum {X} R `{W : WellOrder X R} U x :
  is_upper_bound R U x ->
  exists! y, supremum R U y.
Proof.
  intros.
  (** consider the downwards-closure of [U] and note that we already
     proved that such a set is an [initial_segment].
     Then the rest is relatively easy.
  *)
  unfold supremum.
  destruct (WF_implies_MEP X R) with (S := is_upper_bound R U)
    as [z [Hz0 Hz1]]; try apply W.
  { exists x; auto. }
  exists z; split.
  { split; auto. }
  intros z0 [Hz2 Hz3].
  specialize (Hz1 z0 Hz2).
  specialize (Hz3 z Hz0).
  apply connected; assumption.
Qed.

(** we could replace [succeeded_by R y y0] by [R y y0] but the latter
implies the existence of the former, and the former is (clearly) a
stronger property. *)
Lemma well_order_limit_or_successor {X} R `{WellOrder X R} x :
  (exists y, succeeded_by R y x) \/
    (forall y, R y x -> exists y0, succeeded_by R y y0 /\ R y0 x).
Proof.
  destruct (classic (exists y, succeeded_by R y x)); auto.
  right. intros y Hxy.
  pose proof (well_founded_bounded_has_succ R y x Hxy) as [y0 Hyy].
  exists y0; split; auto.
  apply NNPP.
  intros ?.
  apply Connected_Classical_le in H1 as [|]; try typeclasses eauto.
  - apply Hyy in H1; auto.
  - subst. apply H0. exists y; auto.
Qed.

(** ** Construct the embedding of [rel_restriction R U] into [R]
This construction is used to show that [inr] is a [Simulation].
*)
Section wo_subset_internal_ordinal.
  Context {T : Type} R `{HR : WellOrder T R}.
  Variable (U : Ensemble T).

  Let TU := { x : T | In U x }.

  Let V :=
        fun (rel : _ -> _ -> Prop) (x : TU) (rely_succ : T) =>
          exists rely y, succeeded_by R rely rely_succ
                    /\ rel_restriction R U y x /\ rel y rely.

  (** first show that a relation satisfying the recursive definition
  given in [Hrel] has all the required properties.
      Then construct a relation with this property. *)
  Section describe_rel.
    Variable (rel : TU -> T -> Prop).
    Hypothesis (Hrel : forall x rx,
                   rel x rx <-> supremum R (V rel x) rx).

    Lemma wo_subset_internal_ordinal_rel_decreasing x rx :
      rel x rx ->
      ~ R (proj1_sig x) rx.
    Proof.
      revert rx.
      induction x as [x HI] using
                       (well_founded_induction (rel_restriction R U)).
      intros rx Hrelx.
      rewrite (Hrel x rx) in Hrelx.
      destruct Hrelx as [Hsup0 Hsup1].
      unfold In at 1 in Hsup0.
      unfold In at 1 in Hsup1.
      apply Hsup1.
      intros y [y' [z [Hyy [Hzx Hzy]]]].
      specialize (HI z Hzx y' Hzy).
      intros Hxy.
      destruct Hyy as [Hyy0 Hyy1].
      apply Connected_Classical_le in HI as [|];
        try typeclasses eauto.
      2: {
        subst.
        apply Hyy1 in Hzx.
        contradiction.
      }
      apply Hyy1 in H.
      apply Connected_Classical_le in H as [|];
        try typeclasses eauto.
      2: {
        subst.
        apply asymmetry in Hxy; auto.
      }
      cut (R y y).
      { apply irreflexivity. }
      transitivity (proj1_sig z); auto.
      transitivity (proj1_sig x); auto.
    Qed.

    (** interestingly, this proof does not need induction. *)
    Lemma wo_subset_internal_ordinal_pair_functional x :
      exists! y,
        rel x y.
    Proof.
      rewrite (exists_unique_proper _ _ (Hrel x)).
      unshelve apply (wo_bounded_supremum _ _ (proj1_sig x));
        try typeclasses eauto.
      intros y [y' [z [Hyy [Hzx Hzy]]]].
      intros Hxy.
      pose proof (wo_subset_internal_ordinal_rel_decreasing
                    z y' Hzy) as Hzy0.
      destruct Hyy as [Hyy0 Hyy1].
      apply Connected_Classical_le in Hzy0 as [|];
        try typeclasses eauto; subst; auto.
      - pose proof (Hyy1 (proj1_sig z) H) as ?H.
        apply Connected_Classical_le in H0 as [|];
          try typeclasses eauto; subst; auto.
        + cut (R y y).
          { apply irreflexivity. }
          transitivity (proj1_sig z); auto.
          transitivity (proj1_sig x); auto.
        + apply asymmetry in Hxy; auto.
      - pose proof (Hyy1 (proj1_sig x) Hzx) as ?H.
        apply Connected_Classical_le in H as [|];
          try typeclasses eauto; subst; auto.
        + apply asymmetry in Hxy; auto.
        + apply irreflexivity in Hxy; auto.
    Qed.
  End describe_rel.

  Let V0 :=
        fun (rel : TU -> T) (x : TU) (rely_succ : T) =>
          exists y, succeeded_by R (rel y) rely_succ
                    /\ rel_restriction R U y x.

  Section describe_fn.
    (** We know that if an appropriate relation exists, then we can
    turn it (using constructive definite description) into a
    function. *)
    Variable (rel : TU -> T).
    Hypothesis (Hrel : forall x, supremum R (V0 rel x) (rel x)).

    Lemma wo_subset_internal_ordinal_decreasing x :
      ~ R (proj1_sig x) (rel x).
    Proof.
      induction x as [x IH] using (well_founded_induction (rel_restriction R U)).
      destruct (Hrel x) as [Hsup0 Hsup1].
      unfold In at 1 in Hsup0.
      unfold In at 1 in Hsup1.
      apply Hsup1.
      intros ysucc [z [Hzy Hzx]].
      specialize (IH z Hzx).
      intros Hxy.
      destruct (Hrel z) as [Hzy0 Hzy1].
      apply Connected_Classical_le in IH as [|];
        try typeclasses eauto.
      2: {
        rewrite <- H in *.
        apply Hzy in Hxy; auto.
      }
      apply Hzy in H.
      apply Connected_Classical_le in H as [|];
        try typeclasses eauto.
      2: {
        subst.
        apply asymmetry in Hxy; auto.
      }
      cut (R ysucc ysucc).
      { apply irreflexivity. }
      transitivity (proj1_sig z); auto.
      transitivity (proj1_sig x); auto.
    Qed.

    Lemma wo_subset_internal_ordinal_V_non_succ
      x relx_succ :
      succeeded_by R (rel x) relx_succ ->
      ~ In (V0 rel x) relx_succ.
    Proof.
      intros Hsucc.
      pose proof (Hrel x).
      apply (supremum_successor_not_In
               R (V0 rel x) relx_succ (rel x));
        auto.
    Qed.

    Lemma wo_subset_internal_ordinal_V_order_equiv x0 x1 :
      ~ (rel_restriction R U) x0 x1 <->
      Included (V0 rel x1) (V0 rel x0).
    Proof.
      split.
      - intros Hxx.
        intros rely_succ [y [Hy_succ Hyx]].
        assert (~ (rel_restriction R U) x0 y).
        { intros ?.
          apply Hxx.
          now transitivity y.
        }
        exists y; split; auto.
        apply Connected_Classical_le in H as [|];
          try typeclasses eauto; auto; subst; contradiction.
      - intros Hinc.
        intros Hxx.
        pose proof (Hrel x0) as Hrelx0.
        assert (exists relx0_succ, succeeded_by R (rel x0) relx0_succ)
          as [relx0_succ Hrelx0_succ].
        { eapply well_founded_bounded_has_succ with (y := (proj1_sig x1));
            try typeclasses eauto.
          pose proof (wo_subset_internal_ordinal_decreasing x0) as H2.
          apply Connected_Classical_le in H2 as [|];
            try typeclasses eauto; subst; auto.
          - transitivity (proj1_sig x0); auto.
          - rewrite <- H in *.
            assumption.
        }
        assert (In (V0 rel x1) relx0_succ) as HV1.
        { do 2 red.
          exists x0.
          tauto.
        }
        apply Hinc in HV1.
        apply (wo_subset_internal_ordinal_V_non_succ
                 x0 relx0_succ Hrelx0_succ) in HV1;
          auto.
    Qed.

    Lemma wo_subset_internal_ordinal_order_refl x0 x1 :
      R (rel x0) (rel x1) ->
      rel_restriction R U x0 x1.
    Proof.
      intros Hrxrx.
      apply NNPP.
      intros ?.
      apply wo_subset_internal_ordinal_V_order_equiv in H.
      apply (supremum_Included R (V0 rel x1) (V0 rel x0) (rel x1) (rel x0)) in H;
        auto.
    Qed.

    (** all elements that get added, are greater than previous ones... *)
    Lemma wo_subset_internal_ordinal_V_strict_bound x0 x1 zsucc :
      In (V0 rel x0) zsucc ->
      ~ In (V0 rel x1) zsucc ->
      is_strict_upper_bound R (V0 rel x1) zsucc.
    Proof.
      intros H0z H1z.
      red.
      intros ysucc [y [Hysucc Hyx]].
      apply NNPP.
      intros H2.
      apply Connected_Classical_le in H2 as [|];
        try typeclasses eauto; auto; subst.
      { destruct H0z as [z [Hzsucc Hzx]].
        assert (R (rel z) (rel y)).
        { eapply succeeded_by_order_equiv; eauto;
            typeclasses eauto.
        }
        eapply wo_subset_internal_ordinal_order_refl in H0.
        apply H1z.
        exists z.
        split; auto.
        transitivity y; auto.
      }
      apply H1z.
      exists y.
      tauto.
    Qed.

    Lemma wo_subset_internal_ordinal_V_same_sup x0 x1 :
      rel x0 = rel x1 ->
      (V0 rel x0) = (V0 rel x1).
    Proof.
      intros Heq.
      pose proof (Hrel x0) as Hrel0.
      pose proof (Hrel x1) as Hrel1.
      apply NNPP.
      intros ?.
      apply Ensemble_neq in H as [[z [Hz0 Hz1]]|[z [Hz1 Hz0]]];
        pose proof (wo_subset_internal_ordinal_V_strict_bound _ _ z Hz0 Hz1) as Hz2;
        (assert (rel x0 = z); [apply connected|]).
      1: apply Hrel0; now auto.
      3: rewrite Heq; apply Hrel1; now auto.
      1: rewrite Heq; apply Hrel1; apply is_strict_upper_bound_is_upper_bound;
          try typeclasses eauto; auto.
      2: apply Hrel0; apply is_strict_upper_bound_is_upper_bound;
          try typeclasses eauto; auto.
      all: subst; rewrite <- Heq in *.
      (** This can only happen, if [rel x0] is a limit. But all
          elements of [V _ _] are successors, So we have a
          contradiction. *)
      all: apply supremum_strict_upper_bound_is_limit in Hz2;
        try typeclasses eauto; auto.
      all: destruct Hz0 as [? []]; eauto.
    Qed.

    Lemma wo_subset_internal_ordinal_injective x0 x1 :
      rel x0 = rel x1 -> x0 = x1.
    Proof.
      intros Heq.
      pose proof (wo_subset_internal_ordinal_V_same_sup x0 x1 Heq) as Heq0.
      apply connected;
        apply wo_subset_internal_ordinal_V_order_equiv;
        rewrite Heq0; reflexivity.
    Qed.

    Lemma wo_subset_internal_ordinal_order_equiv x0 x1 :
      (rel_restriction R U x0 x1) <-> R (rel x0) (rel x1).
    Proof.
      split.
      2: apply wo_subset_internal_ordinal_order_refl; now auto.
      (* -> *)
      intros Hxx.
      assert (Strict_Included (V0 rel x0) (V0 rel x1)) as HVinc.
      { assert (~ rel_restriction R U x1 x0) as Hxx0.
        { intros Hxx0; apply asymmetry in Hxx0; auto. }
        apply wo_subset_internal_ordinal_V_order_equiv in Hxx0.
        split; auto.
        intros ?.
        assert (Included (V0 rel x1) (V0 rel x0)).
        { rewrite H in *.
          assumption.
        }
        rewrite <- wo_subset_internal_ordinal_V_order_equiv in H0.
        contradiction.
      }
      assert (~ R (rel x1) (rel x0)).
      { apply (supremum_Included R (V0 rel x0) (V0 rel x1)).
        - apply HVinc.
        - apply Hrel.
        - apply Hrel.
      }
      apply Connected_Classical_le in H as [|];
        try typeclasses eauto; auto; subst.
      exfalso.
      destruct (wo_subset_internal_ordinal_injective x1 x0 H).
      apply HVinc.
      reflexivity.
    Qed.

    Lemma wo_subset_internal_ordinal_successor0 x0 x1 rx1 :
      succeeded_by (rel_restriction R U) x0 x1 ->
      succeeded_by R (rel x0) rx1 ->
      rx1 = rel x1.
    Proof.
      intros Hsucc0 Hsucc1.
      assert (In (V0 rel x1) rx1).
      { exists x0. split; auto.
        apply Hsucc0.
      }
      cut (is_upper_bound R (V0 rel x1) rx1).
      { intros Hbound.
        pose proof (Hrel x1).
        apply H0 in Hbound.
        apply H0 in H.
        apply connected; auto.
      }
      intros rysucc [y [Hrysucc Hyx1]].
      destruct (classic (rel_restriction R U y x0)).
      { assert (In (V0 rel x0) rysucc).
        { exists y; split; auto. }
        pose proof (Hrel x0) as Hrel0.
        apply Hrel0 in H1.
        intros ?.
        apply H1.
        transitivity rx1; auto.
        apply Hsucc1.
      }
      apply Connected_Classical_le in H0 as [|];
        try typeclasses eauto; subst; auto.
      - apply Hsucc0 in H0. contradiction.
      - rewrite <- (succeeded_by_order_equiv R (rel x0) rx1 (rel x0) rysucc);
          auto.
        apply irreflexivity.
    Qed.

    Corollary wo_subset_internal_ordinal_successor x0 x1 :
      succeeded_by (rel_restriction R U) x0 x1 ->
      succeeded_by R (rel x0) (rel x1).
    Proof.
      intros Hsucc.
      assert (R (rel x0) (rel x1)).
      { apply wo_subset_internal_ordinal_order_equiv.
        apply Hsucc.
      }
      destruct (well_founded_bounded_has_succ R (rel x0) (rel x1))
                 as [rx0_succ Hrx0_succ]; auto.
      destruct (wo_subset_internal_ordinal_successor0
                  x0 x1 rx0_succ); auto.
    Qed.

    Lemma wo_subset_internal_ordinal_successor_preim x0 x1 :
      succeeded_by R (rel x0) (rel x1) ->
      succeeded_by (rel_restriction R U) x0 x1.
    Proof.
      intros.
      assert (rel_restriction R U x0 x1).
      { apply wo_subset_internal_ordinal_order_equiv.
        apply H.
      }
      split; auto.
      intros.
      intros ?.
      apply wo_subset_internal_ordinal_order_equiv in H1.
      apply wo_subset_internal_ordinal_order_equiv in H2.
      apply H in H1.
      contradiction.
    Qed.

    Lemma wo_subset_internal_ordinal_downwards_closed' ry :
      (~ exists y, ry = rel y) ->
      is_upper_bound R (fun rx => exists x, rx = rel x) ry.
    Proof.
      intros.
      destruct (WF_implies_MEP _ R wo_WF (fun ry => forall y, ry <> rel y))
                 as [ryy [Hry0 Hry1]].
      { exists ry.
        red. intros ? ?.
        apply H. exists y. assumption.
      }
      assert (~ R ry ryy).
      { apply Hry1.
        intros ? ?.
        subst.
        apply H; eauto.
      }
      cut (is_upper_bound R (fun rx => exists x, rx = rel x) ryy).
      { intros.
        intros ? ?.
        apply H1 in H2.
        apply Connected_Classical_le in H0 as [|]; subst; auto;
          try typeclasses eauto.
        intros ?.
        apply H2.
        transitivity ry; auto.
      }
      clear ry H H0.
      intros Hrx [x]. subst.
      intros ?.
      unshelve edestruct (WF_implies_MEP
                  _ (rel_restriction R U)
                  ltac:(apply rel_induce_preim_WellFounded; apply wo_WF)
                         (fun x => R ryy (rel x)))
                 as [xx [Hx0 Hx1]].
      { exists x. assumption. }
      red in Hx0.
      unfold In at 2 in Hx1.
      clear x H.
      (* now the question: why didn't [xx] get mapped to [ryy]? *)
      pose proof (Hrel xx) as [Hsup0 Hsup1].
      unshelve eapply (Hsup1 ryy _ Hx0).
      clear Hsup1.
      intros rzsucc [z [Hzsucc Hzx]].
      assert (~ R (rel xx) rzsucc).
      { apply Hsup0.
        exists z; auto.
      }
      intros ?.
      destruct Hzsucc as [Hzsucc0 Hzsucc1].
      pose proof (Hzsucc1 ryy).
      assert (R (rel z) ryy).
      { apply NNPP.
        intros Hzy.
        apply Connected_Classical_le in Hzy as [Hzy|];
          try typeclasses eauto; subst.
        - specialize (Hx1 z Hzy).
          contradiction.
        - apply (Hry0 z eq_refl).
      }
      tauto.
    Qed.

    Lemma wo_subset_internal_ordinal_downwards_closed (x : TU) ry :
      R ry (rel x) ->
      exists y, ry = rel y.
    Proof.
      revert x.
      induction ry as [ry IH] using (well_founded_induction R).
      intros x Hryrx.
      apply NNPP. intros Hneg.
      apply wo_subset_internal_ordinal_downwards_closed' in Hneg.
      specialize (Hneg (rel x) (ex_intro _ x eq_refl)).
      contradiction.
    Qed.
  End describe_fn.

  (** The relation is defined via [Wf.Fix_sub], because this makes it
      easier to show correctness. *)
  Definition wo_subset_internal_ordinal_rel : forall x, In U x -> T -> Prop :=
    Wf.Fix_sub
      T R wo_WF (fun x => In U x -> T -> Prop)
                 (fun (x : T)
                    (IH : forall y : { y : T | R y x },
                        In U (proj1_sig y) -> T -> Prop)
                    (_ : In U x) =>
                    supremum
                      R
                      (fun rely_succ : T =>
                         exists rely y (Hyx : R y x) (HyU : In U y), succeeded_by R rely rely_succ /\
                                     IH (exist _ y Hyx) HyU rely)).

  Let rel := fun (x : TU) (rx : T) =>
               wo_subset_internal_ordinal_rel
                 (proj1_sig x) (proj2_sig x) rx.

  Lemma wo_subset_internal_ordinal_rel_correct x rx :
    rel x rx <->
      supremum R (V rel x) rx.
  Proof.
    induction x as [x Hind] using (well_founded_induction (rel_restriction R U)).
    unfold rel at 1. unfold wo_subset_internal_ordinal_rel.
    rewrite Wf.fix_sub_eq.
    { simpl.
      match goal with
      | |- supremum _ ?a _ <-> supremum _ ?b _ =>
          replace b with a; try reflexivity
      end.
      apply Extensionality_Ensembles; split; red; intros ysucc Hy.
      - do 2 red. red in Hy.
        destruct Hy as [rely [y [Hyx [HyU [Hysucc Hfix]]]]].
        exists rely, (exist _ y HyU).
        split; auto.
      - red. do 2 red in Hy.
        destruct Hy as [rely [y [Hysucc [Hyx Hrely]]]].
        exists rely, (proj1_sig y).
        split; auto.
        exists (proj2_sig y).
        split; auto.
    }
    clear.
    intros.
    extensionality Hx.
    match goal with
    | |- supremum _ ?a = supremum _ ?b =>
        replace b with a; try reflexivity
    end.
    apply Extensionality_Ensembles.
    apply Same_set_iff_In.
    intros y. unfold In.
    apply exists_iff_Proper.
    intros z.
    apply exists_iff_Proper.
    intros Hz.
    apply exists_iff_Proper.
    intros ?.
    apply exists_iff_Proper.
    intros ?.
    rewrite H.
    reflexivity.
  Qed.

  Let rel0 x : { rx | rel x rx } :=
    constructive_definite_description _
      (wo_subset_internal_ordinal_pair_functional
         rel wo_subset_internal_ordinal_rel_correct x).

  Let rel1 x := proj1_sig (rel0 x).

  Lemma wo_subset_internal_ordinal_V_correct x :
    V rel x = V0 rel1 x /\
      (forall y, rel x y <-> y = rel1 x).
  Proof.
    induction x as [x IH] using (well_founded_induction (rel_restriction R U));
      split; [apply Extensionality_Ensembles; split; red; intros|].
    - destruct H as [? [? [? []]]].
      do 2 red.
      exists x2. split; auto.
      apply IH in H0 as [_ ?].
      rewrite H0 in H1.
      subst.
      assumption.
    - destruct H as [? []].
      do 2 red.
      exists (rel1 x1), x1.
      split; auto.
      split; auto.
      destruct (IH x1); auto.
      rewrite H2. reflexivity.
    - intros.
      rewrite wo_subset_internal_ordinal_rel_correct.
      unfold rel1.
      pose proof (proj2_sig (rel0 x)).
      rewrite wo_subset_internal_ordinal_rel_correct in H.
      split; intros; subst; auto.
      eapply connected_supremum_unique; eauto; typeclasses eauto.
  Qed.

  Lemma wo_subset_internal_ordinal_fn_correct x :
    supremum R (V0 rel1 x) (rel1 x).
  Proof.
    destruct (wo_subset_internal_ordinal_V_correct x).
    rewrite <- H.
    unfold rel1.
    pose proof (proj2_sig (rel0 x)).
    apply (wo_subset_internal_ordinal_rel_correct x) in H1.
    assumption.
  Qed.

  (** summarize the above statements *)
  Theorem wo_subset_internal_ordinal_Simulation :
    Simulation (rel_restriction R U) R rel1.
  Proof.
    constructor.
    - (* RelationPreserve *)
      red. intros.
      rewrite <- wo_subset_internal_ordinal_order_equiv; auto.
      apply wo_subset_internal_ordinal_fn_correct.
    - (* RelationReflect *)
      red. intros.
      rewrite wo_subset_internal_ordinal_order_equiv; eauto.
      apply wo_subset_internal_ordinal_fn_correct.
    - (* image downwards closed *)
      intros.
      eapply wo_subset_internal_ordinal_downwards_closed; eauto.
      apply wo_subset_internal_ordinal_fn_correct.
  Qed.
End wo_subset_internal_ordinal.

(** **** More theory about simulations
Using the following StackExchange answer #<a href="https://math.stackexchange.com/a/4478289/1070289">#https://math.stackexchange.com/a/4478289/1070289#</a>#.
But the final construction does not seem significantly easier to do
(because a working solution already exists). It might simplify stuff,
because fewer cases/objects have to be considered at the same time.
 *)

Global Instance rel_restriction_proj1_sig_Simulation {T R} U
       `(HU : DownwardsClosed T R U) :
  Simulation (rel_restriction R U) R (@proj1_sig _ _).
Proof.
  constructor; lazy; auto.
  intros [x] t Ht.
  unshelve eexists (exist _ t _); auto.
  apply (downwards_closed R x); assumption.
Qed.

(** if the relation is [WellFounded] and [WeaklyExtensional] and the set is [DownwardsClosed],
    then [proj1_sig] is a [Simulation], so we can explicitly calculate
    the value of any simulation. *)
Lemma rel_restriction_Simulation_value {T R} U
  `{HU : DownwardsClosed T R U} `{HR0 : WellFounded T R}
  `{HR1 : WeaklyExtensional T R} f `{Simulation _ _ (rel_restriction R U) R f} :
  forall x Hx,
    f (exist _ x Hx) = x.
Proof.
  intros.
  replace x with (proj1_sig (exist _ x Hx)) by reflexivity.
  apply (simulation_uniqueness (rel_restriction R U) R);
    auto; try typeclasses eauto.
Qed.

(* we need proof irrelevance for this to work properly. *)
Lemma rel_restriction_Simulation_inclusion
  {T R} U V
  `{HU : DownwardsClosed T R U} `{HV : DownwardsClosed T R V}
  `{HR0 : WellFounded T R} `{HR1 : WeaklyExtensional T R}
  (HUV : Included U V)
  f `{Simulation _ _ (rel_restriction R U) (rel_restriction R V) f} :
  forall x Hx,
    f (exist _ x Hx) = exist _ x (HUV x Hx).
Proof.
  intros.
  (* proof by going via [rel_restriction_Simulation_value] *)
  simpl in *.
  assert (((compose (@proj1_sig _ _) f) (exist _ x Hx)) = proj1_sig (exist _ x (HUV x Hx))).
  { simpl.
    apply (@rel_restriction_Simulation_value _ R U _ _ _ (compose (@proj1_sig _ _) f)).
    eapply Simulation_compose; eauto.
    typeclasses eauto.
  }
  simpl in H0.
  apply subset_eq.
  simpl.
  assumption.
Qed.

Lemma rel_restriction_inclusion_Simulation
  {T R} U V
  `{HU : DownwardsClosed T R U}
  `{HR0 : WellFounded T R} `{HR1 : WeaklyExtensional T R}
  (HUV : _) :
  Simulation (rel_restriction R U) (rel_restriction R V)
             (fun x => exist _ (proj1_sig x) (HUV x)).
Proof.
  constructor.
  - intros ? ? ?.
    apply H.
  - intros ? ? ?.
    apply H.
  - intros.
    destruct (@simulation _ _ _ _ _
                (@rel_restriction_proj1_sig_Simulation T R U HU) x (proj1_sig t)).
    { assumption. }
    exists x0.
    apply subset_eq.
    simpl.
    assumption.
Qed.

(** ** Disjoint union of well-orders
Recall that [Coq.Relation_Operators.le_AsB] denotes the disjoint union
of two relations. *)
Require Import Coq.Wellfounded.Disjoint_Union.
Import Relation_Operators.

Global Instance le_AsB_WellFounded {A B leA leB} `{WellFounded A leA} `{WellFounded B leB} :
  WellFounded (le_AsB A B leA leB).
Proof.
  red.
  apply wf_disjoint_sum;
    assumption.
Qed.

Global Instance le_AsB_Transitive {A B leA leB} `{Transitive A leA} `{Transitive B leB} :
  Transitive (le_AsB A B leA leB).
Proof.
  intros [] [] [] H1 H2;
    inversion H1; subst; clear H1;
    inversion H2; subst; clear H2;
    constructor.
  - transitivity a0; assumption.
  - transitivity b0; assumption.
Qed.

Global Instance le_AsB_WeaklyExtensional {A B leA leB} `{Irreflexive A leA}
       `{WeaklyExtensional A leA} `{WeaklyExtensional B leB} :
  WeaklyExtensional (le_AsB A B leA leB).
Proof.
  red. intros [] [] Heq.
  - cut (a = a0); try congruence.
    apply weakly_extensional.
    cut (forall a a0,
            Included (initial_segment (le_AsB _ _ leA leB) (inl a))
                  (initial_segment (le_AsB _ _ leA leB) (inl a0)) ->
         Included (initial_segment leA a) (initial_segment leA a0)).
    { firstorder. }
    clear. intros.
    red; intros.
    cut (le_AsB _ _ leA leB (inl x) (inl a0)).
    { intros Hl.
      inversion Hl; subst; clear Hl.
      assumption.
    }
    apply H. constructor. assumption.
  - assert (le_AsB _ _ leA leB (inl a) (inl a)).
    { apply Heq. constructor. }
    inversion H2; subst; clear H2.
    apply H in H5.
    contradiction.
  - assert (le_AsB _ _ leA leB (inl a) (inl a)).
    { apply Heq. constructor. }
    inversion H2; subst; clear H2.
    apply H in H5.
    contradiction.
  - cut (b = b0); try congruence.
    apply weakly_extensional.
    cut (forall b b0,
            Included (initial_segment (le_AsB _ _ leA leB) (inr b))
                  (initial_segment (le_AsB _ _ leA leB) (inr b0)) ->
         Included (initial_segment leB b) (initial_segment leB b0)).
    { firstorder. }
    clear. intros.
    red; intros.
    cut (le_AsB _ _ leA leB (inr x) (inr b0)).
    { intros Hl. inversion Hl; subst; clear Hl.
      assumption.
    }
    apply H. constructor. assumption.
Qed.

Global Instance le_AsB_WellOrder {A B leA leB} `{WellOrder A leA} `{WellOrder B leB} :
  WellOrder (le_AsB A B leA leB).
Proof.
  constructor.
  - apply le_AsB_WellFounded.
  - apply le_AsB_Transitive.
  - apply le_AsB_WeaklyExtensional.
Qed.

(** The natural embedding [inl] is actually a simulation. *)
Global Instance well_order_sum_inl_Simulation {T0 T1} R0 R1
  `{W0 : WellOrder T0 R0} `{W1 : WellOrder T1 R1} :
  Simulation R0 (le_AsB _ _ R0 R1) inl.
Proof.
  constructor; lazy.
  - intros. constructor. assumption.
  - intros.
    inversion H; subst; clear H.
    assumption.
  - intros.
    inversion H; subst; clear H.
    eauto.
Qed.

Lemma well_order_sum_le_left {T0 T1} R0 R1 `{W0 : WellOrder T0 R0} `{W1 : WellOrder T1 R1} :
  le_well_order R0 (le_AsB _ _ R0 R1).
Proof.
  exists inl.
  typeclasses eauto.
Qed.

Global Instance Relation_DisjointSum_inr_Preserves {T0 T1} R0 R1 :
  RelationPreserve R1 (le_AsB T0 T1 R0 R1) inr.
Proof.
  intros ? ? ?. constructor. assumption.
Qed.

Corollary le_well_order_restrict {T} R `{W : WellOrder T R} U :
  le_well_order (rel_restriction R U) R.
Proof.
  eexists.
  apply wo_subset_internal_ordinal_Simulation.
Qed.

Lemma le_well_order_RelationPreserve {T0 T1} R0 R1
      `{W0 : WellOrder T0 R0} `{W1 : WellOrder T1 R1} f
      `{RelationPreserve _ _ R0 R1 f} :
  le_well_order R0 R1.
Proof.
  eapply (le_well_order_transitive _ (rel_restriction R1 (Im Full_set f))).
  2: {
    apply le_well_order_restrict.
  }
  unshelve eexists (fun p => exist _ (f p) _).
  { apply Im_def. constructor. }
  constructor.
  + lazy; auto.
  + lazy; auto.
    intros ? ? Hxy.
    destruct (classic (x = y)); subst.
    { apply irreflexivity in Hxy.
      contradiction.
    }
    destruct (strongly_connected x y); auto.
    apply H in H1.
    assert (R1 (f x) (f x)).
    { transitivity (f y); assumption. }
    apply irreflexivity in H2.
    contradiction.
  + intros x [t] ?.
    lazy in H0.
    inversion i; subst.
    exists x0. apply subset_eq.
    reflexivity.
Qed.

Lemma well_order_sum_le_right {T0 T1} R0 R1 `{W0 : WellOrder T0 R0}
      `{W1 : WellOrder T1 R1} :
  le_well_order R1 (le_AsB _ _ R0 R1).
Proof.
  apply (le_well_order_RelationPreserve R1 (le_AsB _ _ R0 R1) inr).
Qed.

(** ** Packed Well-Orders
By bundling the well-orders, we can more easily about collections of
well-ordered sets.  Also, type class inference and tactics like
`transitivity` become available for this type.
*)

Record well_order_packed :=
  { wop_carrier : Type;
    wop_rel : relation wop_carrier;
    wop_WO :> WellOrder wop_rel;
  }.
Global Existing Instance wop_WO.

Definition lt_well_order_packed (W0 W1 : well_order_packed) : Prop :=
  @lt_well_order
    _ _
    (wop_rel W0) (wop_rel W1) W0 W1.

Definition le_well_order_packed (W0 W1 : well_order_packed) : Prop :=
  @le_well_order
    _ _
    (wop_rel W0) (wop_rel W1) W0 W1.

Lemma lt_well_order_Irreflexive {T R} `{WellOrder T R} :
  ~ lt_well_order R R.
Proof.
  intros ?.
  destruct H0 as [f []].
  apply H1. red. intros.
  exists y. apply WO_Simulation_id.
  assumption.
Qed.

Global Instance lt_well_order_packed_Irreflexive :
  Irreflexive lt_well_order_packed.
Proof.
  do 2 red.
  intros.
  destruct x.
  unfold lt_well_order_packed.
  simpl. red. simpl.
  apply lt_well_order_Irreflexive.
Qed.

Global Instance lt_well_order_packed_Transitive :
  Transitive lt_well_order_packed.
Proof.
  do 2 red.
  intros.
  unshelve eapply (lt_well_order_transitive _ (wop_rel y));
    try assumption; apply y.
Qed.

Global Instance lt_well_order_packed_Asymmetric :
  Asymmetric lt_well_order_packed.
Proof.
  apply Irrefl_Trans_impl_Asymmetric.
Qed.

Global Instance le_well_order_packed_Transitive :
  Transitive le_well_order_packed.
Proof.
  red. unfold le_well_order_packed.
  intros.
  eapply (le_well_order_transitive _ (wop_rel y));
    assumption.
Qed.

(** This following is the successor of [W]. We go on to show, that it actually succeeds [W] *)
Definition well_order_successor (W : well_order_packed) : well_order_packed :=
  {|
    wop_rel := rel_adjoin_top (wop_rel W);
  |}.

Definition rel_restriction_WO {T R} `{WellOrder T R} U : well_order_packed :=
  {|
    wop_rel := rel_restriction R U;
  |}.

Definition WO_Simulation_image_packed
       {T0 T1 R0 R1} `{WellOrder T1 R1} f `{Simulation T0 _ R0 R1 f} :
  well_order_packed :=
  rel_restriction_WO
    (Im Full_set f).

(** ** More about the order of well-orders
The goal is to show that [le_well_order] is a total order, and that
[lt_well_order] is [well_founded].
*)

(** These assumptions are never really satisfied in a constructive
   setting, I think. *)
Lemma lt_well_order_packed_successor_squeeze {T0 T1 R0 R1}
      `{W0 : WellOrder T0 R0} `{W1 : WellOrder T1 R1}
      `{HS : StronglyConnected _ R0} `{HV : Connected _ R1}
      f g :
  (forall x0 x1 : option T0, x0 = x1 \/ x0 <> x1) ->
  Simulation R0 R1 f ->
  Simulation R1 (rel_adjoin_top R0) g ->
  ~ surjective f -> ~ surjective g -> False.
Proof.
  intros eqdec_p Hf0 Hg0 Hf1 Hg1.
  assert (forall x, compose g f x = Some x) as Hgf.
  { intros.
    eapply well_order_successor_Some;
      typeclasses eauto.
  }
  contradict Hf1.
  red. intros.
  destruct (g y) as [w|] eqn:E0.
  - exists w.
    rewrite <- Hgf in E0.
    eapply (@injective_class _ _ g) in E0; auto.
    apply (@RelationPreserve_Connected_Irreflexive_Inj
             T1 (option T0) R1 (rel_adjoin_top R0) g
             WellOrder_Connected_Classical
             wf_irrefl).
    apply Hg0.
  - contradict Hg1.
    eapply Simulation_surjective_dec with (x := y);
      try typeclasses eauto; eauto.
    rewrite E0.
    apply rel_adjoin_top_maximal_element.
Qed.

Lemma lt_well_order_successor {T} R `{W : WellOrder T R} :
  lt_well_order R (rel_adjoin_top R).
Proof.
  red.
  exists Some.
  split.
  - eapply well_order_successor_Some_Simulation.
    typeclasses eauto.
  - intros Hs.
    specialize (Hs None) as [].
    discriminate.
Qed.

Definition well_order_succeeded_by {T0 T1} R0 R1 `{WellOrder T0 R0} `{WellOrder T1 R1} : Prop :=
  lt_well_order R0 R1 /\
    forall T2 R2 `(W2 : WellOrder T2 R2),
      lt_well_order R0 R2 -> ~ lt_well_order R2 R1.

(** Restates the above concisely, but with fewer assumptions by using
   classical logic. *)
Lemma lt_well_order_packed_succeeded_by {T} R `{W : WellOrder T R} :
  well_order_succeeded_by R (rel_adjoin_top R).
Proof.
  split.
  { apply lt_well_order_successor. }
  red.
  intros ? ? ? [f []] [g []].
  pose proof (@lt_well_order_packed_successor_squeeze) as Hsqueeze.
  specialize (Hsqueeze _ _ R R2 _ _ _ _ f g).
  apply Hsqueeze; auto; try typeclasses eauto.
  intros ? ?. apply classic.
Qed.

(** For any two well-orders, there exists an well-order into which
both of them (strictly) embed. *)
Lemma lt_well_order_weakjoin_exists {T0 T1} R0 R1
      `{W0 : WellOrder T0 R0} `{W1 : WellOrder T1 R1} :
    lt_well_order R0 (rel_adjoin_top (le_AsB _ _ R0 R1)) /\
      lt_well_order R1 (rel_adjoin_top (le_AsB _ _ R0 R1)).
Proof.
  split.
  - eapply (@lt_well_order_trans_le_lt _ _ _ R0 (le_AsB _ _ R0 R1)).
    + apply well_order_sum_le_left.
    + apply lt_well_order_successor.
  - eapply (@lt_well_order_trans_le_lt _ _ _ R1 (le_AsB _ _ R0 R1)).
    + apply well_order_sum_le_right.
    + apply lt_well_order_successor.
Qed.

Lemma eq_well_order_Simulation_restriction {T0 T1 R0 R1} `{W0 : WellOrder T0 R0}
      `{W1 : WellOrder T1 R1} f `{HF : Simulation _ _ R0 R1 f} :
  eq_well_order R0 (rel_restriction R1 (Im Full_set f)).
Proof.
  unshelve eapply eq_well_order_Simulation_surjective;
    eauto.
  - refine (fun t0 => exist _ (f t0) _).
    apply Im_def. constructor.
  - constructor; lazy; try apply HF.
    intros x [y] Hy.
    apply simulation in Hy as [x0].
    subst. exists x0. apply subset_eq.
    reflexivity.
  - intros [y].
    inversion i; subst.
    exists x. apply subset_eq.
    reflexivity.
Qed.

(** The image of a non-surjective simulation of well-orders is the
   initial segment of some element. *)
Lemma WO_Simulation_non_surj_initial_segment {T0 T1} R0 R1 `{W1 : WellOrder T1 R1}
      f `{Simulation T0 _ R0 R1 f} :
  ~ surjective f ->
  exists t,
    Same_set (Im Full_set f) (initial_segment R1 t).
Proof.
  intros.
  assert (exists x, is_strict_upper_bound R1 (Im Full_set f) x) as [y].
  { apply not_all_ex_not in H0 as [x].
    exists x.
    intros y ?.
    inversion H1; subst; clear H1.
    destruct (strongly_connected (f x0) x); auto.
    - intros ?. contradict H0.
      eauto.
    - apply simulation in H1 as [x1].
      subst. contradict H0.
      eauto.
  }
  apply WO_bounded_downwards_closed_is_initial_segment with (x := y);
    auto.
  apply Simulation_Im_downwards_closed.
Qed.

(* restricts the relation to the initial segment of [x] *)
Definition rel_restriction_inits {X} (R : relation X) (x : X) :=
  rel_restriction R (initial_segment R x).

Lemma le_well_order_packed_succ_None {X} (W : relation X) `{WellOrder X W} :
  le_well_order W (rel_restriction_inits (rel_adjoin_top W) None).
Proof.
  unshelve eexists (fun p => exist _ (Some p) _); constructor;
    try solve [lazy; auto].
  intros x [[y|]].
  - simpl. intros. exists y.
    apply subset_eq. reflexivity.
  - destruct i.
Qed.

Lemma le_well_order_rel_restriction_Same_set {T R} `{W : WellOrder T R} U V :
  Same_set U V ->
  le_well_order
    (rel_restriction R U)
    (rel_restriction R V).
Proof.
  intros Heq.
  unshelve eexists.
  { refine (fun p => exist _ (proj1_sig p) _).
    apply Heq. apply proj2_sig.
  }
  constructor; lazy; auto.
  intros [x] [t] ?.
  unshelve eexists (exist _ t _).
  - apply Heq. assumption.
  - apply subset_eq. reflexivity.
Qed.

Lemma rel_restriction_WO_inits_packed_Simulation {T R} `{W : WellOrder T R} x0 x1 f
      `{Simulation
          _ _
          (rel_restriction R (initial_segment R x0))
          (rel_restriction R (initial_segment R x1)) f} :
  forall y,
    proj1_sig (f y) = proj1_sig y.
Proof.
  intros.
  apply (@WO_Simulation_unique
                {x | In (initial_segment R x0) x} T
                (rel_restriction R _) R
                rel_restriction_WellOrder _
                (compose (@proj1_sig T (initial_segment R _)) f)).
  - typeclasses eauto.
  - typeclasses eauto.
Qed.

Lemma rel_restriction_inits_le_char {T R} `{W : WellOrder T R} x0 x1 :
  le_well_order (rel_restriction_inits R x0) (rel_restriction_inits R x1) <->
    (x0 = x1 \/ R x0 x1).
Proof.
  split.
  - intros [f Hf].
    destruct (classic (x0 = x1)); auto.
    right.
    destruct (strongly_connected x0 x1); auto.
    exfalso.
    apply (@irreflexivity _ R _ x1).
    pose proof (proj2_sig (f (exist _ x1 H0))) as H2.
    simpl in H2.
    rewrite (rel_restriction_WO_inits_packed_Simulation x0 x1 f) in H2.
    assumption.
  - intros Hdec. destruct Hdec.
    { subst.
      exists id.
      apply Simulation_identity.
    }
    unshelve eexists.
    { refine (fun p => exist _ (proj1_sig p) _).
      lazy. transitivity x0; auto.
      apply (proj2_sig p).
    }
    constructor; lazy; auto.
    intros [x Hx] [t Ht] Htx.
    unshelve eexists (exist _ t _).
    2: apply subset_eq; reflexivity.
    simpl. transitivity x; auto.
Qed.

Lemma le_well_order_total {T0 T1} R0 R1 `{W0 : WellOrder T0 R0} `{W1 : WellOrder T1 R1} :
  le_well_order R0 R1 \/ le_well_order R1 R0.
Proof.
  (** First embed both [R0] and [R1] in the same well-order. *)
  destruct (lt_well_order_weakjoin_exists R0 R1) as [[f [Hf0 Hf1]] [g [Hg0 Hg1]]].
  pose (rel_adjoin_top (le_AsB T0 T1 R0 R1)) as R2.
  fold R2 in Hf0, Hg0.
  cut (le_well_order (rel_restriction _ (Im Full_set f))
                     (rel_restriction _ (Im Full_set g)) \/
         le_well_order (rel_restriction _ (Im Full_set g))
                       (rel_restriction _ (Im Full_set f))).
  { pose proof (eq_well_order_Simulation_restriction f) as Hf2.
    pose proof (eq_well_order_Simulation_restriction g) as Hg2.
    intros [Hp|Hp]; [left|right]; red in Hp.
    - unshelve eapply (le_well_order_transitive
                         _ (rel_restriction _ (Im Full_set f))).
      { apply Hf2. }
      unshelve eapply (le_well_order_transitive
                         _ (rel_restriction _ (Im Full_set g))).
      { apply Hp. }
      apply Hg2.
    - unshelve eapply (le_well_order_transitive
                         _ (rel_restriction _ (Im Full_set g))).
      { apply Hg2. }
      unshelve eapply (le_well_order_transitive
                         _ (rel_restriction _ (Im Full_set f))).
      { apply Hp. }
      apply Hf2.
  }
  (** Now replace [WO_Simulation_image_packed _] by
     [rel_restriction R2 (initial_segment _)]. *)
  destruct (WO_Simulation_non_surj_initial_segment _ _ f) as [xf]; auto.
  destruct (WO_Simulation_non_surj_initial_segment _ _ g) as [xg]; auto.
  cut (le_well_order
         (rel_restriction_inits R2 xf)
         (rel_restriction_inits R2 xg) \/
         le_well_order
           (rel_restriction_inits R2 xg)
           (rel_restriction_inits R2 xf)).
  { intros [Hp|Hp]; [left|right].
    - unshelve eapply (le_well_order_transitive
                         _ (rel_restriction_inits R2 xf)).
      { apply le_well_order_rel_restriction_Same_set.
        assumption.
      }
      unshelve eapply (le_well_order_transitive
                         _ (rel_restriction_inits R2 xg)).
      { assumption. }
      apply le_well_order_rel_restriction_Same_set.
      symmetry. assumption.
    - unshelve eapply (le_well_order_transitive
                         _ (rel_restriction_inits R2 xg)).
      { apply le_well_order_rel_restriction_Same_set.
        assumption.
      }
      unshelve eapply (le_well_order_transitive
                         _ (rel_restriction_inits R2 xf)).
      { assumption. }
      apply le_well_order_rel_restriction_Same_set.
      symmetry. assumption.
  }
  rewrite !rel_restriction_inits_le_char.
  (** And complete the proof by comparing the elements. *)
  destruct (classic (xf = xg)); auto.
  destruct (strongly_connected xf xg); auto.
Qed.

Lemma lt_well_order_neg {T0 R0 T1 R1}
  `(W0 : WellOrder T0 R0) `(W1 : WellOrder T1 R1) :
  ~ lt_well_order R0 R1 ->
  le_well_order R1 R0.
Proof.
  intros.
  destruct (le_well_order_total R0 R1); try assumption.
  destruct H0 as [f].
  assert (surjective f).
  { apply NNPP. intros ?.
    apply H. exists f. tauto.
  }
  destruct (eq_well_order_Simulation_surjective f H0 H1).
  assumption.
Qed.

Lemma lt_well_order_succ_step
  {X Y} R0 R1 `{WellOrder X R0} `{WellOrder Y R1} (p : Y) :
  lt_well_order R0 (rel_restriction_inits R1 p) ->
  exists q,
    le_well_order R0 (rel_restriction_inits R1 q) /\
      R1 q p.
Proof.
  intros [f [Hf0 Hf1]].
  destruct (WO_Simulation_non_surj_initial_segment _ _ f) as [q Hq];
    auto.
  exists (proj1_sig q).
  split.
  2: apply (proj2_sig q).
  unshelve eexists (fun r => exist _ (proj1_sig (f r)) _).
  { simpl. apply Hq.
    apply Im_def. constructor.
  }
  constructor; try apply Hf0.
  intros x [t Ht] Hxt.
  do 2 red in Ht.
  do 3 red in Hxt.
  simpl in *.
  apply simulation in Hxt as [[y Hy]].
  subst. do 2 red in Hy.
  simpl.
  (* use the [<-] direction of [Hq] on [Ht] *)
  pose proof ((proj2 Hq) (exist _ y Hy) Ht).
  inversion H1; subst; clear H1.
  exists x0. apply subset_eq. simpl.
  rewrite <- H3. reflexivity.
Qed.

Lemma le_well_order_packed_intersection_exists (F : Ensemble well_order_packed) :
  Inhabited F ->
  exists W, In F W /\
    (forall W0, In F W0 -> le_well_order_packed W W0) /\
      (forall W0, (forall W1, In F W1 -> le_well_order_packed W0 W1) ->
                  le_well_order_packed W0 W).
Proof.
  intros.
  destruct H as [W].
  pose (fun p : wop_carrier (well_order_successor W) =>
          exists W0,
            In F W0 /\
               le_well_order (wop_rel W0) (rel_restriction_inits (wop_rel _) p)) as A.
  assert (Inhabited A).
  { exists None.
    exists W; split; auto.
    apply le_well_order_packed_succ_None.
  }
  apply (WF_implies_MEP _ (wop_rel _)) in H0 as [p [Hp0 Hp1]].
  2: apply well_founded.
  destruct Hp0 as [W0 [HW0 HW1]].
  exists W0; split; auto.
  split; auto.
  intros.
  transitivity {| wop_rel := (rel_restriction_inits (wop_rel _) p) |}; auto.
  red. simpl.
  apply lt_well_order_neg.
  intros ?.
  cut (exists q, In A q /\ (wop_rel (well_order_successor W) q p)).
  { intros [q []].
    apply (Hp1 q); auto.
  }
  apply lt_well_order_succ_step in H1 as [q [Hq0 Hq1]].
  exists q. split; auto.
  exists W1; auto.
Qed.

Global Instance lt_well_order_packed_well_founded :
  WellFounded lt_well_order_packed.
Proof.
  apply MEP_implies_WF.
  intros S HS.
  pose proof HS as HS0.
  apply le_well_order_packed_intersection_exists in HS0 as [W [HW0 [HW1 HW2]]];
    auto.
  exists W; split; auto.
  intros. intros ?.
  apply HW1 in H.
  apply (@irreflexivity _ _ _ y).
  eapply lt_well_order_trans_lt_le; eauto.
Qed.

(** * Example
The natural numbers are well-ordered. *)
Require Import Lia.
Global Instance Nat_lt_WO : WellOrder lt.
Proof.
  split.
  - apply Wf_nat.lt_wf.
  - typeclasses eauto.
  - intros x y Heq.
    destruct (PeanoNat.Nat.lt_trichotomy x y) as [|[|]]; auto;
      apply Heq in H; do 2 red in H; lia.
Qed.

Section simulation_glueing.
  Context {T : Type} {R : T -> _}
    {HR : WellOrder R}.

  Definition rel_restriction_simulation_downwards_closed
    (U : Ensemble T) {HU : DownwardsClosed R U}:
    Simulation (rel_restriction R U) R (@proj1_sig T U).
  Proof.
    split.
    - firstorder.
    - firstorder.
    - intros [x Hx] t.
      simpl.
      intros Ht.
      specialize (HU x Hx t Ht).
      exists (exist _ t HU).
      reflexivity.
  Qed.
End simulation_glueing.
Section simulation_glueing.
  Context {X Y : Type} R0 R1 {HR0 : @WellOrder X R0}
    {HR1 : @WellOrder Y R1}.

  Theorem simulation_glueing
    (H : forall x : X,
        { f | Simulation (rel_restriction R0 (closed_initial_segment R0 x)) R1 f} ) :
    Simulation R0 R1 (fun x => proj1_sig (H x) (exist _ x (@wf_irrefl X R0 _ _))).
  Proof.
    split.
    - intros x0 x1 Hx.
      admit.
    - intros x0 x1 Hx.
      admit.
    - intros.
      admit.
  Abort.
End simulation_glueing.
Section simulation_glueing.
  Context {X Y : Type} R0 R1 `{HR : WellOrder X R0}
    `{HR1 : WeaklyExtensional Y R1}.
  Variable H : forall x : X,
      { f : { x0  : X | In (closed_initial_segment R0 x) x0 } -> Y |
        Simulation (rel_restriction R0 _) R1 f }.

  Lemma simulation_glueing_compat (x0 x1 : X) :
    R0 x0 x1 ->
    forall x Hx0 Hx1,
      proj1_sig (H x0) (exist _ x Hx0) = proj1_sig (H x1) (exist _ x Hx1).
  Proof.
    intros. simpl in *.
    unshelve erewrite (@simulation_uniqueness
                         _ _ (rel_restriction R0 _) R1 (proj1_sig (H x0))
                         (compose (proj1_sig (H x1)) (fun x2 => exist _ (proj1_sig x2) _)));
      try typeclasses eauto.
    { simpl. intros ?.
      pose proof (proj2_sig x2).
      red in H2.
      apply H2.
      transitivity x1; auto.
    }
    { simpl.
      unfold compose.
      simpl.
      rewrite (proof_irrelevance _ Hx1 (fun H1 => Hx0 (transitivity H0 H1))).
      reflexivity.
    }
    - apply (proj2_sig (H _)).
    - eapply Simulation_compose; try apply (proj2_sig (H _)).
      simpl.
      apply rel_restriction_inclusion_Simulation;
        try typeclasses eauto.
  Qed.

  Lemma simulation_glueing_compat0 (x0 x1 : X) :
    ~ R0 x1 x0 ->
    forall x Hx0 Hx1,
      proj1_sig (H x0) (exist _ x Hx0) = proj1_sig (H x1) (exist _ x Hx1).
  Proof.
    intros. simpl in *.
    unshelve erewrite (@simulation_uniqueness
                         _ _ (rel_restriction R0 _) R1 (proj1_sig (H x0))
                         (compose (proj1_sig (H x1)) (fun x2 => exist _ (proj1_sig x2) _)));
      try typeclasses eauto.
    { simpl. intros ?.
      pose proof (proj2_sig x2).
      red in H2.
      apply Connected_Classical_le in H2 as [|];
        try typeclasses eauto.
      - apply H0; transitivity (proj1_sig x2); auto.
      - rewrite H2 in *. contradiction.
    }
    { simpl.
      unfold compose.
      simpl.
      match goal with
      | |- proj1_sig _ (exist _ _ ?a) =
            proj1_sig _ (exist _ _ ?b) =>
          replace a with b;
          try reflexivity
      end.
      apply proof_irrelevance.
    }
    - apply (proj2_sig (H _)).
    - eapply Simulation_compose; try apply (proj2_sig (H _)).
      simpl.
      apply rel_restriction_inclusion_Simulation; auto;
        try typeclasses eauto.
  Qed.

  Lemma simulation_glueing :
    Simulation
      R0 R1
      (fun x : X => proj1_sig (H x)
                   (exist _ x (@wf_irrefl X R0 _ _))).
  Proof.
    constructor.
    - (* RelationPreserve *)
      intros x0 x1 Hxx.
      unshelve erewrite (simulation_glueing_compat x0 x1 Hxx).
      { intros ?. apply asymmetry in Hxx; auto. }
      simpl.
      apply (@sim_preserves _ _ _ _ _ (proj2_sig (H x1))).
      assumption.
    - (* RelationReflect *)
      intros x0 x1 Hxx.
      apply NNPP.
      intros Hx0.
      unfold complement in Hxx.
      unshelve erewrite (simulation_glueing_compat0 x1 x0 _ _ _ _) in Hxx;
        auto.
      apply (@sim_reflects _ _ _ _ _ (proj2_sig (H x0))) in Hxx.
      contradiction.
    - intros.
      destruct (@simulation _ _ _ _ _ (proj2_sig (H x)) (exist _ x (wf_irrefl x)) t);
        auto.
      subst.
      exists (proj1_sig x0).
      unshelve erewrite (simulation_glueing_compat0 (proj1_sig x0) x _ _ _ _).
      { apply (proj2_sig x0). }
      { apply (proj2_sig x0). }
      destruct x0. simpl. reflexivity.
  Qed.
End simulation_glueing.

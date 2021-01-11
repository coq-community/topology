From Coq Require Import Program.Equality.
From Coq Require Import Lia.
From Coq Require Import ClassicalChoice.

Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Export Families.
Require Export FiniteTypes.
Require Export IndexedFamilies.
Require Export CountableTypes.
Require Import Proj1SigInjective.
Require Export Powerset_facts.

Inductive finite_intersections {X:Type} (S:Family X) : Family X :=
  | intro_full: In (finite_intersections S) Full_set
  | intro_S: forall U:Ensemble X, In S U -> In (finite_intersections S) U
  | intro_intersection: forall U V:Ensemble X,
    In (finite_intersections S) U -> In (finite_intersections S) V ->
    In (finite_intersections S) (Intersection U V).

Lemma finite_intersection_is_finite_indexed_intersection:
  forall {X:Type} (S:Family X) (U:Ensemble X),
  In (finite_intersections S) U -> exists J:Type, FiniteT J /\
  exists V:J->Ensemble X,
  (forall j:J, In S (V j)) /\ U = IndexedIntersection V.
Proof.
intros.
induction H.
- exists False.
  split.
  + constructor.
  + exists (False_rect _).
    split.
    * destruct j.
    * symmetry; apply empty_indexed_intersection.
- exists True.
  split.
  + exact True_finite.
  + exists (True_rect U).
    split.
    * destruct j.
      simpl. assumption.
    * apply Extensionality_Ensembles; split; red; intros.
      -- constructor.
         destruct a; simpl.
         assumption.
      -- destruct H0.
         exact (H0 I).
- destruct IHfinite_intersections as [J0 [? [W []]]].
  destruct IHfinite_intersections0 as [J1 [? [W' []]]].
  exists ((J0+J1)%type).
  split.
  + apply finite_sum; trivial.
  + exists (fun s:J0+J1 => match s with
    | inl j => W j
    | inr j => W' j
    end).
    split.
    * destruct j; auto.
    * apply Extensionality_Ensembles; split; red; intros.
      -- destruct H7.
         rewrite H3 in H7; destruct H7.
         rewrite H6 in H8; destruct H8.
         constructor.
         destruct a as [j|j]; auto.
      -- destruct H7.
         constructor.
         ++ rewrite H3; constructor.
            intro j.
            exact (H7 (inl _ j)).
         ++ rewrite H6; constructor.
            intro j.
            exact (H7 (inr _ j)).
Qed.

Lemma finite_indexed_intersection_is_finite_intersection:
  forall {X:Type} (S:Family X) (J:Type) (V:J->Ensemble X),
  FiniteT J -> (forall j:J, In S (V j)) ->
  In (finite_intersections S) (IndexedIntersection V).
Proof.
intros.
induction H.
rewrite empty_indexed_intersection.
constructor.

assert (IndexedIntersection V = Intersection
  (IndexedIntersection (fun j:T => V (Some j)))
  (V None)).
apply Extensionality_Ensembles; split; red; intros.
destruct H1.
constructor.
constructor.
trivial.
trivial.
destruct H1.
constructor.
destruct H1.
destruct a as [j|]; trivial.
rewrite H1.
constructor 3; auto.
constructor 2; trivial.

destruct H1 as [g].
assert (IndexedIntersection V =
  IndexedIntersection (fun x:X0 => V (f x))).
apply Extensionality_Ensembles; split; red; intros.
destruct H3.
constructor.
trivial.
destruct H3.
constructor.
intro.
rewrite <- (H2 a).
trivial.
rewrite H3; auto.
Qed.

Section Lemmas.
Open Scope nat.

Inductive finite_intersections_len {X : Type} (F : Family X) : IndexedFamily nat (Ensemble X) :=
  | intro_fi_len_full : In (finite_intersections_len F 0) Full_set
  | intro_fi_len_S : forall U : Ensemble X, In F U -> In (finite_intersections_len F 1) U
  | intro_fi_len_intersection : forall (U V : Ensemble X) (m k : nat),
                         In (finite_intersections_len F m) U ->
                         In (finite_intersections_len F k) V ->
                         In (finite_intersections_len F (m + k)) (Intersection U V).

Lemma finite_intersections_len_0_full_set
  {X : Type}
  {F : Family X}
  {U : Ensemble X} :
  In (finite_intersections_len F 0) U -> U = Full_set.
Proof.
intro H.
red in H.
dependent induction H.
{ reflexivity. }
rewrite IHfinite_intersections_len.
2: { lia. }
rewrite Intersection_Full_set.
rewrite IHfinite_intersections_len0.
{ reflexivity. }
lia.
Qed.

Lemma finite_intersections_len_1_in
  {X : Type}
  {F : Family X}
  {U : Ensemble X} :
  In (finite_intersections_len F 1) U -> In F U.
Proof.
intro H.
red in H.
dependent induction H.
- assumption.
- destruct m, k;
    discriminate + injection x as x;
    subst.
  + rewrite (finite_intersections_len_0_full_set H), Intersection_Full_set.
    now apply IHfinite_intersections_len0.
  + rewrite (finite_intersections_len_0_full_set H0), Intersection_commutative, Intersection_Full_set.
    apply IHfinite_intersections_len.
    lia.
  + lia.
Qed.

Lemma finite_intersections_len_SS_intersection
  {X : Type}
  {F : Family X}
  {U : Ensemble X}
  (n : nat) :
  In (finite_intersections_len F (S (S n))) U ->
  exists m k V W,
    In (finite_intersections_len F (S m)) V /\
    In (finite_intersections_len F (S k)) W /\
    U = Intersection V W /\
    n = m + k.
Proof.
intro H.
red in H.
dependent induction H.
- destruct m, k;
    discriminate + injection x as x;
    subst.
  + rewrite (finite_intersections_len_0_full_set H), Intersection_Full_set.
    now apply IHfinite_intersections_len0.
  + rewrite (finite_intersections_len_0_full_set H0), Intersection_commutative, Intersection_Full_set.
    apply IHfinite_intersections_len.
    lia.
  + exists m, k, U, V.
    repeat split;
      lia + assumption.
Qed.

Lemma finite_intersections_len_S_exists
  {X : Type}
  {F : Family X}
  {U : Ensemble X}
  {n : nat} :
  In (finite_intersections_len F (S n)) U ->
  exists V W,
    In (finite_intersections_len F n) V /\
    In (finite_intersections_len F 1) W /\
    U = Intersection V W.
Proof.
generalize dependent U.
generalize dependent n.
apply (well_founded_ind lt_wf (fun n =>
  forall U,
    In (finite_intersections_len F (S n)) U ->
  exists V W,
    In (finite_intersections_len F n) V /\
    In (finite_intersections_len F 1) W /\
    U = Intersection V W)).
intros [|n] IH U H.
- apply finite_intersections_len_1_in in H.
  exists Full_set, U.
  now repeat split;
    constructor + rewrite Intersection_Full_set.
- apply finite_intersections_len_SS_intersection in H.
  destruct H as [m [[|k] [V [W [HV [HW [eq1 eq2]]]]]]].
  + rewrite Nat.add_0_r in eq2.
    subst.
    now exists V, W.
  + apply IH in HV; [|lia].
    destruct HV as [V1 [V2 [HV1 [HV2 eq3]]]].
    rewrite eq2, plus_n_Sm.
    exists (Intersection V1 W), V2.
    repeat (constructor; try easy).
    subst.
    now rewrite (Intersection_associative V1 W),
                (Intersection_commutative _ W),
             <- (Intersection_associative V1).
Qed.

Lemma finite_intersections_len_S_choice
  {X : Type}
  (F : Family X)
  (n : nat) :
  exists f : {U : Ensemble X | In (finite_intersections_len F (S n)) U} ->
             {U : Ensemble X | In (finite_intersections_len F n) U} *
             {U : Ensemble X | In (finite_intersections_len F 1) U},
  forall U, proj1_sig U = Intersection (proj1_sig (fst (f U))) (proj1_sig (snd (f U))).
Proof.
apply choice with (R :=
  fun U : {U : Ensemble X | In (finite_intersections_len F (S n)) U} =>
  fun y : {U : Ensemble X | In (finite_intersections_len F n) U} *
          {U : Ensemble X | In (finite_intersections_len F 1) U} =>
    proj1_sig U = Intersection (proj1_sig (fst y)) (proj1_sig (snd y))).
intros [? HU].
destruct (finite_intersections_len_S_exists HU) as [V [W [HV [HW ?]]]].
now exists (exist _ V HV, exist _ W HW).
Qed.

Lemma finite_intersections_len_union
  {X : Type}
  (F : Family X) :
  IndexedUnion (finite_intersections_len F) = finite_intersections F.
Proof.
apply Extensionality_Ensembles.
split.
- intros ? [n U HU].
  red in HU.
  dependent induction HU.
  + apply intro_full.
  + now apply intro_S.
  + now apply intro_intersection.
- intros ? HU.
  red in HU.
  dependent induction HU;
    try destruct IHHU, IHHU0;
    econstructor.
  + constructor.
  + now apply intro_fi_len_S.
  + apply intro_fi_len_intersection.
    exact H1.
    exact H2.
Qed.

Lemma finite_intersections_countable
  {X : Type}
  (F : Family X) :
  Countable F -> Countable (finite_intersections F).
Proof.
intros [f Hf].
rewrite <- finite_intersections_len_union.
apply countable_union.
- apply nat_countable.
- intro n.
  induction n.
  + apply intro_nat_injection with (fun x => 0).
    intros [U HU] [V HV] eq.
    apply proj1_sig_injective.
    simpl.
    now rewrite (finite_intersections_len_0_full_set HU),
                (finite_intersections_len_0_full_set HV).
  + destruct (finite_intersections_len_S_choice F n) as [g Hg],
             IHn as [fn Hfn].
    refine (inj_countable (fun U =>
      (fn (fst (g U)),
       f (exist _ (proj1_sig (snd (g U))) _)))
      countable_nat_product _).
    intros [U HU] [V HV] eq.
  injection eq as eq1 eq2.
  apply Hfn, proj1_sig_eq in eq1.
  apply Hf, proj1_sig_eq in eq2.
  apply Proj1SigInjective.proj1_sig_injective.
  now rewrite Hg, Hg, eq1, eq2.
  Unshelve.
  destruct (snd (g U)).
  now apply finite_intersections_len_1_in.
Qed.

End Lemmas.

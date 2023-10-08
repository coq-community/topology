(** First introduces a predicate [CountableT : Type -> Prop] of countable types.
    Then introduces a similar predicate [Countable : Ensemble X -> Prop] on ensembles.
*)

From Coq Require Import
  Arith
  ArithRing
  ClassicalChoice
  Description
  FunctionalExtensionality
  Lia
  Relation_Definitions
  Program.Subset
  QArith
  ZArith.
From ZornsLemma Require Import
  Cardinals
  DecidableDec
  DependentTypeChoice
  Finite_sets
  FiniteTypes
  FunctionProperties
  FunctionPropertiesEns
  IndexedFamilies
  InverseImage.

Local Close Scope Q_scope.

Set Asymmetric Patterns.

Definition CountableT (X : Type) : Prop :=
  le_cardinal X nat.

Lemma CountableT_is_FiniteT_or_countably_infinite (X : Type) :
  CountableT X -> {FiniteT X} + {eq_cardinal X nat}.
Proof.
intros.
apply exclusive_dec.
- intros [].
  contradiction nat_infinite.
  apply bij_finite with X; auto.
- destruct (classic (FiniteT X)).
  + left; trivial.
  + right.
    apply infinite_nat_inj in H0.
    destruct H as [f], H0 as [g].
    now apply CSB with f g.
Qed.

Lemma nat_countable : CountableT nat.
Proof.
exists id. apply id_bijective.
Qed.

Lemma countable_nat_product: CountableT (nat * nat).
Proof.
pose (sum_1_to_n := fix sum_1_to_n n:nat := match n with
  | O => O
  | S m => (sum_1_to_n m) + n
end).
exists (fun p:nat*nat => let (m,n):=p in
  (sum_1_to_n (m+n)) + n).
assert (forall m n:nat, m<n ->
  sum_1_to_n m + m < sum_1_to_n n).
- intros.
  induction H.
  + simpl.
    auto with arith.
  + apply Nat.lt_trans with (sum_1_to_n m0); trivial.
    assert (sum_1_to_n m0 + 0 < sum_1_to_n m0 + S m0) by auto with arith.
    assert (sum_1_to_n m0 + 0 = sum_1_to_n m0) by auto with arith.
    now rewrite H1 in H0.
- intros [x1 y1] [x2 y2] H0.
  case (lt_eq_lt_dec (x1+y1) (x2+y2)); intro.
  + case s; intro.
    * assert (sum_1_to_n (x1+y1) + y1 < sum_1_to_n (x2+y2) + y2); try lia.
      apply Nat.le_lt_trans with (sum_1_to_n (x1+y1) + (x1+y1)); try lia.
      apply Nat.lt_le_trans with (sum_1_to_n (x2+y2)); try lia.
      apply H.
      lia.
    * assert (y1=y2) by (rewrite e in H0; lia).
      f_equal; lia.
  + cut (sum_1_to_n (x2+y2) + y2 < sum_1_to_n (x1+y1) + y1); try lia.
    apply Nat.le_lt_trans with (sum_1_to_n (x2+y2) + (x2+y2)),
          Nat.lt_le_trans with (sum_1_to_n (x1+y1));
        auto with arith.
Qed.

Lemma countable_sum (X Y : Type) :
  CountableT X -> CountableT Y -> CountableT (X + Y).
Proof.
intros [f] [g].
destruct countable_nat_product as [h].
exists (fun s:X+Y => match s with
  | inl x => h (0, f x)
  | inr y => h (1, g y)
end).
intros [x1|y1] [x2|y2] ?;
  apply H1 in H2; try discriminate H2;
  intros; f_equal;
  apply H + apply H0;
  now injection H2.
Qed.

Lemma countable_product (X Y:Type) :
  CountableT X -> CountableT Y -> CountableT (X * Y).
Proof.
intros [f] [g].
pose (fg := fun (p:X*Y) => let (x,y):=p in (f x, g y)).
destruct countable_nat_product as [h].
exists (fun p:X*Y => h (fg p)).
intros [x1 y1] [x2 y2] H2.
apply H1 in H2.
injection H2 as H3 H4.
apply H in H3.
apply H0 in H4.
now subst.
Qed.

Lemma countable_exp (X Y : Type) :
  FiniteT X -> CountableT Y -> CountableT (X -> Y).
Proof.
intros.
induction H.
- exists (fun _ => 0).
  red; intros.
  extensionality f.
  destruct f.
- destruct (countable_product (T -> Y) Y) as [f]; trivial.
  exists (fun g =>
    f (fun x => g (Some x), g None)).
  intros g1 g2 ?.
  apply H1 in H2.
  extensionality o.
  destruct o;
    injection H2;
    trivial.
  intros.
  pose proof (equal_f H4).
  apply H5.
- destruct H1 as [f [f1 Hf]].
  destruct IHFiniteT as [f0 Hf0].
  exists (fun h => f0 (fun x => h (f x))).
  intros h1 h2 ?.
  apply Hf0 in H1.
  pose proof (equal_f H1).
  simpl in H2.
  extensionality y.
  rewrite <- (proj2 Hf y).
  apply H2.
Qed.

Lemma inj_countable {X Y : Type} (f : X -> Y) :
  CountableT Y -> injective f -> CountableT X.
Proof.
intros [g] ?.
exists (fun x:X => g (f x)).
intros x1 x2 ?.
auto.
Qed.

Lemma surj_countable {X Y : Type} (f : X -> Y) :
  CountableT X -> surjective f -> CountableT Y.
Proof.
intros.
destruct (choice (fun (y:Y) (x:X) => f x = y)) as [finv]; trivial.
apply inj_countable with finv; trivial.
intros x1 x2 ?.
congruence.
Qed.

Lemma FiniteT_impl_CountableT (X : Type) :
  FiniteT X -> CountableT X.
Proof.
intros.
induction H.
- exists (False_rect nat).
  now intro.
- destruct IHFiniteT as [f].
  exists (fun x => match x with
    | Some x0 => S (f x0)
    | None => 0
  end).
  intros [x1|] [x2|] H1;
    injection H1 as H1 + discriminate H1 + trivial.
  now destruct (H0 _ _ H1).
- destruct IHFiniteT as [g],
           H0 as [f [finv]].
  exists (fun y:Y => g (finv y)).
  intros y1 y2 ?.
  apply H1 in H2.
  destruct H0.
  congruence.
Qed.

Lemma positive_countable: CountableT positive.
Proof.
exists nat_of_P.
intros n1 n2 ?.
now apply nat_of_P_inj.
Qed.

Lemma Z_countable: CountableT Z.
Proof.
destruct countable_nat_product as [f],
         positive_countable as [g].
exists (fun n:Z => match n with
  | Z0 => f (0, 0)
  | Zpos p => f (1, g p)
  | Zneg p => f (2, g p)
end).
intros [|p1|p1] [|p2|p2] H1;
  apply H in H1;
  discriminate H1 + trivial;
  injection H1 as H1; f_equal; auto.
Qed.

Lemma Q_countable: CountableT Q.
Proof.
destruct countable_nat_product as [f],
         positive_countable as [g],
         Z_countable as [h].
exists (fun q:Q => match q with
  n # d => f (h n, g d)
end)%Q.
intros [n1 d1] [n2 d2] ?.
apply H in H2.
injection H2 as H2.
f_equal; auto.
Qed.

(** ** Countable ensembles *)
Definition Countable {X : Type} (S : Ensemble X) : Prop :=
  CountableT {x:X | In S x}.

Lemma countable_downward_closed {X : Type} (S T : Ensemble X) :
  Countable T -> Included S T -> Countable S.
Proof.
intros [f H] H0.
exists (fun x => match x with
  | exist x0 i => f (exist _ x0 (H0 _ i))
  end).
intros [x1] [x2] H1.
apply H in H1.
injection H1 as H1.
destruct H1.
now apply subset_eq.
Qed.

Lemma countable_img {X Y : Type} (f : X -> Y) (S : Ensemble X) :
  Countable S -> Countable (Im S f).
Proof.
intros.
assert (forall x, In S x -> In (Im S f) (f x)) by auto with sets.
pose (fS := fun x =>
  match x with
  | exist x0 i => exist _ (f x0) (H0 x0 i)
  end).
apply surj_countable with fS; trivial.
intros [? [x i y e]].
exists (exist _ x i).
simpl.
generalize (H0 x i); intro.
generalize (Im_intro X Y S f x i y e); intro.
now apply subset_eq.
Qed.

Lemma countable_type_ensemble  {X : Type} (S : Ensemble X) :
  CountableT X -> Countable S.
Proof.
intros.
apply (inj_countable (@proj1_sig _ (In S)) H).
intros [? ?] [? ?].
now apply subset_eq_compat.
Qed.

Lemma Finite_impl_Countable: forall {X : Type} (S : Ensemble X),
  Finite S -> Countable S.
Proof.
intros.
now apply FiniteT_impl_CountableT, Finite_ens_type.
Qed.

Corollary countable_empty {X : Type} :
  Countable (@Empty_set X).
Proof.
  apply Finite_impl_Countable.
  apply Empty_is_finite.
Qed.

Corollary countable_singleton {X : Type} (x : X) :
  Countable (Singleton x).
Proof.
  apply Finite_impl_Countable.
  apply Singleton_is_finite.
Qed.

Lemma countable_family_union: forall {X:Type}
  (F:Family X), Countable F ->
  (forall U, In F U -> Countable U) ->
  Countable (FamilyUnion F).
Proof.
intros.
destruct (choice_on_dependent_type (fun (a : { U | In F U })
                               (f:{x:X | In (proj1_sig a) x} -> nat) =>
  injective f)) as [choice_fun_inj].
{ intros [U].
  destruct (H0 U) as [f]; try assumption.
  now exists f.
}
destruct (choice (fun (x:{x:X | In (FamilyUnion F) x}) (a: { U | In F U }) =>
  In (proj1_sig a) (proj1_sig x))) as [choice_fun_a].
{ destruct x as [x [a]].
  now exists (exist _ a i).
}
destruct countable_nat_product as [g],
         H as [h].
exists (fun x:{x:X | In (FamilyUnion F) x} =>
  g (h (choice_fun_a x), choice_fun_inj _ (exist _ _ (H2 x)))).
intros x1 x2 H4.
apply H3 in H4.
injection H4 as H5 H6.
apply H in H5.
revert H6.
generalize (H2 x1), (H2 x2).
rewrite H5.
intros.
apply H1 in H6.
injection H6.
destruct x1, x2.
apply subset_eq_compat.
Qed.

Lemma countable_indexed_union: forall {X A:Type}
  (F:IndexedFamily A X), CountableT A ->
    (forall a:A, Countable (F a)) ->
    Countable (IndexedUnion F).
Proof.
intros.
rewrite indexed_to_family_union.
apply countable_family_union.
- apply countable_img.
  apply countable_type_ensemble.
  assumption.
- intros. destruct H1.
  subst. apply H0.
Qed.

Lemma countable_union2
  {X : Type}
  {U V : Ensemble X} :
  Countable U ->
  Countable V ->
  Countable (Union U V).
Proof.
intros HU HV.
assert (exists h : {x : X | In (Union U V) x} ->
              {x : X | In U x} + {x : X | In V x},
           injective h) as [h Hh].
2: {
  apply inj_countable with (f := h); auto.
  apply countable_sum; assumption.
}
unshelve eexists
  (fun p : { x : X | In (Union U V) x } =>
     match (classic_dec (In U (proj1_sig p))) with
     | left Hl =>
         inl (exist U (proj1_sig p) Hl)
     | right Hr =>
         match (classic_dec (In V (proj1_sig p))) with
         | left Hl =>
             inr (exist V (proj1_sig p) Hl)
         | right Hr0 =>
             False_rect _ _
         end
     end).
{ destruct (proj2_sig p); auto. }
simpl in *.
intros [x0 Hx0] [x1 Hx1] Hx.
simpl in *.
repeat
  (try discriminate;
   try (inversion Hx0; subst; contradiction);
   try (inversion Hx1; subst; contradiction);
   destruct (classic_dec _)).
all: inversion Hx; subst; clear Hx;
  destruct (proof_irrelevance _ Hx0 Hx1);
  reflexivity.
Qed.

Definition countable_img_inj {X Y : Type} (f : X -> Y) (U : Ensemble X) :
  injective_ens f U ->
  CountableT X ->
  Countable (Im U f) :=
  @le_cardinal_img_inj_ens X Y nat f U.

Lemma Countable_as_le_cardinal_ens {X : Type} (U : Ensemble X) :
  Countable U <-> le_cardinal_ens U (@Full_set nat).
Proof.
  split.
  - intros [f Hf].
    pose proof (eq_cardinal_ens_sig U).
    eapply le_cardinal_ens_Proper_l; eauto.
    right. exists f. split; [|firstorder].
    intros ? ?. constructor.
  - intros [[]|[f [_ Hf]]].
    { contradict (H 0). }
    exists (fun p => f (proj1_sig p)).
    intros [x0 H0] [x1 H1] Hx.
    simpl in Hx.
    specialize (Hf x0 x1 H0 H1 Hx).
    apply subset_eq_compat.
    assumption.
Qed.

(** ** Unbounded subsets of [nat] are countably infinite *)
Lemma nat_minimal_element_property_dec
  (U : Ensemble nat) (HUdec : forall n : nat, In U n \/ ~ In U n)
  (HUinh : Inhabited U) :
  exists m : nat, In U m /\ forall n : nat, In U n -> m <= n.
Proof.
  destruct HUinh as [N HN].
  revert U HUdec HN.
  induction N.
  { intros.
    exists 0. split; auto. lia.
  }
  intros U HUdec HN.
  destruct (HUdec 0) as [HU0|HU0].
  { exists 0. split; auto. lia. }
  specialize (IHN (compose U S)) as [m [Hm0 Hm1]];
    auto.
  { intros ?. apply HUdec. }
  destruct (HUdec m) as [HUm|HUm].
  { exists m; split; auto; intros n Hn.
    destruct n; try contradiction.
    apply Hm1 in Hn. lia.
  }
  exists (S m). split; auto.
  intros n Hn.
  destruct n; try contradiction.
  apply le_n_S.
  apply Hm1.
  assumption.
Qed.

Lemma nat_bounded_ens_has_max_dec
  (U : Ensemble nat)
  (HUdec : forall n : nat, In U n \/ ~ In U n)
  (N : nat) :
  (forall n : nat, In U n -> n < N) ->
  Inhabited U ->
  exists n : nat, In U n /\
             forall m : nat, In U m -> m <= n.
Proof.
  intros HN HU.
  induction N.
  { destruct HU as [u Hu].
    specialize (HN u Hu). lia.
  }
  clear HU.
  specialize (HUdec N) as [HN0|HN0].
  - exists N; split; auto.
    intros m Hm. specialize (HN m Hm).
    lia.
  - apply IHN.
    intros n Hn.
    specialize (HN n Hn).
    assert (n <> N).
    { intros ?; congruence. }
    lia.
Qed.

(** if a set [U] has an element [o] and an injective function [succ]
  (possibly defined on a larger set than [U]) such that
  [o] is not in the image of [succ], and
  [U] satisfies an induction principle, then [U] is countably infinite *)
Lemma peano_ensemble_countably_infinite {X : Type}
  (U : Ensemble X) (o : X) (succ : X -> X) :
  In U o ->
  (forall x : X, In U x -> In U (succ x)) ->
  injective_ens succ U ->
  (forall x : X, In U x -> o <> succ x) ->
  (forall P : Ensemble X,
      P o ->
      (forall x, In U x -> P x -> P (succ x)) ->
      forall x, In U x -> P x) ->
  eq_cardinal_ens (@Full_set nat) U.
Proof.
  intros HUo HUsucc Hsucc_inj Hsucc_o HUind.
  right.
  pose (g := fix g (n : nat) : { n : X | In U n } :=
       match n with
       | O => exist U o HUo
       | S n => exist U (succ (proj1_sig (g n)))
                 (HUsucc (proj1_sig (g n)) (proj2_sig (g n)))
       end).
  exists (fun n => proj1_sig (g n)).
  split; [|split].
  - intros x Hx.
    clear Hx.
    induction x.
    { simpl. assumption. }
    simpl. apply HUsucc, IHx.
  - intros x0 x1 Hx0 Hx1 Hx.
    clear Hx0 Hx1.
    revert x1 Hx.
    induction x0; intros x1 Hx.
    { simpl in Hx.
      destruct x1.
      { reflexivity. }
      simpl in Hx.
      apply Hsucc_o in Hx; try contradiction.
      apply proj2_sig.
    }
    simpl in Hx.
    destruct x1.
    { simpl in Hx.
      symmetry in Hx.
      apply Hsucc_o in Hx; try contradiction.
      apply proj2_sig.
    }
    simpl in Hx.
    apply Hsucc_inj in Hx; try now apply proj2_sig.
    apply IHx0 in Hx. congruence.
  - red. apply HUind.
    + exists 0. split; constructor.
    + intros x Hx [y [Hy Hy0]].
      subst.
      exists (S y); split; [constructor|].
      simpl. reflexivity.
Qed.

Theorem nat_unbounded_impl_countably_infinite_dec
  (U : Ensemble nat) (HU : forall n : nat, exists m : nat, In U m /\ n < m)
  (HUdec : forall n : nat, In U n \/ ~ In U n) :
  eq_cardinal_ens U (@Full_set nat).
Proof.
  (* we use [nat_minimal_element_property_dec] to note that [U] is
     well-founded by [lt].
     Then show:
     Hu: the set [U] has a least element [u]
     Hf: the set [U] has a "successor" function [f]
     Hfu: [u] is not in the image of [f]
     Hf_inj: the function [f] is injective on [U]
     HU0: every element of [U] is either [u] or lies in the image of [f]

     Combine these in [peano_ensemble_countably_infinite]
     to obtain a bijection (even an order-isomorphism)
     between [U] and [Full_set].
   *)
  assert (exists u : nat, In U u /\ (forall n : nat, In U n -> u <= n)) as Hu.
  { specialize (HU 0) as [m [Hm0 Hm1]].
    apply nat_minimal_element_property_dec; auto.
    exists m. assumption.
  }
  assert (exists f : nat -> nat,
           (forall n : nat,
             In U n ->
             In U (f n)) /\
             (forall n : nat,
                 In U n ->
                 n < f n) /\
             (forall n : nat,
                 In U n ->
                 forall m : nat,
                   In U m ->
                   n < m -> f n <= m)) as Hf.
  { cut (forall n : nat,
            { fn : nat |
              (In U n ->
               In U fn /\ n < fn /\
                 forall m : nat, In U m -> n < m -> fn <= m) /\
                (~ In U n -> fn = 0) }).
    { intros F.
      exists (fun n => proj1_sig (F n)).
      repeat split; intros n Hn;
        pose proof (proj1 (proj2_sig (F n)) Hn) as [Hn0 [Hn1 Hn2]];
        auto.
    }
    intros n.
    apply constructive_definite_description.
    destruct (HUdec n) as [Hn0|Hn0].
    2: {
      exists 0. repeat split; try contradiction.
      intuition.
    }
    destruct
      (nat_minimal_element_property_dec
         (fun m => In U m /\ n < m)) as [k [[Hk0 Hk1] Hk2]].
    { unfold In.
      intros m.
      destruct (Nat.lt_ge_cases n m).
      2: {
        right. intros []. lia.
      }
      specialize (HUdec m) as [|].
      - left; tauto.
      - right; intros []; tauto.
    }
    { destruct (HU n) as [m Hm].
      exists m. assumption.
    }
    exists k. repeat split; try tauto.
    { firstorder. }
    intros l [Hl _].
    specialize (Hl Hn0) as [Hl0 [Hl1 Hl2]].
    specialize (Hk2 l (conj Hl0 Hl1)).
    specialize (Hl2 k Hk0 Hk1).
    lia.
  }
  destruct Hu as [u [Hu0 Hu1]].
  destruct Hf as [f [Hf0 [Hf1 Hf2]]].
  assert (forall x : nat, In U x -> u <> f x) as Hfu.
  { intros x Hx.
    specialize (Hu1 x Hx).
    specialize (Hf1 x Hx).
    lia.
  }
  (* show that [f] is injective on [U] *)
  assert (injective_ens f U) as Hf_inj.
  { intros x0 x1 Hx0 Hx1 Hx.
    destruct (Nat.lt_trichotomy x0 x1) as [Hxx|[Hxx|Hxx]]; auto.
    - specialize (Hf2 x0 Hx0 x1 Hx1 Hxx).
      specialize (Hf1 x1 Hx1). lia.
    - specialize (Hf2 x1 Hx1 x0 Hx0 Hxx).
      specialize (Hf1 x0 Hx0). lia.
  }
  assert (forall x : nat,
             In U x -> x = u \/ exists y : nat, In U y /\ x = f y) as HU0.
  { intros x Hx.
    destruct (Nat.eq_dec x u); auto.
    right.
    (* [y] must be the greatest element of [U] which satisfies [y < x]. *)
    unshelve epose proof (nat_bounded_ens_has_max_dec
                            (fun y => In U y /\ y < x) _ x)
      as [y Hy].
    - intros k. unfold In.
      destruct (Nat.lt_ge_cases k x).
      2: {
        right. intros []. lia.
      }
      specialize (HUdec k) as [|].
      + left; tauto.
      + right; intros []; tauto.
    - intros k [Hk0 Hk1]. auto.
    - exists u. split; auto.
      specialize (Hu1 x Hx). lia.
    - exists y. split; try apply Hy.
      destruct Hy as [[Hy0 Hy1] Hy2].
      unfold In at 1 in Hy2.
      apply Nat.le_antisymm.
      2: now apply Hf2; auto.
      apply Nat.nlt_ge.
      intros Hfy.
      specialize (Hy2 (f y) (conj (Hf0 y Hy0) Hfy)).
      specialize (Hf1 y Hy0).
      lia.
  }
  assert (forall P : (forall x : nat, Prop),
             P u ->
             (forall (x : nat) (Hx : In U x),
                 P x -> P (f x)) ->
             forall (x : nat), In U x -> P x) as HUind.
  { intros P HP0 HP1 x.
    apply (Wf_nat.lt_wf_rect x (fun x => In U x -> P x)).
    clear x.
    intros x Hind Hx.
    destruct (HU0 x Hx) as [Hx0|[y [Hy Hy0]]]; subst; auto.
  }
  apply eq_cardinal_ens_sym_dec.
  { left. constructor. apply 0. }
  { assumption. }
  apply peano_ensemble_countably_infinite with u f;
    auto.
Qed.

Lemma nat_unbounded_impl_countably_infinite
  (U : Ensemble nat) (HU : forall n : nat, exists m : nat, In U m /\ n < m) :
  eq_cardinal_ens U (@Full_set nat).
Proof.
  apply nat_unbounded_impl_countably_infinite_dec;
    auto.
  intros ?. apply classic.
Qed.

(** The following proofs are in this file, because they require
  [FiniteT] and [nat_unbounded_impl_countably_infinite]. *)
Lemma Finite_as_lt_cardinal_ens
  {X : Type} (U : Ensemble X) :
  Finite U <-> lt_cardinal_ens U (@Full_set nat).
Proof.
  split.
  - (* -> *)
    (* this proof directly constructs a function [X -> nat] using [classic_dec].
       Another proof would do induction over [Finite X] and construct the
       function [X -> nat] inductively *)
    intros HU.
    split.
    + apply Finite_ens_type in HU.
      apply FiniteT_nat_embeds in HU.
      destruct HU as [f Hf].
      right.
      exists (fun x : X =>
           match classic_dec (In U x) with
           | left Hx => f (exist U x Hx)
           | right _ => 0
           end).
      split.
      * apply range_full.
      * intros x0 x1 Hx0 Hx1.
        destruct (classic_dec _); try contradiction.
        destruct (classic_dec _); try contradiction.
        intros Hx.
        apply Hf in Hx.
        inversion Hx; subst; clear Hx.
        reflexivity.
    + intros [[_ H]|H].
      { exact (H 0 ltac:(constructor)). }
      destruct H as [f [Hf0 Hf1]].
      red in Hf0.
      apply nat_infinite.
      apply Finite_ens_type in HU.
      pose (f0 := fun n : nat => exist U (f n) (Hf0 n ltac:(constructor))).
      assert (invertible f0).
      { apply bijective_impl_invertible.
        split.
        - intros n0 n1 Hn.
          inversion Hn; subst; clear Hn.
          apply Hf1 in H0; auto; constructor.
        - intros [x Hx].
          destruct Hf1 as [_ Hf1].
          specialize (Hf1 x Hx) as [n [_ Hn]].
          exists n. subst. unfold f0.
          apply subset_eq. reflexivity.
      }
      destruct H as [g Hg0].
      apply bij_finite with (sig U).
      { assumption. }
      exists g, f0. apply inverse_map_sym, Hg0.
  - (* <- *)
    intros [[[H0 H1]|[f [Hf0 Hf1]]] H2].
    { specialize (H0 0). contradiction. }
    destruct (classic (exists n : nat, forall x : X, In U x -> f x < n)).
    2: {
      contradict H2.
      assert (eq_cardinal_ens (Im U f) (@Full_set nat)).
      { apply nat_unbounded_impl_countably_infinite.
        intros n. apply NNPP.
        intros Hn. contradict H.
        exists (S n). intros x Hx.
        apply NNPP. intros Hx0.
        contradict Hn. exists (f x).
        split.
        { apply Im_def; auto. }
        lia.
      }
      apply eq_cardinal_ens_Im_injective in Hf1.
      apply eq_cardinal_ens_sym.
      eapply eq_cardinal_ens_trans; eauto.
    }
    destruct H as [n Hn].
    (* [n] is an upper bound of the image of [U] under [f] *)
    apply Finite_injective_image with f;
      auto.
    apply nat_Finite_bounded_char.
    exists n. intros m Hm.
    destruct Hm as [x Hx m Hm]; subst.
    apply Hn; auto.
Qed.

Corollary injective_finite_inverse_image
  {X Y : Type} (f : X -> Y) (U : Ensemble Y) :
  injective f ->
  Finite U ->
  Finite (inverse_image f U).
Proof.
  intros Hf HU.
  apply Finite_as_lt_cardinal_ens.
  apply Finite_as_lt_cardinal_ens in HU.
  apply (inverse_image_injective_cardinal_le f U) in Hf.
  eapply le_lt_cardinal_ens_transitive; eauto.
Qed.

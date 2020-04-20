Require Export FiniteTypes Relation_Definitions ZArith QArith IndexedFamilies.
Require Import InfiniteTypes CSB DecidableDec
               FunctionalExtensionality ProofIrrelevance
               DependentTypeChoice ClassicalChoice
               Arith ArithRing.

Local Close Scope Q_scope.

Set Asymmetric Patterns.

Inductive CountableT (X : Type) : Prop :=
  | intro_nat_injection (f : X -> nat) : injective f -> CountableT X.

Lemma CountableT_is_FiniteT_or_countably_infinite (X : Type) :
  CountableT X -> {FiniteT X} + {exists f : X -> nat, bijective f}.
Proof.
intros.
apply exclusive_dec.
- intro.
  destruct H0 as [? [f ?]].
  contradiction nat_infinite.
  apply bij_finite with _ f; trivial.
  apply bijective_impl_invertible; trivial.
- destruct (classic (FiniteT X)).
  + left; trivial.
  + right.
    apply infinite_nat_inj in H0.
    destruct H, H0 as [g].
    now apply CSB with f g.
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
  + apply lt_trans with (sum_1_to_n m0); trivial.
    assert (sum_1_to_n m0 + 0 < sum_1_to_n m0 + S m0) by auto with arith.
    assert (sum_1_to_n m0 + 0 = sum_1_to_n m0) by auto with arith.
    now rewrite H1 in H0.
- intros [x1 y1] [x2 y2] H0.
  case (lt_eq_lt_dec (x1+y1) (x2+y2)); intro.
  + case s; intro.
    * assert (sum_1_to_n (x1+y1) + y1 < sum_1_to_n (x2+y2) + y2).
      ** apply le_lt_trans with (sum_1_to_n (x1+y1) + (x1+y1)).
         *** assert (sum_1_to_n (x1+y1) + (x1+y1) =
               (sum_1_to_n (x1+y1) + y1) + x1);
             [ ring | auto with arith ].
         *** apply lt_le_trans with (sum_1_to_n (x2+y2));
             [ apply H |];
             auto with arith.
      ** rewrite H0 in H1.
         contradict H1.
         auto with arith.
    * assert (y1=y2).
      ** rewrite e in H0.
         now apply plus_reg_l in H0.
      ** f_equal; trivial.
         rewrite H1, plus_comm, (plus_comm x2 y2) in e.
         now apply plus_reg_l in e.
  + assert (sum_1_to_n (x2+y2) + y2 < sum_1_to_n (x1+y1) + y1).
    * apply le_lt_trans with (sum_1_to_n (x2+y2) + (x2+y2)),
            lt_le_trans with (sum_1_to_n (x1+y1));
        auto with arith.
    * rewrite H0 in H1.
      contradict H1.
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
- destruct (countable_product (T -> Y) Y); trivial.
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
- destruct H1, IHFiniteT.
  exists (fun h => f0 (fun x => h (f x))).
  intros h1 h2 ?.
  apply H3 in H4.
  pose proof (equal_f H4).
  simpl in H5.
  extensionality y.
  rewrite <- (H2 y).
  apply H5.
Qed.

Definition Countable {X : Type} (S : Ensemble X) : Prop :=
  CountableT {x:X | In S x}.

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
now destruct H1, (proof_irrelevance _ i i0).
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
now destruct e, (proof_irrelevance _ i0 i1).
Qed.

Lemma countable_type_ensemble  {X : Type} (S : Ensemble X) :
  CountableT X -> Countable S.
Proof.
intros.
apply (inj_countable (@proj1_sig _ (In S)) H).
intros [? ?] [? ?].
now apply subset_eq_compat.
Qed.

Lemma FiniteT_impl_CountableT (X : Type) :
  FiniteT X -> CountableT X.
Proof.
intros.
induction H.
- exists (False_rect nat).
  now intro.
- destruct IHFiniteT.
  exists (fun x => match x with
    | Some x0 => S (f x0)
    | None => 0
  end).
  intros [x1|] [x2|] H1;
    injection H1 as H1 + discriminate H1 + trivial.
  now destruct (H0 _ _ H1).
- destruct IHFiniteT as [g],
           H0 as [finv].
  exists (fun y:Y => g (finv y)).
  intros y1 y2 ?.
  apply H1 in H3.
  congruence.
Qed.

Lemma Finite_impl_Countable: forall {X : Type} (S : Ensemble X),
  Finite _ S -> Countable S.
Proof.
intros.
now apply FiniteT_impl_CountableT, Finite_ens_type.
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

Lemma countable_union: forall {X A:Type}
  (F:IndexedFamily A X), CountableT A ->
    (forall a:A, Countable (F a)) ->
    Countable (IndexedUnion F).
Proof.
intros.
destruct (choice_on_dependent_type (fun (a:A)
                               (f:{x:X | In (F a) x} -> nat) =>
  injective f)) as [choice_fun_inj].
- intro.
  destruct (H0 a).
  now exists f.
- destruct (choice (fun (x:{x:X | In (IndexedUnion F) x}) (a:A) =>
    In (F a) (proj1_sig x))) as [choice_fun_a].
  + destruct x as [x [a]].
    now exists a.
  + destruct countable_nat_product as [g],
             H as [h].
    exists (fun x:{x:X | In (IndexedUnion F) x} =>
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

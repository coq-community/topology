From Coq Require Import
  Classical
  Description
  RelationClasses.
From ZornsLemma Require Import
  Cardinals.Cardinals
  Cardinals.CardinalsEns
  DecidableDec
  FunctionProperties
  FunctionPropertiesEns
  Proj1SigInjective.

(* CSB = Cantor-Schroeder-Bernstein theorem *)

Section CSB.
Variable X Y:Type.
Variable f:X->Y.
Variable g:Y->X.
Hypothesis f_inj: injective f.
Hypothesis g_inj: injective g.

Inductive X_even: X->Prop :=
  | not_g_img: forall x:X, (forall y:Y, g y <> x) -> X_even x
  | g_Y_odd: forall y:Y, Y_odd y -> X_even (g y)
with Y_odd: Y->Prop :=
  | f_X_even: forall x:X, X_even x -> Y_odd (f x).
Inductive X_odd: X->Prop :=
  | g_Y_even: forall y:Y, Y_even y -> X_odd (g y)
with Y_even: Y->Prop :=
  | not_f_img: forall y:Y, (forall x:X, f x <> y) -> Y_even y
  | f_X_odd: forall x:X, X_odd x -> Y_even (f x).

Scheme X_even_coind := Minimality for X_even Sort Prop
  with Y_odd_coind := Minimality for Y_odd Sort Prop.
Scheme X_odd_coind := Minimality for X_odd Sort Prop
  with Y_even_coind := Minimality for Y_even Sort Prop.

Lemma even_odd_excl: forall x:X, ~(X_even x /\ X_odd x).
Proof.
intro.
assert (X_even x -> ~ X_odd x).
2:tauto.
pose proof (X_even_coind (fun x:X => ~ X_odd x) (fun y:Y => ~ Y_even y)).
apply H.
- intuition.
  destruct H1.
  apply H0 with y.
  reflexivity.
- intuition.
  inversion H2.
  apply g_inj in H3.
  apply H1.
  rewrite <- H3.
  assumption.
- intuition.
  inversion H2.
  + apply H3 with x0.
    reflexivity.
  + apply f_inj in H3.
    apply H1.
    rewrite <- H3.
    assumption.
Qed.

Lemma even_odd_excl2: forall y:Y, ~(Y_even y /\ Y_odd y).
Proof.
intro.
assert (Y_odd y -> ~ Y_even y).
2:tauto.
pose proof (Y_odd_coind (fun x:X => ~ X_odd x) (fun y:Y => ~ Y_even y)).
apply H; intuition.
- destruct H1.
  apply H0 with y0.
  reflexivity.
- inversion H2.
  apply g_inj in H3.
  apply H1.
  rewrite <- H3.
  assumption.
- inversion H2.
  + apply H3 with x.
    reflexivity.
  + apply f_inj in H3.
    apply H1.
    rewrite <- H3.
    assumption.
Qed.

Definition finv: forall y:Y, (exists x:X, f x = y) ->
  { x:X | f x = y }.
intros.
apply constructive_definite_description.
destruct H.
exists x.
red; split.
{ assumption. }
intros.
apply f_inj.
transitivity y; trivial.
symmetry; trivial.
Defined.

Definition ginv: forall x:X, (exists y:Y, g y = x) ->
  { y:Y | g y = x }.
intros.
apply constructive_definite_description.
destruct H.
exists x0.
red; split.
{ assumption. }
intros.
apply g_inj.
transitivity x; trivial; symmetry; trivial.
Defined.

Definition ginv_odd: forall x:X, X_odd x ->
  { y:Y | g y = x }.
intros.
apply ginv.
destruct H.
exists y.
reflexivity.
Defined.

Definition finv_noteven: forall y:Y, ~ Y_even y ->
  { x:X | f x = y }.
intros.
apply finv.
apply NNPP.
red; intro.
contradict H.
constructor 1.
intro; red; intro.
apply H0.
exists x.
assumption.
Defined.

Definition CSB_bijection (x:X) : Y :=
  match (classic_dec (X_odd x)) with
  | left o => proj1_sig (ginv_odd x o)
  | right _ => f x
  end.
Definition CSB_bijection2 (y:Y) : X :=
  match (classic_dec (Y_even y)) with
  | left _ => g y
  | right ne => proj1_sig (finv_noteven y ne)
  end.

Lemma CSB_comp1: forall x:X, CSB_bijection2 (CSB_bijection x) = x.
Proof.
intro.
unfold CSB_bijection; case (classic_dec (X_odd x)).
- intro.
  destruct ginv_odd.
  simpl.
  unfold CSB_bijection2;
    case (classic_dec (Y_even x1));
    auto.
  intro.
  destruct x0.
  contradict n.
  apply g_inj in e.
  rewrite e.
  assumption.
- intro.
  unfold CSB_bijection2; case (classic_dec (Y_even (f x))).
  + intro.
    contradict n.
    inversion y.
    * pose proof (H x).
      contradict H1; reflexivity.
    * apply f_inj in H.
      rewrite <- H.
      assumption.
  + intro.
    destruct finv_noteven.
    simpl.
    apply f_inj.
    assumption.
Qed.

Lemma CSB_comp2: forall y:Y, CSB_bijection (CSB_bijection2 y) = y.
Proof.
intro.
unfold CSB_bijection2; case (classic_dec (Y_even y)).
- intro.
  unfold CSB_bijection; case (classic_dec (X_odd (g y))).
  + intro.
    destruct ginv_odd.
    simpl.
    apply g_inj.
    assumption.
  + intro.
    contradict n.
    constructor.
    assumption.
- intro.
  destruct finv_noteven.
  simpl.
  unfold CSB_bijection; case (classic_dec (X_odd x)).
  + intro.
    contradict n.
    rewrite <- e.
    constructor 2.
    assumption.
  + trivial.
Qed.

Theorem CSB_inverse_map :
  exists (h0 : X -> Y) (h1 : Y -> X),
    inverse_map h0 h1.
Proof.
  exists CSB_bijection, CSB_bijection2.
  split.
  - exact CSB_comp1.
  - exact CSB_comp2.
Qed.

Theorem CSB: eq_cardinal X Y.
Proof.
exists CSB_bijection.
exists CSB_bijection2. split.
- exact CSB_comp1.
- exact CSB_comp2.
Qed.

End CSB.

#[export]
Instance le_cardinal_PartialOrder :
  PartialOrder eq_cardinal le_cardinal.
Proof.
split.
- intros [f Hf]; split.
  + exists f. apply invertible_impl_bijective; assumption.
  + destruct Hf as [g Hfg].
    exists g. apply invertible_impl_bijective.
    exists f. apply inverse_map_sym.
    assumption.
- intros [[f Hf] [g Hg]].
  apply CSB_inverse_map with (f := f) (g := g); auto.
Qed.

Theorem CSB_ens {X Y : Type}
  (U : Ensemble X) (V : Ensemble Y)
  (f : X -> Y) (g : Y -> X) :
  range f U V ->
  range g V U ->
  injective_ens f U ->
  injective_ens g V ->
  exists h : X -> Y,
    range h U V /\
      bijective_ens h U V.
Proof.
  intros.
  assert (exists h0 : sig U -> sig V, invertible h0)
    as [h0 Hh].
  { apply CSB with (f := range_restr f U V H)
                   (g := range_restr g V U H0);
      apply injective_ens_char; assumption.
  }
  destruct (classic (inhabited Y)).
  2: {
    assert (X -> False) as HX.
    { intros x.
      apply H3. constructor.
      apply (f x).
    }
    exists (fun x => False_rect Y (HX x)).
    repeat split; intros ? ?; try contradiction.
    contradict H3; constructor; auto.
  }
  clear f g H H0 H1 H2.
  destruct H3 as [y0].
  exists (sig_fn_extend (compose (@proj1_sig Y V) h0) y0).
  assert (range (compose (proj1_sig (P:=V)) h0)
                Full_set V).
  { apply (range_compose _ Full_set).
    - apply range_full.
    - intros ? _. apply proj2_sig.
  }
  split; [|split].
  - apply sig_fn_extend_range; assumption.
  - apply sig_fn_extend_injective_ens.
    apply injective_compose.
    + apply invertible_impl_bijective, Hh.
    + intros ? ?. apply proj1_sig_injective.
  - apply sig_fn_extend_surjective_ens.
    intros y Hy.
    destruct Hh as [h' [Hh0 Hh1]].
    exists (h' (exist V y Hy)).
    split; [constructor|].
    unfold compose.
    rewrite Hh1.
    reflexivity.
Qed.

Corollary le_cardinal_ens_antisymmetry
  {X Y : Type} (U : Ensemble X) (V : Ensemble Y) :
  le_cardinal_ens U V ->
  le_cardinal_ens V U ->
  eq_cardinal_ens U V.
Proof.
  intros [H|[f [Hf0 Hf1]]].
  { left. assumption. }
  intros [H|[g [Hg0 Hg1]]].
  { apply eq_cardinal_ens_sym.
    left. assumption.
  }
  right.
  apply (CSB_ens _ _ f g); assumption.
Qed.

Lemma le_lt_cardinal_ens_transitive {X Y Z : Type}
  (U : Ensemble X) (V : Ensemble Y) (W : Ensemble Z) :
  le_cardinal_ens U V ->
  lt_cardinal_ens V W ->
  lt_cardinal_ens U W.
Proof.
  intros HUV [HVW HVWn].
  split.
  { eapply le_cardinal_ens_transitive; eauto. }
  intros Heq.
  contradict HVWn.
  apply eq_cardinal_ens_sym in Heq.
  apply le_cardinal_ens_antisymmetry; auto.
  eapply le_cardinal_ens_Proper_l; eauto.
Qed.

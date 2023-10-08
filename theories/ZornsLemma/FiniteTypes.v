From Coq Require Import
  Arith
  ClassicalChoice
  Description
  FunctionalExtensionality
  Lia
  Program.Subset.
From ZornsLemma Require Import
  Cardinals
  DecidableDec
  FiniteImplicit
  Finite_sets
  FunctionProperties
  FunctionPropertiesEns
  Image
  IndexedFamilies
  InverseImage
  Powerset_facts.
(* load ProofIrrelevance last, so [proof_irrelevance] is not provided
  by [classic]. Similarly [RelationClasses] must provide [Equivalence] *)
From Coq Require Import
  ProofIrrelevance
  RelationClasses.

Set Asymmetric Patterns.

Inductive FiniteT : Type -> Prop :=
  | empty_finite: FiniteT False
  | add_finite: forall T:Type, FiniteT T -> FiniteT (option T)
  | bij_finite: forall (X Y:Type),
      FiniteT X -> eq_cardinal X Y -> FiniteT Y.

Lemma finite_dec_exists: forall (X:Type) (P:X->Prop),
  FiniteT X -> (forall x:X, P x \/ ~ P x) ->
  (exists x:X, P x) \/ (forall x:X, ~ P x).
Proof.
intros.
revert P H0.
induction H.
- right.
  destruct x.
- intros.
  case (IHFiniteT (fun x:T => P (Some x))
                  (fun x:T => H0 (Some x))).
  + left.
    destruct H1 as [x].
    exists (Some x).
    assumption.
  + intro.
    specialize (H0 None) as [|].
    * left.
      exists None.
      assumption.
    * right.
      destruct x.
      -- apply H1.
      -- assumption.
- destruct H0 as [f [g []]].
  intros.
  specialize  (IHFiniteT (fun x:X => P (f x))
                         (fun x:X => H2 (f x))) as [|].
  * left.
    destruct H3 as [x].
    exists (f x).
    assumption.
  * right.
    intro.
    rewrite <- H1 with x.
    apply H3.
Qed.

Lemma finite_dec_forall: forall (X:Type) (P:X->Prop),
  FiniteT X -> (forall x:X, P x \/ ~ P x) ->
  (forall x:X, P x) \/ (exists x:X, ~ P x).
Proof.
intros.
revert P H0.
induction H.
- left.
  destruct x.
- intros.
  case (IHFiniteT (fun x:T => P (Some x))
                  (fun x:T => H0 (Some x))).
  + intro.
    case (H0 None).
    * left. destruct x; auto.
    * right.
      exists None.
      assumption.
  + right.
    destruct H1 as [x].
    exists (Some x).
    assumption.
- intros.
  destruct H0 as [f [g []]].
  case (IHFiniteT (fun x:X => P (f x))
                  (fun x:X => H1 (f x))).
  + left.
    intro y.
    rewrite <- H2.
    apply H3.
  + right.
    destruct H3 as [x].
    exists (f x).
    assumption.
Qed.

Lemma finite_eq_dec: forall X:Type, FiniteT X ->
  forall x y:X, x = y \/ x <> y.
Proof.
intros.
induction H.
{ destruct x. }
{ destruct x, y.
  4: left; reflexivity.
  2, 3: right; congruence.
  specialize (IHFiniteT t t0) as [|];
    [left|right]; congruence.
}
destruct H0 as [f [g []]].
specialize (IHFiniteT (g x) (g y)) as [|].
- left.
  rewrite <- H1.
  rewrite <- H1 with x.
  rewrite H2.
  reflexivity.
- right.
  contradict H2.
  rewrite H2.
  reflexivity.
Qed.

Lemma finite_dep_choice: forall (A:Type) (B:forall x:A, Type)
  (R:forall x:A, B x->Prop),
  FiniteT A -> (forall x:A, exists y:B x, R x y) ->
  exists f:(forall x:A, B x), forall x:A, R x (f x).
Proof.
intros.
revert B R H0.
induction H.
- intros.
  exists (fun x:False => False_rect (B x) x).
  destruct x.
- intros.
  pose proof (IHFiniteT (fun x:T => B (Some x))
                        (fun x:T => R (Some x))
                        (fun x:T => H0 (Some x))).
  destruct H1.
  pose proof (H0 None).
  destruct H2.
  exists (fun y:option T =>
            match y return (B y) with
            | Some y0 => x y0
            | None => x0
            end).
  destruct x1; auto.
- intros.
  destruct H0 as [f [g []]].
  pose proof (IHFiniteT (fun x:X => B (f x))
                        (fun x:X => R (f x))
                        (fun x:X => H1 (f x))).
  destruct H3.
  unshelve eexists.
  + intros. rewrite <- H2. apply x.
  + intros. simpl. rewrite <- (H2 x0). simpl.
    apply H3.
Qed.

Lemma finite_choice : forall (A B:Type) (R:A->B->Prop),
  FiniteT A -> (forall x:A, exists y:B, R x y) ->
  exists f:A->B, forall x:A, R x (f x).
Proof.
intros. apply finite_dep_choice; assumption.
Qed.

Lemma eq_cardinal_False_sig_Empty_set (X : Type) :
  eq_cardinal False { x : X | In Empty_set x }.
Proof.
  exists (False_rect _),
    (fun p : {x : X | In Empty_set x} =>
       Empty_set_rect X (fun _ => False)
         (proj1_sig p) (proj2_sig p)).
  split.
  - intros; contradiction.
  - intros [].
    destruct i.
Qed.

Lemma eq_cardinal_option_False_True :
  eq_cardinal (option False) True.
Proof.
  exists (fun _ => I), (fun _ => None).
  split.
  - intros []; auto; contradiction.
  - intros []; auto.
Qed.

Lemma True_finite: FiniteT True.
Proof.
apply bij_finite with (option False).
{ do 2 constructor. }
apply eq_cardinal_option_False_True.
Qed.

Lemma eq_cardinal_sum_False (X : Type) :
  eq_cardinal X (X + False).
Proof.
  exists inl, (fun (x : X + False) =>
            match x with
            | inl x => x
            | inr f => False_rect X f
            end).
  split.
  - reflexivity.
  - intros []; try contradiction; reflexivity.
Qed.

Lemma eq_cardinal_sum_option_r (X Y : Type) :
  eq_cardinal (option (X + Y)) (X + option Y).
Proof.
  exists (fun (x:option (X+Y)) =>
       match x with
       | Some (inl x) => inl _ x
       | Some (inr y) => inr _ (Some y)
       | None => inr _ None
       end).
  exists (fun (x:X + option Y) =>
       match x with
       | inl x => Some (inl _ x)
       | inr (Some y) => Some (inr _ y)
       | inr None => None
       end).
  split.
  - intros [[]|]; reflexivity.
  - intros [|[]]; reflexivity.
Qed.

Lemma eq_cardinal_sum_r (X Y0 Y1 : Type) :
  eq_cardinal Y0 Y1 ->
  eq_cardinal (X + Y0) (X + Y1).
Proof.
  intros [f [g Hfg]].
  exists (fun (s : X + Y0) =>
       match s with
       | inl x => inl x
       | inr y => inr (f y)
       end).
  exists (fun (s : X + Y1) =>
       match s with
       | inl x => inl x
       | inr y => inr (g y)
       end).
  split; intros [x|y]; auto; f_equal; apply Hfg.
Qed.

Lemma finite_sum: forall X Y:Type, FiniteT X -> FiniteT Y ->
  FiniteT (X+Y).
Proof.
intros.
induction H0.
- apply bij_finite with X; auto.
  apply eq_cardinal_sum_False.
- apply bij_finite with (option (X + T)).
  { constructor; auto. }
  apply eq_cardinal_sum_option_r.
- apply bij_finite with (X + X0)%type; auto.
  apply eq_cardinal_sum_r.
  assumption.
Qed.

Lemma eq_cardinal_sig_disjoint_Union_sum {X : Type}
  (U V : Ensemble X) :
  Intersection U V = Empty_set ->
  eq_cardinal
    ((sig U) + (sig V))
    (sig (Union U V)).
Proof.
  intros HUV.
  assert (forall x : X, In U x -> In V x -> False) as HUVdisj.
  { intros x HUx HVx.
    eapply Empty_set_rect.
    rewrite <- HUV. split; eassumption.
  }
  clear HUV.
  assert (forall x : X, In (Union U V) x -> {In U x} + {In V x})
    as Hdec.
  { intros x Hx.
    apply exclusive_dec.
    2: { destruct Hx; auto. }
    intros [HUx HVx].
    firstorder.
  }
  exists (fun p : sig U + sig V =>
       match p with
       | inl pU => exist _ (proj1_sig pU)
                    (Union_introl X U V (proj1_sig pU) (proj2_sig pU))
       | inr pV => exist _ (proj1_sig pV)
                    (Union_intror X U V (proj1_sig pV) (proj2_sig pV))
       end).
  exists (fun p =>
       match Hdec (proj1_sig p) (proj2_sig p) with
       | left HU => inl (exist _ (proj1_sig p) HU)
       | right HV => inr (exist _ (proj1_sig p) HV)
       end).
  split.
  - intros [[x Hx]|[x Hx]].
    + simpl. destruct (Hdec x _).
      * f_equal. f_equal. apply proof_irrelevance.
      * specialize (HUVdisj x Hx i). contradiction.
    + simpl. destruct (Hdec x _).
      * specialize (HUVdisj x i Hx). contradiction.
      * f_equal. f_equal. apply proof_irrelevance.
  - intros [x Hx]. simpl.
    destruct (Hdec x Hx);
      simpl; f_equal; apply proof_irrelevance.
Qed.

(* interestingly, this does not require [proof_irrelevance]. *)
Lemma eq_cardinal_sig_Singleton {X : Type} (x0 : X) :
  eq_cardinal (option False) { x : X | In (Singleton x0) x }.
Proof.
  exists (fun _ => exist _ x0 (In_singleton X x0)), (fun _ => None).
  split.
  - intros []; auto. contradiction.
  - intros [x Hx].
    destruct Hx. reflexivity.
Qed.

Lemma FiniteT_sig_Singleton {X : Type} (x0 : X) :
  FiniteT { x : X | In (Singleton x0) x }.
Proof.
  apply bij_finite with (option False).
  { do 2 constructor. }
  apply eq_cardinal_sig_Singleton.
Qed.

Lemma Finite_ens_type: forall {X:Type} (S:Ensemble X),
  Finite S -> FiniteT { x:X | In S x }.
Proof.
intros.
induction H.
- apply bij_finite with False; [now constructor|].
  apply eq_cardinal_False_sig_Empty_set.
- eapply bij_finite with (sig A + sig (Singleton x))%type.
  + apply finite_sum; auto.
    apply FiniteT_sig_Singleton.
  + eapply eq_cardinal_sig_disjoint_Union_sum.
    apply Extensionality_Ensembles; split.
    2: intros ? ?; contradiction.
    intros y []. destruct H2. contradiction.
Qed.

Lemma FiniteT_img: forall (X Y:Type) (f:X->Y),
  FiniteT X -> (forall y1 y2:Y, y1=y2 \/ y1<>y2) ->
  Finite (Im Full_set f).
Proof.
intros X Y f HX HY.
induction HX.
- replace (Im Full_set f) with (@Empty_set Y).
  { constructor. }
  apply Extensionality_Ensembles; split; red; intros.
  + destruct H.
  + destruct H. destruct x.
- assert ((exists x:T, f (Some x) = f None) \/
           (forall x:T, f (Some x) <> f None)) as [H|H].
  { apply finite_dec_exists.
    { assumption. }
    intro.
    apply HY.
  }
  all: clear HY.
  + pose (g := fun (x:T) => f (Some x)).
    replace (Im Full_set f) with (Im Full_set g).
    { apply IHHX. }
    apply Extensionality_Ensembles; split; red; intros.
    * destruct H0. subst. exists (Some x).
      -- constructor.
      -- reflexivity.
    * destruct H0. subst. destruct x.
      -- exists t.
         ++ constructor.
         ++ reflexivity.
      -- destruct H as [x]; exists x.
         ++ constructor.
         ++ symmetry. assumption.
  + pose (g := fun x:T => f (Some x)).
    replace (Im Full_set f) with (Add (Im Full_set g) (f None)).
    { constructor.
      - apply IHHX.
      - red; intro. destruct H0.
        contradiction (H x).
        symmetry; assumption.
    }
    apply Extensionality_Ensembles; split; red; intros.
    * red; intros.
      destruct H0, H0.
      -- exists (Some x).
         ++ constructor.
         ++ assumption.
      -- exists None.
         ++ constructor.
         ++ reflexivity.
    * red; intros.
      destruct H0.
      destruct x.
      -- left. exists t.
         ++ constructor.
         ++ assumption.
      -- right. auto with sets.
- destruct H as [f0 Hf0].
  pose (g := fun (x:X) => f (f0 x)).
  replace (Im Full_set f) with (Im Full_set g).
  { apply IHHX. }
  unfold g.
  rewrite (Im_compose f0 f).
  rewrite <- (proj1 (Im_Full_set_surj f0)); auto.
  apply invertible_impl_bijective.
  assumption.
Qed.

Lemma eq_cardinal_sig_Full_set (X : Type) :
  eq_cardinal { x : X | In Full_set x } X.
Proof.
  exists (@proj1_sig _ Full_set),
    (fun x => exist Full_set x (Full_intro X x)).
  split.
  - intros [x Hx]. simpl.
    destruct Hx. reflexivity.
  - reflexivity.
Qed.

Lemma Finite_full_impl_FiniteT (X : Type) :
  Finite (@Full_set X) -> FiniteT X.
Proof.
  intros HX.
  apply bij_finite with (sig (@Full_set X)).
  - apply Finite_ens_type. assumption.
  - apply eq_cardinal_sig_Full_set.
Qed.

Lemma surj_finite: forall (X Y:Type) (f:X->Y),
  FiniteT X -> surjective f ->
  (forall y1 y2:Y, y1=y2 \/ y1<>y2) ->
  FiniteT Y.
Proof.
intros.
apply bij_finite with {y:Y | In Full_set y}.
2: apply eq_cardinal_sig_Full_set.
rewrite (proj1 (Im_Full_set_surj f)); auto.
apply Finite_ens_type.
apply FiniteT_img; auto.
Qed.

Lemma eq_cardinal_empty_type (X : Type) :
  (X -> False) ->
  eq_cardinal False X.
Proof.
  intros f.
  exists (False_rect X), f.
  split.
  - intros [].
  - intros x; destruct (f x).
Qed.

Lemma eq_cardinal_sig_option_In {X : Type} (U : Ensemble (option X)) :
  In U None ->
  eq_cardinal (option (sig (fun x : X => U (Some x)))) (sig U).
Proof.
  intros HN.
  exists (fun (x:option {x:X | U (Some x)}) =>
       match x return {x:option X | U x} with
       | Some (exist x0 i) => exist U (Some x0) i
       | None => exist U None HN
       end).
  exists (fun (s:{x0:option X | U x0}) =>
       match s return option {x:X | U (Some x)} with
       | exist (Some x0) i => Some (exist (fun y:X => U (Some y)) x0 i)
       | exist None _ => None
       end).
  split.
  - intros [[x Hx]|]; auto.
  - intros [[x|] Hx]; auto.
    f_equal. apply proof_irrelevance.
Qed.

Lemma eq_cardinal_sig_option_nIn {X : Type} (U : Ensemble (option X)) :
  ~ In U None ->
  eq_cardinal (sig (compose U Some)) (sig U).
Proof.
  intros HN.
  exists (fun (x:{x:X | U (Some x)}) =>
       match x return {x:option X | U x} with
       | exist x0 i => exist (fun x:option X => U x) (Some x0) i
       end).
  exists (fun s:{x0:option X | U x0} =>
       match s return {x:X | U (Some x)} with
       | exist (Some x0) i => exist (fun x:X => U (Some x)) x0 i
       | exist None i => False_rect _ (HN i)
       end).
  split.
  - intros [x Hx]. reflexivity.
  - intros [[x|] Hx]; auto.
    contradiction.
Qed.

(** actually [compose U f = inverse_image f U] *)
Lemma eq_cardinal_sig_comp_invertible
  {X Y : Type} (f : X -> Y) (U : Ensemble Y) :
  invertible f ->
  eq_cardinal (sig (compose U f)) (sig U).
Proof.
  intros [g Hfg].
  unfold compose.
  assert (forall y : Y, U y -> U (f (g y))) as HU.
  { intros y Hy. rewrite (proj2 Hfg). assumption. }
  exists (fun p => exist U (f (proj1_sig p)) (proj2_sig p)).
  exists (fun p => exist
             (compose U f)
             (g (proj1_sig p)) (HU (proj1_sig p) (proj2_sig p))).
  split.
  - intros [x Hx].
    simpl. apply subset_eq_compat.
    apply Hfg.
  - intros [y Hy].
    simpl. apply subset_eq_compat.
    apply Hfg.
Qed.

Lemma finite_subtype: forall (X:Type) (P:X->Prop),
  FiniteT X -> (forall x:X, P x \/ ~ P x) ->
  FiniteT {x:X | P x}.
Proof.
intros X P H HP.
induction H.
- apply bij_finite with False.
  { constructor. }
  apply eq_cardinal_empty_type.
  apply proj1_sig.
- destruct (HP None).
  + eapply bij_finite.
    2: apply eq_cardinal_sig_option_In; auto.
    constructor.
    apply IHFiniteT.
    intros x. apply HP.
  + eapply bij_finite.
    2: apply eq_cardinal_sig_option_nIn; auto.
    apply IHFiniteT.
    unfold compose.
    intros x. apply HP.
- destruct H0 as [f Hf].
  apply bij_finite with (sig (compose P f)).
  2: apply eq_cardinal_sig_comp_invertible; auto.
  apply IHFiniteT.
  unfold compose.
  intros x. apply HP.
Qed.

Lemma eq_cardinal_sig_injective_image
  {X Y : Type} (f : X -> Y) (U : Ensemble X) :
  injective f ->
  eq_cardinal (sig (Im U f)) (sig U).
Proof.
  intros Hf.
  assert (forall p : { y : Y | Im U f y },
             { x : X | In U x /\ f x = proj1_sig p }) as finv.
  { intros [y Hy]. simpl.
    apply constructive_definite_description.
    destruct Hy as [x Hx y Hy].
    subst. exists x. split; auto.
    intros x0 []; auto.
  }
  exists (fun p =>
       exist
         U
         (proj1_sig (finv p))
         (proj1 (proj2_sig (finv p)))).
  exists (fun p =>
       exist (Im U f)
         (f (proj1_sig p))
         (Im_def U f (proj1_sig p) (proj2_sig p))).
  split.
  - intros [y Hy].
    simpl.
    destruct (finv (exist _ y Hy)).
    simpl.
    destruct a. simpl in *. subst.
    f_equal. apply proof_irrelevance.
  - intros [x Hx].
    simpl.
    apply subset_eq_compat.
    apply Hf.
    apply (proj2 (proj2_sig (finv (exist _ (f x) (Im_def U f x Hx))))).
Qed.

Lemma inj_finite: forall (X Y:Type) (f:X->Y),
  FiniteT Y -> injective f ->
  (forall y:Y, (exists x:X, f x = y) \/
               (~ exists x:X, f x = y)) ->
  FiniteT X.
Proof.
intros.
apply bij_finite with { y : Y | Im Full_set f y }.
{ apply finite_subtype; auto.
  intros y.
  specialize (H1 y) as [[x Hx]|Hy]; [left|right].
  - subst. apply Im_def; constructor.
  - intros Hy0.
    destruct Hy0 as [x Hx y Hy0].
    subst. contradict Hy; exists x; reflexivity.
}
clear H1.
transitivity (sig (@Full_set X)).
- apply eq_cardinal_sig_injective_image; auto.
- apply eq_cardinal_sig_Full_set.
Qed.

Lemma finite_inj_surj: forall (X:Type) (f:X->X),
  FiniteT X -> injective f -> surjective f.
Proof.
intros.
induction H.
- red. destruct y.
- remember (f None) as f0; destruct f0 as [a|].
  + assert (forall x:T, f (Some x) <> Some a).
    { unfold not; intros.
      rewrite Heqf0 in H1.
      apply H0 in H1.
      discriminate H1.
    }
    pose (g := fun x:T => match f (Some x) with
      | Some y => y
      | None => a
    end).
    assert (surjective g).
    { apply IHFiniteT.
      red; intros.
      remember (f (Some x)) as fx; destruct fx;
      remember (f (Some y)) as fy; destruct fy.
      - unfold g in H2.
        rewrite <- Heqfx in H2; rewrite <- Heqfy in H2.
        destruct H2; assert (f (Some x) = f (Some y)).
        + congruence.
        + apply H0 in H2.
          injection H2; trivial.
      - unfold g in H2;
          rewrite <- Heqfx in H2;
          rewrite <- Heqfy in H2.
        destruct H2.
        contradiction (H1 x).
        symmetry; assumption.
      - unfold g in H2;
          rewrite <- Heqfx in H2;
          rewrite <- Heqfy in H2.
        destruct H2.
        contradiction (H1 y).
        symmetry; assumption.
      - rewrite Heqfx in Heqfy.
        apply H0 in Heqfy.
        injection Heqfy. trivial.
    }
    red; intro.
    destruct y.
    * case (finite_eq_dec _ H t a).
      -- exists None.
         congruence.
      -- destruct (H2 t).
         exists (Some x).
         unfold g in H3.
         destruct (f (Some x));
           congruence.
    * destruct (H2 a).
      exists (Some x).
      unfold g in H3.
      remember (f (Some x)) as fx; destruct fx.
      -- subst. rewrite Heqf0 in Heqfx.
         apply H0 in Heqfx. discriminate Heqfx.
      -- reflexivity.
  + assert (forall x:T, { y:T | f (Some x) = Some y }).
    { intros.
      remember (f (Some x)) as fx; destruct fx.
      - exists t; reflexivity.
      - rewrite Heqf0 in Heqfx.
        apply H0 in Heqfx.
        discriminate Heqfx.
    }
    pose (g := fun x:T => proj1_sig (X x)).
    assert (surjective g).
    { apply IHFiniteT.
      red; intros.
      unfold g in H1.
      repeat destruct X in H1.
      simpl in H1.
      subst.
      rewrite <- e in e0.
      apply H0 in e0.
      symmetry. injection e0; trivial.
    }
    red; intro.
    destruct y.
    * destruct (H1 t).
      unfold g in H2; destruct X in H2.
      simpl in H2.
      exists (Some x).
      congruence.
    * exists None.
      symmetry; assumption.
- destruct H1 as [g [h Hgh]].
  pose (f' := fun (x:X) => h (f (g x))).
  assert (surjective f') as Hf'.
  { apply IHFiniteT.
    apply injective_compose.
    2: apply invertible_impl_bijective; exists g;
      apply inverse_map_sym;
      assumption.
    apply injective_compose; auto.
    apply invertible_impl_bijective; exists h; auto.
  }
  red; intro.
  specialize (Hf' (h y)) as [x Hx].
  unfold f' in Hx.
  exists (g x).
  apply inverse_map_sym in Hgh.
  unshelve eapply (proj1 (invertible_impl_bijective h _)); auto.
  exists g; assumption.
Qed.

Lemma finite_surj_inj: forall (X:Type) (f:X->X),
  FiniteT X -> surjective f -> injective f.
Proof.
intros.
assert (exists g:X->X, forall x:X, f (g x) = x).
{ apply finite_choice with (R:=fun (x y:X) => f y = x);
    assumption.
}
destruct H1 as [g].
assert (surjective g).
{ apply finite_inj_surj.
  { assumption. }
  eapply injective_compose_conv.
  unfold compose.
  intros ? ? ?. rewrite !H1 in H2; assumption.
}
red; intros.
destruct (H2 x).
destruct (H2 y).
subst.
rewrite ?H1 in H3.
subst.
reflexivity.
Qed.

Lemma eq_cardinal_prod_False (X : Type) :
  eq_cardinal False (X * False)%type.
Proof.
  exists (False_rect _), snd.
  split.
  - intros ?; contradiction.
  - intros []; contradiction.
Qed.

Lemma eq_cardinal_prod_option_r (X Y : Type) :
  eq_cardinal (X * Y + X) (X * option Y).
Proof.
  exists (fun (x:X*Y + X) =>
       match x with
       | inl (pair x0 t) => pair x0 (Some t)
       | inr x0 => pair x0 None
       end).
  exists (fun (x:X * option Y) =>
       match x with
       | (x0, Some t) => inl _ (x0, t)
       | (x0, None) => inr _ x0
       end).
  split.
  - intros [[x y]|x]; reflexivity.
  - intros [x [y|]]; reflexivity.
Qed.

Lemma eq_cardinal_prod_r (X Y0 Y1 : Type) :
  eq_cardinal Y0 Y1 ->
  eq_cardinal (X * Y0) (X * Y1).
Proof.
  intros [f [g [Hgf Hfg]]].
  exists (fun p =>
       (fst p, f (snd p))),
    (fun p =>
       (fst p, g (snd p))).
  split.
  - intros [x y]. simpl.
    congruence.
  - intros [x y]. simpl.
    congruence.
Qed.

Lemma finite_prod: forall (X Y:Type), FiniteT X -> FiniteT Y ->
  FiniteT (X*Y).
Proof.
intros.
induction H0.
- apply bij_finite with False.
  { constructor. }
  apply eq_cardinal_prod_False.
- apply bij_finite with (X * T + X)%type.
  2: apply eq_cardinal_prod_option_r.
  apply finite_sum; assumption.
- apply bij_finite with (X * X0)%type; auto.
  apply eq_cardinal_prod_r; assumption.
Qed.

Lemma eq_cardinal_fun_from_False (X : Type) :
  eq_cardinal (option False) (False -> X).
Proof.
  exists (fun _ => False_rect X), (fun _ => None).
  split.
  - intros []; auto; contradiction.
  - intros f; extensionality x; contradiction.
Qed.

Lemma eq_cardinal_fun_option_l (X Y : Type) :
  eq_cardinal ((X -> Y) * Y) (option X -> Y).
Proof.
  exists (fun p o =>
       match o with
       | None => snd p
       | Some x => fst p x
       end).
  exists (fun f => (compose f Some, f None)).
  split.
  - intros [f y]. simpl.
    split.
  - intros f.
    extensionality o.
    destruct o as [x|]; reflexivity.
Qed.

Lemma eq_cardinal_fun_l (X0 X1 Y : Type) :
  eq_cardinal X0 X1 ->
  eq_cardinal (X0 -> Y) (X1 -> Y).
Proof.
  intros [f [g Hfg]].
  exists (fun p : X0 -> Y => compose p g).
  exists (fun p : X1 -> Y => compose p f).
  split; intros p; extensionality x;
    unfold compose; f_equal; apply Hfg.
Qed.

Lemma finite_exp: forall X Y:Type, FiniteT X -> FiniteT Y ->
  FiniteT (X->Y).
Proof.
intros.
induction H.
- apply bij_finite with (option False).
  { do 2 constructor. }
  apply eq_cardinal_fun_from_False.
- apply bij_finite with ((T -> Y) * Y)%type.
  2: apply eq_cardinal_fun_option_l.
  apply finite_prod; assumption.
- apply bij_finite with (X -> Y)%type; auto.
  apply eq_cardinal_fun_l; assumption.
Qed.

Lemma injection_preserves_cardinal: forall (X Y:Type)
  (f:X->Y) (n:nat) (S:Ensemble X), cardinal S n ->
  injective f -> cardinal (Im S f) n.
Proof.
intros.
induction H.
- rewrite image_empty.
  constructor.
- rewrite Im_add.
  constructor; trivial.
  red; intro H3; inversion H3.
  subst. apply H0 in H4. subst.
  contradiction.
Qed.

Lemma FiniteT_dec_Ensemble_has_cardinal
  {X : Type} (U : Ensemble X) :
  FiniteT X ->
  (forall x, In U x \/ ~ In U x) ->
  exists n, cardinal U n.
Proof.
  intros.
  generalize dependent U.
  induction H.
  - intros. exists 0.
    pose proof (False_Ensembles_eq U Empty_set).
    subst.
    constructor.
  - intros.
    specialize (IHFiniteT
                  (fun t : T =>
                     In U (Some t))).
    destruct IHFiniteT as [m].
    { intros. unfold In at 1 3.
      apply H0.
    }
    specialize (H0 None) as [|].
    + exists (S m).
      replace U with (Add (Im (fun t : T => In U (Some t)) Some) None).
      1: constructor.
      1: apply injection_preserves_cardinal.
      * assumption.
      * red; intros; congruence.
      * intros ?. inversion H2; subst; clear H2. congruence.
      * extensionality_ensembles; try (subst; assumption).
        destruct x.
        -- left. exists t; auto.
        -- right. constructor.
    + exists m.
      replace U with (Im (fun t : T => In U (Some t)) Some).
      1: apply injection_preserves_cardinal.
      1: assumption.
      1: red; intros; congruence.
      extensionality_ensembles.
      * subst. assumption.
      * destruct x; try contradiction.
        exists t; auto.
  - intros.
    destruct H0 as [f Hf].
    specialize (IHFiniteT
                  (fun x : X =>
                     In U (f x))).
    destruct IHFiniteT as [m].
    { intros. unfold In at 1 3.
      apply H1.
    }
    exists m.
    replace U with (Im (fun x : X => In U (f x)) f).
    1: apply injection_preserves_cardinal.
    1: assumption.
    + red; intros.
      apply invertible_impl_bijective in H2;
        assumption.
    + extensionality_ensembles.
      * subst. assumption.
      * destruct Hf as [g []].
        exists (g x); auto.
        unfold In at 1. rewrite H4.
        assumption.
Qed.

Corollary FiniteT_dec_Finite X (U : Ensemble X) :
  FiniteT X ->
  (forall x : X, In U x \/ ~ In U x) ->
  Finite U.
Proof.
  intros.
  apply FiniteT_dec_Ensemble_has_cardinal in H0;
    try assumption.
  destruct H0 as [n].
  apply cardinal_finite with (n := n).
  assumption.
Qed.

Corollary FiniteT_Finite X (U : Ensemble X) :
  FiniteT X -> Finite U.
Proof.
  intros.
  apply FiniteT_dec_Finite;
    try assumption.
  intros. apply classic.
Qed.

Corollary FiniteT_has_nat_cardinal' (X : Type) :
  FiniteT X ->
  exists n, cardinal (@Full_set X) n.
Proof.
  intros.
  apply FiniteT_dec_Ensemble_has_cardinal;
    [assumption|].
  intros. left. constructor.
Qed.

Corollary FiniteT_has_nat_cardinal (X : Type) :
  FiniteT X ->
  exists! n:nat, cardinal (@Full_set X) n.
Proof.
intros.
apply -> unique_existence; split.
- apply FiniteT_has_nat_cardinal'.
  assumption.
- red; intros.
  apply cardinal_unicity with X Full_set; trivial.
Qed.

Definition FiniteT_nat_cardinal (X:Type) (H:FiniteT X) : nat :=
  proj1_sig (constructive_definite_description _
              (FiniteT_has_nat_cardinal X H)).
Lemma FiniteT_nat_cardinal_def: forall (X:Type) (H:FiniteT X),
  cardinal (@Full_set X) (FiniteT_nat_cardinal X H).
Proof.
intros; unfold FiniteT_nat_cardinal.
destruct constructive_definite_description.
assumption.
Qed.
Lemma FiniteT_nat_cardinal_cond: forall (X:Type) (H:FiniteT X)
  (n:nat),
  cardinal (@Full_set X) n ->
  FiniteT_nat_cardinal X H = n.
Proof.
intros.
pose proof (FiniteT_has_nat_cardinal X H).
destruct H1.
red in H1.
destruct H1.
transitivity x.
- symmetry; apply H2.
  apply FiniteT_nat_cardinal_def.
- apply H2; trivial.
Qed.

Lemma FiniteT_nat_cardinal_False:
  FiniteT_nat_cardinal False empty_finite = 0.
Proof.
apply FiniteT_nat_cardinal_cond.
rewrite (False_Ensembles_eq _ Empty_set).
constructor.
Qed.

Lemma FiniteT_nat_cardinal_option:
  forall (X:Type) (H:FiniteT X),
  FiniteT_nat_cardinal (option X) (add_finite X H) =
  S (FiniteT_nat_cardinal X H).
Proof.
intros.
apply FiniteT_nat_cardinal_cond.
rewrite option_Full_set_Im.
constructor.
- apply injection_preserves_cardinal.
  + apply FiniteT_nat_cardinal_def.
  + red; intros x1 x2 Heq; injection Heq; trivial.
- red; intro.
  inversion H0.
  discriminate H2.
Qed.

Lemma FiniteT_nat_cardinal_bijection:
  forall (X Y:Type) (H:FiniteT X) (Heq : eq_cardinal X Y),
    FiniteT_nat_cardinal Y (bij_finite X Y H Heq) =
    FiniteT_nat_cardinal X H.
Proof.
intros.
apply FiniteT_nat_cardinal_cond.
destruct Heq as [f Hf].
apply invertible_impl_bijective in Hf.
destruct Hf as [f_inj f_surj].
rewrite (proj1 (Im_Full_set_surj f)).
2: { assumption. }
apply injection_preserves_cardinal; trivial.
apply FiniteT_nat_cardinal_def.
Qed.

Lemma unique_FiniteT_nat_cardinal:
  exists! f: (forall (X:Type), FiniteT X -> nat),
  f False empty_finite = 0 /\
  (forall (X:Type) (H:FiniteT X),
     f (option X) (add_finite X H) = S (f X H)) /\
  (forall (X Y:Type) (H:FiniteT X) (Heq : eq_cardinal X Y),
     f Y (bij_finite X Y H Heq) = f X H).
Proof.
match goal with |- @ex ?T (@unique ?T ?f) =>
  apply -> (@unique_existence T f) end.
split.
- exists FiniteT_nat_cardinal.
  repeat split.
  + exact FiniteT_nat_cardinal_False.
  + exact FiniteT_nat_cardinal_option.
  + exact FiniteT_nat_cardinal_bijection.
- red; intros f g Hf Hg.
  destruct Hf as [HFalse_f [Hoption_f Hbijection_f]].
  destruct Hg as [HFalse_g [Hoption_g Hbijection_g]].
  extensionality X; extensionality HFinite.
  generalize HFinite.
  induction HFinite.
  + intro.
    destruct (proof_irrelevance _ empty_finite HFinite).
    congruence.
  + intro.
    destruct (proof_irrelevance _ (add_finite T HFinite) HFinite0).
    rewrite Hoption_f, Hoption_g, IHHFinite. reflexivity.
  + intro.
    destruct (proof_irrelevance _ (bij_finite _ _ HFinite H) HFinite0).
    now rewrite Hbijection_f, Hbijection_g, IHHFinite.
Qed.

(* Finite types can’t map surjectively onto [nat]. *)
Lemma FiniteT_nat_no_surj (X : Type) :
  FiniteT X ->
  ~ exists f : X -> nat, surjective f.
Proof.
intros.
induction H.
- intro. destruct H.
  specialize (H O).
  destruct H.
  assumption.
- intro. destruct H0 as [f].
  apply IHFiniteT. clear IHFiniteT.
  exists (fun x =>
       if (f None) <? f (Some x) then
         pred (f (Some x))
       else
         f (Some x)).
  red; intros.
  destruct (H0 y) as [[|]].
  + destruct (f None <? y) eqn:E.
    * destruct (H0 (S y)) as [[|]].
      -- exists t0. subst. rewrite H2. simpl.
         replace (f None <? S (f (Some t))) with true.
         { reflexivity. }
         symmetry.
         rewrite Nat.ltb_lt.
         rewrite Nat.ltb_lt in E.
         apply Nat.lt_lt_succ_r.
         assumption.
      -- subst. rewrite H2 in E.
         rewrite Nat.ltb_lt in E.
         apply Nat.nlt_succ_diag_l in E.
         contradiction.
    * exists t. subst. rewrite E. reflexivity.
  + destruct (H0 (S y)) as [[|]].
    -- exists t. subst. rewrite H2.
       replace (f None <? S (f None)) with true.
       { reflexivity. }
       symmetry.
       rewrite Nat.ltb_lt.
       constructor.
    -- rewrite H1 in H2.
       apply n_Sn in H2.
       contradiction.
- intro.
  destruct H0 as [f Hf].
  destruct H1 as [h Hh].
  contradict IHFiniteT.
  exists (compose h f).
  apply surjective_compose; auto.
  apply invertible_impl_bijective; auto.
Qed.

Lemma FiniteT_nat_embeds {X : Type} :
  FiniteT X -> exists f : X -> nat, injective f.
Proof.
intros.
induction H.
- exists (fun _ => O).
  red; intros.
  contradiction.
- destruct IHFiniteT as [f].
  exists (fun a => match a with
           | None => O
           | Some b => S (f b)
           end).
  red; intros.
  destruct x, y; try discriminate.
  + inversion H1; subst; clear H1.
    apply H0 in H3.
    rewrite H3. reflexivity.
  + reflexivity.
- destruct H0 as [f [g Hfg]].
  destruct IHFiniteT as [h Hh].
  exists (compose h g).
  apply injective_compose; auto.
  apply invertible_impl_bijective.
  exists f.
  apply inverse_map_sym; assumption.
Qed.

Lemma eq_cardinal_unit_option_False :
  eq_cardinal (option False) unit.
Proof.
  exists (fun _ => tt), (fun _ => None).
  split.
  - intros []; auto; contradiction.
  - intros []; reflexivity.
Qed.

Lemma FiniteT_unit : FiniteT unit.
Proof.
  apply bij_finite with (option False).
  { do 2 constructor. }
  apply eq_cardinal_unit_option_False.
Qed.

Lemma eq_cardinal_bool_sum_unit :
  eq_cardinal (unit + unit) bool.
Proof.
  exists (fun p =>
       match p with
       | inl _ => true
       | inr _ => false
       end),
    (fun p : bool => if p then inl tt else inr tt).
  split.
  - intros [[]|[]]; reflexivity.
  - intros []; reflexivity.
Qed.

Lemma FiniteT_bool : FiniteT bool.
Proof.
  apply bij_finite with (unit + unit)%type.
  2: apply eq_cardinal_bool_sum_unit.
  apply finite_sum; apply FiniteT_unit.
Qed.

Lemma finite_nat_initial_segment: forall n:nat,
  FiniteT { m:nat | m < n }.
Proof.
intros.
apply Finite_ens_type.
apply finite_nat_initial_segment_ens.
Qed.

Lemma finite_nat_initial_segment_le (n : nat) :
  FiniteT { m : nat | (m <= n)%nat }.
Proof.
apply Finite_ens_type.
replace (fun _ => _) with (fun m => m < S n).
{ apply finite_nat_initial_segment_ens. }
apply Extensionality_Ensembles; split; intros m Hm;
  cbv in *; lia.
Qed.

Lemma infinite_nat_inj: forall X:Type, ~ FiniteT X ->
  exists f:nat->X, injective f.
Proof.
intros.
assert (inhabited (forall S:Ensemble X, Finite S ->
  { x:X | ~ In S x})).
{ pose proof (choice (fun (x:{S:Ensemble X | Finite S}) (y:X) =>
    ~ In (proj1_sig x) y)).
  simpl in H0.
  match type of H0 with | ?A -> ?B => assert B end.
  { apply H0.
    intros.
    apply NNPP.
    red; intro.
    pose proof (not_ex_not_all _ _ H1); clear H1.
    destruct x.
    assert (x = Full_set).
    { apply Extensionality_Ensembles; red; split; auto with sets. }
    subst.
    contradict H.
    apply Finite_full_impl_FiniteT.
    assumption.
  }
  clear H0.
  destruct H1.
  exists.
  intros.
  exists (x (exist _ S H1)).
  exact (H0 (exist _ S H1)).
}
destruct H0.

assert (forall (n:nat) (g:forall m:nat, m<n -> X),
  { x:X | forall (m:nat) (Hlt:m<n), g m Hlt <> x }).
{ intros.
  assert (Finite (fun x:X => exists m:nat, exists Hlt:m<n,
             g m Hlt = x)).
  { pose (h := fun x:{m:nat | m<n} =>
      g (proj1_sig x) (proj2_sig x)).

    match goal with |- @Finite X ?S => assert (S =
      Im Full_set h) end.
    - apply Extensionality_Ensembles; red; split; red; intros; destruct H0.
      + destruct H0.
        now exists (exist (fun m:nat => m < n) x0 x1).
      + destruct x.
        now exists x, l.
    - rewrite H0; apply FiniteT_img.
      + apply finite_nat_initial_segment.
      + intros.
        apply classic.
  }
  destruct (X0 _ H0).
  unfold In in n0.
  exists x.
  intros; red; intro.
  contradiction n0; exists m; exists Hlt; exact H1.
}
pose (f := Fix Wf_nat.lt_wf (fun n:nat => X)
  (fun (n:nat) (g:forall m:nat, m<n->X) => proj1_sig (X1 n g))).
simpl in f.
assert (forall n m:nat, m<n -> f m <> f n).
{ pose proof (Fix_eq Wf_nat.lt_wf (fun n:nat => X)
    (fun (n:nat) (g:forall m:nat, m<n->X) => proj1_sig (X1 n g))).
  fold f in H0.
  simpl in H0.
  match type of H0 with | ?A -> ?B => assert (B) end.
  - apply H0.
    intros.
    replace f0 with g.
    { reflexivity. }
    extensionality y; extensionality p; symmetry; apply H1.
  - intros.
    specialize (H1 n).
    destruct X1 in H1.
    simpl in H1.
    destruct H1.
    auto.
}
exists f.
red; intros m n ?.
destruct (Compare_dec.lt_eq_lt_dec m n) as [[Hlt|Heq]|Hlt]; trivial.
- contradiction (H0 n m).
- now contradiction (H0 m n).
Qed.

Lemma nat_infinite: ~ FiniteT nat.
Proof.
red; intro.
assert (surjective S).
{ apply finite_inj_surj; trivial.
  red; intros.
  injection H0; trivial.
}
destruct (H0 0).
discriminate H1.
Qed.

Lemma FiniteT_cardinality {X : Type} :
  FiniteT X <-> lt_cardinal X nat.
Proof.
split; intros.
- split.
  + destruct (FiniteT_nat_embeds H) as [f].
    exists f. assumption.
  + intros H0.
    apply nat_infinite.
    apply bij_finite with X; assumption.
- destruct H as [[f Hf] H].
  apply NNPP. intro.
  destruct (infinite_nat_inj _ H0) as [g].
  contradict H.
  apply CSB_inverse_map with (f := f) (g := g);
    auto.
Qed.

Lemma finite_indexed_union {A T : Type} {F : IndexedFamily A T} :
  FiniteT A ->
  (forall a, Finite (F a)) ->
  Finite (IndexedUnion F).
Proof.
intro H.
induction H;
  intros.
- replace (IndexedUnion F) with (@Empty_set T).
  + constructor.
  + extensionality_ensembles.
    destruct a.
- replace (IndexedUnion F) with (Union (IndexedUnion (fun t => In (F (Some t)))) (F None)).
  + apply Union_preserves_Finite.
    * apply IHFiniteT.
      intro.
      apply H0.
    * apply H0.
  + extensionality_ensembles.
    * econstructor.
      eassumption.
    * econstructor.
      eassumption.
    * destruct a.
      ** left.
         econstructor.
         eassumption.
      ** now right.
- destruct H0 as [f Hf].
  replace (IndexedUnion F) with (IndexedUnion (fun x => F (f x))).
  + apply IHFiniteT.
    intro.
    apply H1.
  + extensionality_ensembles.
    * econstructor.
      eassumption.
    * destruct Hf as [g Hfg].
      exists (g a). rewrite (proj2 Hfg).
      assumption.
Qed.

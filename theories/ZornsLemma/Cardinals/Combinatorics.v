(** Collect many constructive [eq_cardinal] results. *)
From Coq Require Fin.
From Coq Require Import
  Description
  FunctionalExtensionality
  Morphisms
  Program.Basics.
From ZornsLemma Require Import
  Cardinals.Cardinals
  DecidableDec
  EnsemblesImplicit
  FunctionProperties.

(* give precedence to [proof_irrelevance] *)
From Coq Require Import ProofIrrelevance.
Import ProofIrrelevanceFacts.

Set Asymmetric Patterns.

(** ** Basic types *)
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

Lemma eq_cardinal_option_False_True :
  eq_cardinal (option False) True.
Proof.
  exists (fun _ => I), (fun _ => None).
  split.
  - intros []; auto; contradiction.
  - intros []; auto.
Qed.

Lemma eq_cardinal_unit_option_False :
  eq_cardinal (option False) unit.
Proof.
  exists (fun _ => tt), (fun _ => None).
  split.
  - intros []; auto; contradiction.
  - intros []; reflexivity.
Qed.

(** ** Sigma types *)
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

(** interestingly, this does not require [proof_irrelevance]. *)
Lemma eq_cardinal_sig_Singleton {X : Type} (x0 : X) :
  eq_cardinal (option False) { x : X | In (Singleton x0) x }.
Proof.
  exists (fun _ => exist _ x0 (In_singleton X x0)), (fun _ => None).
  split.
  - intros []; auto. contradiction.
  - intros [x Hx].
    destruct Hx. reflexivity.
Qed.

(** disjoint union *)
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

(** If [U] is an ensemble of [option X] and does contain [None],
  then [sig U] has the same cardinality as "the ensemble of [X] which
  'is' in [U]" plus one element. *)
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

(** If [U] is an ensemble of [option X] and does *not* contain [None],
  then [sig U] has the same cardinality as "the ensemble of [X] which
  'is' in [U]". *)
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

(** ** Sum types *)
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

Instance eq_cardinal_sum_Proper :
  Proper (eq_cardinal ==> eq_cardinal ==> eq_cardinal) sum.
Proof.
  intros X0 X1 [f0 [f1 []]].
  intros Y0 Y1 [g0 [g1 []]].
  exists (sum_rect
       (fun _ => X1 + Y1)%type
       (compose inl f0)
       (compose inr g0)).
  exists (sum_rect
       (fun _ => X0 + Y0)%type
       (compose inl f1)
       (compose inr g1)).
  split; intros [|]; simpl;
    unfold compose; f_equal; auto.
Qed.

(** ** Product types *)
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

Instance eq_cardinal_prod_Proper :
  Proper (eq_cardinal ==> eq_cardinal ==> eq_cardinal) prod.
Proof.
  intros X0 X1 [f0 [f1 []]].
  intros Y0 Y1 [g0 [g1 []]].
  exists (fun p => (f0 (fst p), g0 (snd p))).
  exists (fun p => (f1 (fst p), g1 (snd p))).
  split; intros []; simpl; f_equal; auto.
Qed.

(** ** Function types *)
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

(** ** Booleans *)
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

(** ** Coq stdlib [Fin.t] *)
Lemma eq_cardinal_Fin_S (n : nat) :
  eq_cardinal (option (Fin.t n)) (Fin.t (S n)).
Proof.
  exists (fun o =>
       match o with
       | None => Fin.F1
       | Some p => Fin.FS p
       end).
  exists (fun p : Fin.t (S n) =>
       Fin.caseS'
         p (fun _ => option (Fin.t n))
         None Some).
  split.
  - intros [|]; reflexivity.
  - revert n.
    apply Fin.rectS.
    + intros n. simpl.
      reflexivity.
    + intros n p _.
      simpl. reflexivity.
Qed.

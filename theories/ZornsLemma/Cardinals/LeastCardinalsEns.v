(** ** Definitions concerning least cardinals *)
From ZornsLemma Require Import
  Cardinals.CardinalsEns
  Cardinals.Comparability
  Families
  Image.

(** [U] is an element of [P] with minimal cardinality,
    where [P : Family X] *)
Definition least_cardinal_subset
  {X : Type} (P : Family X) (U : Ensemble X) : Prop :=
  In P U /\
    forall V : Ensemble X,
      In P V -> le_cardinal_ens U V.

(** [U] is an element of [P] with minimal cardinality,
    where [P] is a collection of arbitrary ensembles. *)
Definition least_cardinal
  (P : forall {X : Type} (U : Ensemble X), Prop)
  {X : Type} (U : Ensemble X) : Prop :=
  P U /\
    (forall (Y : Type) (V : Ensemble Y),
        P V -> le_cardinal_ens U V).

Definition least_cardinal_ext
  {X : Type} (P : Family X) {Y : Type} (V : Ensemble Y) :=
  least_cardinal
    (fun Z W =>
       exists U : Ensemble X,
         In P U /\ eq_cardinal_ens U W) V.

Lemma least_cardinal_ext_subset
  {X : Type} (P : Family X) (U : Ensemble X) :
  least_cardinal_subset P U ->
  least_cardinal_ext P U.
Proof.
  intros [HU0 HU1].
  split.
  - exists U; split; auto. reflexivity.
  - intros Y V [U' [HU'0 HU'1]].
    specialize (HU1 U' HU'0).
    eapply le_cardinal_ens_Proper_r; eauto.
Qed.

Lemma least_cardinal_ext_to_subset
  {X : Type} (P : Family X) {Y : Type} (V : Ensemble Y) :
  least_cardinal_ext P V ->
  exists U : Ensemble X,
    least_cardinal_subset P U /\ eq_cardinal_ens U V.
Proof.
  intros [[U [HU0 HU1]] HV1].
  exists U. split; auto.
  split; auto.
  intros W HW.
  apply eq_cardinal_ens_sym in HU1.
  eapply le_cardinal_ens_Proper_l; eauto.
  apply HV1. exists W; split; auto.
  reflexivity.
Qed.

Lemma least_cardinal_unique P {X : Type} (U : Ensemble X)
  {Y : Type} (V : Ensemble Y) :
  least_cardinal P U ->
  least_cardinal P V ->
  eq_cardinal_ens U V.
Proof.
  intros [HU0 HU1] [HV0 HV1].
  specialize (HU1 Y V HV0).
  specialize (HV1 X U HU0).
  apply le_cardinal_ens_antisymmetry;
    assumption.
Qed.

Lemma le_cardinal_ens_wf {X : Type} (F : Family X) :
  Inhabited F ->
  exists U, least_cardinal_subset F U.
Proof.
Admitted.

Corollary least_cardinal_ext_exists {X : Type} (F : Family X) :
  Inhabited F ->
  exists U : Ensemble X, least_cardinal_ext F U.
Proof.
  intros HF.
  destruct (le_cardinal_ens_wf F HF) as [U HU].
  exists U.
  apply least_cardinal_ext_subset.
  assumption.
Qed.

Lemma least_cardinal_exists
  (P : forall {X : Type} (U : Ensemble X), Prop) {X : Type} (U : Ensemble X) :
  P U -> exists (Y : Type) (V : Ensemble Y), least_cardinal (@P) V.
Proof.
  intros HU.
  pose (F := fun V : Ensemble X =>
               exists (Y : Type) (W : Ensemble Y),
                 P Y W /\ eq_cardinal_ens V W).
  assert (F U) as HU0.
  { exists X, U; split; auto; reflexivity. }
  (* every ensemble that satisfies [P] has a representative of the
     possibly smaller cardinality in [X]. *)
  assert (forall {Y : Type} (W : Ensemble Y),
             P Y W -> exists (V : Ensemble X),
               F V /\ le_cardinal_ens V W) as HFmin.
  { intros Y W HW.
    destruct (le_cardinal_ens_total U W).
    { exists U; auto. }
    destruct H as [[]|].
    { exists Empty_set. split.
      - exists Y, W. split; auto.
        apply eq_cardinal_ens_empty.
        apply H0.
      - apply le_cardinal_ens_Empty_set.
    }
    destruct H as [f [Hf0 Hf1]].
    exists (Im W f). split.
    - exists Y, W. split; auto.
      apply eq_cardinal_ens_sym.
      apply eq_cardinal_ens_Im_injective.
      assumption.
    - apply eq_cardinal_ens_le.
      apply eq_cardinal_ens_sym.
      apply eq_cardinal_ens_Im_injective.
      assumption.
  }
  destruct (le_cardinal_ens_wf F) as [V [[Y [W [HV0 HV1]]] HV2]].
  { exists U. assumption. }
  exists Y, W. split; auto.
  intros Z Q HQ.
  eapply le_cardinal_ens_Proper_l; eauto.
  specialize (HFmin Z Q HQ) as [R [HR0 HR1]].
  specialize (HV2 R HR0).
  eapply le_cardinal_ens_transitive; eauto.
Qed.

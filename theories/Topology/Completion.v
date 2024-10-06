From Coq Require Import Description ProofIrrelevance Psatz.
From Topology Require Export Completeness.
From Topology Require Import UniformTopology RTopology.

Section Completion.
  Context {X : TopologicalSpace}
    (d : X -> X -> R) (d_metric : metric d)
    (d_metrizes : metrizes X d).

  Local Lemma Rabs_bound (a b : R) :
    (- b <= a <= b) <-> Rabs a <= b.
  Proof.
    split.
    - intros. unfold Rabs.
      destruct (Rcase_abs _); lra.
    - intros. unfold Rabs in *.
      destruct (Rcase_abs _); lra.
  Qed.

  Local Lemma metric_alternate_triangle_ineq (x y z : X) :
    R_metric (d x z) (d y z) <= d x y.
  Proof.
    unfold R_metric.
    rewrite <- Rabs_bound.
    pose proof (triangle_inequality
                 d_metric x y z).
    pose proof (triangle_inequality
                 d_metric y x z).
    rewrite (metric_sym d_metric y x) in H0.
    lra.
  Qed.

  Lemma completion_exists_nondense :
    exists (Y : Type) (d' : Y -> Y -> R) (d'_metric : metric d')
      (i : X -> Y),
      isometry d d' i /\ complete d'.
  Proof.
    destruct (classic (inhabited X)).
    2: {
      unshelve eexists False, (False_rect _), _, _.
      3: split.
      - constructor; intros; contradiction.
      - intros x; apply H; constructor; apply x.
      - intros ? ?; contradict H; constructor; auto.
      - intros x; contradiction (x 0%nat).
    }
    destruct H as [x0].
    (* we now construct Y as the uniform space of functions X->R,
       with base point "distance from x0"; the embedding of X into this
       space is to send x to "distance from x".
       We do not use the Cauchy completion, because Coq deals badly with quotients.
     *)
    exists (uniform_space R_metric (d x0)),
      (uniform_metric R_metric (d x0) R_metric_is_metric (inhabits x0)),
      (uniform_metric_is_metric _ _ _ _ _ _).
    unshelve refine (let H0:=_ in ex_intro _ (fun x:X => exist _ (d x) (H0 x)) _);
      [|split].
    * intros.
      exists (d x0 x).
      intros x1 Hx1.
      destruct Hx1. subst.
      apply metric_alternate_triangle_ineq.
    * red; intros x1 x2.
      unfold uniform_metric.
      destruct sup as [? i]; simpl.
      apply Rle_antisym; apply i.
      -- red; intros x3 Hx3.
         destruct Hx3. subst.
         apply metric_alternate_triangle_ineq.
      -- exists x1; [constructor|].
         rewrite metric_zero; auto.
         rewrite (metric_sym d_metric x2 x1).
         unfold R_metric.
         rewrite Rminus_0_r.
         symmetry; apply Rabs_right, Rle_ge, metric_nonneg, d_metric.
    * apply uniform_metric_complete.
      apply R_metric_complete.
  Qed.

  Theorem completion_exists:
    exists (Y:TopologicalSpace) (i : X -> Y)
      (d' : Y -> Y -> R) (d'_metric : metric d'),
      metrizes Y d' /\
        dense (Im Full_set i) /\
        isometry d d' i /\ complete d'.
  Proof.
    intros.
    (* first of all, it suffices to construct a (Y, d') without the
       density condition; then the restriction of d' to the closure of X
       is again complete, and X is dense in it *)
    destruct completion_exists_nondense as [Y [d' [d'_metric [i [Hi_iso d'_comp]]]]].
    pose (F := closure (Im Full_set i) (X:=MetricTopology d' d'_metric)).
    exists (SubspaceTopology F).
    assert (forall x:X, In F (i x)) as HFi.
    { intros.
      apply closure_inflationary.
      exists x; trivial.
      constructor.
    }
    exists (fun x:X => exist _ (i x) (HFi x)).
    pose (d'' := fun y1 y2 : SubspaceTopology F=> d' (proj1_sig y1) (proj1_sig y2)).
    exists d''.
    assert (d'_metric0 : metric d'').
    { apply d_restriction_metric. assumption. }
    assert (d'_metrizes0 : metrizes _ d'').
    { apply metric_space_subspace_topology_metrizes;
        auto.
      apply MetricTopology_metrized.
    }
    exists d'_metric0.
    split; auto.
    repeat split.
    2: {
      intros ? ?. simpl.
      apply Hi_iso.
    }
    2: {
      apply
        (@closed_subset_of_complete_is_complete
           (MetricTopology d' d'_metric) d' d'_metric
           (MetricTopology_metrized _ d' d'_metric)
           F d'_comp (closure_closed _)
        ).
    }
    pose proof (@dense_in_closure
                  (MetricTopology d' d'_metric) (Im Full_set i)).
    match goal with
    | H : dense ?a |- dense ?b =>
        replace b with a; auto
    end.
    apply Extensionality_Ensembles; split; red.
    - intros [x Hx0] [Hx1].
      simpl in Hx1.
      inversion Hx1; subst; clear Hx1.
      exists x0; auto.
      apply subset_eq_compat; auto.
    - intros [x Hx0] ?.
      inversion H0; subst; clear H0.
      constructor. simpl.
      exists x0; [constructor|].
      inversion H2; subst; clear H2; auto.
  Qed.
End Completion.

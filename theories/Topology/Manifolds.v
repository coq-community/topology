From Topology Require Import Homeomorphisms SubspaceTopology EuclideanSpaces.

Definition restriction {X Y: Type} (f : X -> Y) (U : Ensemble X): {x | U x} -> {y | Im U f y}.
intro x.
apply (exist _ (f (proj1_sig x))).
apply (Im_intro _ _ _ _ _ (proj2_sig x)).
reflexivity.
Defined.

Inductive local_homeomorphism {X Y : TopologicalSpace}
                              (f : point_set X -> point_set Y) : Prop :=
| intro_local_homeomorphism:
  (forall (x: point_set X),
    exists U:Ensemble (point_set X),
      open_neighborhood U x /\
      open (Im U f) /\
      @homeomorphism (SubspaceTopology U) (SubspaceTopology (Im U f)) (restriction f U)) ->
    local_homeomorphism f.


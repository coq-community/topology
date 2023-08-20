(** The [ZornsLemma] and [Topology] libraries declare implicit
    arguments on the definitions of the coq std. library which are
    concerned with [Ensembles].
    If someone wants to use these libraries, but does not want to use
    the same convention for implicit arguments, they can import this
    file.

    This file resets the implicit arguments set by
    - ZornsLemma.EnsemblesImplicit
    - ZornsLemma.FiniteImplicit
    - ZornsLemma.ImageImplicit
    - ZornsLemma.Relation_Definitions_Implicit
*)

From Coq Require Import
     Relation_Definitions Sets.Ensembles Sets.Finite_sets Sets.Image.

Arguments reflexive : clear implicits.
Arguments transitive : clear implicits.
Arguments symmetric : clear implicits.
Arguments antisymmetric : clear implicits.
Arguments equiv : clear implicits.
Arguments preorder : clear implicits.
Arguments Build_preorder : clear implicits.
Arguments preord_refl : clear implicits.
Arguments preord_trans : clear implicits.
Arguments order : clear implicits.
Arguments Build_order : clear implicits.
Arguments ord_refl : clear implicits.
Arguments ord_trans : clear implicits.
Arguments ord_antisym : clear implicits.
Arguments equivalence : clear implicits.
Arguments Build_equivalence : clear implicits.
Arguments equiv_refl : clear implicits.
Arguments equiv_trans : clear implicits.
Arguments equiv_sym : clear implicits.
Arguments PER : clear implicits.
Arguments Build_PER : clear implicits.
Arguments per_sym : clear implicits.
Arguments per_trans : clear implicits.
Arguments inclusion : clear implicits.
Arguments same_relation : clear implicits.
Arguments commut : clear implicits.

Arguments In : clear implicits.
Arguments Included : clear implicits.
Arguments Singleton : clear implicits.
Arguments Union : clear implicits.
Arguments Add : clear implicits.
Arguments Intersection : clear implicits.
Arguments Couple : clear implicits.
Arguments Triple : clear implicits.
Arguments Complement : clear implicits.
Arguments Setminus : clear implicits.
Arguments Subtract : clear implicits.
Arguments Disjoint : clear implicits.
Arguments Inhabited : clear implicits.
Arguments Strict_Included : clear implicits.
Arguments Same_set : clear implicits.
Arguments Extensionality_Ensembles : clear implicits.
Arguments Empty_set : clear implicits.
Arguments Full_set : clear implicits.

Arguments Finite : clear implicits.

Arguments Im : clear implicits.
Arguments Im_def : clear implicits.
Arguments Im_add : clear implicits.
Arguments image_empty : clear implicits.
Arguments finite_image : clear implicits.
Arguments Im_inv : clear implicits.
Arguments not_injective_elim : clear implicits.
Arguments cardinal_Im_intro : clear implicits.
Arguments In_Image_elim : clear implicits.
Arguments injective_preserves_cardinal : clear implicits.
Arguments cardinal_decreases : clear implicits.
Arguments Pigeonhole : clear implicits.
Arguments Pigeonhole_principle : clear implicits.

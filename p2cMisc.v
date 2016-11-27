Add Rec LoadPath "/home/daniel/UniMath/UniMath" as UniMath.

Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.

Require Import RezkCompletion.precategories.
Require Import RezkCompletion.functors_transformations.

Load functCats.

Local Notation "a --> b" := (precategory_morphisms a b) (at level 50).
(* Local Notation "'hom' a b" := (precategory_morphisms a b) (at level 2). *)
Local Notation "f ;; g" := (compose f g) (at level 50, format "f  ;;  g").
Local Notation "D ^^ C" := (hs_funct_precat C D) (at level 2).


Definition iso_comp_via
  {C : precategory} {a c : C}
  (b : C)
    : (iso a b) -> (iso b c) -> (iso a c).
Proof.
  intros f g.
  apply (iso_comp f g).
Defined.

Lemma functor_pointwise_iso_from_iso
  {C : precategory} {D : hs_precategory} {F G : D ^^ C}
  (u : iso F G)
    : forall a : C, iso (get_funct F a) (get_funct G a).
Proof.
  apply (functor_iso_pointwise_if_iso C D (get_hs D) F G u (pr2 u)).
Defined.

Definition mor_to_nat_trans
  {C : precategory} {D : hs_precategory}
  {F G : D^^C}
  (u : nat_trans (get_funct F) (get_funct G))
    : F --> G.
Proof.
  apply u.
Defined.


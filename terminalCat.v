(* This file is used later to define identities in 2-categories *)

Add Rec LoadPath "/home/daniel/UniMath/UniMath" as UniMath.

Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.

Require Import RezkCompletion.precategories.
Require Import RezkCompletion.functors_transformations.

Local Notation "'hom' C" := (precategory_morphisms (C := C)) (at level 2).
Local Notation "f ;; g" := (compose f g) (at level 50, format "f  ;;  g").





Definition terminal_cat_ob_mor : precategory_ob_mor.
Proof.
  apply (precategory_ob_mor_pair unit).
  apply (fun x => fun y => unit).
Defined.

Definition terminal_cat_data : precategory_data.
Proof.
  apply (precategory_data_pair terminal_cat_ob_mor).
  (* identity *)
  intro c.
  apply tt.
  (* composition *)
  intros a b c f g.
  apply tt.
Defined.

(* what happened to assoc? *)
Definition terminal_precat : precategory.
Proof.
  apply (tpair _ terminal_cat_data).
  repeat split; simpl.
  (* left unitor *)
  - intros ? ? ?.
    apply isapropunit.
  (* right unitor *)
  - intros ? ? ?.
    apply isapropunit.
Defined.

Definition terminal_precat_isotoid
  {a b : terminal_precat}
    : iso a b -> a = b.
Proof.
  intro f.
  apply isapropunit.
Defined.

Definition terminal_cat : category.
Proof.
  apply (tpair _ terminal_precat).
  split.
    - intros a b.
      apply (gradth _ terminal_precat_isotoid).
      + intro p.
        destruct a, b.
        apply (ifcontrthenunitl0 _ p). 
      + intro f.
        apply (eq_iso _ f).
        apply (isapropunit).
    - unfold has_homsets. 
      intros a b.
      apply isasetaprop.
      intros x y.
      apply isapropunit.
Defined.

(* a function on objects gives a functor *)
Definition terminal_cat_functors_data
  {C : hs_precategory}
    : (terminal_cat -> C) ->  functor_data terminal_cat C.
Proof.
  intro c.
  apply (tpair _ (fun x : terminal_cat => c x)).    
  intros a b.
  intro f.
  destruct a, b.
  apply identity.
Defined.

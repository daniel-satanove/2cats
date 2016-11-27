Add Rec LoadPath "/home/daniel/UniMath/UniMath" as UniMath.

Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.

Require Import RezkCompletion.precategories.
Require Import RezkCompletion.functors_transformations.
Require Import RezkCompletion.whiskering.

Load terminalCat.

Local Notation "a --> b" := (precategory_morphisms a b) (at level 50).
Local Notation "f ;; g" := (compose f g) (at level 50, format "f  ;;  g").
Local Notation "# F" := (functor_on_morphisms F)(at level 3).

Definition get_hs
  (C : hs_precategory)
    : has_homsets C
:= pr2 (pr2 C).

Definition hs_precat_pair
  (C : precategory) (hs : has_homsets C)
    : hs_precategory.
Proof.
  unfold hs_precategory.
  apply (tpair _ (pr1 C)).  
  split.  
  apply (pr2 C).
  apply hs.
Defined.

Definition hs_funct_precat
  (C : precategory) (D: hs_precategory)
    : hs_precategory.
Proof.
  apply (hs_precat_pair (functor_precategory C D (pr2 (pr2 D)))). 
  apply (functor_category_has_homsets C D (get_hs D)).
Defined.

Local Notation "D ^^ C" := (hs_funct_precat C D) (at level 2).

(* coercion isn't working (??) when I want to apply a functor from D ^^ C
   to an object of C, need something with coercion to funclass? *)
Definition get_funct
  {C : precategory} {D : hs_precategory} (F : D ^^ C)
    : functor C D.
Proof.
  apply F.
Defined.

Definition dget_funct
  {C D : precategory} {E : hs_precategory}
  (F : (E^^D)^^C )
  (c : C)
    : functor D E.
Proof.
  apply (get_funct F c).  
Defined.

Definition tget_funct
  {B C D : precategory} {E : hs_precategory}
  (F : ((E^^D)^^C)^^B )
  (b : B) (c : C)
    : functor D E.
Proof.
  apply (dget_funct F b c).  
Defined.

Arguments get_funct {C D} / F.
Arguments dget_funct {C D E} / F c.
Arguments tget_funct {B C D E} / F b c.

Definition get_nat
  {C : precategory} {D : hs_precategory} {F G : D^^C}
  (u : F --> G)
    : nat_trans (get_funct F) (get_funct G).
Proof.
  apply u.
Defined.

Definition dget_nat
  {C D : precategory} {E : hs_precategory} {F G : (E^^D)^^C}
  (v : F --> G) (c : C) 
    : nat_trans (dget_funct F c) (dget_funct G c).
Proof.
  apply (get_nat v c).
Defined.

Definition funct_cat
  (C : precategory) (D : category)
    : category.
Proof.
  apply (tpair _ (functor_precategory C D (pr2 (pr2 D)))).
  apply (is_category_functor_category C D).
Defined.

Local Notation "[ C , D ]'" := (funct_cat C D) (at level 2).

(* If 2categories.v still compiles, delete this
Definition function_from_functor_cat
  {C : precategory} {D : category}
    : [C, D]' -> C -> D.
Proof.
  intro f.
  apply f.
Defined.
*)

(* function from terminal cate defines a functor *)
Definition terminal_cat_functors
  {C : hs_precategory}
    : (terminal_cat -> C) ->  C ^^ terminal_cat.
Proof.
  intro x.
  apply (tpair _ (terminal_cat_functors_data x)).
  split.
  - intro a.
    destruct a.
    simpl.   
    apply idpath.
  - intros a b c f g.
    destruct a, b, c.
    simpl.
    apply (pathsinv0 (id_left _ _ _ (identity (x tt)))).
Defined.

(* precomposition *)
Definition funct_precomp_data
  {C : precategory} {D : hs_precategory} 
  (F : D^^C) (E : hs_precategory)
    : functor_data E^^D E^^C.
Proof.
  apply (tpair _ (functor_composite _ _ _ F)). 
  intros G G' u.
  apply (pre_whisker (get_funct F) u).
Defined.

Definition funct_precomp
  {C : precategory} {D : hs_precategory} 
  (F : D^^C) (E : hs_precategory)
    : functor E^^D E^^C.
Proof.
  apply (tpair _ (funct_precomp_data F E)).
  split.
  - intro G.
    apply pre_whisker_identity.
    apply get_hs.
  - intros G G' G'' u v.
    apply pre_whisker_composition.
    apply get_hs.
Defined.

(* postcomposition *)
Definition funct_postcomp_data    
  {C : hs_precategory} {D : hs_precategory}
  (E : precategory) (F : D^^C)
    : functor_data C^^E D^^E.
Proof.
  apply (tpair _ (fun G' : C^^E =>  functor_composite _ _ _ G' F)).
  intros G G' u.
  apply (post_whisker u (get_funct F)).
Defined.

Definition funct_postcomp    
  {C : hs_precategory} {D : hs_precategory}
  (E : precategory) (F : D^^C)
    : functor C^^E D^^E.
Proof.
  apply (tpair _ (funct_postcomp_data E F)).
  split.
  - intro G.
    apply nat_trans_eq.
    apply get_hs.
    intro a.
    apply (functor_id (get_funct F)).
  - intros G G' G'' u v.
    apply nat_trans_eq.
    apply get_hs.
    intro a. 
    apply (functor_comp (get_funct F)).
Defined.

(* argument swaping functor (E^^D)^^C ^^ (E^^C)^^D 

   The general pattern is to define the object function, then functor
   data, then the actual functor. This is done several times. *) 
Definition funct_arg_swap_ob_to_ob_to_data
  {C D : precategory} {E : hs_precategory}
    : (E^^D)^^C -> (D -> (functor_data C E)).
Proof.
  intros F d.
  apply (tpair _ (fun c : C => dget_funct F c d)). 
  intros a b f. 
  (* re-figure out the args thing so it unfolds get_funct automatically *)
  unfold dget_funct; unfold get_funct.
  apply (# (get_funct F) f).
Defined.

Definition funct_arg_swap_ob_to_ob_to_funct
  {C D : precategory} {E : hs_precategory}
    : (E^^D)^^C -> (D -> (E^^C)).
Proof.
  intros F d.
  apply (tpair _ ((funct_arg_swap_ob_to_ob_to_data F) d)). 
  split.
  - intro a; simpl.
    rewrite (functor_id (get_funct F)).
    apply idpath.
  - intros a b c f g; simpl.
    rewrite (functor_comp (get_funct F)).
    apply idpath.
Defined.

Definition funct_arg_swap_on_mor
  {C D : precategory} {E : hs_precategory}
  (F : (E^^D)^^C) {a b : D} (f : a --> b)
    : forall c : C, (dget_funct F c) a --> (dget_funct F c) b.
Proof.
  intro c.
  apply (#(dget_funct F c) f).
Defined.

Definition funct_arg_swap_ob_to_funct_data
  {C D : precategory} {E : hs_precategory}
    : (E^^D)^^C -> (functor_data D E^^C).
Proof.
  intro F.
  apply (tpair _ (funct_arg_swap_ob_to_ob_to_funct F)).
  intros a b f; simpl.
  apply (tpair _ (funct_arg_swap_on_mor F f)).
  intros x y g.
  (* get the natural transformation data from (# F g) *)
  set (H := pr2 (#(get_funct F) g)).
  simpl in *.
  apply (pathsinv0 (H a b f)).
Defined.

Definition funct_arg_swap_ob
  (C D : precategory) (E : hs_precategory)
    : (E^^D)^^C -> (E^^C)^^D.
Proof.
  intro F.
  apply (tpair _ (funct_arg_swap_ob_to_funct_data F)).
  split.
  - intro a. 
    apply nat_trans_eq.
    apply get_hs.
    intro c.
    apply (functor_id (dget_funct F c)).
  - intros a b c f g.
    apply nat_trans_eq.
    apply get_hs.
    intro d.
    apply (functor_comp (dget_funct F d)).
Defined.

Definition funct_arg_swap_mor_mor
  {C D : precategory} {E : hs_precategory} {F G : (E^^D)^^C}
  (u : F --> G) (d : D)
    : forall c : C, 
       get_funct (funct_arg_swap_ob_to_funct_data F d) c --> 
       get_funct (funct_arg_swap_ob_to_funct_data G d) c.
Proof.
  intro c.
  apply (dget_nat u c d).
Defined.
 
Definition funct_arg_swap_mor
  {C D : precategory} {E : hs_precategory} {F G : (E^^D)^^C}
  (u : F --> G)
    : forall d : D, (funct_arg_swap_ob_to_funct_data F) d -->
                    (funct_arg_swap_ob_to_funct_data G) d.
Proof.
  intro d; simpl.
  apply (tpair _ (funct_arg_swap_mor_mor u d)).
  intros a b f; simpl.
  unfold funct_arg_swap_mor_mor.
  unfold dget_nat; unfold get_nat.
  (* There should be a nicer way of doing this, like inverse functional
     extensionality or generalize d or something.*)
  apply (nat_trans_eq_pointwise _ _ _ _ _ _ (pr2 u a b f)).
Defined.

Definition funct_arg_swap_data
  (C D : precategory) (E : hs_precategory)
    : functor_data (E^^D)^^C (E^^C)^^D.
Proof.
  apply (tpair _ (funct_arg_swap_ob C D E)).
  intros F G u.
  simpl.
  apply (tpair _ (funct_arg_swap_mor u)).
  intros a b f.   
  apply nat_trans_eq.
  apply get_hs.
  intro c.
  simpl.  
  unfold funct_arg_swap_mor_mor.
  apply (pr2 (dget_nat u c)).
Defined.

Definition funct_arg_swap
  {C D : precategory} {E : hs_precategory}
    : functor ((E^^D)^^C) ((E^^C)^^D).
Proof.
  apply (tpair _ (funct_arg_swap_data C D E)).
  split.
  - intro a.
    apply nat_trans_eq.
    apply get_hs.
    intro y.
    apply nat_trans_eq.
    apply get_hs.
    intro x.
    simpl.
    unfold funct_arg_swap_mor_mor.
    unfold dget_funct; unfold get_funct.
    unfold dget_nat; unfold get_nat.
    simpl.
    apply idpath.
  - intros a b c f g.
    apply nat_trans_eq.
    apply get_hs.
    intro y.
    apply nat_trans_eq.
    apply get_hs.
    intro x.
    simpl.
    unfold funct_arg_swap_mor_mor.
    unfold dget_nat; unfold get_nat.
    simpl.
    apply idpath.
    (* I wonder why this takes so long to compute. If I remove the simpls
       right before the idpath, then the idpath takes a long time to check
       *)
Defined.

(* Definition of the comp functor *)
Definition functor_comp_functor_fun
  (C D E : hs_precategory)
    : (D ^^ C) -> ((E ^^ C) ^^ (E ^^ D)).
Proof.
  intro F.  
  apply (funct_precomp F E).
Defined.

Definition functor_comp_functor_nat
  {C D E : hs_precategory}
  (F G : D ^^ C) (u : F --> G)
    : forall H : E ^^ D, (funct_precomp F E) H --> (funct_precomp G E) H.
Proof.
  intro H.
  apply post_whisker.
  apply u.
Defined.
  
Definition functor_comp_functor_data
  (C D E : hs_precategory)
    : functor_data (D ^^ C) ((E ^^ C) ^^ (E ^^ D)).
Proof.
  apply (tpair _ (fun F : D ^^ C => funct_precomp F E)).
  intros F G u.
  apply (tpair _ (functor_comp_functor_nat F G u)). 
  intros H H' r.
  apply nat_trans_eq. 
  apply get_hs.
  intro a.
  simpl.
  apply pathsinv0.
  apply (pr2 r (pr1 F a) (pr1 G a) (pr1 u a)).
Defined.

Definition functor_comp_functor
  (C D E : hs_precategory)
    : ((E ^^ C) ^^ (E ^^ D)) ^^ (D ^^ C).
Proof.
  apply (tpair _ (functor_comp_functor_data C D E)).
  split.
  - intro F.
    apply nat_trans_eq. apply get_hs.
    intro G.
    apply nat_trans_eq. apply get_hs.
    intro a.
    simpl.
    apply functor_id.
  - intros F F' F'' u u'.
    apply nat_trans_eq. apply get_hs.
    intro G.
    apply nat_trans_eq. apply get_hs.
    intro a.
    simpl.
    apply functor_comp.
Defined.
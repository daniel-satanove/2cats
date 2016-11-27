Add Rec LoadPath "/home/daniel/UniMath/UniMath" as UniMath.

Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.
Require Import UniMath.Foundations.Proof_of_Extensionality.funextfun. 

Require Import UniMath.RezkCompletion.precategories.
Require Import RezkCompletion.functors_transformations.
Require Import UniMath.RezkCompletion.HLevel_n_is_of_hlevel_Sn.

Load pre2categories_clean.

Local Notation "a ==> b" := (precategory_morphisms a b) (at level 50).
Local Notation "f ;; g" := (compose f g) (at level 50, format "f  ;;  g").

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "D ^^ C" := (hs_funct_precat C D) (at level 2).
Local Notation "[ C , D ]'" := (funct_cat C D) (at level 2).
Local Notation "a --> b" := (homc a b) (at level 50).

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

Definition hsprecat_ob_mor
  : pre2cat_ob_mor.
Proof.
  apply (tpair (fun C : UU => C -> C -> hs_precategory) hs_precategory).
  intros C D.
  apply (D ^^ C).
Defined.

Definition hsprecat_1data
  : pre2cat_1data.
Proof.
  apply (tpair _ hsprecat_ob_mor).
  split.
  - intro a.
    apply terminal_cat_functors.
    intro x; destruct x.
    apply functor_identity.
  - intros a b c.
    apply functor_comp_functor.    
Defined.


Definition hsprecat_massoc_mor
  {A B C D : hsprecat_1data}
  (F : A --> B) (G : B --> C) (H : C --> D)
    : mcomp (mcomp F G) H ==> mcomp F (mcomp G H).
Proof.
  apply (tpair _ (fun x => identity 
                   (get_funct H (get_funct G (get_funct F x))))).
  intros a b f.
  pathvia (# (get_funct (mcomp (mcomp F G) H)) f).
    apply id_right.
  pathvia (# (get_funct (mcomp F (mcomp G H))) f).
    apply idpath.
  apply pathsinv0.
  apply id_left.
Defined.

Definition hsprecat_massoc_mor_inv
  {A B C D : hsprecat_1data}
  (F : A --> B) (G : B --> C) (H : C --> D)
    : mcomp F (mcomp G H) ==> mcomp (mcomp F G) H.
Proof.
  apply (tpair _ (fun x => identity 
                   (get_funct H (get_funct G (get_funct F x))))).
  intros a b f; simpl.
  pathvia (# (get_funct (mcomp (mcomp F G) H)) f).
    apply id_right.
  pathvia (# (get_funct (mcomp F (mcomp G H))) f).
    apply idpath.
  apply pathsinv0.
  apply id_left.
Defined.

Definition hsprecat_massoc
  (A B C D : hsprecat_1data)
  : pre2cat_massoc_type A B C D. 
Proof.
  intros F G H.
  apply (tpair _ (hsprecat_massoc_mor F G H)).
  apply (is_iso_qinv _ (hsprecat_massoc_mor_inv F G H)).
  split.
    - apply nat_trans_eq.
      apply get_hs.
      intro a.
      simpl.
      apply (id_right _ (pr1 H (pr1 G (pr1 F a)))).
    - apply nat_trans_eq.
      apply get_hs.
      intro a.
      simpl.
      apply (id_right _ (pr1 H (pr1 G (pr1 F a)))).
Defined.

Definition hsprecat_llwhiskassoc
  (A B C D : hsprecat_1data)
  : pre2cat_llwhisk_assoc_type (hsprecat_massoc A B C D).
Proof.
  intros F G H H' w.
  apply nat_trans_eq.
  apply get_hs.
  intro a.
  simpl.  
  pathvia (pr1 w (pr1 G (pr1 F a))).
  apply id_right.
  apply pathsinv0.
  apply id_left.
Defined.

Definition hsprecat_lrwhiskassoc
  (A B C D : hsprecat_1data)
  : pre2cat_lrwhisk_assoc_type (hsprecat_massoc A B C D).
Proof.
  intros F G G' v H.
  apply nat_trans_eq.
  apply get_hs.
  intro a.
  simpl.  
  pathvia (# (pr1 H) (pr1 v (pr1 F a))).
  apply id_right.
  apply pathsinv0.
  apply id_left.
Defined.

Definition hsprecat_rrwhiskassoc
  (A B C D : hsprecat_1data)
  : pre2cat_rrwhisk_assoc_type (hsprecat_massoc A B C D).
Proof.
  intros F F' u G H.
  apply nat_trans_eq.
  apply get_hs.
  intro a.
  simpl.  
  pathvia (#(pr1 H) (# (pr1 G) (pr1 u a))).
  apply id_right.
  apply pathsinv0.
  apply id_left.
Defined.

Definition hsprecat_assoc
  : pre2cat_assoc (hsprecat_1data).
Proof.
  unfold pre2cat_assoc.
  intros A B C D.
  apply (pre2cat_assoc_trans_constructor A B C D
                                   (hsprecat_massoc A B C D)
                                   (hsprecat_llwhiskassoc A B C D)
                                   (hsprecat_lrwhiskassoc A B C D)
                                   (hsprecat_rrwhiskassoc A B C D)).
Defined.


(* reference
Definition pre2cat_str_massoc_type
  (C : pre2cat_1data)
:= forall (a b c d : C)
             (f : a --> b)
             (g : b --> c)
             (h : c --> d),
     mcomp (mcomp f g) h = mcomp f (mcomp g h).

(* it's just refl, but it's hard to make coq realize this *)
Definition hsprecat_ob_assoc
  {A B C D : hsprecat_1data} (F : A --> B) (G : B --> C) (H : C --> D)
 : pr1 (functor_composite_data 
                    (functor_composite_data (get_funct F) (get_funct G))
                    (get_funct H))
                = pr1 (functor_composite_data (get_funct F) 
                        (functor_composite_data (get_funct G) 
                                                (get_funct H))).
Proof.
  apply idpath.
Defined.

Definition hsprecat_str_massoc
  : pre2cat_str_massoc_type hsprecat_1data.
Proof.
  intros A B C D F G H.
  apply functor_eq.
  apply get_hs.
  apply (total2_paths (hsprecat_ob_assoc F G H)). 
  apply idpath.
Defined.

Definition hsprecat_massoc
  (A B C D : hsprecat_1data)
  : pre2cat_massoc_type A B C D. 
Proof.
   intros F G H. 
   apply (idtoiso (hsprecat_str_massoc A B C D F G H)).
Defined.


(*
Definition hsprecat_massoc_exp
  (A B C D : hsprecat_1data)
Proof.
*) 

Lemma idtoiso_precompose2 
  (C : precategory) (a a' b : C)
  (p : a = a') (f : a' ==> b) 
    : (idtoiso p) ;; f = transportf (fun a => a ==> b) (!p) f.
Proof.
  destruct p.
  apply id_left.
Qed.

Check idtoiso_postcompose.

Lemma idtoiso_id1
  (C : precategory) (a a': C)
  (p : a = a') 
    : pr1 (idtoiso p) = transportf (fun a => a ==> a') (!p) (identity a').
Proof.
  pathvia (pr1 (idtoiso p) ;; identity a').
  apply pathsinv0.
  apply id_right.
  apply (idtoiso_precompose2 _ _ _ _ p (identity a')).
Defined.

Lemma idtoiso_id2
  (C : precategory) (a a': C)
  (p : a = a') 
    : pr1 (idtoiso p) = transportf (fun b => a ==> b) (p) (identity a).
Proof.
  pathvia (identity a ;; (pr1 (idtoiso p))). 
  apply pathsinv0.
  apply id_left.
  apply (idtoiso_postcompose _ _ _ _ p (identity a)).
Defined.

Lemma proofirrelevance_idpath
  (X : UU) (is : isaprop X) (x : X)
  : proofirrelevance X is x x = idpath x.
Proof.
 apply (!(pr2 (is x x) (idpath x))).
Defined.

Lemma functor_eq_idpath
  {C D : hs_precategory}  (F : functor C D) 
    : functor_eq C D (get_hs D) F F (idpath (pr1 F)) = idpath F.
Proof.
  simpl.
  unfold functor_eq.
  Check total2_paths.
  unfold transportf.
  simpl.
  unfold idfun.
  rewrite (proofirrelevance_idpath (is_functor (pr1 F)) 
            (isaprop_is_functor _ _ _ (pr1 F)) (pr2 F)).
  destruct F.
  simpl.
  apply idpath.
Defined.


Definition functor_eq_ob_eq
  {C D : hs_precategory} {F G : D ^^ C}
  (p : F = G) (a : C)
    : get_funct F a = get_funct G a.
Proof.
  apply (maponpaths (fun F => (get_funct F a)) p).
Defined.

Definition idtoiso_nat_commute
  {C D : hs_precategory} {F G : D ^^ C}
  (p : F = G) (a : C)
    : ((get_nat (idtoiso p)) a)
        = (idtoiso (functor_eq_ob_eq p a)).
Proof.
  destruct p.
  apply idpath.
Defined.

Definition total2_idpath
  {X : UU} {Y : X -> UU} (x : total2 Y)
    : total2_paths (idpath (pr1 x)) (idpath (pr2 x)) = idpath x. 
Proof.
  destruct x.
  apply idpath.
Defined.

Definition unget_nat
  {C D : hs_precategory} {F G : D ^^ C}
  (u : nat_trans (get_funct F) (get_funct G))
    : F ==> G
:= u.



(* 

f :a --> b, g g' : b --> c, p : g = g', want f;;g = f;;g', take idtoiso
and get f;;g ==> f;;g' = lwhisk idtoiso p.

*)

Lemma lwhisk_iso
  {C : pre2cat_1data} {a b c : C}
  (f : a --> b) {g g' : b --> c} (v : iso g g')
     : iso (mcomp f g) (mcomp f g'). 
Proof. 
  apply (tpair _ (lwhisk f v)).
  apply (is_iso_qinv _ (lwhisk f (inv_from_iso v) )). 
  split.
  - pathvia (lwhisk f (v ;; inv_from_iso v)). 
    apply pathsinv0.
    apply functor_comp.
    set (H := maponpaths (lwhisk f) (iso_inv_after_iso v)).
    pathvia (lwhisk f (identity g)).
    apply H.
    apply functor_id.
  - pathvia (lwhisk f (inv_from_iso v ;; v)). 
    apply pathsinv0.
    apply functor_comp.
    set (H := maponpaths (lwhisk f) (iso_after_iso_inv v)).
    pathvia (lwhisk f (identity g')).
    apply H.
    apply functor_id.
Defined.


Definition eq_lwhisk
  {C : pre2cat_1data} {a b c : C}
  (f : a --> b) {g g' : b --> c} (p : g = g')
    : mcomp f g = mcomp f g'
:= maponpaths (mcomp f) p.

Lemma idtoiso_eq_lwhisk
  {C : pre2cat_1data} {a b c : C}
  (f : a --> b) {g g' : b --> c} (p : g = g')
     : lwhisk f (idtoiso p) = idtoiso (eq_lwhisk f p). 
Proof.
  destruct p.
  apply functor_id.
Defined.

(* there is absolutely no reeason why I should need this *)

Definition idtoiso_massoc_on_ob_simpl
  {A B C D : hsprecat_1data} 
  (F : A --> B) (G : B --> C) 
  {H H' : C --> D} (w : H ==> H')
  (a : pr1 A)
    : functor_eq_ob_eq (hsprecat_str_massoc A B C D F G H') a 
       = idpath (pr1 H' (pr1 G (pr1 F a))).
Proof. 
  unfold functor_eq_ob_eq.
  simpl. 
  unfold hsprecat_str_massoc.
  unfold hsprecat_ob_assoc.
  simpl total2_paths.           
  unfold maponpaths.
  unfold functor_eq.
  simpl total2_paths.  

Definition idtoiso_massoc_simpl
  {A B C D : hsprecat_1data} 
  (F : A --> B) (G : B --> C) 
  {H H' : C --> D} (w : H ==> H')
  (a : pr1 A)
    : # (pr1 H') (identity (pr1 G (pr1 F a))) 
      = get_nat (idtoiso (hsprecat_str_massoc A B C D F G H')) a.
Proof.
  pathvia (identity (pr1 H' (pr1 G (pr1 F a)))).
  apply functor_id.
  unfold get_nat.
  set (ascH' := (hsprecat_str_massoc A B C D F G H')).

  set (S := (pr2 (pr1 (idtoiso ascH' )))).
  unfold is_nat_trans in S.
  set (T := S a a (identity a)).
  simpl in T. 
  

  Check (idtoiso (functor_eq_ob_eq ascH' a)).
  pathvia (pr1 (idtoiso (functor_eq_ob_eq ascH' a))).
    Focus 2.
    unfold functor_eq_ob_eq.
    apply (!( idtoiso_nat_commute ascH' a)).
  (*
  set (S := (pr2 (pr1 (idtoiso ascH' )))).
  unfold is_nat_trans in S.
  set (T := S a a (identity a)).
  *)


  (* there should be a less ugly way of doing this with pathscomp0 or
     something *)
  pathvia (transportf _
         (functor_eq_ob_eq ascH' a)
         (identity ((get_funct (mcomp (mcomp F G) H')) a))).
    Focus 2.
    apply (! idtoiso_id2 _ _ _ (functor_eq_ob_eq ascH' a)).
  simpl.
  unfold functor_eq_ob_eq.

  Check functtransportf.
  set (f := fun F' : D ^^ (get_precat A) => (get_funct F' a)).
  set (P := hom (pr1 D) (pr1 H' (pr1 G (pr1 F a)))). 
  set (R := functtransportf f P ascH'
        (identity (pr1 H' (pr1 G (pr1 F a))))).
  pathvia (transportf (fun x : D ^^ (get_precat A) => P (f x)) ascH'
        (identity (pr1 H' (pr1 G (pr1 F a))))).
    Focus 2.             
    apply R.
  simpl.
  unfold P.
  unfold f.
  unfold get_funct.
    

  unfold ascH'.
  unfold hsprecat_str_massoc. 
  unfold hsprecat_ob_assoc.
  unfold get_funct.
  unfold P.
  unfold f.

 Abort.
 
Definition hsprecat_llwhiskassoc
  (A B C D : hsprecat_1data)
  : pre2cat_llwhisk_assoc_type (hsprecat_massoc A B C D).
Proof.
  (* unfold everything and turn this into something familiar and simplify *)
  intros F G H H' w.
  set (ascH := (hsprecat_str_massoc A B C D F G H)).
  set (ascH' := (hsprecat_str_massoc A B C D F G H')).
  unfold hsprecat_massoc.
  unfold lwhisk.
  simpl. 
  (* fold ascH. fold ascH'. *)
  apply nat_trans_eq.
  apply get_hs.
  intro a.
  simpl.  
  (*
  set (s := pr2(pr1 (idtoiso (hsprecat_str_massoc A B C D F G H)))).
  unfold is_nat_trans in s.  
  *)
  set (t := pr2 w).
  unfold is_nat_trans in t.
  set (T := ! (t  (pr1 G (pr1 F a)) (pr1 G (pr1 F a))
                  (identity (pr1 G (pr1 F a))))).
  (*  assert (get_nat (idtoiso (hsprecat_str_massoc A B C D F G H')) a
           = # (pr1 H') (identity (pr1 G (pr1 F a)))).
  *)

  (* pull [a] into [idtoiso] so we can turn them into transports *)
  pathvia (idtoiso (functor_eq_ob_eq ascH a) ;; pr1 w (pr1 G (pr1 F a))).
    Focus 2.  
    rewrite (! idtoiso_nat_commute ascH a).
    apply idpath.
  pathvia (pr1 w (pr1 G (pr1 F a)) ;; (idtoiso (functor_eq_ob_eq ascH' a))).
    rewrite (! idtoiso_nat_commute ascH' a).
    apply idpath.

  rewrite idtoiso_postcompose.
  rewrite idtoiso_precompose2.

  unfold functor_eq_ob_eq.
  set (f := fun F' : D ^^ (get_precat A) => (get_funct F' a)).
  set (P := fun b : (pr1 D) => (pr1 H) ((pr1 G) ((pr1 F) a)) ==> b).
  set (R := functtransportf f P ascH' (pr1 w ((pr1 G) ((pr1 F) a)))).
  pathvia (transportf (fun x => P (f x)) 
       ascH'  (pr1 w ((pr1 G) ((pr1 F) a)))).
  apply (!R).  

  set (f' := 

  unfold ascH'.  
  unfold hsprecat_str_massoc.    
  simpl.

Definition hsprecat_2data
  : str_pre2cat_2data.
Proof.
  apply (tpair _ hsprecat_1data).
  split.
    
(*
Definition terminal_pre2cat_ob_mor
  unfold pre2cat_ob_mor.
  apply (pre2cat_ob_mor_pair terminal_cat).
  intros x y.
  unfold hs_precategory.
  Check terminal_cat.
  apply (tpair _ (precategory_data_from_precategory terminal_cat)).
  split.
  - split. 
    + split.
      * intros a b f.
        destruct (identity a ;; f).
        destruct f.
        apply idpath.
      * intros a b f.
        destruct (identity a ;; f).
        destruct f.
        apply idpath.
    + intros a b c d f g h.
      destruct (f ;; (g ;; h)).
      destruct ((f ;; g );; h).
      apply idpath.
  - set (H := pr2 (pr2 terminal_cat)).
    apply H.
Defined.
*)


(*
*** Local Variables: ***
*** coq-prog-name: "/home/daniel/UniMath/sub/coq/bin/coqtop" ***
*** coq-prog-args: ("-emacs" "-indices-matter" "-type-in-type" "-R" "/home/daniel/UniMath/UniMath/" "UniMath") ***
*** End:***
*)
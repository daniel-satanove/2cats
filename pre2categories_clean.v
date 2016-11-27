Add Rec LoadPath "/home/daniel/UniMath/UniMath" as UniMath.

Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.

Require Import RezkCompletion.precategories.
Require Import RezkCompletion.functors_transformations.

Load p2cMisc.

Local Notation "a ==> b" := (precategory_morphisms a b) (at level 50).
(* Local Notation "'hom' a b" := (precategory_morphisms a b) (at level 2). *)
Local Notation "f ;; g" := (compose f g) (at level 50, format "f  ;;  g").

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "D ^^ C" := (hs_funct_precat C D) (at level 2).
Local Notation "[ C , D ]'" := (funct_cat C D) (at level 2).

(** This is "already defined," I think in the Load?
Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).
**)





(* nested sigma definition of a 2-precategory this closely mirrors the
   precategories.v file 
    
   pre2cat_ob_mor
   - objects
   - morphisms

   pre2cat_1data
   - composition
   - identity

   pre2cat_2data
   - associativity
   - right unitor
   - left unitor

   pre2category
   - pentagon
   - unitor triangle

*)

(* objects and hom categories *)
Definition pre2cat_ob_mor
:= total2(fun C : UU => C -> C -> hs_precategory).

(* function for constructing an ob mor pair *)
Definition pre2cat_ob_mor_pair
  (C : UU) (mor : C -> C -> hs_precategory)
    : pre2cat_ob_mor
:= tpair _ C mor.

(* one of several coercier functions so that we can consider C as its
   type of objects as well as a category, so we can do things like a : C
   without resorting to something like a : ob C *)
Definition pre2cat_ob_mor_to_UU_coercer
  : pre2cat_ob_mor -> UU
:= fun C => @pr1 _ _ C.
Coercion pre2cat_ob_mor_to_UU_coercer : pre2cat_ob_mor >-> UU.

Definition homc
  {C : pre2cat_ob_mor} 
    : C -> C -> hs_precategory 
:= pr2 C.

Local Notation "a --> b" := (homc a b) (at level 50).

(*
Local Notation "'homc' C" := (pre2cat_hom (C := C)) (at level 2).
*)

Definition pre2cat_id
  (C : pre2cat_ob_mor)
:= forall a : C, (a --> a) ^^ terminal_cat.

Definition pre2cat_comp
  (C : pre2cat_ob_mor)
:= forall a b c : C, ((a --> c) ^^ (b --> c)) ^^ (a --> b).

Definition pre2cat_1data 
:= total2 (fun C => dirprod (pre2cat_id C) (pre2cat_comp C)).

Definition pre2cat_1data_to_ob_mor_coercer
  (C : pre2cat_1data)
    : pre2cat_ob_mor
:= pr1 C.
Coercion pre2cat_1data_to_ob_mor_coercer 
  : pre2cat_1data >-> pre2cat_ob_mor.

Definition pre2cat_1data_pair
  (C : pre2cat_ob_mor)
  (id : forall a : C, (a --> a) ^^ terminal_cat)
  (comp : forall a b c : C, ((a --> c) ^^ (b --> c)) ^^ (a --> b))
    : pre2cat_1data
:= tpair _ C (dirprodpair id comp).


(* lemmas for the id functor *)

Definition pre2cat_id_from_1data
  (C : pre2cat_1data)
    : pre2cat_id C
:= pr1 (pr2 C).

Definition id_funct
  {C : pre2cat_1data} {a : C}
    : functor terminal_cat (a --> a).
Proof.
  apply (pre2cat_id_from_1data C a).
Defined.

Definition id_funct_cat
  {C : pre2cat_1data} (a : C)
    : (a --> a) ^^ terminal_cat.
Proof.
  apply (pre2cat_id_from_1data C a).
Defined.

Definition id_functor
  {C : pre2cat_1data} (a : C)
    : functor terminal_cat (a --> a).
Proof.
  apply (pre2cat_id_from_1data C a).
Defined.

Definition id_mor
  {C : pre2cat_1data}
    : forall a : C, (a --> a).
Proof.
  intro a.
  apply (id_funct tt).
Defined.  

(* lemmas for the comp functor *)

Definition pre2cat_comp_from_1data
  (C : pre2cat_1data)
    : pre2cat_comp C
:= pr2 (pr2 C).

Definition comp_funct
  {C : pre2cat_1data} {a b c : C}
    : functor (a --> b) ((a --> c) ^^ (b --> c)).
Proof.
  apply (pre2cat_comp_from_1data C a b c).
Defined.

Definition comp_functor
  {C : pre2cat_1data} (a b c : C)
    : functor (a --> b) ((a --> c) ^^ (b --> c)).
Proof.
  apply (pre2cat_comp_from_1data C a b c).
Defined.

Definition mcomp
  {C : pre2cat_1data} {a b c : C}
    : (a --> b) -> (b --> c) -> (a --> c).
Proof.
  intros f g.
  apply (get_funct (comp_funct f) g).
Defined.

Definition lwhisk
  {C : pre2cat_1data} {a b c : C} {g g' : b --> c}
  (f : a --> b) (v : g ==> g')
    : mcomp f g ==> mcomp f g'.
Proof.
  apply (# (get_funct (comp_funct f))).
  apply v.
Defined.

Definition rwhisk
  {C : pre2cat_1data} {a b c : C} {f f' : a --> b}
  (u : f ==> f') (g  : b --> c)
    : mcomp f g ==> mcomp f' g.
Proof.
  (* why does this take so long? *)
  apply (# comp_funct u).
Defined.

(*
Definition vcomp
  {C : pre2cat_1data} {a b : C} {f g h : a --> b}
    : f ==> g -> g ==> h -> f ==> h. 
Proof.
  intros u v.
  apply (u ;; v).
Defined.
*)

(* pre2cat_2data *)


(* associativity *)

(* composition of 3 arrows functor, brackets on the left *)
Definition comp3_left
  {C : pre2cat_1data} (a b c d: C)
    : (((a --> d) ^^ (c --> d)) ^^ (b --> c)) ^^ (a --> b)
:= functor_composite _ _ _ (comp_functor a b c)
                           (funct_postcomp (b --> c) (comp_functor a c d)).

(* composition of 3 arrows functor, brackets on the right *)
Definition comp3_right
  {C : pre2cat_1data} (a b c d: C)
    : (((a --> d) ^^ (c --> d)) ^^ (b --> c)) ^^ (a --> b).
Proof.
  apply funct_arg_swap.
  apply (funct_postcomp _ funct_arg_swap). 
  apply (functor_composite _ ((b --> d) ^^ (c --> d)) _).
  apply (comp_functor b c d).
  apply funct_postcomp.
  apply funct_arg_swap.
  apply (comp_functor a b d).
Defined.

(* these two are sanity checks, not sure if they are needed later *)
Definition comp3_is_mcomp_left
  {C : pre2cat_1data} {a b c d : C}
  (f : a --> b) (g : b --> c) (h : c --> d)
    : tget_funct (comp3_left a b c d) f g h 
         = mcomp (mcomp f g) h.
Proof.
  simpl.                            
  apply idpath.
Defined.

Definition comp3_is_mcomp_right
  {C : pre2cat_1data} {a b c d : C}
  (f : a --> b) (g : b --> c) (h : c --> d)
    : tget_funct (comp3_right a b c d) f g h 
         = mcomp f (mcomp g h). 
Proof.
  simpl.                            
  apply idpath.
Defined.

Definition pre2cat_assoc
  (C : pre2cat_1data) 
:= forall a b c d : C, iso (comp3_left a b c d) (comp3_right a b c d).

(*
Definition pre2cat_str_assoc
  (C : pre2cat_1data)
:= forall a b c d : C, comp3_left a b c d = comp3_right a b c d. 

(* this will be used later to get a weak pre2cat from a strict one *)
Definition pre2cat_weaken_assoc
  (C : pre2cat_1data)
    : pre2cat_str_assoc C -> pre2cat_assoc C.
Proof. 
  intro p.
  intros a b c d.  
  apply idtoiso.
  apply p.
Defined.
*)

(* right and left unitors *)

(* compose with id functor on the right *)
Definition pre2cat_rcomp_unit
  {C : pre2cat_1data}  (a b : C)
    : ((a --> b) ^^ (a --> b)) ^^ terminal_cat.
Proof.
  apply (functor_composite _ (a --> a) _).
  apply (id_functor a).
  apply (comp_functor a a b).
Defined.

(* compose with id functor on the left *)
Definition pre2cat_lcomp_unit
  {C : pre2cat_1data}  (a b : C)
    : ((a --> b) ^^ (a --> b)) ^^ terminal_cat.
Proof.
  apply (functor_composite _ (b --> b) _).
  apply (id_functor b).
  apply funct_arg_swap.
  apply (comp_functor a b b).
Defined.

(* identity on (a --> b) *)
Definition pre2cat_id_on_homcat 
  {C : pre2cat_1data}  (a b : C)
    : ((a --> b) ^^ (a --> b)) ^^ terminal_cat.
Proof.
  apply terminal_cat_functors.
  intro x.
  apply (functor_identity).      
Defined.

(* identity on the right cancels *)
Definition pre2cat_runitor
  (C : pre2cat_1data) 
:= forall a b : C, iso (pre2cat_rcomp_unit a b)
                       (pre2cat_id_on_homcat a b). 

(* identity on the left cancels *)
Definition pre2cat_lunitor
  (C : pre2cat_1data) 
:= forall a b : C, iso (pre2cat_lcomp_unit a b)
                       (pre2cat_id_on_homcat a b). 

(*
Definition pre2cat_str_runitor
  (C : pre2cat_1data) 
:= forall a b : C, (pre2cat_rcomp_unit a b) = (pre2cat_id_on_homcat a b). 

Definition pre2cat_str_lunitor
  (C : pre2cat_1data) 
:= forall a b : C, (pre2cat_lcomp_unit a b) = (pre2cat_id_on_homcat a b). 

Definition pre2cat_weaken_runitor
  (C : pre2cat_1data)
    : pre2cat_str_runitor C -> pre2cat_runitor C.
Proof.
  intros p a b.
  apply idtoiso.
  apply p.
Defined.

Definition pre2cat_weaken_lunitor
  (C : pre2cat_1data)
    : pre2cat_str_lunitor C -> pre2cat_lunitor C.
Proof.
  intros p a b.
  apply idtoiso.
  apply p.
Defined.
*)

Definition pre2cat_2data
:= total2(fun C : pre2cat_1data => dirprod (pre2cat_assoc C)
                                     (dirprod (pre2cat_runitor C)
                                              (pre2cat_lunitor C))).  

Definition pre2cat_2data_to_1data_coercer
  (C : pre2cat_2data)
    : pre2cat_1data
:= pr1 C.
Coercion pre2cat_2data_to_1data_coercer 
  : pre2cat_2data >-> pre2cat_1data.

(*
Definition str_pre2cat_2data
:= total2( fun C : pre2cat_1data => dirprod (pre2cat_str_assoc C)
                                      (dirprod (pre2cat_str_runitor C)
                                               (pre2cat_str_lunitor C))).

(* sends assoc and unitor equalities to idtoiso fo them *)
Definition str_pre2cat_weaken_2data
  (C : str_pre2cat_2data)
    : pre2cat_2data.
Proof.
  apply (tpair _ (pr1 C)).
  split.
  apply (pre2cat_weaken_assoc (pr1 C)).
  apply (pr1 (pr2 C)).
  split.
  apply (pre2cat_weaken_runitor (pr1 C)). 
  apply (pr1 (pr2 (pr2 C))).
  apply (pre2cat_weaken_lunitor (pr1 C)). 
  apply (pr2 (pr2 (pr2 C))).
Defined.
Coercion str_pre2cat_weaken_2data
  : str_pre2cat_2data >-> pre2cat_2data.
*)

Definition comp_funct_assoc
  (C : pre2cat_2data)
:= pr1 (pr2 C). 

(* associativity on morphisms *)
Definition massoc
  {C : pre2cat_2data} {a b c d : C} 
    : forall (f : a --> b) (g : b --> c) (h : c --> d),
     iso (mcomp (mcomp f g) h) (mcomp f (mcomp g h)).
Proof.
  intros f g h.
  assert (M : iso
         (tget_funct (comp3_left a b c d) f g h)
         (tget_funct (comp3_right a b c d) f g h)).
  apply (functor_pointwise_iso_from_iso  
          (functor_pointwise_iso_from_iso 
            (functor_pointwise_iso_from_iso (comp_funct_assoc C a b c d) f)
           g)).
  rewrite comp3_is_mcomp_left in M.
  rewrite comp3_is_mcomp_right in M.
  apply M.
Defined.

(*
Definition str_massoc
  {C : str_pre2cat_2data} {a b c d : C}
    : forall (f : a --> b) (g : b --> c) (h : c --> d),
     (mcomp (mcomp f g) h) = (mcomp f (mcomp g h)).
Proof.
  intros f g h.
  set (p := (pr1 (pr2 C))).
  apply ((maponpaths (fun F => tget_funct F f g h)) (p a b c d)).
Defined.
*)


(* pentagon *)

(* This is the two-side path of the pentagon which is simpler since it only
   uses bare massoc *)
Definition pre2cat_pentagon1
  {C : pre2cat_2data} {a b c d e : C}
    : forall (f : a --> b) (g : b --> c) (h : c --> d) (k : d --> e),
        iso (mcomp (mcomp (mcomp f g) h) k) (mcomp f (mcomp g (mcomp h k))).
Proof.
  intros f g h k.
  (* (((fg)h)k) -~> ((fg)(hk)) *)
  apply (iso_comp_via (mcomp (mcomp f g) (mcomp h k))).   
  apply (massoc (mcomp f g) h k).
  (* ((fg)(hk)) -~> (f(g(hk))) *)
  apply (massoc f g (mcomp h k)).
Defined.

(* this is the three-side path. There is implicitly some whiskering going on,
   but it would be more work to prove that whiskering of an iso is an iso.
   If one were to prove that, looking at this lemma would be a good place to
   start. *)
Definition pre2cat_pentagon2
  {C : pre2cat_2data} {a b c d e : C}
    : forall f : (a --> b),
      forall g : (b --> c),
      forall h : (c --> d),
      forall k : (d --> e),
        iso (mcomp (mcomp (mcomp f g) h) k) (mcomp f (mcomp g (mcomp h k))).
Proof.
  intros f g h k.
  (* (((fg)h)k) -~> ((f(gh))k) *)
  apply (iso_comp_via (mcomp (mcomp f (mcomp g h)) k)).
  - (* we prove this by proving that the comp functor applied to the iso massoc
       is an iso *)
    assert (H : @iso ((a --> e) ^^ (d --> e)) (comp_funct (mcomp (mcomp f g) h))
                                            (comp_funct (mcomp f (mcomp g h)))).
    + apply (functor_on_iso _ _ _ _ _ (massoc f g h)).
    + apply (functor_pointwise_iso_from_iso H).
  - (* ((f(gh))k) -~> (f((gh)k)) *) 
    apply (iso_comp_via (mcomp f (mcomp (mcomp g h) k))).
    + apply (massoc f (mcomp g h) k).
    + (* (f((gh)k)) -~> (f(g(hk))) *) 
      apply (functor_on_iso _ _ _ _ _ (massoc g h k)). 
Defined.

Definition pre2cat_pentagon
  (C : pre2cat_2data)
:= forall (a b c d e : C) 
          (f : a --> b) (g : b --> c) (h : c --> d) (k : d --> e),
     pre2cat_pentagon1 f g h k = pre2cat_pentagon2 f g h k.


(* unitor triangle *)

(* this is a rather different style of proof. Are there drawbacks to it? *)
Definition mrunit
  {C : pre2cat_2data} {a b: C}
  (f : a --> b) 
    : iso (mcomp (id_mor a) f) f.
Proof.
  set (runit := (pr1 (pr2 (pr2 C)))).  
  set (runitab := runit a b).
  set (H := (functor_pointwise_iso_from_iso runitab) tt).
  set (J := (functor_pointwise_iso_from_iso H) f).
  apply J.
Defined.

Definition mlunit
  {C : pre2cat_2data} {a b: C}
  (f : a --> b) 
    : iso (mcomp f (id_mor b)) f.
Proof.
  set (lunitab := (pr2 (pr2 (pr2 C))) a b).  
  set (H := (functor_pointwise_iso_from_iso 
              ((functor_pointwise_iso_from_iso lunitab) tt) f)).
  apply H.
Defined.

Definition pre2cat_unitriangle1
  (C : pre2cat_2data) {a b c: C}
  (f : a --> b) (g : b --> c)
    : iso (mcomp (mcomp f (id_mor b)) g) (mcomp f g). 
Proof.
  assert (H : @iso ((a --> c) ^^ (b --> c)) (comp_funct (mcomp f (id_mor b))) 
                                            (comp_funct f )).
  apply (functor_on_iso _ _ _ _ _ (mlunit f)). 
  apply (functor_pointwise_iso_from_iso H).
Defined.

Definition pre2cat_unitriangle2
  (C : pre2cat_2data) {a b c: C}
  (f : a --> b) (g : b --> c)
    : iso (mcomp (mcomp f (id_mor b)) g) (mcomp f g). 
Proof.
  apply (iso_comp_via (mcomp f (mcomp (id_mor b) g))).
  - apply massoc.
  - apply (functor_on_iso _ _ _ _ _ (mrunit g)). 
Defined.

Definition pre2cat_unitriangle
  (C : pre2cat_2data) 
:= forall (a b c: C) (f : a --> b) (g : b --> c),
     pre2cat_unitriangle1 C f g = pre2cat_unitriangle2 C f g.

(* main definitions *)

Definition pre2cats
:= total2(fun C : pre2cat_2data => dirprod (pre2cat_pentagon C)
                                           (pre2cat_unitriangle C)).

(*
Definition str_pre2cats
:= total2(fun C : str_pre2cat_2data => dirprod (pre2cat_pentagon C)
                                           (pre2cat_unitriangle C)).
*)

Definition pre2cats_to_pre2cat_2data_coercer
  : pre2cats -> pre2cat_2data
:= pr1.
Coercion pre2cats_to_pre2cat_2data_coercer 
  : pre2cats >-> pre2cat_2data.

(*
Definition str_pre2cats_weaken
  : str_pre2cats -> pre2cats.
Proof.
  intro C.
  (* why doesn't the coercion work? *)
  apply (tpair _ (str_pre2cat_weaken_2data (pr1 C))).
  split.
  apply (pr1 (pr2 C)).
  apply (pr2 (pr2 C)).
Defined.
Coercion str_pre2cats_weaken 
  : str_pre2cats >-> pre2cats.
*)

(* construction lemmas *)

(* assoc *)


(* the following four definitions are to make the later lemmas shorter *)
Definition pre2cat_massoc_type
  {C : pre2cat_1data} (a b c d : C) 
:= forall f : a --> b,
   forall g : b --> c,
   forall h : c --> d,
     iso (mcomp (mcomp f g) h) (mcomp f (mcomp g h)).

Definition pre2cat_llwhisk_assoc_type
  {C : pre2cat_1data} {a b c d : C} 
  (asc : pre2cat_massoc_type a b c d)
:= forall (f : a --> b) (g : b --> c) 
          (h h' : c --> d) (w : h ==> h'),
            lwhisk (mcomp f g) w ;; asc f g h' 
              = asc f g h ;; lwhisk f (lwhisk g w).

Definition pre2cat_lrwhisk_assoc_type
  {C : pre2cat_1data} {a b c d : C} 
  (asc : pre2cat_massoc_type a b c d)
:= forall (f : a --> b) 
          (g g' : b --> c) (v : g ==> g')
          (h : c --> d), 
            rwhisk (lwhisk f v) h ;; asc f g' h 
              = asc f g h ;; lwhisk f (rwhisk v h).

Definition pre2cat_rrwhisk_assoc_type
  {C : pre2cat_1data} {a b c d : C} 
  (asc : pre2cat_massoc_type a b c d)
:= forall (f f': a --> b) (u : f ==> f')
          (g : b --> c) (h : c --> d), 
            rwhisk (rwhisk u g) h ;; asc f' g h 
              = asc f g h ;; rwhisk u (mcomp g h).


(* we construct the assoc constructor iteratively, removing arguments *)
Definition pre2cat_assoc_constructor1
  {C : pre2cat_1data}
  {a b c d : C} 
  (asc : pre2cat_massoc_type a b c d) 
  (ll : pre2cat_llwhisk_assoc_type asc)
    : forall f : a --> b,
      forall g : b --> c,
         (dget_funct (comp3_left a b c d) f g)  
           ==> (dget_funct (comp3_right a b c d) f g).
Proof.
  intros f g.
  apply mor_to_nat_trans.
  unfold dget_funct; unfold get_funct.
  set (H := (asc f g)).
  apply (tpair _ (fun h : c --> d => (pr1 (asc f g h)) )).
  intros h h' w.
  apply ll.
Defined.

(*
Definition pre2cat_assoc_constructor1'
  {C : pre2cat_1data}
  {a b c d : C} 
  (asc : pre2cat_massoc_type a b c d) 
  (ll : pre2cat_llwhisk_assoc_type asc)
    : forall f : a --> b,
      forall g : b --> c,
         iso (dget_funct (comp3_left a b c d) f g)  
             (dget_funct (comp3_right a b c d) f g).
Proof.
  intros f g. 
  set (H := (pre2cat_assoc_constructor1 asc ll f g)).
  apply (functor_iso_from_pointwise_iso _ _ _ _ _ H).
  intro h.
  apply (pr2 (asc f g h)).
Defined.
*)

Definition pre2cat_assoc_constructor2
  {C : pre2cat_1data}
  {a b c d : C} 
  (asc : pre2cat_massoc_type a b c d) 
  (ll : pre2cat_llwhisk_assoc_type asc)
  (lr : pre2cat_lrwhisk_assoc_type asc)
    : forall f : a --> b,
        get_funct (comp3_left a b c d) f  
           ==> get_funct (comp3_right a b c d) f.
Proof.
  intro f; unfold get_funct.
  apply mor_to_nat_trans.
  apply (tpair _ (pre2cat_assoc_constructor1 asc ll f)).
  intros g g' v; simpl.
  apply nat_trans_eq.
  apply get_hs.
  intro h.
  simpl.
  apply lr.   
  (* why does this take so long? *)
Defined.

(*
Definition pre2cat_assoc_constructor2'
  {C : pre2cat_1data}
  {a b c d : C} 
  (asc : pre2cat_massoc_type a b c d) 
  (ll : pre2cat_llwhisk_assoc_type asc)
  (lr : pre2cat_lrwhisk_assoc_type asc)
    : forall f : a --> b,
        iso (get_funct (comp3_left a b c d) f)
            (get_funct (comp3_right a b c d) f).
Proof.
  intro f; unfold get_funct.
  set (H := (pre2cat_assoc_constructor2 asc ll lr f)); 
  unfold get_funct in H.
  apply (functor_iso_from_pointwise_iso _ _ _ _ _ H).
  intro g.
  apply (functor_iso_if_pointwise_iso _ _ _ _ _ ).  
  intro h.
  apply (pr2 (asc f g h)).
Defined.
*)

Definition pre2cat_assoc_constructor3
  {C : pre2cat_1data} {a b c d : C} 
  (asc : pre2cat_massoc_type a b c d) 
  (ll : pre2cat_llwhisk_assoc_type asc)
  (lr : pre2cat_lrwhisk_assoc_type asc)
  (rr : pre2cat_rrwhisk_assoc_type asc)
   : comp3_left a b c d ==> comp3_right a b c d. 
Proof.
  apply mor_to_nat_trans.
  unfold get_funct.
  apply (tpair _ (pre2cat_assoc_constructor2 asc ll lr)).
  intros f f' u.
  apply nat_trans_eq.
  apply get_hs.
  intro g.
  apply nat_trans_eq.
  apply get_hs.
  intro h.
  apply rr. (* slow *)
Defined.

Definition pre2cat_assoc_constructor
  {C : pre2cat_1data} (a b c d : C) 
  (asc : pre2cat_massoc_type a b c d) 
  (ll : pre2cat_llwhisk_assoc_type asc)
  (lr : pre2cat_lrwhisk_assoc_type asc)
  (rr : pre2cat_rrwhisk_assoc_type asc)
   : iso (comp3_left a b c d) (comp3_right a b c d).
Proof.
  set (H := (pre2cat_assoc_constructor3 asc ll lr rr)).
  apply (functor_iso_from_pointwise_iso _ _ _ _ _ H).
  intro f.
  apply (functor_iso_if_pointwise_iso _ _ _ _ _ ).  
  intro g.
  apply (functor_iso_if_pointwise_iso _ _ _ _ _ ).  
  intro h.
  apply (pr2 (asc f g h)).
Defined.

Definition pre2cat_assoc_constructor'
  {C : pre2cat_1data} 
  (asc : forall a b c d : C, pre2cat_massoc_type a b c d) 
  (ll : forall a b c d : C, pre2cat_llwhisk_assoc_type (asc a b c d))
  (lr : forall a b c d : C, pre2cat_lrwhisk_assoc_type (asc a b c d))
  (rr : forall a b c d : C, pre2cat_rrwhisk_assoc_type (asc a b c d))
   : forall a b c d : C, iso (comp3_left a b c d) (comp3_right a b c d).
Proof.
  intros a b c d.
  set (H := (pre2cat_assoc_constructor3 (asc a b c d) 
                                        (ll a b c d)
                                        (lr a b c d)
                                        (rr a b c d))).
  apply (functor_iso_from_pointwise_iso _ _ _ _ _ H).
  intro f.
  apply (functor_iso_if_pointwise_iso _ _ _ _ _ ).  
  intro g.
  apply (functor_iso_if_pointwise_iso _ _ _ _ _ ).  
  intro h.
  apply (pr2 (asc a b c d f g h)).
Defined.

(* unitor constructors *)

Definition pre2cat_mrunitor_type
  (C : pre2cat_1data) 
:= forall (a b : C) (f : a --> b), iso (mcomp (id_mor a) f) f.
          
Definition pre2cat_lwhisk_unit_type
  {C : pre2cat_1data}
  (runit : pre2cat_mrunitor_type C)
:= forall (a b : C) (f f': a --> b) (u : f ==> f'),
      lwhisk (id_mor a) u ;; runit a b f' = runit a b f ;; u. 

           
Definition pre2cat_runitor_constructor1
  {C : pre2cat_1data} 
  (runit : pre2cat_mrunitor_type C) 
  (lwsku : pre2cat_lwhisk_unit_type runit)
    : forall (a b : C) (x : terminal_cat),
           get_funct (pre2cat_rcomp_unit a b) x  
             ==> get_funct (pre2cat_id_on_homcat a b) x.
Proof. 
  intros a b.
  intro x; destruct x.
  apply mor_to_nat_trans; unfold get_funct.
  apply (tpair _ (fun f => pr1 (runit a b f))).
  intros g h u.
  simpl.
  apply (lwsku a b g h u).
Defined.

Definition terminal_cat_mor_is_id
  {a : terminal_cat} (f : a ==> a) 
    :  f = identity a. 
Proof.
  destruct f.
  destruct (identity a).
  apply idpath.
Defined.


Definition pre2cat_runitor_constructor2
  {C : pre2cat_1data} 
  (runit : pre2cat_mrunitor_type C) 
  (lwsku : pre2cat_lwhisk_unit_type runit)
    : forall a b : C, (pre2cat_rcomp_unit a b) ==> (pre2cat_id_on_homcat a b).
Proof.
  intros a b.
  apply mor_to_nat_trans; unfold get_funct.
  apply (tpair _ ((pre2cat_runitor_constructor1 runit lwsku) a b)).
  intros x y u.
  apply nat_trans_eq.
  apply get_hs.
  intro f.
  destruct x, y.
  simpl.
  rewrite (terminal_cat_mor_is_id u).
  
  pathvia (identity (mcomp (id_mor a) f) ;; (pr1 (runit a b f))).
  - apply (maponpaths (fun u => u ;; (pr1 (runit a b f)))).
    (* for some reason this doesn't work if I add in the tt argument to T
       *)
    set (T := functor_id (id_functor a) ).
    rewrite T.
    assert (U : #(comp_functor a a b) (identity ((id_functor a) tt))
                  = identity ((comp_functor a a b) ((id_functor a) tt))).
    apply functor_id.
    pathvia (identity 
              (get_funct ((comp_functor a a b) ((id_functor a) tt)) f)
            ).
    + apply (maponpaths (get_nat)) in U.
      apply (maponpaths 
               (fun F : nat_trans 
         (get_funct ((comp_functor a a b) ((id_functor a) tt)))
         (get_funct ((comp_functor a a b) ((id_functor a) tt)))
                                => F f)) in U. 
      apply U.
    + apply idpath.
  - pathvia (pr1 (runit a b f)).
    apply id_left.
    apply pathsinv0.
    apply id_right.
Defined.

Definition pre2cat_assoc_constructor_exp
  {C : pre2cat_1data} (a b c d : C) 
  (asc : pre2cat_massoc_type a b c d) 
  (ll : pre2cat_llwhisk_assoc_type asc)
  (lr : pre2cat_lrwhisk_assoc_type asc)
  (rr : pre2cat_rrwhisk_assoc_type asc)
   : iso (comp3_left a b c d) (comp3_right a b c d).
Proof.
  set (H := (pre2cat_assoc_constructor3 asc ll lr rr)).
  Check functor_iso_from_pointwise_iso.
  apply (functor_iso_from_pointwise_iso _ _ _ _ _ H).
  intro f.
  Check functor_iso_if_pointwise_iso.
  apply (functor_iso_if_pointwise_iso _ _ _ _ _ ).  
  intro g.
  apply (functor_iso_if_pointwise_iso _ _ _ _ _ ).  
  intro h.
  apply (pr2 (asc f g h)).
Defined.


Definition pre2cat_runitor_constructor
  {C : pre2cat_1data} 
  (runit : forall (a b : C) (f : a --> b), iso (mcomp (id_mor a) f) f)
  (lwsku : pre2cat_lwhisk_unit_type runit)
    : pre2cat_runitor C.
Proof.
  intros a b.
  apply (functor_iso_from_pointwise_iso _ _ _ _ _
           ((pre2cat_runitor_constructor2 runit lwsku) a b)).
  intro x.
  apply (functor_iso_if_pointwise_iso _ _ _ _ _).
  intro f.
  set (H := pr2 (runit a b f)).
  Check (H f).
  apply (H f). 

  simpl in H.
  unfold pre2cat_runitor_constructor2.
  apply H.


  apply (tpair _ ((pre2cat_runitor_constructor2 runit lwsku) a b)).
  

  Check functor_pointwise_iso_from_iso.

   
  set (H := (functor_pointwise_iso_from_iso runit a b) tt).
  set (J := (functor_pointwise_iso_from_iso H) f).
  apply (runit a b).

*)

(*
Definition pre2cat_assoc_strictness1
  (C : pre2cat_2data) 
:= forall a b c d : C, comp3_left a b c d = comp3_right a b c d.  

Definition pre2cat_assoc_strictness2
  {C : pre2cat_2data} 
  (p : pre2cat_assoc_strictness1 C)
:= forall a b c d : C, idtoiso (p a b c d) = compFunctAssoc C a b c d. 

Definition pre2cat_assoc_strictness
  (C : pre2cat_2data)
:= total2(@pre2cat_assoc_strictness2 C).

Definition pre2cat_strict_massoc1
  {C : pre2cat_2data} {a b c d: C}
  (p : pre2cat_assoc_strictness C) 
  (f : a --> b) (g : b --> c) (h : c --> d)
    : mcomp (mcomp f g) h = mcomp f (mcomp g h).
Proof.
  destruct p as [p q].
  apply ((maponpaths (fun F => tget_funct F f g h)) (p a b c d)).
Defined.

Definition pre2cat_strict_massoc2
  {C : pre2cat_2data} {a b c d: C}
  (p : pre2cat_assoc_strictness C) 
  (f : a --> b) (g : b --> c) (h : c --> d)
    : mcomp (mcomp f g) h = mcomp f (mcomp g h).
Proof.
  destruct p as [p q].
  unfold pre2cat_assoc_strictness1 in p.
  unfold pre2cat_assoc_strictness2 in q.
  set (r := p a b c d).
  assert (s : p a b c d = r).
    apply idpath.
  rewrite s in q.
  destruct (p a b c d).
  apply ((maponpaths (fun F => tget_funct F f g h)) (p a b c d)).
Defined.
*)

(* Theorem pre2cat_assoc_strict_to_weak 
     {C : pre2cat_2data} {a b c d e: C} 
     {f : a --> b} {g : b --> c} {h : c --> d} {k : d --> e} 
     (p : pre2cat_assoc_strictness C) 
       : pre2cat_pentagon f g h k. 
   Proof. 
     unfold pre2cat_pentagon; unfold pre2cat_pentagon1; unfold pre2cat_pentagon2. 
     unfold iso_comp_via. rewrite (pre2cat_strict_massoc p f g h).
     destruct (pre2cat_strict_massoc p f g h).
*)

(*
Definition str_pre2cat_pentagon1
  {C : str_pre2cat} {a b c d e : C}
    : forall (f : a --> b) (g : b --> c) (h : c --> d) (k : d --> e),
        (mcomp (mcomp (mcomp f g) h) k) = (mcomp f (mcomp g (mcomp h k))).
Proof.
  intros f g h k.
  pathvia (mcomp (mcomp f g) (mcomp h k)).   
  apply (str_massoc (mcomp f g) h k).
  apply (str_massoc f g (mcomp h k)).
Defined.

Definition str_pre2cat_pentagon2
  {C : str_pre2cat} {a b c d e : C}
    : forall (f : a --> b) (g : b --> c) (h : c --> d) (k : d --> e),
        (mcomp (mcomp (mcomp f g) h) k) = (mcomp f (mcomp g (mcomp h k))).
Proof.
  intros f g h k.
  pathvia (mcomp (mcomp f (mcomp g h)) k).
  apply (maponpaths (fun x => mcomp x k)  (str_massoc f g h)).
  pathvia (mcomp f (mcomp (mcomp g h) k)).
  apply (str_massoc f (mcomp g h) k).
  apply (maponpaths _ (str_massoc g h k)).
Defined.
*)

(* this all goes earlier *)
(*
Lemma get_funct_idtoiso_commute
  (C : precategory) (D : hs_precategory) 
  (F : D ^^ C)
  (a b : C)
  (p : a = b)
    : #(get_funct F) (pr1 (idtoiso p)) = idtoiso (maponpaths (get_funct F) p). 
Proof.
  destruct p.
  apply functor_id.
Defined.
*)


(*
Lemma get_funct_idtoiso_commute
  {C : precategory} {D : hs_precategory} 
  {F G : D ^^ C}
  (p : F = G)
  (a : C)
    : get_nat (pr1 (idtoiso p)) a 
        = idtoiso (maponpaths (fun F => get_funct F a) p).   
Proof.
  destruct p.
  apply idpath.
Defined.

Lemma tget_funct_idtoiso_commute
  {B C D : precategory} {E : hs_precategory} 
  {F G : ((E ^^ D) ^^ C) ^^ B}
  (p : F = G)
  (b : B) (c : C) (d : D)
    : (get_nat (pr1 (get_nat (pr1 (idtoiso p)) b) c) d)
        = pr1 (idtoiso (maponpaths (fun F => tget_funct F b c d) p)).   
Proof.
  destruct p.
  simpl.
  apply idpath.
Defined.

Lemma functor_on_iso_idtoiso_commute
  {C : precategory} {D : hs_precategory}
  {a b : C}
  (F : D ^^ C)
  (p : a = b) 
    : functor_on_iso _ _ (get_funct F) _ _ (idtoiso p) 
        = idtoiso (maponpaths (get_funct F) p).
Proof.
  destruct p.
  apply eq_iso.
  simpl.
  apply functor_id.
Defined.

Lemma str_pre2cat_massoc_is_idtoiso
  {C : str_pre2cat} {a b c d : C}
  (f : a --> b) (g : b --> c) (h : c --> d) 
    : massoc f g h = idtoiso (str_massoc f g h).
Proof.
  apply eq_iso.
  unfold str_massoc.  
  apply (tget_funct_idtoiso_commute (pr1 (pr2 C) a b c d) f g h). 
Defined.

Lemma idtoiso_concat2
  {C : precategory} {a b c : C} (p : a = b) (q : b = c)
    : iso_comp (idtoiso p) (idtoiso q) = idtoiso (p @ q). 
Proof.
  destruct p.
  simpl.
  apply eq_iso.
  unfold iso_comp.
  simpl.
  apply id_left.
Defined.

Theorem str_pre2cat_pentagon
  (C : str_pre2cat) {a b c d e : C} 
  (f : a --> b) (g : b --> c) (h : c --> d) (k : d --> e) 
    : pre2cat_pentagon (str_pre2cat_weaken_to_2data C) f g h k.
Proof.
  unfold pre2cat_pentagon; unfold pre2cat_pentagon1; unfold pre2cat_pentagon2.
  unfold iso_comp_via.
  rewrite (str_pre2cat_massoc_is_idtoiso (mcomp f g) h k).
  rewrite (str_pre2cat_massoc_is_idtoiso f g (mcomp h k)).
  pathvia (idtoiso ((str_massoc (mcomp f g) h k) 
                     @ (str_massoc f g (mcomp h k)))).
  apply (idtoiso_concat2 _ _).
  rewrite (str_pre2cat_massoc_is_idtoiso g h k).
  rewrite (str_pre2cat_massoc_is_idtoiso f g h).
  rewrite (str_pre2cat_massoc_is_idtoiso f (mcomp g h) k).
  rewrite (functor_on_iso_idtoiso_commute).  
  rewrite (idtoiso_concat2).
  pathvia (iso_comp
            (functor_pointwise_iso_from_iso
               (idtoiso (maponpaths _ (str_massoc f g h))) k)
            (idtoiso
               (str_massoc f (mcomp g h) k @
                maponpaths (get_funct (compFunct f)) (str_massoc g h k)))).
  - 

*)

(*
Definition pre2cat_assoc_strictness1
 (C : pre2cat_1data)
:= @comp3left C = @comp3right C. 

Definition pre2cat_assoc_strictness2
  {C : pre2cat_1data}
  (p : pre2cat_assoc_strictness1 C)
:= u = fun a b c d : C => nat_trans_id (comp3left a b c d). 
*)
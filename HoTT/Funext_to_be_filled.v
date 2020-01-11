Set Universe Polymorphism.

From Coq Require Import ssreflect ssrfun ssrbool.

(*** HoTT definitions *)

(* Definition of dependent sums and projections, with notations *)

Inductive sigT {A:Type} (P:A -> Type) : Type :=
    existT : forall x:A, P x -> sigT P.

Definition π1 {A} {P:A -> Type} (x:sigT P) : A := match x with
                                      | existT _ a _ => a
                                      end.

Definition π2  {A} {P:A -> Type} (x:sigT P) : P (π1 x) :=
  match x return P (π1 x) with
  | existT _ _ h => h
  end.

Notation "{ x : A & P }" := (sigT (A:=A) (fun x => P)) : type_scope.
Notation " ( x ; p ) " := (existT _ x p).

(* identity function and composition *)

Notation id := (fun x => x). 

Notation compose := (fun g f x => g (f x)).

Notation "g ∘ f" := (compose g%function f%function) (at level 1): function_scope.

(* Definition of equality *)

Inductive I (A : Type) (x : A) : A -> Type :=
  refl : I A x x.

Arguments refl {_} _.

Notation "x = y" := (I _ x y): type_scope.

Definition subst (A:Type) (t:A) (P : forall y:A, t = y -> Type)
           (u : A) (p : t = u) (v:P t (refl t)) : P u p :=
  match p with
  | refl _ => v (* : P t (refl t) *)
  end.

(* Check computation behaviour of subst *)

Section subst_computation. 

  Variable A : Type.
  Variable t : A.
  Variable P : forall y:A, t = y -> Type. 
  Variable v : P t (refl t).
  
  Eval cbn in
      subst A t P t (refl t) v.  
  
End subst_computation. 

(* Some omega-groupoid laws on equality *)

Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z.
  rewrite p. exact q.
Defined.

Notation "p @ q" := (concat p q) (at level 20).

Definition inverse {A : Type} {x y : A} (p : x = y) : y = x
    := match p with refl _ => refl _ end.

Notation "p ^" := (inverse p) (at level 3, format "p '^'").

Notation "f == g" := (forall x, f x = g x) (at level 3).

Definition apD10 {A} {B:A->Type} {f g : forall x, B x} (h:f=g)
  : f == g
  := fun x => match h with refl _ => refl _  end.

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with refl _ => u end.

Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing).

Definition concat_p1 A (x y :A) (e: x = y) : e @ refl _ = e.
Proof.
  by elim: e.
Defined. 

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with refl _ => refl _ end.

Definition ap_V {A B : Type} (f : A -> B) {x y : A} (p : x = y) :
  ap f (p^) = (ap f p)^.
Proof.
  by elim: p.
Defined.

Definition concat_Vp {A : Type} {x y : A} (p : x = y) : p^ @ p = refl _.
  by elim: p.
Defined. 

Definition concat_pV {A : Type} {x y : A} (p : x = y) : p @ p^ = refl _.
  by elim: p.
Defined. 

Definition inv2 A (x y :A) (e: x = y) : e^ ^= e.
Proof.
  by elim: e.
Defined.

Definition ap_pp {A B : Type} (f : A -> B) {x y z : A} (p : x = y) (q : y = z) :
  ap f (p @ q) = (ap f p) @ (ap f q).
  by elim: p q. 
Defined.

Definition moveR_M1 {A : Type} {x y : A} (p q : x = y) :
  refl _ = p^ @ q -> p = q.
Proof.
  by elim: p q. 
Defined.

Definition concat_1p {A : Type} {x y : A} (p : x = y) :
  refl _ @ p = p := refl _.

Definition moveL_M1 {A : Type} {x y : A} (p q : x = y) :
  refl _ = q @ p^ -> p = q.
Proof.
  elim: p q => q h. rewrite h. apply concat_p1.
Defined.

Definition moveL_M1' {A : Type} {x y : A} (p q : x = y) :
  q^ @ p = refl _ -> p = q.
Proof.
  elim: p q => q e. rewrite concat_p1 in e.
  by rewrite <- inv2, e. 
Defined.

Definition moveR_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
  : u = p # v -> p^ # u = v.
Proof.
  by elim: p u v.
Defined.

Definition moveR_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
  : u = p^ # v -> p # u = v.
Proof.
  by elim: p u v.
Defined.

Definition concat_A1p {A : Type} {f : A -> A} (p : forall x, f x = x) {x y : A} (q : x = y) :
  (ap f q) @ (p y) = (p x) @ q.
  elim: q. by rewrite concat_p1.
Defined.

Definition moveL_Vp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y) :
  r @ q = p -> r = p @ q ^.
Proof.
  elim: r q => q e. elim: e. by rewrite concat_pV. 
Defined.

Definition concat_p_pp {A : Type} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  p @ (q @ r) = (p @ q) @ r.
  elim: p q => q; by elim: q r.
Defined.

Definition ap_compose {A B C : Type} (f : A -> B) (g : B -> C) {x y : A} (p : x = y) :
  ap (g ∘ f) p = ap g (ap f p).
  by elim: p. Defined. 

Definition concat_pA1 {A : Type} {f : A -> A} (p : forall x, x = f x) {x y : A} (q : x = y) :
  (p x) @ (ap f q) =  q @ (p y).
  elim: q. apply concat_p1.
Defined.

Definition ap2 {A A' B:Type} (f:A -> A' -> B) {x y:A} (p:x = y)
  {x' y':A'} (q:x' = y') : f x x' = f y y'
  := match p with refl _ => match q with refl _ => refl _ end end.


Definition transport_paths_Fl {A B : Type} {f g : A -> B} {x1 x2 : A}
  (p : x1 = x2) (q : f x1 = g x1)
  : transport (fun x => f x = g x) p q = (ap f p)^ @ q @ (ap g p).
Proof.
  elim: p. by rewrite concat_p1.
Defined.

Definition concat_V A (x y z:A) (e:x=y) (e' : y = z) : (e @ e')^ =
                                                       e' ^@ e ^.
elim: e e' => e'. by elim: e'. 
Defined. 

(* Structure of equality on dependent sums *)

Definition path_sigma_uncurried {A : Type} (P : A -> Type) (u v : {x:A & P x})
           (pq : {p : π1 u = π1 v & π2 u = p^# π2 v})
: u = v.
Proof.
  elim : pq => p q.
  elim: u p q => [u1 u2] p q. elim : v p q => [v1 v2] p q. cbn in *. 
  elim: p v2 q => v2 q. cbn in q. by elim: q. 
Defined.

Definition pr1_path {A} `{P : A -> Type} {u v : sigT P} (p : u = v) : π1 u = π1 v := ap π1 p.

Notation "p ..1" := (pr1_path p) (at level 50).

Definition pr2_path {A} `{P : A -> Type} {u v : sigT P} (p : u = v)
  : π2 u = p..1^ # π2 v.
  by elim p. 
Defined.
    
Notation "p ..2" := (pr2_path p) (at level 50). 


(* Structure of equality on dependent sums *)

(* How transport acts on ap *)

Definition transport_ap {A B : Type} (P : B -> Type) (f : A -> B) {x y : A}
           (p : x = y) (z : P (f x)) : transport P (ap f p) z =
                                       transport (fun x => P (f x)) p z.
Proof.
  by elim: p.
Defined.

(* How transport acts on arrows *)

Definition transport_arrow {A : Type} {B C : A -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : B x1 -> C x1) (y : B x2)
  : (transport (fun x => B x -> C x) p f) y  =  p # (f (p^ # y)).
Proof.
  by elim: p f y.
Defined.

(* How transport acts on equality type *)

Definition transport_paths_l {A : Type} {x1 x2 y : A} (p : x1 = x2) (q : x1 = y)
  : transport (fun x => x = y) p q = p^ @ q.
Proof.
    by elim: p q. 
Defined.

Definition transport_paths_r {A : Type} {x y1 y2 : A} (p : y1 = y2) (q : x = y1)
  : transport (fun y => x = y) p q = q @ p.
Proof.
    by elim: p; rewrite concat_p1.
Defined.

(* Definition of equivalences *)

Class IsEquiv {A : Type} {B : Type} (f : A -> B) := BuildIsEquiv {
  e_inv :> B -> A ;
  e_sect : forall x, e_inv (f x) = x;
  e_retr : forall y, f (e_inv y) = y;
  e_adj : forall x : A, e_retr (f x) = ap f (e_sect x);
}.

Arguments e_inv {_ _} _ {_} _.
Arguments e_sect {_ _} _ {_} _.
Arguments e_retr {_ _} _ {_} _.
Arguments e_adj {_ _} _ {_} _.


Class Equiv A B := BuildEquiv {
  e_fun :> A -> B ;
  e_isequiv :> IsEquiv e_fun
}.

Notation "A ≃ B" := (Equiv A B) (at level 20).


Arguments e_fun {_ _} _ _.
Arguments e_isequiv {_ _ _}.

Typeclasses Transparent e_fun e_inv.

Coercion e_fun : Equiv >-> Funclass.

(* other adjunction coherence from e_adj *)
Theorem other_adj A B (f:A->B) {H : IsEquiv f} (b : B):
  e_sect f (IsEquiv := H) (e_inv f b) = ap (e_inv f) (e_retr f b).
Proof.
Admitted.
 
(* The inverse of an equivalence is an equivalence *)

Instance isequiv_inverse A B (f:A->B) {H : IsEquiv f} : IsEquiv (e_inv f) 
    := BuildIsEquiv _ _ (e_inv f) f (e_retr f) (e_sect f) (other_adj _ _ _).

Definition Equiv_inverse {A B : Type} (e: A ≃ B) : B ≃ A := BuildEquiv _ _ (e_inv (e_fun e)) (isequiv_inverse _ _ _).  

Typeclasses Transparent e_fun e_inv.


(* Adjunctification of an isomorphism *)

Definition e_inv' {A B : Type} (e : A ≃ B) : B -> A := e_inv (e_fun e).
Definition e_sect' {A B : Type} (e : A ≃ B) := e_sect (e_fun e).
Definition e_retr' {A B : Type} (e : A ≃ B) := e_retr (e_fun e).
Definition e_adj' {A B : Type} (e : A ≃ B) := e_adj (e_fun e).


Definition issect'  {A B : Type} (f : A -> B) (g : B -> A)
           (issect : g ∘ f == id) (isretr : f  ∘ g == id) :=
  fun x =>
    ap g (ap f (issect x)^)  @  ap g (isretr (f x))  @  issect x.

Definition is_adjoint' {A B : Type} (f : A -> B) (g : B -> A)
           (issect : g∘ f == id) (isretr : f  ∘ g == id) (a : A) : isretr (f a) = ap f (issect' f g issect isretr a).
Proof.
  rewrite /issect'; apply: moveL_M1.
  rewrite ?ap_pp -concat_p_pp -ap_compose.
  pose b := (ap2 _ (refl _) (concat_pA1 (fun b => (isretr b)^) (ap f (issect a)))).
  apply: (concat _ (b _ _ _ _)) => {b}.
  rewrite -concat_p_pp.
  move: (concat_A1p (fun b => (isretr b)) (isretr (f a)))=> /= /(moveL_Vp _ _ _).
  rewrite -concat_p_pp concat_pV concat_p1 ap_compose=> i.
  apply: concat.
  2:{ apply: ap2; first reflexivity; rewrite concat_p_pp.
      apply ap2; last reflexivity.
      apply: concat; last (apply ap2; [symmetry; exact i| reflexivity]).
      symmetry; apply concat_pV. }
  rewrite -?ap_compose /=; symmetry; apply: (concat (ap_pp ((f ∘ g) ∘f) _ _)^ _).
  by rewrite concat_Vp.
Defined.

Definition isequiv_adjointify {A B : Type} (f : A -> B) (g : B -> A)
           (issect : g∘ f == id) (isretr : f  ∘ g == id)  : IsEquiv f
  := BuildIsEquiv A B f g (issect' f g issect isretr) isretr 
                  (is_adjoint' f g issect isretr).

(* ap is an equivalence *)

Definition ap_inv_equiv {A B} (f : A -> B) `{IsEquiv _ _ f} x y : f x = f y -> x = y.
Proof.
  move => X. exact ((e_sect f x)^@ ap (e_inv f) X @ e_sect f y).
Defined.

Definition ap_inv_equiv' {A B} (f : A -> B) `{IsEquiv _ _ f} x y : e_inv f x = e_inv f y -> x = y.
Proof.
  move => X. exact ((e_retr f x)^@ ap f X @ e_retr f y).
Defined.

Definition ap_id A (x y:A) (e:x = y) : ap id e = e.
Proof.
  by elim: e. 
Defined.

Instance IsEquiv_ap_transport A (P : A -> Type) {x y : A} (p : x = y) (u v : P x)
  : IsEquiv (@ap _ _ (fun (X : P x) => p # X) u v).
Proof. 
  unshelve econstructor; cbn. 
  - by elim: p.
  - elim: p => e. apply ap_id.
  - elim: p => e. apply ap_id.
  - move =>e; elim: e. by elim: p. 
Defined. 

(* can be found in theories/Basics/Equivalences.v *)

Instance isequiv_ap A B {x y : A} (f:A->B) {H:IsEquiv f}
  : IsEquiv (@ap _ _ f x y).
Proof. 
  unshelve refine (isequiv_adjointify _ _ _ _). 
  - by apply ap_inv_equiv. 
  - move =>e; elim: e. unfold ap_inv_equiv. cbn. rewrite concat_p1.
    apply concat_Vp.
  - move =>e. unfold ap_inv_equiv.
    rewrite ?ap_pp. rewrite ap_V. rewrite <- ?e_adj.
    rewrite <- ap_compose. rewrite <- concat_p_pp.
    rewrite concat_A1p. rewrite concat_p_pp. by rewrite concat_Vp.
Defined. 

(* functional extensionality axiom *)

Definition Funext := forall (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g).
 
(* Level of homotopy of types *)

Definition IsContr (A:Type) := { x : A & forall y, x = y}.
Existing Class IsContr. 

Fixpoint IsTrunc n A := match n with
                           | O => IsContr A
                           | S n => forall x y:A, IsTrunc n (x = y)
                           end.

Definition IsHProp A := IsTrunc 1 A.

(* begin contractible is the lowest level of truncation *)

Definition path_contr {A} `{IsContrA : IsContr A} (x y : A) : x = y
  := let contr := π2 IsContrA in (contr x)^ @ (contr y).

Definition path2_contr {A} `{IsContr A} {x y : A} (p q : x = y) : p = q.
Proof.
  assert (K : forall (r : x = y), r = path_contr x y).
  { move => r; elim: r. symmetry. unfold path_contr. apply concat_Vp. }
  exact (K p @ (K q)^).
Defined.

Definition contr_paths_contr A `{IsContr A} (x y : A) : IsContr (x = y).
  unshelve econstructor.
  exact (path_contr x y).
  exact (path2_contr _).
Defined.

(* begin proof irrelevant is the same as IsHprop *)

Definition IsIrr A := forall x y : A, x = y. 

Definition IsIrr_inhab_IsContr A (H: IsIrr A) : A -> IsContr A :=
  fun x => existT _ x (H x).
  
Definition IsHProp_to_IsIrr A : IsHProp A -> IsIrr A :=
  fun H x y => π1 (H x y).

Definition IsIrr_to_IsHProp A : IsIrr A -> IsHProp A.
  unshelve econstructor.
  - apply X.
  - move => e. apply: path2_contr. by apply IsIrr_inhab_IsContr.
Defined.
    
Definition IsHProp_inhab_isContr A {H:A -> IsContr A} : IsHProp A.
  apply IsIrr_to_IsHProp. move => x y. refine (path_contr _ _); auto. 
Defined.

(* Singleton types are contractible*)

Definition singleton A (x:A) := {y : A & x = y}.

Definition singleton_IsContr A x : IsContr (singleton A x).
Proof.
  unshelve econstructor.
  - unfold singleton. exists x. apply refl.
  - move => [y e]. apply path_sigma_uncurried. cbn.
    exists e.
    rewrite (transport_paths_r e^ e). by rewrite concat_pV.
Defined. 

(* Preservation of homotopy level *)

Definition contr_equiv A B (f : A -> B)
  `{IsContr A} `{IsEquiv A B f}
  : IsContr B.
Proof.
  unshelve econstructor.
  - exact (f (π1 H)).
  - move => b. rewrite <- (e_retr f b).
    apply (ap _ (π2 H _)).
Defined. 

Definition trunc_equiv n A B (f : A -> B)
  `{IsTrunc n A} `{IsEquiv A B f}
  : IsTrunc n B.
Proof.
  move: A B f IsTrunc0 H. elim: n => [ | n IHn] => A B f IsTrunc_ H.  
  - cbn in *. apply (contr_equiv A B f). 
  - move => x y. unshelve eapply (IHn (e_inv f x = e_inv f y) (x = y)).
    + apply ap_inv_equiv. apply isequiv_inverse. 
    + apply IsTrunc_.
    + exact (@isequiv_inverse _ _ (ap (e_inv f)) (isequiv_ap B A (e_inv f))).
Defined.

Definition IsTrunc_Forall {funext:Funext} A (B : A -> Type) n
           (H : forall x, IsTrunc n (B x)) : IsTrunc n (forall x, B x).
Proof.
  move: A B H. elim: n => [|n IHn] => A B H.
  - unshelve econstructor.
    + move => a. apply (π1 (H a)).
    + move => f. apply funext. move => a. apply (π2 (H a)).
  - move => f g. cbn in H.
    unshelve eapply (trunc_equiv _ _ _ (e_inv (apD10))). 
    + auto.
    + apply IHn => a. exact (H a (f a) (g a)). 
    + apply isequiv_inverse.
Defined. 

(* IsTrunc is a mere proposition *) 

Definition IsHProp_IsTrunc n A {funext : Funext} :
  IsHProp (IsTrunc n A).
Proof.
  apply IsIrr_to_IsHProp. move: A. elim: n => [| n IHn] => A H H'. 
  - apply path_sigma_uncurried.  unshelve econstructor.
    + exact (π2 H (π1 H')).
    + apply funext => x. by unshelve eapply path2_contr. 
  - apply funext => x. apply funext => y. 
    exact (IHn (x = y) (H x y) (H' x y)).
Defined.

(* homotopy fiber *)

Definition hfiber {A B : Type} (f : A -> B) (y : B) := { x : A & f x = y }.

Definition hfiber_canonical {A B : Type} (f : A -> B) (x : A) : hfiber f (f x)
  := (x ; refl _).

(* Isequiv f <-> forall y, IsContr (hfiber f y) *)

Definition IsEquiv_hfiber_IsContr {A B : Type} (f : A -> B) :
  IsEquiv f -> forall y, IsContr (hfiber f y).
Proof.
  move => H y. unshelve econstructor.
  - exists (e_inv f y). exact (e_retr f y).
  - move => [x e]. apply path_sigma_uncurried. unshelve econstructor; cbn.
    + elim: e. exact (e_sect f x).
    + elim: e.
      rewrite <- (transport_ap (fun X => X = f x) f). 
      rewrite (e_adj f). rewrite transport_paths_l. rewrite concat_p1.
      rewrite ? ap_V. cbn. by rewrite inv2.  
Defined.

Definition hfiber_IsEquiv_IsContr {A B : Type} (f : A -> B) :
  (forall y, IsContr (hfiber f y)) -> IsEquiv f.
Proof.
  move => fib. unshelve econstructor.
  - move => y. exact (π1 (π1 (fib y))).
  - move => x; cbn.
    pose (π2 (fib (f x))). cbn in i.
    exact ((i (hfiber_canonical f x))..1). 
  - move =>y. apply (π2 (π1 (fib y))).
  - move => x; cbn. 
    rewrite (π2 (fib (f x)) (hfiber_canonical f x)..2). 
    rewrite <- (transport_ap (fun X => X = f x) f).
    rewrite transport_paths_l. rewrite concat_p1.
    rewrite ? ap_V. by rewrite inv2. 
Defined.

(* beign an equivalence is HProp (not finished) *)

Definition IsEquiv_compose {funext:Funext} {A B C: Type} (f : A -> B) (H:IsEquiv f)
           : IsEquiv (fun (g:C -> A) => f ∘ g).
Proof.
  unshelve refine (isequiv_adjointify _ _ _ _).
  - exact (fun g => (e_inv f) ∘ g).
  - move => g. apply funext => b. apply e_sect.
  - move => g. apply funext => a. apply e_retr.
Defined. 

Definition rinv {A B : Type} (f : A -> B) := {g:B->A & f ∘ g = id}. 

Definition rinv_IsContr {funext:Funext} {A B : Type} (f : A -> B) (H:IsEquiv f)
  : IsContr (rinv f).
Proof.
  apply IsEquiv_hfiber_IsContr. unshelve eapply IsEquiv_compose; auto.
Defined.

(* Definition rcoh {A B : Type} (f : A -> B) (H:rinv f) := *)
(*   {eta: (π1 H) ∘ f = id & forall x:A, apD10 (π2 H) (f x)  = ap f (apD10 eta x) }.  *)

Definition rcoh {A B : Type} (f : A -> B) (H:rinv f) :=
  {eta: (π1 H) ∘ f = id & (fun x => ap f (apD10 eta x)) = (fun x => apD10 (π2 H) (f x)) }. 

Definition rcoh_IsContr {funext:Funext} {A B : Type} (f : A -> B) (H:IsEquiv f) (Hrinv:rinv f)
  : IsContr (rcoh f Hrinv).
Proof.
  (* apply IsEquiv_hfiber_IsContr. cbn.   *)
Admitted.



(* Equivalences between dependent products *)

Definition functor_forall {A B} `{P : A -> Type} `{Q : B -> Type}
    (f : B -> A) (H : forall b:B, P (f b) -> Q b)
  : (forall a:A, P a) -> (forall b:B, Q b) := fun g b => H b (g (f b)).

Instance isequiv_functor_forall {funext : Funext} {A B} {P : A -> Type} {Q : B -> Type}
         (f : B -> A) `{!IsEquiv f} (g : forall b, P (f b) -> Q b) `{!forall b, IsEquiv (g b)}
  : IsEquiv (functor_forall f g).
Proof.
  unshelve refine (isequiv_adjointify _ _ _ _).
  - apply (functor_forall (e_inv f)) => a y.
    exact (transport P (e_retr f a) (e_inv (g _) y)).
  - move => h. cbn.  apply funext => a. unfold functor_forall.
    move: (e_retr f a) => e.
    (* Don't understand why this doesn't work *)
    (*elim: e. *)
    refine (I_rect _ _ (fun y i => transport P i _ = h y) _ _ e).
    cbn. apply e_sect. 
  - move => h; apply funext => b. unfold functor_forall. 
    rewrite e_adj. move : (e_sect f b) => e.
    refine (I_rect _ _ (fun y i => g y (transport P (ap f i) _) = h y) _ _ e).
    cbn. apply e_retr.
Defined.


Instance Equiv_forall (A A' : Type)  (B : A -> Type) (B' : A' -> Type)
         (eA : A ≃ A') (eB : forall x, B (e_inv eA x) ≃ B' x )
         {funext : Funext}
         : (forall x:A , B x) ≃ (forall x:A', B' x).
Proof.
  unshelve refine (BuildEquiv _ _ (functor_forall (e_inv eA) (fun x => e_fun (eB x))) _).
  unshelve eapply isequiv_functor_forall. auto. apply isequiv_inverse.
  move => a'. exact (@e_isequiv _ _ (eB a')). 
Defined.

(* Equivalences between dependent sums *)

Fixpoint sigma_map {A B P Q} (f: A -> B) (g : forall a, P a -> Q (f a)) (l : sigT P) : sigT Q :=
  match l with
  | existT _ a l => existT _ (f a) (g a l)
  end. 

Definition sigma_map_compose {A B C P Q R } (f: A -> B) (f' : B -> C)
           (g : forall a, P a -> Q (f a)) (g' : forall b, Q b -> R (f' b))
           (l : sigT P):
  sigma_map f' g' (sigma_map f g l) = sigma_map (f' ∘ f) (fun a l => g' (f a) (g a l)) l.
Proof.
  by elim: l. 
Defined.

Definition sigma_map_eq {A P} (f: A -> A) (g : forall a, P a -> P (f a))
           (H : forall x, f x = x) (H' : forall a (l : P a), (H a)^ # l = g a l) (l : sigT P) :
 sigma_map f g l = l.
Proof.
  elim: l => a p. apply path_sigma_uncurried. cbn.
  exists (H a). by rewrite H'. 
Defined.

Definition naturality'  {A B} `{P : A -> Type} `{Q : B -> Type}
           (f : A -> B) 
           (e' : forall a, P a -> Q (f a)) a b (e : a = b) z:
  transport (Q ∘ f) e (e' _ z) = e' _ (e # z).
Proof.
  by elim: e. 
Defined.

Definition Equiv_Sigma (A A':Type) (B: A -> Type) (B': A' -> Type)
           (eA: A ≃ A') (eB : forall x, B x ≃ B' (e_fun eA x) ) :
  (sigT B) ≃ (sigT B').
Proof.
  unshelve refine (BuildEquiv _ _ _ (isequiv_adjointify _ _ _ _)).
  - unshelve refine (sigma_map eA (fun x => e_fun (eB x))). 
  - pose (sigma_map (e_inv eA) (fun a => e_inv (eB (e_inv eA a)))).
    move => x. apply s. exists (π1 x).
    apply (transport B' (e_retr eA _)^). exact (π2 x).
  - move => [a b]. apply path_sigma_uncurried; cbn. 
    unshelve econstructor.
    + apply e_sect.
    + rewrite e_adj. rewrite <- ap_V, transport_ap.
      rewrite (naturality' (e_fun eA) eB). apply e_sect.
  - move => [a b]. apply path_sigma_uncurried. cbn.
    unshelve econstructor.
    + apply e_retr. 
    + apply e_retr. 
Defined. 








Definition transport_pV {A : Type} (P : A -> Type) {x y : A} (p : x = y) (z : P y)
  : p # p^ # z = z.
  by elim: p z. 
Defined.

Definition transport_Vp {A : Type} (P : A -> Type) {x y : A} (p : x = y) (z : P x)
  : p^ # p # z = z.
  by elim: p z. 
Defined.

Instance isequiv_path {A B : Type} (p : A = B)
  : IsEquiv (transport (fun X:Type => X) p).
refine (BuildIsEquiv _ _ _ (transport (fun X:Type => X) p^)
                     (transport_Vp id p)
                     (transport_pV id p)
  _). by elim p.  
Defined.

Definition equiv_path (A B : Type) (p : A = B) : A ≃ B
  := BuildEquiv _ _ (transport (fun X:Type => X) p) _.

Axiom isequiv_equiv_path : forall (A B : Type), IsEquiv (equiv_path A B).

Existing Instance isequiv_equiv_path.

Definition path_universe_uncurried {A B : Type} (f : A ≃ B) : A = B
  := Equiv_inverse (BuildEquiv _ _ (equiv_path A B) _) f.

Definition path_universe {A B : Type} (f : A -> B) {feq : IsEquiv f} : (A = B)
  := path_universe_uncurried (BuildEquiv _ _ f feq).

Definition transport_path_universe_uncurried
           {A B : Type} (f : A ≃ B) (z : A)
  : transport (fun X:Type => X) (path_universe_uncurried f) z = f z.
Proof.
  exact (apD10 (ap e_fun (e_retr (equiv_path A B) f)) z). 
Defined.

Definition transport_path_universe
           {A B : Type} (f : A -> B) {feq : IsEquiv f} (z : A)
  : transport (fun X:Type => X) (path_universe f) z = f z
  := transport_path_universe_uncurried (BuildEquiv A B f feq) z.


Definition path_universe_V_uncurried {funext :Funext} {A B : Type} (f : A ≃ B)
  : path_universe_uncurried (Equiv_inverse f) = (path_universe_uncurried f)^.
Proof.
Admitted.

Definition path_universe_V {funext:Funext} {A B} `(f : A -> B) `{IsEquiv A B f}
  : path_universe (Equiv_inverse (BuildEquiv _ _ f _)) = (path_universe f)^
  := path_universe_V_uncurried (funext:=funext) (BuildEquiv A B f _).



Definition naturality {A} `{P : A -> Type} `{Q : A -> Type}
           (f : forall a, P a -> Q a) a b (e : a = b) (z:P a):
  transport Q e (f a z) = f b (transport P e z).
Proof.
  by elim: e. 
Defined.

Definition IsHSet A := IsTrunc 2 A.

Definition StreicherK X := forall (x:X) (p:x=x), p = refl x.

Definition StreicherK_HSet X : StreicherK X -> IsHSet X. 
Proof.
  move => K x y. apply IsIrr_to_IsHProp => e e'.
  elim: e' e => e. apply K. 
Defined.

Definition reflexiveRelation_hprop_aux X (R : X -> X -> Type)
           (Rcompat : forall x y, R x y -> x = y) :
  forall x y z (p:x=y) (r:R x z),
    transport (fun X => X = _) p (Rcompat x z r) =
    Rcompat y z (transport (fun X => R X _) p r).
  move => x y z p r.
  apply (@naturality _ (fun x => R x z) (fun x => x = z) (fun x => Rcompat x z)).
Defined. 

Definition reflexiveRelation_hprop X (R : X -> X -> Type) (HR : forall x y, IsHProp (R x y))
           (Rrefl : forall x, R x x) (Rcompat : forall x y, R x y -> x = y) :
  IsHSet X. 
Proof.
  apply StreicherK_HSet => x p.
  move: (reflexiveRelation_hprop_aux _ _ Rcompat _ _ _ p (Rrefl x)).
  rewrite transport_paths_l.
  assert (e : transport (fun X : X => R X x) p (Rrefl x) = Rrefl x).
  apply HR.
  rewrite e. clear e. 
  move/(moveL_Vp _ _ _).
  by rewrite concat_pV -(concat_1p p^)=> /inverse /(moveL_M1 _ _).
Defined.

Definition IsHProp_False: IsHProp False.
Proof. 
  apply IsIrr_to_IsHProp => e. elim: e.
Defined.

Definition not (A:Type) := A -> False. 

Definition IsHProp_double_neg {funext:Funext} A : IsHProp (not (not A)).
Proof.
  unshelve eapply IsTrunc_Forall; auto.
  move => _; apply IsHProp_False.
Defined.

Definition Decidable_classical P (dec_P : P + not P)
  : not (not P) -> P. 
Proof. 
  elim: dec_P => p n.
  - exact p. 
  - destruct (n p).
Defined. 

Definition Hedberg {funext:Funext}  A (dec_paths_ : forall a b : A, ((a = b) + not (a = b))%type)
  : IsHSet A.
Proof.
  apply (reflexiveRelation_hprop _ (fun a b => not (not (a = b)))).
  - move => x y. by unshelve eapply IsHProp_double_neg.
  - move => a n. apply (n (refl a)).
  - move => a b. by apply Decidable_classical.    
Defined.

Definition Hedberg_alt A (dec_paths_ : forall a b : A, (a = b) + not (a = b)%type)
  : IsHSet A.
Proof.
  move => a b.

  assert (lemma: forall p: a = b,  
             match dec_paths_ a a, dec_paths_ a b with
             | inl r, inl s => p = r^ @ s
             | _, _ => False
             end).
  {
    destruct p.
    destruct (dec_paths_ a a) as [pr | f].
    - apply inverse. apply concat_Vp.
    - exact (f (refl a)).
  }

  apply IsIrr_to_IsHProp; intros p q.
  move: (dec_paths_ a b) lemma => e. elim: e => [e | n e].
  + move: (dec_paths_ a a) => ea; elim: ea => ea H.
    * exact (H p @ (H q)^). 
    * elim: (H e). 
  + elim: (n p).  
Defined.

Definition neq_true_false : not (true = false).
Proof.
  assert (forall b (e:true = b), match b with
                                    | true => True
                                    | false => False
                                    end).
  move => b e. by elim: e. 
  move => e; exact (H false e). 
Defined. 

Definition Decidable_eq_bool : forall (x y : bool),  (x = y) + not (x = y).
Proof.
  move => x y; elim: x ; elim: y.
  - by left. 
  - right. apply neq_true_false.
  - right => e. apply neq_true_false. exact e^.
  - by left. 
Defined.

Definition S_inv : forall (x y : nat),  S x = S y -> x = y.
Proof.
  by inversion 1. 
Defined. 

Definition Decidable_eq_nat : forall (x y : nat),  (x = y) + not (x = y).
move => x y. elim: x y => [| x IHx] => y; case: y => [| y].
- by left.
- right => H; inversion H.
- right; intro H; inversion H.
- case (IHx y) => H.
  + left. exact (ap S H).
  + right => e. apply (H (S_inv _ _ e)).
Defined.


(*** Exercises *)

Definition pw_eq A (B : A -> Type) (f g : forall x, B x) := forall x, f x = g x.

Infix "f == g" := (pw_eq _ _ f g) (at level 50). 

Definition weak_funext := forall A (B : A -> Type) (f g : forall x, B x),
  f == g -> f = g.

Definition retract_of A B := {f : A -> B & {g : B -> A & forall x, g (f x) = x}}.

Definition lemma1 A (B : A -> Type) (f : forall x, B x) :
  retract_of {g : forall x, B x & f == g} (forall x, {y : B x & f x = y}).
Proof.
Admitted.

Definition lemma2 (wf: weak_funext) A (B : A -> Type) (f : forall x, B x) :
  IsContr (forall x, {y : B x & f x = y}).
Proof.
Admitted.

Definition lemma3 A (B : A -> Type) (f : forall x, B x)
           (wf : weak_funext) : wf A B f f (fun x => refl _) = refl _ ->
                                forall g (h: f == g), apD10 (wf _ _ f g h) = h.
Proof.
Admitted.

Definition lemma4 
           (wf : weak_funext) : {wf' : forall A B (f g: forall x:A, B x), f == g -> f = g &
                                 forall A B f, wf' A B f f (fun x => refl _) = refl _}.
Proof.
Admitted.

Definition weak_is_strong (wf : weak_funext) : Funext.
Proof.
  move => A B f g. unshelve eapply isequiv_adjointify.
  - exact (π1 (lemma4 wf) A B f g). 
  - move => []. exact (π2 (lemma4 wf) A B f).
  - apply lemma3. exact (π2 (lemma4 wf) A B f).
Defined. 

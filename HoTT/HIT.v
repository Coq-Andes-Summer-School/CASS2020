Set Universe Polymorphism.

From CASS.HoTT Require Import HoTT MyInt. 

Definition apD {A} {B : A -> Type} (f:forall x, B x) {x y:A} (p:x = y) :
  p # (f x) = f y
  := match p with refl _ => refl _ end.


Module Export Intervalerval.
  Private Inductive Interval : Type :=
  | zeroI : Interval
  | oneI : Interval.

  Axiom seg : zeroI = oneI. 
  
  Definition Interval_ind
             (P: Interval -> Type) 
             (b0: P zeroI)
             (b1: P oneI)
             (s : seg # b0 = b1)
  : forall i, P i
    := fun i => match i with
                | zeroI => b0
                | oneI => b1
                end.

   Axiom Interval_ind_seg : forall 
             (P: Interval -> Type) 
             (b0: P zeroI)
             (b1: P oneI)
             (s : seg # b0 = b1),
  apD (Interval_ind P b0 b1 s) seg = s.
   
End Intervalerval.


Section Interval_computation. 

  Variable i : Interval. 
  Variable P : Interval -> Type. 
  Variable b0 : P zeroI.
  Variable b1 : P oneI.
  Variable s : seg # b0 = b1.                 
  
  Eval cbn in
      Interval_ind P b0 b1 s zeroI.

  Eval cbn in
      Interval_ind P b0 b1 s oneI.

End Interval_computation.

Definition Interval_IsContr : IsContr Interval.
Proof.
  unshelve econstructor.
  - exact zeroI.
  - unshelve refine (Interval_ind _ _ _ _).
    + exact (refl zeroI).
    + exact seg.
    + apply transport_paths_r.
Defined. 

Definition transport_const {A B : Type} {x1 x2 : A} (p : x1 = x2) (y : B)
  : transport (fun x => B) p y = y.
Proof.
  destruct p.  exact (refl y).
Defined.

Definition Interval_funext (A : Type)  (B :A -> Type) (f g : forall a, B a):
       f == g -> f = g.
Proof.
  intro p.
  pose (pp := fun x => Interval_ind (fun _ => B x) (f x) (g x) (transport_const _ _ @ p x)).
  pose (q := (fun i x => pp x i) : Interval -> (forall x, B x)).
  exact (ap q seg).
Defined.


Module Export Squash.
  Private Inductive trunc (A : Type) : Type :=
  | tr : A -> trunc A.

  Arguments tr {_} _.
  
  Axiom trunc_hprop : forall A (a b : trunc A), a = b.

  Definition trunc_rec A B
             (f: A -> B)
             (hprop : IsHProp B)
  : trunc A -> B
    := fun a => match a with
                | tr a => f a
                end.

  Axiom trunc_rec_eq : forall A B
                              (f: A -> B)
                              (hprop : IsHProp B)
                              (a a': trunc A),
      ap (trunc_rec A B f hprop) (trunc_hprop A a a') =
      (IsHProp_to_IsIrr _ hprop _ _).
  
End Squash.

Definition trunc_ind A
           (P: trunc A -> Type) 
           (f: forall a, P (tr a))
           (hprop : forall a, IsHProp (P a))
  : forall a, P a.
Proof.
  intro a. refine (trunc_rec A (P a) _ (hprop a) a).
  intro a'. exact ((trunc_hprop _ _ _) # (f a')).
Defined. 


Module Export Circle.
  Private Inductive S1 : Type :=
  | base : S1.

  Axiom loop : base = base.

  Definition S1_ind (P : S1 -> Type)
             (b: P base)
             (l : loop # b = b)
  : forall x, P x
    := fun x => match x with
                | base => b
                end.

  Axiom S1_ind_eq : forall (P : S1 -> Type)
             (b: P base)
             (l : loop # b = b),
      apD (S1_ind P b l) loop = l.

  Definition S1_rec (B : Type)
             (b: B)
             (l : b = b)
  : S1 -> B
    := fun x => match x with
                | base => b
                end.

  Axiom S1_rec_eq : forall B
             (b: B)
             (l : b = b),
      ap (S1_rec B b l) loop = l.

End Circle.

Variable notS: Type.
Variable notSet : not (IsHSet notS).

Definition loop_not_refl : not (loop = refl base).
Proof.
  intro e.
  apply notSet. apply StreicherK_HSet. intros x p. 
  pose (S1_rec_eq notS x  p). rewrite e in i. apply inverse. exact i.
Defined.



Module Export Suspension.

  Private Inductive Susp (A:Type) : Type :=
  | N : Susp A
  | S : Susp A.
             
  Axiom merid : forall A, A -> (N A) = (S A).

  Arguments N {_}.
  Arguments S {_}.
  Arguments merid {_} _.
  
  Definition Susp_rec A (B : Type)
             (n s: B) 
             (m : A -> n = s)
  : Susp A -> B
    := fun x => match x with
                | N => n
                | S => s
                end.

  Axiom Susp_rec_eq : forall A (B : Type)
             (n s: B) 
             (m : A -> n = s) a,
      ap (Susp_rec A B n s m) (merid a) = m a.
  
  Definition Susp_ind A (P : Susp A -> Type)
             (n : P N)
             (s : P S)
             (m : forall a, (merid a) # n = s)
  : forall x, P x
    := fun x => match x with
                | N => n
                | S => s
                end.

  Axiom Susp_ind_eq : forall A (P : Susp A -> Type)
             (n : P N)
             (s : P S)
             (m : forall a, (merid a) # n = s) a,
      apD (Susp_ind A P n s m) (merid a) = m a.

End Suspension.


Definition Susp_bool_S1 : Susp bool ≃ S1.
Proof.
  unshelve econstructor.
  - unshelve refine (Susp_rec bool S1 _ _ _).
    + exact base.
    + exact base.
    + intro b. destruct b.
      * exact (refl _).
      * exact loop.
  - unshelve refine (isequiv_adjointify _ _ _ _).
    + unshelve refine (S1_rec (Susp bool) _ _).
      * exact N.
      * exact (merid false @ (merid true)^).
    + unshelve refine (Susp_ind bool _ _ _ _); cbn. 
      * reflexivity.
      * exact (merid true).
      * intro b; destruct b; cbn.
        ** rewrite (transport_paths_Fl (g := id) (merid true) (refl N)).
           rewrite ap_id.
           rewrite ap_compose. rewrite Susp_rec_eq.
           cbn. reflexivity. 
        ** rewrite (transport_paths_Fl (g := id) (merid false) (refl N)).
           rewrite ap_id.
           rewrite ap_compose. rewrite Susp_rec_eq.
           rewrite S1_rec_eq. rewrite concat_V. rewrite concat_p1.
           rewrite <- concat_p_pp. rewrite concat_Vp.
           rewrite concat_p1. apply inv2.
    + unshelve refine (S1_ind _ _ _); cbn. 
      * reflexivity.
      * rewrite (transport_paths_Fl (g := id) loop (refl base)).
        cbn. rewrite ap_id.
        rewrite ap_compose. rewrite S1_rec_eq.
        repeat rewrite ap_pp. rewrite ap_V. 
        rewrite Susp_rec_eq. cbn. rewrite concat_p1.
        rewrite concat_V. 
        rewrite inv2. rewrite Susp_rec_eq. 
        rewrite <- concat_p_pp. cbn. apply concat_Vp.
Defined.


Definition IsEquiv_id {A : Type} : IsEquiv (fun x:A => x).
  unshelve econstructor.
  - exact id.
  - reflexivity. 
  - reflexivity. 
  - reflexivity. 
Defined.


Definition S1_code : S1 -> Type
  := S1_rec _ Int (path_universe succ_int).

(* Transporting in the codes fibration is the successor autoequivalence. *)


Definition transport_S1_code_loop (z : Int)
  : transport S1_code loop z = succ_int z.
Proof.
  refine ((transport_ap id S1_code loop z)^ @ _).
  unfold S1_code. rewrite S1_rec_eq.
  apply transport_path_universe.
Defined.

Definition transport_S1_code_loopV {funext:Funext} (z : Int)
  : transport S1_code loop^ z = pred_int z.
Proof.
  refine ((transport_ap id S1_code loop^ z) ^@ _).
  rewrite ap_V.
  unfold S1_code; rewrite S1_rec_eq.
  rewrite <- (path_universe_V (funext:= funext) succ_int).
  apply transport_path_universe.
Defined.

(* Encode by transporting *)

Definition S1_encode (x:S1) : (base = x) -> S1_code x
  := fun p => transport S1_code p zero.

(* Decode by iterating loop. *)


Definition S1_decode {funext:Funext}  (x:S1) : S1_code x -> (base = x).
Proof.
  revert x;
    unshelve refine (S1_ind (fun x => S1_code x -> base = x) _ _).
  cbn. exact (loopexp loop).
  apply funext; intros z; simpl in z.
  refine (transport_arrow _ _ _ @ _).
  refine (transport_paths_r loop _ @ _).
  rewrite (transport_S1_code_loopV (funext:=funext)).
  destruct z as [[|n] | | [|n]]; simpl.
  rewrite <- concat_p_pp. rewrite concat_Vp. apply concat_p1.
  repeat rewrite <- concat_p_pp. rewrite concat_Vp.
  rewrite concat_p1. reflexivity. 
  apply concat_Vp. reflexivity. 
  reflexivity.
Defined.

(* The nontrivial part of the proof that decode and encode are equivalences is showing that decoding followed by encoding is the identity on the fibers over [base]. *)


Definition S1_encode_loopexp {funext:Funext} (z:Int)
  : S1_encode base (loopexp loop z) = z.
Proof.
  destruct z as [n | | n]; unfold S1_encode.
  - induction n; simpl in *.
    + refine (moveR_transport_V _ loop _ _ _).
      apply inverse. apply transport_S1_code_loop.
    + rewrite transport_pp.
      refine (moveR_transport_V _ loop _ _ _).
      refine (_ @ (transport_S1_code_loop _)^).
      assumption.
  - reflexivity.
  - induction n; simpl in *.
    + apply transport_S1_code_loop.
    + rewrite transport_pp.
      refine (moveR_transport_p _ loop _ _ _).
      refine (_ @ (transport_S1_code_loopV _)^).
      assumption.
      auto. 
Defined.

(* Now we put it together. *)

Definition S1_encode_isequiv {funext:Funext} (x:S1) : IsEquiv (S1_encode x).
Proof.
  refine (isequiv_adjointify (S1_encode x) (S1_decode x) _ _).
  (* This side is trivial by path induction. *)
  intro p; destruct p. cbn. reflexivity.

  (* Here we induct on [x:S1].  We just did the case when [x] is [base]. *)
  refine (S1_ind (fun x => forall x0 : S1_code x, S1_encode x (S1_decode x x0) = x0)
    S1_encode_loopexp _ _).
  (* What remains is easy since [Int] is known to be a set. *)
  apply funext. intros z. apply (hset_int (funext:=funext)).
  Unshelve. all : auto. 
Defined.

Definition equiv_loopS1_int {funext:Funext} : (base = base) ≃ Int
:= BuildEquiv _ _ (S1_encode base) (S1_encode_isequiv (funext:=funext) base).


Module Export CylinderHIT.
  Private Inductive Cyl {X Y} (f: X -> Y) : Y -> Type :=
    | top : forall x, Cyl f (f x)
    | base : forall y, Cyl f y.

  Axiom cyl_eq : forall {X Y} {f: X -> Y}, (base f) ∘ f == (top f).

  Global Arguments top {X Y f} x.
  Global Arguments base {X Y f} y.
  
  Definition Cyl_ind {X Y} {f: X -> Y}
             (P: forall y, Cyl f y -> Type) 
             (top': forall x, P (f x) (top x))
             (base': forall y, P y (base y))
             (cyl_eq' : forall x, (cyl_eq x) # (base' (f x)) = top' x)
  : forall y (w: Cyl f y), P y w
    := fun y w => match w with
                  | top x => top' x
                  | base x => base' x
                end.
End CylinderHIT.

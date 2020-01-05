Set Universe Polymorphism.
From CASS.HoTT Require Import HoTT.
(* ** Positive Numbers *)

Inductive Pos : Type :=
| one : Pos
| succ_pos : Pos -> Pos.

Definition one_neq_succ_pos (z : Pos) : not (one = succ_pos z)
  := fun p => transport (fun s => match s with one => unit | succ_pos t => False end) p tt.

Definition succ_pos_injective {z w : Pos} (p : succ_pos z = succ_pos w) : z = w
  := transport (fun s => z = (match s with one => w | succ_pos a => a end)) p (refl z).

(** ** Definition of the Integers *)

Inductive Int : Type :=
| neg : Pos -> Int
| zero : Int
| pos : Pos -> Int.

Definition neg_injective {z w : Pos} (p : neg z = neg w) : z = w
  := transport (fun s => z = (match s with neg a => a | zero => w | pos a => w end)) p (refl z).

Definition pos_injective {z w : Pos} (p : pos z = pos w) : z = w
  := transport (fun s => z = (match s with neg a => w | zero => w | pos a => a end)) p (refl z).

Definition Empty := False. 

Definition neg_neq_zero {z : Pos} : not (neg z = zero)
  := fun p => transport (fun s => match s with neg a => z = a | zero => Empty | pos _ => Empty end) p (refl z).

Definition pos_neq_zero {z : Pos} : not (pos z = zero)
  := fun p => transport (fun s => match s with pos a => z = a | zero => Empty | neg _ => Empty end) p (refl z).

Definition neg_neq_pos {z w : Pos} : not (neg z = pos w)
  := fun p => transport (fun s => match s with neg a => z = a | zero => Empty | pos _ => Empty end) p (refl z).

(* ** Decidable paths and truncation. *)

Definition decpaths_int : forall a b : Int, (a = b) + not (a = b)%type.
Proof.
  intros [n | | n] [m | | m].
  revert m; induction n as [|n IHn]; intros m; induction m as [|m IHm].
  exact (inl (refl _)).
  exact (inr (fun p => one_neq_succ_pos _ (neg_injective p))).
  exact (inr (fun p => one_neq_succ_pos _ (inverse (neg_injective p)))).
  destruct (IHn m) as [p | np].
  exact (inl (ap neg (ap succ_pos (neg_injective p)))).
  exact (inr (fun p => np (ap neg (succ_pos_injective (neg_injective p))))).
  exact (inr neg_neq_zero).
  exact (inr neg_neq_pos).
  exact (inr (neg_neq_zero ∘ inverse )).
  exact (inl (refl _)).
  exact (inr (pos_neq_zero ∘ inverse)).
  exact (inr (neg_neq_pos ∘ inverse)).
  exact (inr pos_neq_zero).
  revert m; induction n as [|n IHn]; intros m; induction m as [|m IHm].
  exact (inl (refl _)).
  exact (inr (fun p => one_neq_succ_pos _ (pos_injective p))).
  exact (inr (fun p => one_neq_succ_pos _ (inverse (pos_injective p)))).
  destruct (IHn m) as [p | np].
  exact (inl (ap pos (ap succ_pos (pos_injective p)))).
  exact (inr (fun p => np (ap pos (succ_pos_injective (pos_injective p))))).
Defined.

Definition hset_int {funext:Funext} : IsHSet Int.
Proof.
  unshelve eapply Hedberg; auto.  apply decpaths_int.
Defined.

(* ** The successor autoequivalence. *)

Definition succ_int (z : Int) : Int
  := match z with
       | neg (succ_pos n) => neg n
       | neg one => zero
       | zero => pos one
       | pos n => pos (succ_pos n)
     end.

Definition pred_int (z : Int) : Int
  := match z with
       | neg n => neg (succ_pos n)
       | zero => neg one
       | pos one => zero
       | pos (succ_pos n) => pos n
     end.

Instance isequiv_succ_int : IsEquiv succ_int | 0.
Proof.
  refine (isequiv_adjointify succ_int pred_int _ _).
  intros [[|n] | | [|n]]; reflexivity.
  intros [[|n] | | [|n]]; reflexivity.
Defined.

(** ** Iteration of equivalences *)

(** *** Iteration by positive numbers *)

Section IterPos.
  Context {A} (f : A -> A).

  Fixpoint iter_pos (n : Pos) : A -> A
    := match n with
         | one => f
         (** Should this be (iter_pos f n (f a))? *)
         | succ_pos n => f ∘ (iter_pos n)
       end.

  Definition iter_pos_succ_l (n : Pos) (a : A)
  : iter_pos (succ_pos n) a = f (iter_pos n a)
    := refl _.

  Fixpoint iter_pos_succ_r (n : Pos) (a : A)
  : iter_pos (succ_pos n) a = iter_pos n (f a)
    := match n with
         | one => refl _
         | succ_pos n => ap f (iter_pos_succ_r n a)
       end.

End IterPos.

(** *** Iteration by arbitrary integers *)

Section Iteration.

  (** Iteration by arbitrary integers requires the endofunction to be an equivalence, so that we can define a negative iteration by using its inverse. *)
  Context {A} (f : A -> A) `{IsEquiv _ _ f}.

  Definition iter_int (n : Int) : A -> A
  := match n with
       | neg n => iter_pos (Equiv_inverse (BuildEquiv _ _ f _)) n
       | zero => id
       | pos n => iter_pos f n
     end.

  Definition iter_int_succ_l (n : Int) (a : A)
  : iter_int (succ_int n) a = f (iter_int n a).
  Proof.
    destruct n as [[|n]| |n]; cbn.
    - apply inverse. apply e_retr.  (** -1 *)
    - apply inverse. apply e_retr.  (** -1 *)
    - reflexivity.              (** 0 *)
    - reflexivity.              (** n *)
  Defined.

  Definition iter_int_succ_r (n : Int) (a : A)
  : iter_int (succ_int n) a = iter_int n (f a).
  Proof.
  Admitted.

  Definition iter_int_pred_l (n : Int) (a : A)
  : iter_int (pred_int n) a = Equiv_inverse (BuildEquiv _ _ f _) (iter_int n a).
  Proof.
    destruct n as [n| |[|n]]; cbn.
    - reflexivity.              (** -n *)
    - reflexivity.              (** 0 *)
    - apply inverse. apply e_sect.  (** 1 *)
    - apply inverse. apply e_sect.  (** n *)
  Defined.

  Definition iter_int_pred_r (n : Int) (a : A)
  : iter_int (pred_int n) a = iter_int n (Equiv_inverse (BuildEquiv _ _ f _) a).
  Proof.
  Admitted.

End Iteration.

(** ** Exponentiation of loops *)

Fixpoint loopexp_pos {A : Type} {x : A} (p : x = x) (n : Pos) : (x = x)
  := match n with
       | one => p
       | succ_pos n => loopexp_pos p n @ p
     end.

Definition loopexp {A : Type} {x : A} (p : x = x) (z : Int) : (x = x)
  := match z with
       | neg n => loopexp_pos p^ n
       | zero => refl _
       | pos n => loopexp_pos p n
     end.

Definition ap_loopexp {A B} (f : A -> B) {x : A} (p : x = x) (z : Int)
: ap f (loopexp p z) = loopexp (ap f p) z.
Proof.
Admitted.

(** Under univalence, exponentiation of loops corresponds to iteration of autoequivalences. *)

Definition transport_pp {A : Type} (P : A -> Type) {x y z : A} (p : x = y) (q : y = z) (u : P x) :
  p @ q # u = q # p # u.
  destruct p, q; reflexivity.
Defined. 

Definition equiv_path_loopexp 
           {A : Type} (p : A = A) (z : Int) (a : A)
  : equiv_path A A (loopexp p z) a = iter_int (equiv_path A A p) z a.
Proof.
  destruct z as [n| |n]; try reflexivity.
  all:induction n as [|n IH]; try reflexivity; cbn in *.
  all:refine (transport_pp _ _ _ _ @ _); apply ap, IH.
Defined.

Definition loopexp_path_universe 
           {A : Type} (f : A ≃ A) (z : Int) (a : A)
: transport id (loopexp (path_universe f) z) a
  = iter_int f z a.
Proof.
  set (g := (path_universe f)).
  rewrite <- (e_retr (equiv_path A A) f).
  refine (_ @ equiv_path_loopexp _ z a).
  refine (ap (fun q => equiv_path A A (loopexp q z) a) _).
  apply inverse. destruct f. reflexivity. 
Defined.

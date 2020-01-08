(** printing < %\ensuremath{<}% *)
(** printing <~> %\ensuremath{\simeq}% *)
(** printing Coq %\Coq% *)
(** printing {| %\ensuremath{\{}% *)
(** printing |} %\ensuremath{\}}% *)
(** printing todo %\alert{Exercise}% *)
(** printing todoimpl %\alert{exercise}% *)
(** printing elided %\dots% *)

(* begin hide *)
Set Warnings "-notation-overridden".

Require Import CASS2020.partiality_recursion.
Require Import Utf8 List Program Lia Arith Compare_dec.
Require Import Relation_Operators.
Require Import ssreflect.
Arguments clos_trans [A].

Arguments map {A B}.
Close Scope list_scope.
Check @eq.
Axiom todo : forall {A}, A.
Ltac todo := apply todo.

From Equations Require Import Equations.
Set Asymmetric Patterns.

Implicit Types A B : Set.
(* end hide *)
(** %\subsection{Indexed Datatypes}\begin{frame}{Indexed datatypes: vectors}% *)

(** Size-indexed version of lists. *)

Inductive vec (A : Type) : nat -> Type :=
| nil : vec A 0
| cons n : A -> vec A n -> vec A (S n).

(** 
  The empty vector [nil] has size [O] while the [cons] operation
  increments the size by one.

  - Indexed
  - Recursive
  - Terms _and_ types carry more information *)
(** %\end{frame}\begin{frame}{Notations}% *)

(** We declare notations similar to lists
  on vectors, as the size information will generally be left _implicit_. *)

Arguments nil {A}.
Arguments cons {A n}.

Notation "x :: v" := (cons x v) : vector_scope.
Notation "[ ]" := nil : vector_scope.
Notation "[ x ]" := (cons x nil) : vector_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) .. )) : vector_scope.

Example v3 : vec bool 3 :=
 @cons bool 2 true (@cons _ 1 true (@cons _ 0 false nil)).

Example v3' : vec bool 3 :=
 cons true (cons true (cons false nil)).

(**
%\end{frame}\begin{frame}{Recall return clauses}%
*)

Fixpoint vmap {A B} {n} (f : A → B) (v : vec A n) : vec B n
:= match v in vec _ k (* binds *) return vec B k with
   | nil => nil
   | cons n a v' => cons (f a) (vmap f v')
   end.

(** %\pause% *)
Definition vhead {A} {n} (v : vec A (S n)) : A :=
  match v in vec _ k
    return match k with 0 => unit | S k => A end with
    | nil => tt
    | cons n a v' => a
  end.
  
(** We are encoding with the [match] in the return clause the discrimination
  of [0] and [S n]. *)
  
(**
%\end{frame}\begin{frame}{With equality instead:}%
*)

Program Definition vhead_eq {A} {n} (v : vec A (S n)) : A :=
  match v in vec _ k return k = S n -> A with    
  | nil => fun (eq : 0 = S n) => False_rect _ _
  | cons n' a v' => fun (eq : S n' = S n) => a
  end (@eq_refl _ (S n)).


(** Same problem, we need to explicitely witness equality manipulations
  in the branches.
  
  - Highly complicated!
  - Obscures the computational content with these "commutative cuts" and
    coercions
  
  *)

(** %\end{frame}\begin{frame}{Programming with dependent pattern-matching}% *)
(** 

  - Mixes proofs/invariants with datastructures
  - Advantage: less partiality and "garbage" representations, invariants are explicit
  - Disadvantage: more involved definitions and proofs.
  - Need for reasoning on equalities to justify inversions in general (fancy 
    return clauses are not enough).

  - Certified Programming with Dependent Types %\citep{chlipala2011certified}%
    goes into many tricks needed to program with these types in
    Coq.

  - Equations: higher-level notation for writting these programs,
    close to Agda/Idris syntax.

    - Equations _embeds_ the equational theory of inductive types
      in the pattern-matching algorithm.
    - Lets you focus on the program rather than making it type-check!
*)
(** %\end{frame}% *)

(** %\subsection{Introduction to Equations}\begin{frame}\frametitle{Introduction to \Equations}%

  In Coq!

 %\end{frame}%
*)

(* begin hide *)
Set Equations Transparent.
Import Inaccessible_Notations.
Local Open Scope equations_scope.

(** ** Inductive families *)
Local Open Scope vector_scope.

(** Now let us define the usual map on vectors. *)
Equations map {A B} (f : A -> B) {n} (v : vec A n) : vec B n :=
map f (n:=?(0)) [] := [] ;
map f (a :: v) := f a :: map f v.

Print map.

(** Here the value of the index representing the size of the vector 
  is directly determined by the constructor, hence in the case tree
  we have no need to eliminate [n]. This means in particular that 
  the function [map] does not do any computation with [n], and 
  the argument could be eliminated in the extracted code.
  In other words, it provides only _logical_ information about 
  the shape of [v] but no computational information.

  The [map] function works on every member of the [vec] family,
  but some functions may work only for some subfamilies, for example
  [tail]:
*)

Equations tail {A n} (v : vec A (S n)) : vec A n :=
tail (a :: v') := v'.

(** The type of [v] ensures that [tail] can only be applied to 
  non-empty vectors, moreover the patterns only need to consider 
  constructors that can produce objects in the subfamily [vec A (S n)],
  excluding [nil]. The pattern-matching compiler uses unification 
  with the theory of constructors to discover which cases need to 
  be considered and which are impossible. In this case the failed 
  unification of [0] and [S n] shows that the [nil] case is impossible.
  This powerful unification engine running under the hood permits to write
  concise code where all uninteresting cases are handled automatically. *)

Equations head {A n} (v : vec A (S n)) : A :=
head (a :: v') := a.
  
(** ** Derived notions, No-Confusion

    For this to work smoothlty, the package requires some derived definitions
    on each (indexed) family, which can be generated automatically using
    the generic [Derive] command. Here we ask to generate the signature,
    heterogeneous no-confusion and homogeneous no-confusion principles for vectors: *)

Derive NoConfusion for nat.
Derive Signature NoConfusion NoConfusionHom for vec.

(** To go further and implement a safe lookup function on vectors,
  we introduce an inductive definition of bounded natural numers [fin n].
  [fin n] represents the interval [ (0..n] ]. 
*)

Inductive fin : nat -> Set :=
  | f0 : forall n, fin (S n)
  | fS : forall n, fin n -> fin (S n).

Derive Signature for fin.

Arguments f0 {n}.
Arguments fS {n}.

(** For example, [fin 3] has the following inhabitants: *)

Check f0 : fin 3.
Check fS f0 : fin 3.
Check fS (fS f0) : fin 3.

(** But [fS (fS (fS f0))] is not an inhabitant of [fin 3]: *)

Fail Check fS (fS (fS f0)) : fin 3.

(** We can hence prove that [fin 0] is not inhabited: *)
Equations fin0 : fin 0 -> False := 
  fin0 !.

(** Our safe lookup can now be concisely written: it takes
  an index that must be within the bounds of the vector. *)

Equations nth {A} {n} (v : vec A n) (f : fin n) : A := 
nth (a :: _) f0 := a;
nth (_ :: v) (fS f) := nth v f.

(** The exercises associated with the lecture provide more examples of the 
  use of vectors and finite numbers. *)

(** ** Dependent elimination tactics 
   
  Alternatively to writing dependent pattern-matching programs, 
  we can also use dependent elimination whenever needed 
  in proof mode using the [depelim] and [dependent elimination] tactics
  provided by Equations. *)

Goal fin 0 -> False.
Proof.
  intros f.
  depelim f.
Qed.

Lemma vec_eq_dec {A n} `{EqDec A} (v w : vec A n) : { v = w } + { v <> w }.
Proof.
  induction v.




























  - dependent elimination w.
    left; auto. 
  - dependent elimination w as [@cons n' a' v'].
    case: (eq_dec a a') => [->|na].
    case: (IHv v') => [->|nv].
    left; auto.
    right=> [=]. Undo.
    right=> eq. noconf eq. contradiction.
    right=> eq. noconf eq. by [].
Qed.

(** * Pattern-matching on equality
  
  Recall, the sum type [{ A } + { B }] is a constructive variant of disjunction 
  that can be used in programs to give at the same time a boolean algorithmic information 
  (are we in branch [A] or [B]) and a _logical_ information (a proof witness of [A] or [B]).
  Hence its constructors [left] and [right] take proofs as arguments. The [eq_refl] proof 
  term is the single proof of [x = x] (the [x] is generaly infered automatically).
*)

Equations equal (n m : nat) : { n = m } + { n <> m } := 
equal O O := left eq_refl ;
equal (S n) (S m) with equal n m := {
  equal (S n) (S ?(n)) (left eq_refl) := left eq_refl ;
  equal (S n) (S m) (right p) := right _ } ;
equal x y := right _.

(** Of particular interest here is the inner program refining the recursive result.
  As [equal n m] is of type [{ n = m } + { n <> m }] we have two cases to consider:
  
  - Either we are in the [left p] case, and we know that [p] is a proof of [n = m],
    in which case we can do a nested match on [p]. The result of matching this equality
    proof is to unify [n] and [m], hence the left hand side patterns become [S n] and
    [S ?(n)] and the return type of this branch is refined to [{ n = n } + { n <> n }].
    We can easily provide a proof for the left case. 
    
  - In the right case, we mark the proof unfilled with an underscore. This will
    generate an obligation for the hole, that can be filled automatically by a 
    predefined tactic or interactively by the user in proof mode (this uses the
    same obligation mechanism as the Program extension
    %\cite{sozeau.Coq/FingerTrees/article}%). In this case the automatic tactic 
    is able to derive by itself that [n <> m -> S n <> S m].
*)

(* end hide *)
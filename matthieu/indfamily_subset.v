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

Inductive vec (A : Type) : nat -> Type :=
| nil : vec A 0
| cons n : A -> vec A n -> vec A (S n).
Arguments nil {A}.
Arguments cons {A n}.

Notation "x :: v" := (cons x v) : vector_scope.
Notation "[ ]" := nil : vector_scope.
Notation "[ x ]" := (cons x nil) : vector_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) .. )) : vector_scope.
(* end hide *)
(**
%\begin{frame}{It's all the same}%

  - Inductive families vs subset types.
  - Structure vs property. *)

Definition ilist A n := {l : list A | length l = n}.
(** %\pause% *)

(** Let's show this type is _isomorphic_ to vectors. *)

Record Iso (A B : Type) :=
  { iso_lr : A -> B; iso_rl : B -> A;
    iso_lr_rl : forall x, iso_lr (iso_rl x) = x;
    iso_rl_lr : forall x, iso_rl (iso_lr x) = x }.

(** %\end{frame}\begin{frame}{Exercise}% *)

Program Fixpoint vect_ilist {A n} (v : vec A n) : ilist A n :=
  match v in vec _ n return ilist A n with 
  | nil => Datatypes.nil (* The [nil] constructor of [list] *)
  | cons n x xs => Datatypes.cons x (vect_ilist xs)
  end.

Fixpoint ilist_vect {A} (l : list A) : vec A (length l) :=
  todoimpl.

Program Definition vect_ilist_iso {A} (n : nat) :
  Iso (vec A n) (@ilist A n) :=
  {| iso_lr := fun x => vect_ilist x ;
     iso_rl := fun x => ilist_vect x |}.
Solve Obligations with todo.

(** The relationship can be made explicit, categorically or using a
  universe of datatypes: Ornaments %\citep{DBLP:conf/lics/DagandM13,DBLP:journals/jfp/Dagand17}%.

%\end{frame}% *)

(**
%\section{Conclusion}\begin{frame}{More examples}%

 - Matrices, any bounded datastructure
*)

 Definition square_matrix {A} n := vec (vec A n) n. 

(** 
 - Balancing/shape invariants: e.g. red-black trees.
 - Type-preserving evaluators (equations_evaluator.v, with an exercise)
 - See equations_exercises.v for some more! *)

(** %\end{frame}\begin{frame}{A little history}%

  Many flavors of inductive families and DPM.

  - DML %\citep{XiPfenning1999DTP}%: ML + integer indexed types (presburger arithmetic)
  - Agda %\citep{norell:thesis}%, Epigram %\citep{epigram:pratprog}%. 
    UIP rule for non-linear cases and a higher level construction
  - Agda (Cockx), Equations (Sozeau). Avoid the UIP rule, staying compatible with HoTT.
  - Haskell, OCaml GADTs: indices can be types only, not arbitrary terms.
  - F* %\citep{DBLP:conf/popl/SwamyHKRDFBFSKZ16}%: indices can be values, subset types à la PVS (no proof terms)
  - CoqMT %\citep{DBLP:conf/csl/BlanquiJS07}%: Coq Modulo Theories, conversion includes arbitrary decidable theories.
    No coercions!

  And many others: ATS (Xi), Beluga (Pientka), %\ensuremath{\Omega}%mega (Sheard), Trellys (Weirich), %\dots%

  %\end{frame}\begin{frame}{Bibliography}% 

On dependent pattern-matching and inductive families in Dependent Type Theory: 
- %\cite{paulin93tlca}%: Inductive types in the Coq system Coq.
- %\cite{DBLP:conf/birthday/GoguenMM06}%. The notion of generalization by equalities
  and simplification procedure. McBride's papers include a large number of examples.
- %\cite{DBLP:journals/jfp/CockxD18}% and %\cite{equationsreloaded}%: state of the art
  in Agda and Coq. This allows to do pattern-matching without the K/UIP rule, incompatible
  with Univalence.

%\end{frame}%
**)
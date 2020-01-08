(** printing < %\ensuremath{<}% *)
(** printing <~> %\ensuremath{\simeq}% *)
(** printing Coq %\Coq% *)
(** printing {| %\ensuremath{\{}% *)
(** printing |} %\ensuremath{\}}% *)
(** printing todo %\alert{Exercise}% *)
(** printing todoimpl %\alert{exercise}% *)
(** printing elided %\dots% *)
(**
%\section{Inversion of Inductive Families}
\frame<beamer>{\frametitle{Dependently-Typed Programming in \Coq}\tableofcontents[sectionstyle=show/shaded,subsectionstyle=show/show/hide]}
\subsection{General Inductive Families}
\begin{frame}{Inductive predicates}%
*)
(* begin hide *)
Require Import List.
Require Import ssreflect.
Module Judgments.
(* end hide *)
(** 
 Judgments and in general inductively defined derivation trees can be
 represented using indexed inductive types. 

 A typical de Bruijn encoding of STLC. *)

Inductive type := 
  | cst | arrow : type -> type -> type.
Inductive term := 
  | var : nat -> term
  | lam : type -> term -> term
  | app : term -> term -> term.
Definition ctx := list type.

(** %\end{frame}\begin{frame}{Judgments}%

  The typing relation can be defined as the inductive family: *)

Inductive typing : ctx -> term -> type -> Prop :=
| Var : forall (G : ctx) (x : nat) (A : type), 
    List.nth_error G x = Some A -> 
    typing G (var x) A

| Abs : forall (G : ctx) (t : term) (A B : type),
    typing (A :: G) t B ->
    typing G (lam A t) (arrow A B)

| App : forall (G : ctx) (t u : term) (A B : type),
    typing G t (arrow A B) ->
    typing G u A ->
    typing G (app t u) B.

(** %\end{frame}% *)
(** %\subsection{Generalization by Equalities}\begin{frame}{Generalizing by equalities}%

 Suppose you want to show:
*)

Lemma invert_var Γ x T (H : typing Γ (var x) T) :
  List.nth_error Γ x = Some T.
Proof. elim: H => [G x' A Hnth|G t A B HB|G t u A B HAB HA].
(** [[
  x : nat
  G : ctx
  x' : nat
  A : type
  H : nth_error G x' = Some A
  ============================
   nth_error G x = Some A
subgoal 2 (ID 384) is:
 nth_error G x = Some (arrow A B)
subgoal 3 (ID 394) is:
 nth_error G x = Some B
]]
 *)
Abort.
(** %\end{frame}% *)
(** %\begin{frame}{Generalizing by equalities}% 
*)

Lemma invert_var Γ x T (H : typing Γ (var x) T) :
  List.nth_error Γ x = Some T.
Proof.
  inversion H. subst. assumption.
Qed.

(** %\end{frame}% *)
(** %\begin{frame}{Generalizing by equalities}% 


  - Generalizing by equalities to keep information that is otherwise lost by the eliminator. 
  - Generalizes the return clause

    [match t return P with]

    into
[[
match t as v return t = v -> P with
| S y => fun H : t = S y => ...
| ...
end
]]

  - For full generality, pack inductive value with its indices in a 
    sigma-type:
[[
match (t : I u) in I i as v return (u; t) =_{i & I i} (i; v) -> P with
...
]]
%\end{frame}% *)
(** %\begin{frame}{Understanding \texttt{inversion}}% *)

Lemma invert_var' Γ x T (H : typing Γ (var x) T) :
  List.nth_error Γ x = Some T.
Proof. 
  remember (var x) as t. move:Heqt.
(** [[
Γ: ctx
x: nat
T: type
t: term
H: typing Γ t T
================
t = var x -> nth_error Γ x = Some T 
]] 

%\end{frame}\begin{frame}\frametitle{Information is kept!}%
Goal: [t = var x -> nth_error Γ x = Some T]
*)
    
  elim: H => [G x' A Hnth|G b A B HB|G f u A B HAB HA].

(** [[
G: ctx
x': nat
A: type
Hnth: nth_error G x' = Some A
------------------
var x' = var x -> nth_error G x = Some A

... -> lam A b = var x -> nth_error G x = Some (arrow A B)

... -> app f u = var x -> nth_error G x = Some B
]] 

%\end{frame}% *)
(* begin hide *)
  all:admit.
Admitted.

End Judgments.
(* end hide *)

(** %\begin{frame}{Specialization by unification}%

  In general we simplify the resulting equations according to:
  - substitution (a.k.a. [eq_rect] rule):

    [(forall (y : nat) (e : y = t) -> P y e) <~> P t eq_refl] ([y] $\notin$ [FV(t)])
  - injectivity: [(S u = S v -> P) <~> (u = v -> P)]
  - discrimination: [(0 = 1 -> P) <~> P]
  - acyclicity; [(y = c y -> P) <~> P]
  - _deletion_ (a.k.a. axiom K):

    [(forall (y : nat) (e : y = y) -> P y e) <~> (forall (y : nat), P y eq_refl)]
    
%\end{frame}% *)
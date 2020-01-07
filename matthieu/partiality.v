(** printing < %\ensuremath{<}% *)
(** printing <~> %\ensuremath{\simeq}% *)
(** printing Coq %\Coq% *)
(** printing {| %\ensuremath{\{}% *)
(** printing |} %\ensuremath{\}}% *)
(** printing todo %\alert{Exercise}% *)
(** printing todoimpl %\alert{exercise}% *)
(** printing elided %\dots% *)
(* begin hide *)
From CASS2020 Require Import demoenv.
From Coq Require Import Program.
From Coq Require Import ssreflect.
Close Scope boolean_if_scope. 
Open Scope general_if_scope.
(** Lists and [map] *)

Print list.
Require Import Utf8 List Program Lia Le.
Check False_rect.
Axiom ax : False.
Ltac admit := elim ax.
Ltac todo := admit.
Axiom todoimpl : forall {A}, A.
Ltac elided := admit.
Set Asymmetric Patterns.

(* end hide *)
(** 
%\begin{frame}{Variants of nth}%

 - Partial function *)

Fail Fixpoint nth {A} (l : list A) (n : nat) : A :=
match l, n with
| nil,       n => _ (* ??? *)
| cons x xs, 0 => x
| cons _ xs, S n => nth xs n
end.

(** - Encoding partiality with the option type *)

Fixpoint nth_option {A} (l : list A) (n : nat) : option A :=
  match l, n with
  | nil, _ => None
  | cons x xs, 0 => Some x
  | cons _ xs, S n => nth_option xs n
  end.

Lemma nth_in_domain {A} (l : list A) n : n < length l ->
  exists a, nth_option l n = Some a. Proof. elided. Qed.
(** %\end{frame}\begin{frame}\frametitle{A total version}% *)

(** - Using a default value in place of exceptions *)

Fixpoint nth_default {A} (d : A) (l : list A) (n : nat) : A :=
  match l, n with
  | nil, _ => d
  | cons x xs, 0 => x
  | cons _ xs, S n => nth_default d xs n
  end.

Lemma nth_default_map {A B} (l : list A) n (f : A -> B) d :
  f (nth_default d l n) = nth_default (f d) (map f l) n.
Proof. Admitted.

Definition nth_default_bug :=
  nth_default 0 [] 3.

(** 
%\end{frame}\begin{frame}{A correct by construction version}%
 *)

(** - The total function, with types depending on values: *)

Example nth : ∀ A (l : list A), {n : nat | n < length l} → A.
Proof.
  move=> A. elim => [ |x l IHl].
  - move=> [n H].
    exfalso. inversion H.
  - move=> [[ | n'] H].
    + simpl in *. exact x.
    + apply IHl. exists n'. simpl in *; lia.
Defined.

Extraction nth.

(** 
  - The computational content is mixed with the proof: 
    not clear we return the "right" [A]!
  - The erasure is however the same as ML's [nth] *)
(** %\end{frame}% *)

(** 
%\subsection{Subset Types}\begin{frame}{Subset types}%

  Recall subset types are sigma types where the second component is a proposition:

  [{ x : A | P } <-> sigma A (fun x : A => P)]

 - Constructor: *)

Check (exist : forall A (P : A -> Prop),
          ∀ x : A, P x → { x : A | P x }).

(** - Projections:  *)

Check (proj1_sig : ∀ A P, {x : A | P x} → A).
Check (proj2_sig : ∀ A P (p : {x : A | P x}), P (proj1_sig p)).

(** - Binding notation: *)

Check (proj2_sig : forall A P (x : A | P x), P (proj1_sig x)).

(** %\end{frame}% *)
(** 
%\begin{frame}{Examples}% *)

Check (@exist nat (fun x : nat => x = x) 0 eq_refl
      : { x : nat | x = x }).

Check exist (fun x : nat => x = x) (S 0) eq_refl
      : { x : nat | x = x }.

Check exist (fun x : nat => x <= S x) (S 0) (le_S _ _ (le_n 1))
      : { x : nat | x <= S x }.

Check (fun x : { x : nat | x < 42 } => ` x)
  : { x : nat | x < 42 } -> nat.

(** %\end{frame}% *)
(** 
%\begin{frame}{Strong specifications}%

  *)

Definition euclid_spec :=
  forall (x : nat) (y : nat | 0 < y),
    { (q, r) : nat * nat | x = q * `y + r }.
    

(** %\end{frame}% *)


(** 
%\begin{frame}[fragile]{Program \citep{sozeau.Coq/FingerTrees/article}}%

 - A tool to program with _subset_ types (inspired by PVS).
   In the programming literature (F*, Liquid Haskell, ...):
   refinement types / liquid types

 - Coq's type system + the rules:
 
  %\begin{mathpar}
  \irule{Sub-Proj}{Γ \vdash t : \{ x : A~|~P \}}{Γ \vdash t : A}

  \irule{Sub-Proof}{Γ \vdash t : A \quad Γ, x : A ⊢ P : \Prop}{Γ ⊢ t : \{ x : A~|~P \}}
  \end{mathpar}%

  %\textsc{Sub-Proj}% is an implicit projection/coercion.
  Note that %\textsc{Sub-Proof}% does _not_ require a proof term.
  
 - An elaboration to Coq terms with holes for the missing proof terms.

%\end{frame}%
%\begin{frame}[fragile]{Program II}%

 - An elaboration to Coq terms with holes for the missing proof terms.
  %\begin{mathpar}
  \irule{Sub-Proj}{Γ \vdash t : \{ x : A~|~P \}}{Γ \vdash \cst{proj1\_sig}~t : A}

  \irule{Sub-Proof}{Γ \vdash t : A \quad Γ, x : A ⊢ P : \Prop \quad Γ ⊢ ?p : P~t}{Γ ⊢ \constr{exist}~t~?p : \{ x : A~|~P \}}
  \end{mathpar}%

 - This inserts projections and coercions with _proof obligations_ [?p]
   everywhere needed.

 - The translation is correct for a type theory with proof-irrelevant [Prop] %\citep{sozeau.thesis}%.

%\end{frame}% *)
(**
%\begin{frame}{Examples}% *)

Require Import Arith Program.

(** Notation [!] expresses an unreachable point of the program.
  It abbreviates an application of [False_rect]. *)

Program Definition imposs (H : 0 = 1) : False := !.

(** The %\textsc{Sub-Proof}% rule at work: *) 

Program Definition exists_nonzero : { x : nat | 0 < x } := 1.
    
(** If the specification is not inhabited then some obligations will remain unprovable. *)

Program Definition exists_lt_zero : { x : nat | x < 0 } := 0.
Admit Obligations.

(** %\end{frame}\begin{frame}{Examples}%
  Using a match expression and [!], let's implement a total [head] function: *)

Program Definition head {A} (l : list A | l <> []) : A := 
   match l (* using implicit coercion to carrier *) with
   | [] => ! (* impossible *)
   | x :: xs => x
   end.

(** Now look at its extraction to OCaml: *)

Eval cbv beta zeta delta [head] in head.
Extraction head.
(**
[[
let head = function
| Nil -> assert false (* absurd case *)
| Cons (x, _) -> x
]]  
*)
(** 
%\end{frame}% *)
(**
%\begin{frame}{Decorating terms}% *)

(** The definition of [head] is actually: h
[[
 λ (A : Type) (l : {l : list A | l ≠ []}),
       match l.1 as l' return (l' = l.1 → A) with
       | [] => λ Heq_l : [] = l.1, !
       | hd :: wildcard' => λ _ : hd :: wildcard' = l.1, hd
       end eq_refl
]]

  where head_obligation_1 is of type:
[[
 ∀ (A : Type) (l : {l : list A | l ≠ []}), [] = l.1 → False
]]

  - Program automatically _generalizes_ by equalities between 
    the original matched object and the patterns.
  - Provides the necessary _logical_ information from the program,
    to solve obligations.
*)
(** %\end{frame}% *)
(** %\subsection{Reflecting Computations in Types}\begin{frame}\frametitle{A safe lookup function}% *)
Program Fixpoint safe_nth {A} (l : list A)
         (n : nat | n < (length l)) : A := todoimpl.
  
Eval unfold safe_nth in safe_nth.

Extraction safe_nth.

(** %\end{frame}% *)
(* begin hide *)
Notation " ( x &? ) " := (exist _ x _)
                           (format "( x  &? )").

(** A "dependant" lemma. *)

Lemma patch {A B} (f : A -> B) l :
  { m : nat | m < length l } ->
  { m : nat | m < length (map f l) }.
Proof.
  move=> [n H]. exists n.
  by rewrite map_length.
Defined.

Lemma safe_nth_map {A B} (l : list A) n
     (f : A -> B) :
  f (safe_nth l n) =
  safe_nth (map f l) (patch f l n).
Proof.
(*   elim: l n => [|a l' IHl'] n.
  - simpl. bang.
  - case: n => [[|n'] Hn]; simpl.
    + reflexivity.
    + rewrite IHl'. simpl.
      Fail reflexivity. repeat f_equal.
      apply proof_irrelevance.
 *)
 Admitted.

(* end hide *)

(** %\begin{frame}\frametitle{The sumbool type}% 
  
  Coq includes a special disjunction of two propositions [A] and [B] but
  which is computational: that is we can know in a program which of the left
  or right branch is taken.  *)

Inductive sumbool (A B : Prop) : Set :=
| left : A -> sumbool A B
| right : B -> sumbool A B.
Arguments left {A B}.
Arguments right {A B}.

Notation " { A } + { B } " := (sumbool A B) : type_scope.

(** The [dec] combinator allows to _reflect_ a test on a boolean in the types. *)
 
Definition dec : forall b : bool, { b = true } + { b = false } :=
  fun b => match b return { b = true } + { b = false } with
            | true => left eq_refl
            | false => right eq_refl
            end.

(** %\end{frame}% *)
(** %\begin{frame}\frametitle{Reflecting boolean tests}% 

  By default, Program does not do the generalization by equalities for boolean tests:
*)

Program Definition f (n m : nat) : { n = m } + { n <> m } :=
  if n =? m then left _ else right _.
  Next Obligation. (** No hypothesis to show (n = m) *) Abort.
(* begin hide *)
  Admit Obligations.
(* end hide *)
  
(** The [dec] combinator allows to _reflect_ the test in the types: *)
Program Definition g (n m : nat) : { n = m } + { n <> m } :=
  if dec (n =? m) then left _ else right _.

Next Obligation. (** One hypothesis [n ?= m = true] *)
  by apply: beq_nat_true. Qed.

Next Obligation. (** One hypothesis [n ?= m = false] *)
  by apply: beq_nat_false. Qed.

(** %\end{frame}% *)
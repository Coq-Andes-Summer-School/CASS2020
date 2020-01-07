From mathcomp Require Import all_ssreflect.
(*** Functions, 
Higher-Order Functions ***)

(* Functions are defined by binding, abstracting their argument in
   the body of their definition. *)

Definition plus_five (n : nat) : nat := n + 5.

(* Note: we will make more precise later how type 'nat' is defined, and
what the infix '+' refers to. *)


(* Moreover, typing constraints are enforced : in Coq one can only
   handle well-typed terms. *)

(* 'About' is an important query command for defined constants (only) *)
About plus_five.

(* 'Check' gives the type of an arbitrarily complex term, or hints 
   about the reasons why the term is not well-typed. *)
Check 7.
Check plus_five 7.

Fail Check plus_five plus_five.

(* Functions can be higher-order, i.e., take arguments which
   themselves have an arrow type: *)

Definition iter_twice (f : nat -> nat) (x : nat) : nat := f (f x).

(* Note that type annotations are optional when they can be
 inferred  from other typing constraints. Handle with care... *)

(* 'iter_twice' is a program (and so is plus_five), which can be
 evaluated by a reduction machine which performs the expected
 unfolding of definitions, and substitutions. *)

Eval compute in iter_twice plus_five 7.


(* But something more than just unfolding and substitution happened here,
let us see what. *)

(*** Data Structures,
 Programs ***)

(** Enumerated types: colors and booleans **)

(* Our first definition of a data structure, as an Inductive type: *)

Inductive color : Set := red | green | blue.

Check red.
Check color.

(*
- 'color' is the name we chose for the type we defined
- 'Type' is a type annotation
- 'red', 'green' 'blue' are the (only) inhabitants of type 'color',
  also called constructors. 
*)

(* A program operating on 'color's, by case analysis, also called
   pattern matching. *)

Definition swap_red_green (c : color) : color :=
match c with
| red => green 
| green => red
| blue => blue
end.

(* Pattern matching defines rewrite rules, which can be used by a
   reduction machine for evaluating programs *)

Eval compute in swap_red_green green.

Eval compute in swap_red_green (swap_red_green green).

(* Booleans are defined as an enumerated inductive type, exactly as color. *)
Print bool.

(* But it has a syntactic sugar for pattern matching *)
Definition is_false (b : bool) : bool := if b then false else true.

(* And infix notations for boolean operations. *)
Eval compute in true && false || false && (false || true).

Search "_ && _".
About andb.
Print andb.

(** Recursive inductive types: natural numbers **)

Print nat.

(*
- 'nat' is the name we chose for the type we defined (pretty-printed by my UI)
- 'Set' is a type annotation
- 'O', 'S' are the  constructors, but only 'O' is an inhabitant.
*)


(* The (closed) inhabitants of type nat are the smallest *)
(* collection of terms containing O and closed under S. *)

Unset Printing Notations.

Check 1.
Check 17.

Set Printing Notations.

(* A program operating on 'nat' by case analysis, also called
   pattern matching. *)

Definition is_one (n : nat) : bool :=
  match n with
    |O => false 
    |S O => true
    |_ => false 
  end.

Eval compute in is_one 8.

(* A recursive program, defined by case analysis and recursive call *)

Module sandbox0.

Fixpoint addn (n m : nat) : nat :=
  match n with
  |0 => m
  |S k => S (addn k m)
  end.

End sandbox0.

(* addn is isomorphic to the program hidden behind the infix plus used *)
(* in the first example *)
Fail Search "+".
Search  "_ + _".


(* Here as well, the rewrite rules corresponding to each branch of the *)
(* pattern matching are used to reduce programs *)

Eval compute in addn 2 3.


(* We are now ready to implement boolean predicates on nat, like comparison.
   Here is a convenient syntax for nested case analysis. *)

Fixpoint leq (n m : nat) : nat :=
  match n, m with
  | 0, _ => true
  | S _, 0 => false 
  | S k, S l => leq k l
  end.

(* Note the output message : Coq has checked that leq is terminating *)


(* Riddle: what is this? *)
Module sandbox1.
Inductive foo : Set :=  a : foo -> foo | b : foo -> foo | c : foo.
End sandbox1.


Require Import BinNat.

Print positive.
Open Scope positive_scope.

Unset Printing Notations.

Check 1.
Check 2.
Check 3.

Close Scope positive_scope.
Set Printing Notations.

(** Polymorphic Datatypes: Containers **)

(* A polymorphic type is a type itself parameterized by a type. *)

(* One of the simplest examples: an option type *)

Print option.

Check option nat.
Check option bool.

(* In fact, 'option' has an arrow type (sort) *)
Print option.
Check option.

(* Now a type whose inhabitants are pairs of natural numbers *)
Inductive nat_pair : Set := mk_nat_pair : nat -> nat -> nat_pair.

(* The constructor is building a pair*)
Check mk_nat_pair 3 4.

(* Pattern matching destructs a pair *)
Definition nat_pair_fst (p : nat_pair) : nat :=
  match p with
  |mk_nat_pair n m => n
  end.

(* We can design a polymorphic version of nat_pair, with a star infix notation. *)
Print prod.


(* Polymorphic lists, in a name space: *)

Module sandbox.

Inductive list (A : Type) : Type :=
    nil : list A | cons : A -> list A -> list A.


(* Remark : this nature of polymorphism triggers a fair 
   amount of verbosity.*)

About nil.
About cons.

Check cons nat 3 (cons nat 2 (nil nat)).

(* Type inference at work *)
Check cons _ 3 (cons _ 2 (nil _)).

End sandbox.

(* One can even do better and declare the polymorphic arguments as
implicits: then they will no more be provided. This is what the standard 
library does. *)

Fail Check cons _ 3 (cons _ 2 (nil _)).
Check cons 3 (cons 2  nil).

About nil.
Check nil.

About cons.
Check cons.

(* Remark : this can be seen as a polymorphic variant of type nat... *)


(* Exercise: how to implement a function extracting the head of
   a list? Caveat: Coq functions have to be total ... *)

(* First solution: use option *)
Definition option_head (A : Type) (l : list A) : option A :=
  match l with
  |nil => None
  |cons x _ => Some x
  end.

(* pros: captures the exceptional case. 
   cons: contaminating monadic style. *)

(* Second solution : use an exceptional value *) 
Definition dflt_head (A : Type) (dflt : A) (l : list A) : A :=
  match l with
  |nil => dflt 
  |cons x  _ => x
  end.

(* pros: better compositionality. 
   cons: requires an inhabited type, risks of confusion. *)

(*** Statements and Proofs. ***)


(** Trivial proofs, by computation **)

(* Polymorphic equality, with an infix notation '=' *)
About eq.

(* Check checks that a statement is well-formed *)
Check 3 = 2 + 1.

Fail Check nil = 2.

(* But of course not that it is provable :) *)
Check true = false.

(* Stating and proving our first (ground) identity, interactively. *)
Lemma three_is_two_plus_one : 3 = 2 + 1.
Proof. by []. Qed.

(* The proof is trivial, because both hand-sides are *)
(* convertible, that is equal modulo "computation" *)

(* Proofs by conversion also hold for non-ground terms: here is
a statement with parameters, proved by conversion. *)

Lemma add0n n : 0 + n = n.
Proof. by []. Qed.

(* In order to go beyond the known rewrite rules, case analysis 
   can be needed. *)
Lemma negbK b : negb (negb b) = b.
Proof.
case: b. (* and now the proof is by conversion in both cases. *)
- by [].
- by [].
Qed.

(* As we shall see, conversion can be used with profit to automate proofs
   and absorb bureaucracy. *)


(** Case analysis, recurrence, induction **)
(* Now an equivalence statement between two boolean predicates *)

Check leq.
Check eqn.

Lemma muln_eq0 m n : (m * n == 0) = (m == 0) || (n == 0).
Proof.
(* We need a case analysis on the natural numbers. *)
case: m => [| k].
- by [].
- case: n => [| l]; last first. (* Let's do the easy case first. *)
  + by [].
  + rewrite muln0. 
    by [].
Qed.

(* Here as well we can improve the script... *)

(* We need to reason by recurrence (induction) on m *)
Lemma leqnn n : n <= n = true.
Proof.
elim: n => [| k].
- by [].
- by [].
Qed.

(** Applying a lemma **)

(* How to use lemma leqnn in a proof step. *)

Module sandbox2. 

(* Note that I have used a "coercion" here, which allows me to 
   ommit the _ = true *)
Lemma foo1 a b : a + b <= a + b = true.
Proof.
apply: leqnn. (* finds the value of parameters *)
Qed.

Lemma foo2 a : a <= 0 + a = true.
apply: leqnn. (* conversion took care of aligning a and 0 + a *)
Qed.

End sandbox2.

(*** Propositions as types, 
  proofs as programs ***)


Module sandbox3.

(* This is our first implication, a simple arrow.*)
Lemma tauto (A : Prop) : A -> A.
Proof.
move=> hA.
apply: hA.
Qed.

About tauto.
Print tauto.

Definition tauto' (A : Prop) : A -> A := fun x => x.

About tauto'.
Print tauto'.

Check forall A : Prop, A -> A.

Check erefl.

(* We can define proof terms using definitions *)
Definition negbK (b : bool) : negb (negb b) = b :=
  match b with 
    true => erefl 
  | false => erefl
end.


(* We can define functions in interactive mode *)

Definition negb (b : bool) : bool.
case: b.
- apply: false.
- apply: true.
Defined.

Eval compute in (negb true).

End sandbox3.

(* Statements with parameter variables of type nat, bool, etc. are 
types depending on these variables. They are called dependent products. *)
Check muln_eq0. 
Check forall m n : nat, (m * n == 0) = (m == 0) || (n == 0).
(* on paper, ∀ is sometimes also denoted Π:
  Π m : nat, Π n : nat, (m * n == 0) = (m == 0) || (n == 0). *)

(* muln_eq0 is a type of functions taking two arguments and computing a proof
   of the corresponding instance of the statement *)
Check muln_eq0 3 4.

(* The 'apply' tactic juste computes the appropriate arguments from the goal. *)

(* This correspondence goes a long way: 
- conjunctions are stated as types of pairs, whose proofs are pairs of proofs, 
- disjunctions are stated as sum types, whose proofs are either a proof of one 
  branch or a proof of the other branch.
- proofs of existential statements are a pair of a witness and a proof,
etc.

As a result, Coq's type theory and the corresponding programming language 
provides alone the rules of the logic, and the syntax of proofs. Proof checking
is type checking.

*)

(** Back to proofs by induction **)

Module sandbox4.

(* Mind the messages output by Coq *)
Inductive nat : Set := O | S : nat -> nat.

Check nat_ind.

(* In Coq, the primitive concept is in fact the 'match' and 'fix' terms *)
Print nat_ind.

End sandbox4.

(* But `nat_ind` is what the 'elim' tactic uses *)

Module sandbox5.
Lemma leqnn n : n <= n. 
Proof.
Fail apply: nat_ind.
(* Guessing P is too hard for apply' s heuristic*)
apply: (nat_ind (fun k =>  k <= k)).
(* and this argument is what is guessed by the elim tactic, which
 moreover has intro pattern facilities. *)
Admitted.


(*** Automation ***)

(** Proofs by computational reflection **)

Variables (dom : Type) (op2 : dom -> dom -> dom) (z u : dom).

(* We assume op2 x z = op2 z x = x for any x *)
Hypothesis (op2zd : left_id z op2).
Hypothesis (op2dz : right_id z op2).

(* A useful auxiliary data structure: abstract syntax trees *)
Inductive expr :=
  Zero | One | Op2 : expr -> expr -> expr.

(* Evaluation of an expr to a term of type dom: *)
Fixpoint eval_expr (e : expr) : dom :=
  match e with
  |Zero => z
  |One => u
  |Op2 e1 e2 => op2 (eval_expr e1) (eval_expr e2)
  end.

(* Normalization, i.e. ereasing occurrences of z *)
Fixpoint normal_expr (e : expr) : expr :=
  match e with
  |Zero => e
  |One => e
  |Op2 e1 e2 =>
   let ne1 := normal_expr e1 in
   if ne1 is Zero then normal_expr e2
   else
     let ne2 := normal_expr e2 in
     if ne2 is Zero then ne1 else Op2 ne1 ne2
  end.

(* Correctness theorem, relies on 
the assumptions on op2 and z and u.
This version provides a semi-decision procedure in dom. *)
Lemma normal_correct (e1 e2 : expr) :
  normal_expr e1 = normal_expr e2 ->
  eval_expr e1 = eval_expr e2.
Proof.
Admitted.

(* If an oracle guesses e1 and e2, we can prove this identity
"by computation" *)
Lemma baz : op2 z (op2 u z) = u.
Proof.
pose e1 := Op2 Zero (Op2 One Zero).
pose e2 := One.
apply: (normal_correct e1 e2). by [].
Qed.

(* We cannot implement such an oracle as a Coq function, but we could
use, e.g. the Ltac metalanguage available at top-level. *)

(* The latter example is a baby ring tactic. Here is the real one: *)
Open Scope nat_scope.

Lemma ring_test (f : nat -> bool) (b : bool) (n m : nat) (k : nat):
  (if (f k) then n else m) + 2 * m  + 0 * n =
  m + (if (f k) then n else m) + m.
Proof.
  ring.
Qed.


(** Proofs by type inference **)

Fixpoint even (n : nat) : bool := 
  match n with
  |0 => true
  |S k => negb (even k)
  end.

Lemma even0 : even 0. Proof. by []. Qed.

Lemma even_double n : even (2 * n). Admitted.

Lemma even_add n m : even n -> even m -> even (n + m). Admitted.


Section ManifestEvenNumbers.

Variable P : nat -> Prop.

Hypothesis Peven : forall n : nat, even n -> P n.

Lemma foo_curry n m : P ( (2 * n + 0) + 2 * m + 0).
Proof.
apply: Peven.
(* boring and fragile: calls for an automation tactic... *)
apply: even_add; last by exact: even0.
apply: even_add; last by exact: even_double.
apply: even_add; last exact: even0.
exact: even_double.
Qed.

(* Let us try a different approach, based on so-called sigma-types *)

Record even_nat := EvenNat {val : nat; even_val : even val = true}.

(* - Inhabitants of even_nat are pairs of a natural number n, 
and a proof that it is even. 
   - EvenNat is the constructor of this (inductive) type
   - val is the first projection, onto the natural number
   - even_val is the second projection, onto the proof.
*)

(* Using our theory of even, we can build elements of even_nat *)
Canonical even_nat0 := EvenNat _ even0.

Canonical even_nat_double (n : nat) := EvenNat _ (even_double n).

Canonical even_nat_add (n m : even_nat) := 
  EvenNat _ (even_add _ _ (even_val n) (even_val m)). 

Hypothesis Peven_uncurry : forall n : even_nat, P (val n).

Lemma foo_uncurry (n m : nat) : P ( (2 * n + 0) + 2 * m + 0).
Proof.
apply: Peven_uncurry.
Qed.

(* Our "Canonical" declarations have added hints to the unification
   algorithm, which provide canonical solutions to otherwise
   unsolvable unification problems. *)

(* See also "Canonical Structures for the Working Coq User" AM and E. Tassi *)
End ManifestEvenNumbers.
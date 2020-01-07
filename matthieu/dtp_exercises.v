From Coq Require Import Program List Lia ssreflect.
Close Scope boolean_if_scope. 
Open Scope general_if_scope.
Require Import Equations.Prop.Subterm.
Obligation Tactic := program_simpl.
Axiom todo : forall {A}, A.
Ltac todo := apply: todo.

(** Exercises on dependent pattern-matching and recursion.
  Lecture at CASS 2020. *)

(** * Subset types *)

Definition non_zero n :=
  match n with
  | 0 => false
  | S _ => true
  end.

(* Give witnesses of the following types:
  - a function that increments a number, returning a proof that it is non-zero.
  - a function that takes two positive natural numbers, and returns their addition 
    as another positive natural number. *)

Program Definition incr_numbner (n : nat) : { n' : nat | todo } := todo.

Program Definition add_pos : todo := todo.

(** ** Buffer*)(**

  We define a type buffer that can hold 0 to 2 values of a type [A].*)

Inductive buffer A : Type :=
| empty : buffer A
| one : A -> buffer A
| two : A -> A -> buffer A.

(** Exercise: Define two boolean predicates that tell if a buffer is empty or full,
    named [empty_buffer] and [full_buffer]. *)

(** Exercise: Using Program and subset types, Write functions [give] that removes an
   element from a non-empty buffer 
   and [take] that adds an element to a non-full buffer. *)

(** ** Filter*)(**

  Give a strong specification and program a variant of [filter] on lists
  that returns the filtered list and a proof that all its elements 
  satisfy the predicate. You can use the [In] predicate to express
  membership in the list [r]. To reflect [if then else] 
  conditionals on booleans, used the [dec] combinator that transforms
  a boolean b into a proof of [{ b = true } + { b = false }]. *)

Check In.

Program Fixpoint filter_dep {A} (l : list A) (p : A -> bool) : { r : list A | todo } := 
  match l with
  | [] => []
  | x :: xs => todo
  end.
Next Obligation. todo. Defined. (* Use defined to let the guardedness check look at the proof *)


(** * Dependent elimination: *)
(** We define the following indexed inductive type: *)

Inductive excl_or : bool -> bool -> Prop :=
| excl_or_left : excl_or true false
| excl_or_right : excl_or false true.

(** The proposition [excl_or p q] is inhabited only if p is true and q is false or vice-versa *)

(** Show that <= and > have mutually exclusive results: *)

Definition gtb x y := Nat.ltb y x.

Lemma leqb_gt_excl n m :  excl_or (Nat.leb n m) (gtb n m).
Proof.
  todo.
Qed.

(** A typical use of this property is to dependently eliminate
  the proof of [excl_or] in a goal containing occurrences of [Nat.leb]
  and [gtb]: this will replace all occurrences with either [true] and [false],
  cutting down the 2^2 possible boolean combinations down to the two combinations
  of interest:
*)

Lemma test_leb {A} n m (t f : A) : (if Nat.leb n m then t else f) = (if gtb n m then f else t).
Proof.
  case: (leqb_gt_excl n m). all:reflexivity.
Qed.

(** This uses a dependent elimination of the [excl_or] inductive.

  Following this example, prove the following proposition 
  using dependent pattern-matching explicitely.
  Use the [refine] tactic to gradually build the proof term. *)

Lemma excl_or_neq b b' : excl_or b b' -> b <> b'.
Proof.
  move=> p.
  (* refine (match p in excl_or b b' return _ with end). *)
Admitted.

(** The exact same principle applies to the elimination of the [reflect] predicate
  seen in the first lecture. *)

(** ** A small universe*)(**

  Indexed inductive types are often used to reflect the typing structure of values
  in some particular domain. Here we define type code for natural and boolean values:
*)

Inductive ty := Nat | Bool.

(** We can then make a new type of natural or boolean values, indexed by the type code: *)

Inductive val : ty -> Set :=
| nat_val : nat -> val Nat
| bool_val : bool -> val Bool.

(** A value in [val ty] can either be a natural number when [ty] is [Nat] or a boolean
  when [ty] is [Bool]. This allows to write generic functions that can work on either
   natural or boolean values. Here: a function that tests if the value is the least
   value in the naturals or booleans (false is considered below true). *)

Definition val_bottom {ty} (v : val ty) : bool :=
  match v with
  | nat_val 0 => true
  | nat_val (S _) => false
  | bool_val false => true
  | bool_val true =>  false
  end.

(** Moreover, using dependent elimination, we can write *type-preserving* functions, that
   ensure that if the generic operation takes a value in type [ty] it returns a value in the
   same type. Write such a function [val_incr] that takes a nat or bool value and increments it
   (adding 1 to the natural, and mapping true and false to true) *)

Definition val_incr {ty} (v : val ty) : val ty := todo.

(** State and prove a lemma showing that for any typ and [val] [v] of this type, 
    val_bottom of val_incr of this value always returns false. *)

Lemma val_incr_bottom : todo.
Proof. todo. Qed.

(** * Well-founded recursion *)

(** ** Quicksort:*)(**

  Quicksort is not a structurally recursive definition:

[[
  qs : list A -> list A
  qs [] = []
  qs (x :: xs) = qs lower ++ (x :: qs upper) 
    where lower = filter (fun y => y <= x) xs
          upper = filter (fun y => x < y) xs          
]] 

  Using Program Fixpoint, find a measure for which this function is terminating
  and solve the corresponding proof obligations. Use [About filter] to find lemmas
  related to [skipn] and the [lia] decision procedure to solve arithmetic goals. 
    You can consult the fine reference manual page for help: 
      https://coq.inria.fr/refman/addendum/program.html#coq:cmd.program-fixpoint 

  You will need to prove lemmas about the relation of [filter] and [length] to
   solve the generated obligations. 
  You can use the [Nat.leb] and [Nat.ltb] functions to program the comparisons.
  *)

Program Fixpoint qs {A} (l : list A) : list A := todo.

(** *** Extra exercise, Difficult (requires inductive predicates): prove the correctness properties of QuickSort.*)(**

    - First show that the returned list has the same elements as the first one.
    - Then that the list is sorted, using the [Sorted] predicate below.
      You will need lemmas about concatenation of [Sorted] lists and use
      the [last] function on lists.
*)

Inductive HdRel (A : Type) (R : A -> A -> Prop) (a : A) : list A -> Prop :=
| HdRel_nil : HdRel A R a nil
| HdRel_cons : forall (b : A) (l : list A), R a b -> HdRel A R a (b :: l).

Inductive Sorted (A : Type) (R : A -> A -> Prop) : list A -> Prop :=
| Sorted_nil : Sorted A R nil
| Sorted_cons : forall (a : A) (l : list A), HdRel A R a l -> Sorted A R l ->
    Sorted A R (a :: l).

(** ** Merge sort function*)(**
  
  Suppose now we want to implement a merging sort algorithm: as a building block,
  we need a function that takes two sorted lists and interleaves their elements 
  to produce a sorted lists containing the two original lists. Use [Nat.ltb] to
  compare the head elements of the two lists.
  *)

Fixpoint merge (l l' : list nat) : list nat := 
match l, l' with
| [], l' => l'
| l, [] => l
| a :: l, a' :: l' => todo
end.

(** Again, this function is not structurally recursive, as the recursive calls will 
  make only one of the arguments decrease. Use a measure to show its termination. *)

Check merge.

(** ** Ackermann*)(**

  The ackermann function is a standard example of non-primitive recursive 
  definition. As such, it falls outside the syntactic guard criterion of recursive
  definitions: 
*)

Fail Fixpoint ackermann (m n : nat) : nat :=
  match m, n with
  | 0, 0 => 1
  | 0, S n' => S (S n')
  | S m', 0 => ackermann m' 1
  | S m', S n' => ackermann m' (ackermann (S m') n')
  end.

(** Indeed [ackermann] is neither structurally recursive on [m] or [n] as 
  we call [ackerman] on [S m'] in the inner recursive call (not a strict subterm of [m])
  and on [m'] (a strict subterm of [m]) and [ackermann (S m') n'] (not a subterm of [n]) 
  in the outer one. 

  The function is however well-founded on the *lexicographic* ordering of the pair of
  arguments [(m, n)]:
  at each recursive call, either the first argument [m] decreases strictly or it stays 
  the same but the second argument decreases strictly. *)

(* Using the [wf] annotation of Program and using the [Subterm.lexprod] definition of lexicographic
   ordering of two relations, define the ackermann function *)

Program Fixpoint ackermann (p : nat * nat) (* { wf todo p } *) : nat := todo.

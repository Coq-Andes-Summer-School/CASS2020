From mathcomp Require Import all_ssreflect.

(* Implement the exclusive disjunction on booleans.
   Remember that (negb b) is the negation of boolean b. *)

Definition xorb b := if b then negb else id.

Lemma xorTb b : xorb true b = ~~ b. 
Proof. by []. Qed.

Lemma xorbN a b : xorb a (negb b) = negb (xorb a b).
Proof. by case: a; case: b. Qed.

(* Implement a boolean equality test on natural numbers *)
Fixpoint eqn (m n : nat) : bool := 
  match m, n with
  | 0, 0 => true
  | S m', S n' => eqn m' n'
  | _, _ => false
  end.

Lemma eq_eqn (n m : nat) : n = m -> eqn n m = true.
Proof.
move=>-> {n}.
by elim: m => [ |m].
Qed.

Lemma eqn_eq n m : eqn n m = true -> n = m.
Proof.
elim: n m => [| n ihn]; case=> [| m] //=.
by move/ihn->.
Qed.

(* Define an inductive type for binary trees (without labels) *)

Inductive tree : Set :=
| Leaf : tree
| Parent : tree -> tree -> tree.


(* Define a function counting the number of nodes in a tree *)

Fixpoint size  (t : tree) : nat :=
  match t with
  | Leaf => 1
  | Parent l r => size l + size r
  end.

(* Define a tree with one node, with three nodes, and test your size function *)

Definition one_tree : tree := Leaf.

Definition three_tree : tree :=
  Parent (Parent Leaf Leaf) Leaf.

Eval compute in size one_tree.

Eval compute in size three_tree.

(* Define a function counting the depth of the tree.
Hint: you can use the function
maxn : nat -> nat -> nat
to compute the maximum of two natural numbers.
 *)
Fixpoint depth (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Parent l r => S (maxn (depth l) (depth r))
  end.

(* Test your depth function *)

Eval compute in depth one_tree.

Eval compute in depth three_tree.

Eval compute in depth (Parent Leaf (Parent Leaf Leaf)).

(* State and prove that the size of a binary_tree is always positive. *)
(* Note that we can ommit the _ = true because of the is_true
  coercion. *)
Lemma lt0_size (t : tree) : 0 < size t.
Proof.
 (* /= simplifies by computation, // closes trivial subgoals, //= does both.*)
elim: t => [| t1 iht1 t2 ih2] //=.
by rewrite addn_gt0 iht1.
Qed.

(* State and prove that the height is smaller than the number of nodes. *)

Lemma leq_depth_size (t : tree) : depth t <= size t.
Proof.
elim: t => [| t1 iht1 t2 iht2] /=; first by [].
wlog h : t1 t2 iht1 iht2 / depth t1 <= depth t2.
  move=> hwlog.
  case/orP: (leq_total (depth t1) (depth t2)) => [le12 | le21].
  - exact: hwlog.
  - by rewrite addnC maxnC; apply: hwlog.
move/maxn_idPr: h->.
suff : size t2 < size t1 + size t2 by apply: leq_ltn_trans.
(* The last rewrite item lt0_addr works becuase it is in fact an equality
0 < size t = true *)
by rewrite -[X in X < _]add0n ltn_add2r lt0_size.
Qed.

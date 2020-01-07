From mathcomp Require Import all_ssreflect.

(* Implement the exclusive disjunction on booleans *)

Definition xorb b := (* your definition here *)

Lemma xorTb b : xorb true b = ~~ b. 
Proof. 
admit. 
(* your proof here *)
Admitted. (* turn into Qed once done *)

Lemma xorbN a b : xorb a (negb b) = negb (xorb a b).
Proof. 
admit. 
(* your proof here *)
Admitted. (* turned into Qed once done *)


(* Implement a boolean equality test on natural numbers *)
Fixpoint eqn (m n : nat) : bool := (* your definition here *)

Lemma eq_eqn (n m : nat) : n = m -> eqn n m = true. Admitted.

Lemma eqn_eq  (n m : nat) : eqn n m = true -> n = m. Admitted.

(* Define an inductive type for binary trees (without labels) *)

Inductive tree : Set := (* your definition here *)

(* Define a function counting the number of nodes in a tree *)

Fixpoint size  (t : tree) : nat := (* your definition here *)

(* Define a tree with one node, with three nodes, and test your size function *)

Definition one_tree : tree :=  (* your definition here *)

Definition three_tree : tree :=  (* your definition here *)

Eval compute in size one_tree.

Eval compute in size three_tree.


(* Define a function counting the depth of the tree.
Hint: you can use the function
maxn : nat -> nat -> nat
to compute the maximum of two natural numbers.
 *)
Fixpoint depth (t : tree) : nat :=  (* your definition here *)

(* Test your depth function *)

(* State and prove that the size of a binary_tree is always positive. *)
Lemma lt0_size (t : tree) :  (* your statement here *).
Proof.
(* your proof here *)
Qed.

(* State and prove that the height is smaller than the number of nodes. *)
Lemma leq_depth_size  (t : tree) : (* your statement here *).
Proof.
(* your proof here *)
Qed.

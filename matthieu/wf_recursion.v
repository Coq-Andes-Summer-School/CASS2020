(** printing < %\ensuremath{<}% *)
(** printing > %\ensuremath{>}% *)
(**
%\begin{frame}{Program Example}% *)
(* begin hide *)
Require Import ssreflect.
Require Import Arith Lia Program.
Close Scope boolean_if_scope. 
Open Scope general_if_scope.
Extraction Inline proj1_sig projT2 projT1 Sumbool.sumbool_of_bool.
Obligation Tactic := program_simpl.
(* end hide *)

Program Fixpoint euclid (x : nat)
        (y : nat | 0 < y) (* Binder for subsets *)
        { wf lt x } : (* Wellfounded definition *)
  { (q, r) : nat * nat | x = q * y + r } (* Rich type *) := 
  if dec (Nat.ltb x y) then (0, x)
  else let 'pair q r := euclid (x - y) y in
      (S q, r).

Next Obligation. move/Nat.ltb_ge: H. lia. Qed.
Next Obligation.
  move: Heq_anonymous.
  case: euclid => [[q' r'] H']; simpl in * => [= -> -> ].
  move/Nat.ltb_ge: e. lia.
Defined.

(* begin hide *)
Extraction Inline euclid_func.
Recursive Extraction euclid.
(* end hide *)
(**
%\end{frame}% *)

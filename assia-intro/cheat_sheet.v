From mathcomp Require Import all_ssreflect.

(* Coq Andes Summer School Cheat Sheet. *)
(* Some parts are copied/adapted from:*)
(* https://github.com/coq/coq/wiki/Quick-Reference-for-Beginners *)
(* For a complete reference see the Coq Reference Manual: *)
(*  (https://coq.inria.fr/distrib/current/refman/index.html *)

(*** Structure of the document:***)

(*
= Declarations:
  Definition
  Argument
  Fixpoint
  Lemma
  Theorem


= Management of the goal: 
introduction
generalization
clearing

= Trivial proofs:
computation
assumption
hints

= Proofs on inductive definitions:
case analysis
induction

= Logical connectives in Prop:
implication
universal quantification
conjunction
disjunction
negation
existential
double implication
reflect

= Rewriting, congruence

= Queries and Inspection:
  Search
  About
  Check
  Print

*)


(*** Declarations ***)

(* Definition :
   A [Definition] declares a term, a type, a proposition, or a non-recursive
   function. It looks like:

     Definition <name> : <type> := <value>.

   It's possible to omit the <type> if Coq can infer it from the value, which
   then looks like:

     Definition <name> := <value>.

   But we strongly suggest that you enforce type annotations in definitions,
   for the sake of documentation and robustness.

   For functions, the arguments can go before or after the colon. That is, saying:

     Definition <name> : <type1> -> <type2> -> <type3> := 
     fun <argname> <argname> => <body>

   ...is equivalent to:

     Definition <name> (<argname> : <type1>) : <type2> -> <type3> := 
     fun <argname> => <body>
     Definition <name> (<argname> : <type1>) (<argname : <type2>) : <type3> := 
     <body>
 *)

Module DefinitionExamples.
  (* defining numbers *)
  Definition x : nat := 5.
  Definition y := 5. 
  (* y is a [nat], because of the default notation scope. Handle with care...*)

  (* defining (non inductive) types *)
  Definition two_nats : Type := nat * nat. 
  (* represents a pair of natural numbers, using an infix notation for 
     the type [prod] used in the 1st lecture. *)

  (* defining functions *)
  Definition add2 : nat -> nat := fun n => n + 2.
  Definition add3 (n : nat) : nat := n + 3.
  Definition make_pair : nat -> nat -> two_nats := fun n m => (n, m).

  (* The following are all equivalent to [make_pair] *)
  Definition make_pair' (a : nat) : nat -> two_nats := fun b => (a,b).
  Definition make_pair'' (a : nat) (b : nat) : two_nats := (a,b).
  Definition make_pair''' (a b : nat) : two_nats := (a,b).

  (* Definitions by case analysis on an inductive argument *)
  Definition is_zero (n : nat) : bool :=
    match n with
      |0 => true
      |S k => false
    end.

  (* Case analysis on a boolean can use a specific if ... then ... else ...
    syntax *)
  Definition neg_bool (b : bool) : bool := if b then false else true.

  (* defining propositions and predicates *)
  Definition nat_pos : Prop := forall x : nat, 0 <= x.
  Definition nat_pos' (x : nat) : Prop := 0 <= x. (* equivalent to [nat_pos] *)

  (* This [Prop] is false; you wouldn't be able to prove it, 
     but you can state it because the sentence is well-typed. *)
  Definition nat_neg : Prop := forall x : nat, x < 0.

  (* This one is not well-typed *)
  Fail Definition nat_boo : Prop := 5 = cons 2 nil.

  (* This one looks ill-typed, but a coercion has been inserted *)
  Definition bool_pos : Prop := forall b : bool, b < 2.

  (* See the "Queries and Inspection" section *)
    Set Printing Coercions.
    Print bool_pos.
    Print nat_of_bool.

  (* Turning an argument into an implicit one *)
   Definition foo (A : Set) (x : A) : A := x.

   About foo.

   Check foo nat 1.

   (* Curly braces indicate an implicit argument *)
   Arguments foo {A} x.

   About foo.
   Fail  Check foo nat 1.

   Check foo 1.

   (* Another option is to use curly braces at the time of
   definition *)
   Definition foo_impl {A : Set} (x : A) : A := x.

   Check foo_impl 1.

   (* The Argument command in fact allows to fine-tune a definition
   with several more options. See the reference manual. *)

End DefinitionExamples.


(* Fixpoint :
   [Fixpoint] defines a *recursive* function. Syntax is similar to [Definition]:

     Fixpoint <name> : <type> := 
     fun <arguments...> => <body>.
     Fixpoint <name> (<argname> : <type>) (argname : <type>) ... : <type> := 
     <body>.

  Such a definition is accepted if termination is ensured by a recursive call
  on a strict subterm. 
 *)

Module FixpointExamples.
  (* loop and decrement n until we reach 0 *)
  Fixpoint countdown (n : nat) : nat :=
    match n with
    | O => n
    | S x => countdown x 
    (* "x" is the name I chose for n's predecessor; changing
       the name won't break anything *)
    end.

  (* naive exponentiation : if the fixpoint has more than one inductive 
     argument, it is useful to document which one is decreasing, for the sake of
     documentation. *)
  Fixpoint power_of (b : nat) (e : nat) {struct e} : nat :=
    match e with
    | O => 1 (* returns 1 if e = 0 *)
    | S n => b * power_of b n (* if e = n + 1 for some n, return b * b^n with a
                                 recursive call *)
    end.

End FixpointExamples.

(* Lemma :
   [Lemma] is the most common type of proof declaration. It allows to define a 
   term using a gradual, interactive construction, possibly using 
   instructions called tactics. This mode of interaction is called "proof-mode".

The syntax looks like:

      Lemma <name> : <proof statement>.
      Proof.
        <proof body>
      Qed.
  
  [Theorem], [Remark], [Corollary ] are synonyms.

   You can omit writing [Proof] before your proof, but it's convention, and
   visually helps separate the proof from the proof statement when the statement
   is long and complicated.

   The <proof statement> can in fact be any type, but it is usually a type 
   of type [Prop].
*)


(*
   If you don't finish your proof but want to exit your lemma, you can't use
   [Qed]. Instead, you have two options: [Admitted]. 
   This will let other proofs see and use your unfinished
   lemma, even though you haven't yet proven it. Naturally, this means it's
   important to remember if you're depending on an admitted lemma, because it
   means your top-level proof might not be correct. To see the admitted proofs
   a lemma or theorem depends on, type [Print Assumptions <lemma/theorem name>].
 *)
Module LemmaExamples.
  (* [True] has the type [Prop], so it technically counts as a proof statement *)
  Lemma simple : True.
  Proof.
    by []. (* in this case, we just tell Coq "this proof is easy". See
   the "Trivial Proofs" section below" *)
  Qed.

  (* Lemmas can take arguments, like definitions. These are parameters of the
  statement, i.e. prenex universal quantification. *)
  Lemma nat_nonneg (a : nat) : 0 <= a.
  Proof.
    by [].
  Qed.

(* We could also have stated the lemma as:
  Lemma nat_nonneg : forall (a : nat),  0 <= a.
but the previous version saves us the bureaucracy of introducing (naming) 
the parameters in the context. *)

 Lemma nat_nonneg' (a : nat) : 0 <= a.
  Proof.
    admit. (* give up the current branch of the proof. *)
  Admitted.
End LemmaExamples.

(*** Management of the goal ***)


(* A proof in progress looks like this in the dedicated buffer:

<name1> : <type1>
<name1> : <type1>
...
<namek> : <typek>
===================
<statement>

What is above the ===== is the proof context, a list of named 
assumptions, with their type. What is above the ==== is a type,
with possible prenex quantification and arrows. Part of the
formal proof, the boring one, deals with moving items around
the ====. Only the top most assumption or quantified variable
can be named and used to the context: this is an introduction step.
Any item from the context can be pushed on top of the statement
(provided that this complies with possible dependencies): this
is a generalization step. *)

Module ManagementExamples.

Lemma leq_addr (n m : nat) : n <= n + m.
Proof.
(* generalization *)
move: n.
(* introduction *)
move=> n.
(* generalizing several items at once *)
move: n m.
(* introducing several items at once *)
move=> n m.
(* generalizing a subterm *)
move: (n + m). Undo.
(* generalizing a subterm and introducing it in one go *)
move: (n + m) => k. Undo.
(* Same, and clearing m in passing *)
move: (n + m) => k {m}.
Admitted.

End ManagementExamples.

(*** Trivial Proofs ***)

(* As much as possible, simple proofs = short scripts.
The [by []] tactic solves trivial goals, and fails if it did not work.
Trivial here means:*)

Module TrivialExamples.

(* By computation *)
Lemma three_plus_two : 3 + 2 = 5. Proof. by []. Qed.

(* Because the current goal corresponds to a hypothesis in the *)
(* context or in the premise. *)
Lemma is_assumption (n m :nat) : n <= m -> n = m + 34 -> n <= m.
Proof.
by [].
Qed.

(* Because the current goal is an instance of a database of hints *)
Lemma leqnn_hint (n : nat) : n <= n.
Proof. by []. Qed.

(* The database of hints can be extended using the command:
Hint Resolve <name of the lemma>.

A resolving hint should not feature preconditions (the statement should 
 not be an implication, as these would not be solved by the [by []] tactic.
*)

(* Finally, in non-trivial proof, a final call to [[by []]] can be
   replaced by a prenex [by]. It is a good practice to tag the line
   terminating a proof with such a prenex [by], but this is specially
   useful in the case of proofs with subgoals (e.g., case analysis). *)

(* Tactics used in this proof are explained in the next sections. *)
Lemma prenex_by (n m : nat) : n = m -> n + m = n + n.
Proof. by move=> e; rewrite e. Qed.

End TrivialExamples.


(*** Proofs on inductive definitions ***)


Module ProofsInductiveDefinitionsExamples.

(* Case analysis on bool *)

(* Note that (~~ b) denotes (negb b), not to be confused with *)

Lemma bool_tauto (b1 b2 : bool) : b1 || ~~ b1.
Proof.
case: b1. (* opens two subgoals, we use [-] bullet to mark the *)
          (* paragraph devoted to each of them, respectively. Other *)
          (* available bullets are [+] and [*] *)
- by [].
- by [].
Qed.

Lemma bool_tauto_better (b1 b2 : bool) : b1 || ~~ b1.
Proof.
by case: b1.
Qed.

(* Below, term (S n) is denoted with a postfix notation n.+1 *)

(* Simple case analysis on nat *)
Lemma leqn0 n : (n <= 0) = (n == 0).  Proof. by case: n. Qed.

(* But often, we need to name the extra variable created in the second *)
(* branch of the case analysis. We do so using a so-called *)
(* intro-pattern. Intro-patterns are the features that take care of *)
(* the bureaucracy generated by a previous tactic. Intro-patterns *)
(* happen after an arrow [=>]. The most obvious thing we want to do is *)
(* naming, and that what the move => <name1> <name2> did. We do the *)
(* same, here but a bracket allows to give names in parallel to the *)
(* material relevant to each subgoal. *)

Lemma leqn0_name n : (n <= 0) = (n == 0).  Proof. by case: n => [| k]. Qed.

(* Simple induction on nat *)

Lemma leqnn n : n <= n.
Proof.
elim: n => [| k].
- by [].
- by [].
Qed.

(* Generalizing before starting induction *)

Lemma leqNgt0 m n : (m <= n) = ~~ (n < m).
Proof. 
elim: m n => [|m IHm]. 
- move=> k. by [].
- move=> k. case: k.
  +  by [].
  +  by [].
Qed.

(* Introducing a variable in both branches *)
Lemma leqNgt1 m n : (m <= n) = ~~ (n < m).
Proof. 
elim: m n => [|m IHm] k.  
- by [].
- case: k.
  +  by [].
  +  by [].
Qed.

(* Killing trivial subgoal with the // switch before introducing a *)
(* variable in the remaining branches *)
Lemma leqNgt2 m n : (m <= n) = ~~ (n < m).
Proof. 
elim: m n => [|m IHm] // k.  
- case: k.
  +  by [].
  +  by [].
Qed.

(* Killing trivial subgoal with the // switch before performing a *)
(* case analysis on a variable in the remaining branches. *)
Lemma leqNgt3 m n : (m <= n) = ~~ (n < m).
Proof. 
elim: m n => [|m IHm] // [].  
  +  by [].
  +  by [].
Qed.

(* Factoring the [by] *)
Lemma leqNgt4 m n : (m <= n) = ~~ (n < m).
Proof. 
by elim: m n => [|m IHm] // [].  
Qed.

(* Simplification in an intro pattern: /= simplifies both goals by *)
(* computation and can be inserted anywhere in an intro-pattern. It *)
(* is often useful after an case analysis*)

Lemma simpl_switch_bool b1 b2 : b1 && b2 = b2 && b1.
Proof. 
case: b1 => /=.
Admitted.

(* predn is the predecessor on nat (predn 0 == 0) and has postfix *)
(* notation .-1 *)
Lemma leq_pred1 n : n.-1 <= n. 
Proof. 
case: n => [| k] /=. 
- by [].
- by [].
Qed.

(* Combining simplification and closing of trivial branches: //= *)
Lemma leq_pred2 n : n.-1 <= n. 
Proof. 
case: n => [| k] //=. 
Qed.

(* For this simple lemma, the shortest proof script would not require *)
(* these switch. *)
Lemma leq_pred3 n : n.-1 <= n. 
Proof.  by case: n. Qed.


End ProofsInductiveDefinitionsExamples.


(*** Logical connectives in Prop ***)



Module ConnectiveExamples.


(* True is a unit type (an inductive singleton type) in Prop*)
Print True.

(* False is the empty type: an inductive with no constructor. *)
Print False.

(* Stating and proving an implication *)
Lemma impl_intro (A B : Prop) : A -> B -> A.
Proof.
move=>hA hB.
by [].
Qed.

(* Using an implication by modus ponens on the goal *)
Lemma impl_elim1 (A B : Prop) : (A -> B) -> A -> B.
Proof.
move=> hAB hA.
apply: hAB.
by [].
Qed.

(* [exact] is the combination or apply and by *)
Lemma impl_elim1' (A B : Prop) : (A -> B) -> A -> B.
Proof.
move=> hAB hA.
exact: hAB.
Qed.



(* Using an implication by modus ponens on the context *)
Lemma impl_elim2 (A B : Prop) : (A -> B) -> A -> B.
Proof.
move=> hAB hA.
move/hAB: hA. (* hA is generalized, then given as argument to hAB, and *)
              (* the resulting term is generalized. *)
by [].
Qed.

(* Using an implication by modus ponens on the context *)
Lemma impl_elim3 (A B : Prop) : (A -> B) -> A -> B.
Proof.
move=> hAB hA.
move/hAB: hA => hB. (* same as before, but introducing the resulting *)
              (* application using the name hB *)
by [].
Qed.

(* Using an implication by modus ponens on the context, in the intro pattern*)
Lemma impl_elim4 (A B : Prop) : (A -> B) -> A -> B.
Proof.
move=> hAB /hAB hB.
by [].
Qed.


(* The corresponding tactics to conjunction, disjunction, existential *)
(* statements are tightly linked to the fact that the underlying *)
(* data-structures of the proofs are terms of inductive types. *)


(* Stating an proving a conjunction *)
Lemma conj_intro (A B : Prop) : A -> B -> A /\ B.
Proof.
move=> hA hB.
split. (* creates two subgoals, for each component *)
- by [].
- by [].
Qed.

(* Using a conjunction *)
Lemma conj_elim_r (A B : Prop) : A /\ B -> B.
Proof.
move=> hAoB.
case: hAoB => hA hB. (* creates two hypothesis, that we name in one go *)
by [].
Qed.


(* Stating and proving a disjunction *)
Lemma disj_intro_r (A B : Prop) : B -> A \/ B.
Proof.
move=> hB.
(* we chose which side we will prove *)
right. (* or [left] for the other one *)
by [].
Qed.

(* Using a disjunction *)
Lemma disj_elim (A B : Prop) : A \/ B -> B \/ A.
Proof.
move=> AoB.
case: AoB => [hA | hB]. (* creates two subgoals, and we name the *)
                      (* hypothesis created in each case *)
- by right.
- by left.
Qed.


(* Negation of A is denoted ~ A, which unfolds to A -> False. So *)
(* working with negation is basically similar to working with *)
(* implication. *)


(* Using a negation: the [contradiction] tactic is specific to *)
(* obviously inconsistent contexts. In such cases, the tactic resorts to
   the ex False quod libert rule: *)

(* Ex Falso Quod Libet *)
Check False_ind.

Lemma neg_elim (A B : Prop) : A -> ~ A -> B.
Proof.
move=> hA nA.
contradiction.
Qed.

(* Stating and proving  a negation *)
Lemma neg_intro (A : Prop) : A -> ~ ~ A.
Proof.
move=> hA hnA.
apply: hnA.
by [].
Qed.

(* Remark: the converse implication ~ ~ A -> A is not provable without *)
(* an extra axiom, and thus proof patterns like contraposition are not *)
(* available on Prop statements. But they are in for boolean statements *)
(* Note that (~~ b) denotes (negb b), not to be confused with *)
(*   ~  ~  b with unfolds to ~ (~ (b = true)) *)

Lemma bool_neg_neg (b : bool) : ~~ (~~ b) = b.
Proof. by case: b. Qed.

(* Contraposition:
contra : forall c b : bool, (c -> b) -> ~~ b -> ~~ c
 *) 
About contra.
(* And variants, e.g., *)
About contraLR.

(* Stating and proving  a disjunction, with boolean predicates *)
Lemma neg_intro_with_bool (n : nat) : n = 0 -> ~ (0 < n).
Proof.
move=> e. (* We will see that we can use a rewrite intro pattern in the *)
         (* "Rewrite" section *)
by rewrite e. (* by computation, to ~ (false = true) *)
Qed.


(*Stating and proving an existential statement *)
Lemma ex_intro : exists n : nat, n = 0.
Proof. exists 0. by []. Qed.

(* Using an existential statement *)
Lemma ex_elim (m : nat) : (exists n : nat, m = S n) -> 0 < m.
Proof.
case=> k hk. (* k s the witness, hk is its property *)
by rewrite hk.
Qed.


(* A double implication is just the conjunction of two implications *)
Lemma equiv (A B : Prop) : A /\ B <-> B /\ A. 
Proof.
split.
- by case=> hA hB; split.
- by case=> hB hA; split.
Qed.

(* Equivalences between a term of type bool and a term of type Prop is
better stated using the [reflect] constant:

reflect <prop statement> <bool statement>

It is logically equivalent to a double implication:
 *)

About iffP. 
  (* forall (P Q : Prop) (b : bool), 
       reflect P b -> (P -> Q) -> (Q -> P) -> reflect Q b *)

About rwP. (*  forall (P : Prop) (b : bool), reflect P b -> P <-> b *)

(* Stating and proving a reflect statement. Remember that a coercion *)
(* is hiding the (_ = true) which turn booleans to Prop. *)
Lemma orP (b1 b2 : bool) : reflect (b1 \/ b2)  (b1 || b2).
Proof.
apply: (iffP idP). (* we ca use iffP to fall back to a double implication *)
- case: b1; case: b2=> //=; intuition. (* intuition is for *)
                                (* intuitionistic tautologies *)
- by case=> e; rewrite e //= orbT.
Qed.

(* Using a reflect statement. Using a view feature of the tactic *)
(* language, one can combine a deductive operation like *)
(* intro/generalization/case/elim, with a modus ponens on an item in *)
(* the context *)

Lemma reflect_use1 (b1 b2 : bool) : b1 || b2 -> ~ b1 -> b2.
Proof.
case/orP.
- by [].
- by [].
Qed.

Lemma reflect_use2 (b1 b2 : bool) : b1 \/ b2 -> (b1 || b2) || b2.
Proof.
move/orP=> e.
rewrite e. (* or more concisely move/orP=> -> *)
by [].
Qed.

End ConnectiveExamples.


(*** Rewriting, congruence ***)

Module RewriteExamples.

(* Simple rewrite, left to right *)
Lemma ex1 (n m k : nat) : n = m -> n + k = m + k.
Proof. move=> e. rewrite e. by []. Qed.


(* Right to left *)
Lemma ex2 (n m k : nat) : n = m -> n + k = m + k.
Proof. move=> e. rewrite -e. by []. Qed.

(* Several rules in one go *)
Lemma ex3 (n m k : nat) : n = m -> m = k -> n + m = k + k.
Proof. move=> e1 e2. rewrite e1 -e2. by []. Qed.

(* Rewrite instead of name in the intro pattern. *)
Lemma ex4 (n m k : nat) : n = m -> m = k -> n + m = k + k.
Proof. move=> -> <-. by []. Qed.

(* Interleaving rewriting and simplification : the /= switch *)
(* simplifies the goal(s) modulo computation *)
Lemma ex5 (n m : nat) : n = m.+1 -> ~~ (n == 0).
Proof. move=> e. rewrite e /=. by []. Qed.

(* A alternative version where everything happens in the intro pattern *)
Lemma ex6 (n m : nat) : n = m.+1 -> ~~ (n == 0).
Proof. move=> -> /=. by []. Qed.
 
(* The most concise one of course only needs the rewrite, as [by] takes *)
(* care of computation. *)

Lemma ex7 (n m : nat) : n = m.+1 -> ~~ (n == 0).
Proof. by move=> ->. Qed.

(* Selecting an occurrence with a pattern *)
Lemma ex8 (n m : nat) : n = m -> n + (n + m) = m + (n + m).
Proof.
move=> e. rewrite [X in X + _ = _]e. by [].
Qed.


(* Congruence tactic *)
Lemma congr (a b c k : nat) : a = b -> b + c = k -> a + (b + c) = b + k.
Proof.
move=> e1 e2. 
congr (_ + _).
- by [].
- by [].
Qed.

Lemma pairP (A B : Type) (a : A) (b : B) : 
  pair a b = (fst (pair a b), snd (pair a b)).
Proof. 
congr (_, _).
Qed.

(*** Inspection, Queries ***)

(* Search :

   One of the most useful commands for discovering lemmas or functions that have

   already been defined is [Search].
 *)

Module SearchExamples.

  (* simple statements : you can search about functions or about already-defined
     terms like 2, or even expressions like (1+1). *)
  Search _ muln.
  (* restricts the search to occurrences in the conclusion *)
  Search _ logn.
  Search 2.

  (* You can restrict to some given libraries *)
  Search muln in prime.


  (* You can also [Search] for things containing multiple expressions *)
  Search muln logn.


  (* We can also [Search] types, like [nat] and [list], to get every function or
  definition with that type as a subset of its type signature, and every lemma
  that has the type in its proof statement. *)
  Search nat.
  Search list in seq. (* the Mathematical Components library for lists *)
  Search (seq nat). (* look for lemmas/functions about lists of natural numbers *)
  Search _ (nat -> nat -> bool). (* look for functions that take in two natural
                                  numbers and return a boolean *)


  (* Extremely usefully, [Search] allows you to leave "blanks" in expressions
     using underscores. *)
  Search _ (_ + (_ + _)). 
  Search _ (logn _ _ = 0). (* find any lemma that says something about
                               [logn] that are 0 *)

  (* You can also use [?] to define variables, which lets you repeat them within
     the expression to narrow down your search. *)
  Search _ (?x * ?x).
  Search _ (?x * _ <= ?x * _).

  (* you can attach scope delimiters to [Search] expressions, which means that in
     this [Search] the [1]  and [*] are interpreted as the *integer* 1 and the
     function [Z.mul] (integer multiplication), instead of the *natural number* 1
     and the function [Nat.mul] (natural number multiplication). *)
  Search (_ + _)%coq_nat. (* Vanilla Coq addition on nat *)
  Search (_ + _)%N. (* Mathematical Components addition on nat *)
End SearchExamples.

(* About gives useful information about a defined constant, including
   its type and the status (implicit or not) of its argument. *)
About cons.

(* Check tries to type-check arbitrary terms *)
Check 0.
Check nat.

(* Print displays the body of a definition, and the definition of *)
(* inductive types. *)
Print negb.

Print nat.

(** 
       
                                                                  
             _____         _   _      
            |_   _|___ ___| |_|_|___  
              | | | .'|  _|  _| |  _| 
              |_| |__,|___|_| |_|___| 
                                      
      __                                    
     |  |   ___ ___ ___ _ _ ___ ___ ___ ___ 
     |  |__| .'|   | . | | | .'| . | -_|_ -|
     |_____|__,|_|_|_  |___|__,|_  |___|___|
                   |___|       |___|        
    
    
   Beta Ziliani (FAMAF, UNC y CONICET, Argentina) 




or...




   ╦ ╦┬ ┬┬ ┬  ┌─┐┌┐┌┌┬┐  ╦ ╦┌─┐┬ ┬  ┌┬┐┌─┐
   ║║║├─┤└┬┘  ├─┤│││ ││  ╠═╣│ ││││   │ │ │
   ╚╩╝┴ ┴ ┴   ┴ ┴┘└┘─┴┘  ╩ ╩└─┘└┴┘   ┴ └─┘
       ╔╗ ┬ ┬┬┬  ┌┬┐  ╦═╗┌─┐┌┐ ┬ ┬┌─┐┌┬┐  
       ╠╩╗│ │││   ││  ╠╦╝│ │├┴┐│ │└─┐ │   
       ╚═╝└─┘┴┴─┘─┴┘  ╩╚═└─┘└─┘└─┘└─┘ ┴   
     ╔═╗┬─┐┌─┐┌─┐┌─┐  ╔═╗┌─┐┬─┐┬┌─┐┌┬┐┌─┐ 
     ╠═╝├┬┘│ ││ │├┤   ╚═╗│  ├┬┘│├─┘ │ └─┐ 
     ╩  ┴└─└─┘└─┘└    ╚═╝└─┘┴└─┴┴   ┴ └─┘ 
   
      


            ... and how tactic languages help us.
*)

(** 

+------------------------------------------------+
| Why talk about building robust proofs?         |
+------------------------------------------------+
|                                                |
| Proof development is like software development |
|                                                |
| - Proofs grow iteratively                      |
|                                                |
| - Definitions changes from time to time        |
|                                                |
| - Writing code/proofs is easy, knowing what    |
|   problem to solve is the real hard part.      |
|                                                |
|        (Do not keep old code/proofs!)          |
|                                                |
+------------------------------------------------+




+------------------------------------------------+
| How to build robust proofs?                    |
+------------------------------------------------+
|                                                |
| Like with software development, you need:      |
|                                                |
| - Good abstractions.                           |
|                                                |
| - Good programming practices.                  |
|                                                |
|   + Avoid code duplication, use good naming    |
|     conventions, etc.                          |
|                                                |
|  >>> Tactic languages help us with these <<<   |
|                                                |
+------------------------------------------------+

*)


(**

 _____  _          _       _                     _ 
|  __ \(_)        | |     (_)                   | |
| |  | |_ ___  ___| | __ _ _ _ __ ___   ___ _ __| |
| |  | | / __|/ __| |/ _` | | '_ ` _ \ / _ \ '__| |
| |__| | \__ \ (__| | (_| | | | | | | |  __/ |  |_|
|_____/|_|___/\___|_|\__,_|_|_| |_| |_|\___|_|  (_)

*)

(*!
I use company-coq in Emacs. Some simbols will
display differently in your setup. At the 
bottom of this file there is a list of 
symbols used.
*)





(*!

Example: An optimized arithmetic evaluator

*)

Require Import Arith.Arith.
Require Import ssreflect.

Module Optimizer.

(**

Idea: have a syntactic representation of
arithmetic operations so we can write a sound
optimizer.

Ingredients:
- The type of arithmetic expressions [ aexp ].
- An evaluator: [ ⟦a⟧ₙ ]
- An optimizer: [ optimize a ]
- A proof of soundness: [ ⟦optimize a⟧ₙ = ⟦a⟧ₙ ]

*)

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Notation "x `+ y" := (APlus x y)
  (at level 50, left associativity).
Notation "x `- y" := (AMinus x y)
  (at level 50, left associativity).
Notation "x `* y" := (AMult x y)
  (at level 40, left associativity).
Notation "` n" := (ANum n)
  (at level 0).


(** We can evaluate an arithmetic expression *)
Reserved Notation "[[ a ]]_n".

Coercion ANum : nat >-> aexp.

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | `n => n
  | a1 `+ a2 => [[a1]]_n + [[a2]]_n
  | a1 `- a2 => [[a1]]_n - [[a2]]_n
  | a1 `* a2 => [[a1]]_n * [[a2]]_n
  end
where "[[ a ]]_n" := (aeval a).

Example test_aeval1:
  [[ 2 `+ 2 ]]_n = 4.
Proof. simpl. reflexivity. Qed.

(** ** Optimization *)

(**

The following function takes an arithmetic
expression and slightly simplifies it, changing
every occurrence of [0 `+ e] into just [e].

*)

Fixpoint optimize (a:aexp) : aexp :=
  match a with
  | `n => `n
  | 0 `+ e2 => optimize e2
  | e1 `+ e2 => (optimize e1) `+ (optimize e2)
  | e1 `- e2 => (optimize e1) `- (optimize e2)
  | e1 `* e2 => (optimize e1) `* (optimize e2)
  end.
(** (Note: there are two pattern-matches here!) *)


(** To make sure our optimization is doing the
    right thing we can test it on some examples
    and see if the output looks OK. *)

Eval compute in optimize (2 `* (0 `+ (0 `+ 1))).

(** But if we want to be sure the optimization is
    correct -- i.e., that evaluating an optimized
    expression gives the same result as the
    original -- we should prove it. *)
Theorem optimize_sound_vanilla: forall a,
  [[optimize a]]_n = [[a]]_n.

(** Proofs can be written in a variety of forms. *)

(** Vanilla Coq of An Inexperience User *)
Proof.
  intros a. induction a.
  - simpl. reflexivity.
  - destruct a1.
    + destruct n.
      * simpl. apply IHa2.
      * simpl. rewrite IHa2. reflexivity.
    + simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
Qed.

(** Problems:

  - repeats a lot of similar operations.

  - it resorts to arbitrary named variables.

  - The proof breaks at any change in the context
    or in the naming conventions in Coq.

  - What if we add...?

    [Let a1 := `1.]

*)

(** Proof without naming usign ssreflect. *)
Theorem optimize_sound: forall a,
  [[optimize a]]_n = [[a]]_n.
Proof.
  elim. (* induction on the first variable *)
  - (* ANum *)
    by []. (* trivial case *)
  - (* APlus *) case. (* case on the left expr. *)
    + (* a1 = ANum n *) case=>/=.
      * (* n = 0 *)  by [].
      * (* n <> 0 *) by move=>? _ ? -> .
    + (* a1 = APlus a1_1 a1_2 *)
      by move=> /= ? ? -> ? -> .
    + (* a1 = AMinus a1_1 a1_2 *)
      by move=> /= ? ? -> ? -> .
    + (* a1 = AMult a1_1 a1_2 *)
      by move=> /= ? ? -> ? -> .
  - (* AMinus *)
    by move=> /= ? -> ? -> .
  - (* AMult *)
    by move=> /= ? -> ? -> .
Qed.

(** Better, but still has a lot of repetition. *)

(** A shorter proof with some automation. *)
Theorem optimize_sound_short: forall a,
  [[optimize a]]_n = [[a]]_n.
Proof.
  elim;
    (* Most cases follow directly by the IH *)
    try (by move=> /= ? -> ? ->).
    (* but the remaining cases --ANum and APlus--
       are different: *)
  - (* ANum *) by [].
  - (* APlus *)
    case;
      (* Again, most cases follow directly by IH *)
      try (by move=> /= ? ? -> ? ->).
      (* The interesting case, on which [try]
       does nothing, is when [e1 = ANum n]. In
       this case, we have to destruct [n] (to see
       whether the optimization applies) and
       rewrite with the induction hypothesis. *)
    + (* a1 = ANum n *)
      by case=>[|?] /= ? ? -> .
Qed.

(** If we remove the comments, we see that the
    whole proof is only a few lines long now: (I
    am inlining the first case) *)
Theorem optimize_sound_no_comments: forall a,
  [[optimize a]]_n = [[a]]_n.
Proof.
  elim; first by []; try (by move=> /= ? -> ? ->).
  (* APlus *)
  case; try (by move=> /= ? ? -> ? ->).
  (* a1 = ANum n *)
  by move=>[|?] /= ? ? -> .
Qed.

(** We avoided the repetition in the proof and the
 explicit use of generated names. However, there
 is still a big issue here: we need to remember
 the exact positions of variables and hypotheses
 (the [?] and [->])!  *)



(*! Writing custom tactics *)

(** Let's write an alternative formulation,
without having to remember positions. The idea is
to pick from the context the right hypotheses to
do rewrite. *)

(** We write a tactic using Ltac, the tactic
language of Coq. *)

(* Ltac is a cmd to define new tactics *)
Ltac rewrite_hyps :=
  match goal with(* (meta)pattern match the goal *)  
  | [ H : _ = _ |- _ ] => (* find a hypothesis
                            with an equality *)
    rewrite H; clear H; rewrite_hyps
    (* rewrite and remove [H] and continue *)
  | _ => by [] (* there is nothing to rewrite *)
  end.

(** Simplify and move everything in the list of
hypotheses. *)
Ltac solve_rewriting := move=> /= *; rewrite_hyps.

Theorem optimize_sound_auto: forall a,
  [[optimize a]]_n = [[a]]_n.
Proof.
  elim; first by []; try solve_rewriting.
  (* only APlus is left *)
  case; try solve_rewriting.
  (* the ANum is the only interesting case *)
  case=>/= *; solve_rewriting.
Qed.

End Optimizer.

Ltac solve_rewriting := Optimizer.solve_rewriting.


(*!

  Adapting proofs to changes in definitions 

*)

(** We now perform a reasonable change and see how
that affects our proof. Instead of having one case
for each binary operator, we squish them in one
case. *)
Module BinOp.

Inductive binop := OPlus | OMinus | OMult.

Inductive aexp : Type :=
  | ANum (n : nat)
  | ABinOp (op : binop) (a1 a2 : aexp).

(** This is exactly the same *)
Notation "x `+ y" := (ABinOp OPlus x y)
  (at level 50, left associativity).
Notation "x `- y" := (ABinOp OMinus x y)
  (at level 50, left associativity).
Notation "x `* y" := (ABinOp OMult x y)
  (at level 40, left associativity).
Notation "` n" := (ANum n)
  (at level 0).

Reserved Notation "[[ a ]]_n".
Coercion ANum : nat >-> aexp.

(** Same here *)
Fixpoint aeval (a : aexp) : nat :=
  match a with
  | `n => n
  | a1 `+ a2 => [[a1]]_n + [[a2]]_n
  | a1 `- a2 => [[a1]]_n - [[a2]]_n
  | a1 `* a2 => [[a1]]_n * [[a2]]_n
  end
where "[[ a ]]_n" := (aeval a).

(** The optimizer is a bit different *)
Fixpoint optimize (a:aexp) : aexp :=
  match a with
  | `n => ANum n
  | 0 `+ e2 => optimize e2
  | e1 `+ e2 => (optimize e1) `+ (optimize e2)
  | ABinOp op e1 e2 =>
    ABinOp op (optimize e1) (optimize e2)
           (* One case to rule them all *)
  end.

(** We introduced the change; let's replay now the
proof and see how it breaks. *)
Theorem optimize_sound_broken: forall a,
  [[optimize a]]_n = [[a]]_n.
Proof.
  elim; first by []; try solve_rewriting.
  case; try solve_rewriting.
  (* So far, the proof went smoothly. But before
  we were casing on a [nat] and now it is an
  [aexp]. The error is not enlightning. *)
  Fail case=>/= *; solve_rewriting.
Abort.

(** The actual proof *)
Theorem optimize_sound_auto: forall a,
  [[optimize a]]_n = [[a]]_n.
Proof.
  elim; first by [].
  (* now the case is on binop *)
  case; try solve_rewriting.
  (* OPlus is the only case left *)
  (* now the case is on aexp *)
  case; last solve_rewriting.
  (* ANum is the interesting case *)
  case=>/= *; solve_rewriting.
Qed.

(** Idea: specify the type of the element to
perform elimination or case analysis so we always
know before hand why the proof breaks.

Let's do a tactic to check the type of the first
variable in the goal. *)

Ltac check_arg T :=
  lazymatch goal with
  | [ |- forall x:T, _ ] => idtac
  | [ |- forall x:?A, _ ] => fail "expecting" T "got" A
  | _ => fail "not a forall"
  end.

(** Add some nice notation because why not *)
Tactic Notation "✓" constr(T) := check_arg T.

Theorem optimize_sound_checking_types: forall a,
  [[optimize a]]_n = [[a]]_n.
Proof.
  ✓ aexp; elim; first by [].
  ✓ binop; case; try solve_rewriting.
  ✓ aexp; case; last solve_rewriting.
  ✓ nat; case=>/= *; solve_rewriting.
Qed.

(** If we have used the check in the original
proof, we would have gotten a much better error
message. *)
Theorem optimize_sound_broken: forall a,
  [[optimize a]]_n = [[a]]_n.
Proof.
  ✓ aexp; elim; first by []; try solve_rewriting.
  Fail ✓ aexp; case; try solve_rewriting.
 Abort.

(**

+------------------------------------------------+
| Recap                                          |
+------------------------------------------------+
|                                                |
| Tactic languages allow us to improve a proof   |
|                                                |
| - Adding automation ([solve_rewriting])        |
|                                                |
| - Specifying specific goals to solve           |
|   ([first], [last], ...)                       |
|                                                |
| - Adding checks to make failures show at the   |
|   exact point of breakage.                     |
|                                                |
+------------------------------------------------+

*)


(*! Specifying the exact cases *)

(** There is one last annoyence: we have no
guarantee that the case we're solving is actually
the case we want to solve: what is [first] or
[last]? When should [try] succeed?

We change the optimizer to do one more thing:
*)
Fixpoint optimize_more (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | 0 `+ e2 => optimize_more e2
  | 1 `* e2 => optimize_more e2
  | ABinOp op e1 e2 =>
    ABinOp op (optimize_more e1) (optimize_more e2)
  end.

(** If we replay the same proof as for [optimize],
    it breaks: *)
Theorem optimize_more_sound_broken: forall a,
  [[optimize_more a]]_n = [[a]]_n.
Proof.
  ✓ aexp; elim; first by [].
  ✓ binop; case; try solve_rewriting.
  ✓ aexp; case; last solve_rewriting.
  ✓ nat; case=>/= *; solve_rewriting.
Fail Qed. (** We have more cases! *)
Abort.

(** We'd like to write a tactic to select specific
cases in an elim/case, something of the sort

  ✓ binop; case; except OPlus, OMult do
       solve_rewriting.

Unfortunately, Ltac won't help us here: there is
no support for this, or at least no simple way to
solve it without resorting to ugly hacks.

We need to bring another tactic language.

This is not the only limitation of Ltac: another
limitation is present already in the [✓] tactic,
as it doesn't work properly for polymorphic types:
*)

Example an_ltac_issue : forall l: list nat, True.
Proof.
  Fail ✓ (list _); case.
  ✓ (list nat); case. (* Far from ideal... *)
Abort.


(*

+------------------------------------------------+
| The Mtac2 **typed** tactic language            |
+------------------------------------------------+
|                                                |
| - Tactics are written in Gallina, and have     |
|   a Coq type.                                  |
|                                                |
| - Supports features not present in Ltac.       |
|   + And misses others!                         |
|                                                |
| - Limited interaction with Ltac.               | 
|   + Full support is impossible (Ltac's hell!). |
|                                                |
| - Under development, yet already usable.       |
|   + Although performance is still a problem.   |
|                                                |
+------------------------------------------------+
*)


(** We will make little use of its __typed__
nature, which is crucial in certain types of
tactics (see [Kaiser et al., ICFP 2018] for this
kind of use).

The point we make here is to show features that
are useful to code proofs and must therefore be
incorporated into tactic languages.

We start by re-doing the tactics we wrote so far,
but now in Mtac2.
*)

From Mtac2 Require Import Mtac2 ConstrSelector.
Import T.

(** Here we are just "importing" other tactics:
    the ones from ssreflect and the tactic
    [solve_rewriting] tactic we did above. *)
Definition ssrelim :=
  ltac "Coq.ssr.ssreflect.elim" [m:].
Definition ssrcase :=
  ltac "Coq.ssr.ssreflect.case" [m:].
Definition solve_rewriting :=
  ltac "solve_rewriting" [m:]
  || M.failwith "Rewrite can't solve this".

(** We re-create [check_arg] because of Ltac's
    issue. We define a specific exception for it.
    *)
Definition WrongType (T: Type) : Exception.
Proof. constructor. Qed.

(** [check_arg] is almost the same as the Ltac
    version. *) 
Definition check_arg (T : Type) :=
  mtry
    match_goal with
    | [[? P |- forall x: T, P x]] => idtac
    end
  with NoPatternMatches => raise (WrongType T)
  end.


(** Note: It is a Coq definition! We can write a
standard Coq notation for it: *)
Notation "✓" := check_arg. 

Example not_an_mtac2_issue : forall l: list nat, True.
MProof. (* <-- Note the MProof command! *)
  ✓ (list _) &> ssrcase.  (* [&>] is like [;] *)
Abort.

(** We can write the proof almost as we did before.
    [|1>] is [first] and [l>] is [last]
 *)
Theorem optimize_sound_mtac2: forall a,
  [[optimize a]]_n = [[a]]_n.
MProof.
  ✓ aexp &> ssrelim |1> reflexivity.
  ✓ binop &> ssrcase &> try solve_rewriting.
  ✓ aexp &> ssrcase l> solve_rewriting.
  ✓ nat &> ssrcase &> solve_rewriting.
Qed.

(** So far, we gain little to what we had. The
interesting bit comes when we can specify exactly
what are the cases we expect will remain in the
proof. For this we use the tactical included in
Mtac2 to specify the specific cases a tactic must
apply: *)
Theorem optimize_sound_mtac2_except: forall a,
  [[optimize a]]_n = [[a]]_n.
MProof.
  ✓ aexp &> ssrelim &> except ABinOp do reflexivity.
(* Note: we can also use the positive:
                      case ANum do reflexivity
*)
  ✓ binop &> ssrcase &>
             except OPlus do solve_rewriting.
  ✓ aexp &> ssrcase &>
             except ANum do solve_rewriting. 
  ✓ nat &> ssrcase &> solve_rewriting.
Qed.

(** When we use the same proof for [optimize_more]
we see the error we get: *)
Theorem optimize_more_sound_mtac2_broken: forall a,
  [[optimize_more a]]_n = [[a]]_n.
MProof.
  ✓ aexp &> ssrelim &> except ABinOp do reflexivity.
  Fail ✓ binop &> ssrcase &>
                  except OPlus do solve_rewriting.
  (* Remember that the original proof continued
  solving the [OPlus] case. *)
Abort.

(** The error message could be improved. Good
news: we can do it easily! The Mtac2 tactics are
all written in Gallina, so we can simply rewrite
them at will for our project (of course, we can
and should also push to Mtac2's repo!). *)

Import TacticsBase.T.
Import M.notations.

(** Let's define an exception to show the
constructor of the failing case. *)
Definition ExceptException {A} (constr: A) 
           (e: Exception) : Exception.
Proof. constructor. Qed.

(** Yes, I love notations! *)
Notation "'FAILS' 'IN' 'CONSTRUCTOR' c 'WITH' e" :=
  (ExceptException c e) (at level 0).

(** [apply_except] takes a list of constructors
[l] and a tactic [t] *)
Definition apply_except (l : mlist dyn)
         (t : tactic) : selector unit := fun goals=>
  a_constr <- match mhd_error l with
              | mSome d=> M.ret d
              | _ => M.failwith "apply_except: empty list" end;
  dcase a_constr as T, c in
  constrs <- get_constrs T;
  M.fold_left (fun accu (d : dyn)=>
      dcase d as c in
      i <- ConstrSelector.index c;
      let ogoal := mnth_error goals i in
      match ogoal with
      | mSome (m: _, g) =>
         mif M.find (fun d'=>M.bunify d d' UniCoq) l then
           M.ret ((m:tt, g) :m: accu)
         else
           newgoals <-
(*            v--- here is the interesting bit *)
              mtry open_and_apply t g
              with [? e] e =>
                M.raise (ExceptException c e)
              end;
           let res := dreduce (@mapp, @mmap) (accu +m+ newgoals) in
           filter_goals res
      | mNone => M.failwith "snth_indices"
      end) constrs goals.

Notation "'except' c , .. , d 'do' t" :=
  (apply_except (Dyn c :m: .. (Dyn d :m: [m:]) ..) t) (at level 40).


(** We try the same proof again. *)
Theorem optimize_more_sound_mtac2: forall a,
  [[optimize_more a]]_n = [[a]]_n.
MProof.
  ✓ aexp &> ssrelim &> except ABinOp do reflexivity.
  Fail ✓ binop &> ssrcase &> except OPlus do
                  solve_rewriting.
(* What a lovely error message! *)

(* (here is the proof for reference) *)
  ✓ binop &> ssrcase &>
     except OPlus, OMult do solve_rewriting.

(* (Note: nothing prevents us here to screw up the
order, we need extra support from Coq's bullets to
solve this) *)
  - ✓ aexp &> ssrcase &>
       except ANum do solve_rewriting. 
    ✓ nat &> ssrcase &> solve_rewriting.
  - ✓ aexp &> ssrcase &>
       except ANum do solve_rewriting. 
    ✓ nat &> ssrcase &> except S do solve_rewriting.
    ✓ nat &> ssrcase &> except 0 do solve_rewriting.
    simpl &> intros.
    rewrite Nat.add_0_r.
    solve_rewriting.
Qed.



(** When applied to a real proof (also from SF) we
    get...  (demo PE.V) *) 

(*

+------------------------------------------------+
| Mtac2: Summary                                 |
+------------------------------------------------+
|                                                |
| - Lets you write your own tactics              |
|                                                |
| - Its tactics are written in Mtac2             |
|   + You can easily adapt them to your needs    |
|                                                |
| - It is typed                                  |
|   + More robust tactics                        |
|   + (Sometimes) needs convoluted patterns      |
|                                                |
| - Has performance issues                       |
|                                                |
+------------------------------------------------+

*)


(*! Before concluding: One liners *)

(** An alternative to the full-control style of
proving advocated here is to use heavy
proof-search. Let's bring THE HAMMER! *)

From Hammer Require Import Hammer.

Tactic Notation "☭" := hammer.

Theorem optimize_more_sound_oneliner: forall a,
  [[optimize_more a]]_n = [[a]]_n.
Proof.
  ✓ aexp; elim; ☭.
Qed.

(** Problems:

  - It often takes way too long to solve or fail.

  - When it fails you don't know why and how to
    fix it.  *)
Theorem optimize_bad_oneliner: forall a,
  [[optimize_more a]]_n = [[a `+ 1]]_n.
Proof.
  (* ✓ aexp; elim; ☭. *)
Abort.

(*

+------------------------------------------------+
| Conclusions                                    |
+------------------------------------------------+
|                                                |
| - Write your proofs as you write code:         |
|   + Use good practices!                        |
|                                                |
| - There is a tension between two paradigms:    |
|   + More control but less automation?          |
|   + More automation but less control?          |
|                                                |
| - My take: controled automation with custom    |
|            tactics.                            |
|                                                |
| - Tactic languages today have limitations:     |
|   + Ltac: inconsistent semantics, limited      |
|           primitives, etc.                     |
|   + Mtac2: slow, a bit **too** safe...         |
|   + Ltac2: still under development             |
|                                                |
+------------------------------------------------+



+------------------------------------------------+

 _______ _     _ _______ __   _ _     _ _______   /
    |    |_____| |_____| | \  | |____/  |______  / 
    |    |     | |     | |  \_| |    \_ ______| .  

+------------------------------------------------+
*)








(** * Supplementary material *)





(** We will now move to a different kind of
tactics: we will take a natural number and convert
it to a *)

Ltac to_aexp n :=
  lazymatch n with
  | 0 => constr: (ANum 0)
  | S ?n' =>
    let res := to_aexp n' in
    lazymatch res with
    | ANum ?x => constr: (ANum (S x))
    | _ => fail "Can't deal with it"
    end
  | ?n + ?m =>
    let resn := to_aexp n in
    let resm := to_aexp m in
    constr: (ABinOp OPlus resn resm)
  | ?n - ?m =>
    let resn := to_aexp n in
    let resm := to_aexp m in
    constr: (ABinOp OMinus resn resm)
  | ?n * ?m =>
    let resn := to_aexp n in
    let resm := to_aexp m in
    constr: (ABinOp OMult resn resm)
  end.

Definition test_nat :=
  ltac:(let h := to_aexp 2 in exact h).
Definition test_plus :=
  ltac:(let h := to_aexp (1+1) in exact h).
Print test_plus.

Definition test_minus_mult :=
  ltac:(let h := to_aexp (1-2*3) in exact h).
Print test_minus_mult.

Fail Definition test_not_ok :=
  ltac:(let h := to_aexp (S (1+1)) in exact h).

(** We can add a proof that the result evaluates
to the same. *)
Ltac to_aexp_w_proof n :=
  let res := to_aexp n in
  let x := fresh in
  constr: (existT (fun x:aexp=> [[x]]_n = n) res eq_refl).

Definition test_nat_w_proof :=
  ltac:(let h := to_aexp_w_proof 2 in exact h).
Print test_nat_w_proof.

Import M.
Import M.notations.

Definition to_aexp : nat -> M aexp :=
  mfix1 to_aexp (n: nat) : M aexp := 
  mmatch n with
  | 0 => ret (ANum 0)
  | [? n'] S n' =>
    res <- to_aexp n';
    match res with
    | ANum x => M.ret (ANum (S x))
    | _ => M.failwith "Can't deal with it"
    end
  | [? n m] n + m =>
    resn <- to_aexp n;
    resm <- to_aexp m;
    ret (ABinOp OPlus resn resm)
  | [? n m] n - m =>
    resn <- to_aexp n;
    resm <- to_aexp m;
    ret (ABinOp OMinus resn resm)
  | [? n m] n * m =>
    resn <- to_aexp n;
    resm <- to_aexp m;
    ret (ABinOp OMult resn resm)
  end.

(** It is too typed: it fails because we do not
have a proof for every nat. *)
Fail Definition to_aexp_w_proof (n: nat)
  : M {a: aexp & [[a]]_n = n} :=
  a <- to_aexp n;
  ret (existT _ a eq_refl).

Definition to_eq {A} {x y : A} (meq : x =m= y) : x = y :=
  match meq in _ =m= y return x = y with
  | meq_refl => eq_refl
  end.
Coercion to_eq: meq >-> eq.

Definition to_aexp_lying_proof (n: nat) : M {a: aexp & [[a]]_n = n} :=
  a <- to_aexp n;
  mmatch [[a]]_n with
  | n => [pf] ret (existT _ a (to_eq pf))
  end.

Definition test_nat_w_proof_mtac2 := ltac:(mrun (to_aexp_lying_proof 2)).

Definition rewrite1r {A} (x: A) : tactic := trewrite RightRewrite [m: Dyn x].

Definition rewrite1l {A} (x: A) : tactic := trewrite LeftRewrite [m: Dyn x].

Obligation Tactic := simpl; intros.

Program
Definition to_aexp_w_proof : forall n:nat, M {a:aexp & [[a]]_n = n} :=
  mfix1 to_aexp (n: nat) : M {a:aexp & [[a]]_n = n} :=
  let P := fun a=> [[a]]_n = n in
  mmatch n with
  | 0 => ret (existT P (ANum 0) _)
  | [? n'] S n' =>
    '(existT _ res pf) <- to_aexp n';
    match res with
    | ANum x => ret (existT P (ANum (S x)) _)
    | _ => M.failwith "Can't deal with it"
    end
  | [? n m] n + m =>
    '(existT _ resn pfn) <- to_aexp n;
    '(existT _ resm pfm) <- to_aexp m;
    ret (existT P (ABinOp OPlus resn resm) _)
  | [? n m] n - m =>
    '(existT _ resn pfn) <- to_aexp n;
    '(existT _ resm pfm) <- to_aexp m;
    ret (existT P (ABinOp OMinus resn resm) _)
  | [? n m] n * m =>
    '(existT _ resn pfn) <- to_aexp n;
    '(existT _ resm pfm) <- to_aexp m;
    ret (existT P (ABinOp OMult resn resm) _)
  end.
Next Obligation.
MProof.
  (select (_ =m= _) >>= rewrite1r)%tactic.
  reflexivity.
Qed.
Next Obligation.
MProof.
  (select (_ =m= _) >>= rewrite1r)%tactic.
  rewrite <- pf. (select (_ = res) >>= rewrite1l)%tactic.
  reflexivity.
Qed.
Next Obligation.
  discriminate.
Qed.
Next Obligation.
MProof.
  rewrite -> pfn, pfm. (select (_ =m= n + m) >>= rewrite1l)%tactic.
  reflexivity.
Qed.
Next Obligation.
MProof.
  rewrite -> pfn, pfm. (select (_ =m= n - m) >>= rewrite1l)%tactic.
  reflexivity.
Qed.
Next Obligation.
MProof.
  rewrite -> pfn, pfm. (select (_ =m= n * m) >>= rewrite1l)%tactic.
  reflexivity.
Qed.















(*! Closing words  *)
(* 
   This is just a little demo of what we can do thanks to
   having our tactics coded withing the rich type system of
   Coq. In the real implementation of Mtac2 Dependent types
   helped us ensure such invariants, remove dead code, and
   greatly factorize code. And we are not yet done!
*)


(*
      _______ _     _ _______ __   _ _     _ _______   /
         |    |_____| |_____| | \  | |____/  |______  / 
         |    |     | |     | |  \_| |    \_ ______| .  
                                                        
*)

(* Local Variables: *)
(* company-coq-local-symbols: (("[[" . ?⟦) ("]]" . ?⟧) ("_n" . ?ₙ) ("&>" . ?⊳) ("[[?" . (?⟦ (Br . Bl) ?\?)) ("|1>" . (?⊳ (Br . Bl) ?₁)) ("l>" . (?⊳ (Br . Bl) ?ₗ))) *)
(* End: *)

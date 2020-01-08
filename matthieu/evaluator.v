From Coq Require Import Program.Basics Program.Tactics.
From Equations Require Import Equations.
From Coq Require Import List.
From Coq Require Import Utf8.

Import ListNotations.
Set Equations Transparent.

Axiom todo : forall {A}, A.
Ltac todo := apply todo.

(** We will now formalize a simply-typed lambda-calculus and write an evaluator for it.

  We will formalize only _well-typed_ terms, using a representation know as 
  "intrinsically-typed syntax".
  
  Our type structure is very simple: only one base type [unit] and the [arrow] type
  to type functions. *)

Inductive Ty : Set :=
| unit : Ty
| arrow (t u : Ty) : Ty.

Derive NoConfusion for Ty.

(** We define a shortcut notation for arrows in our AST of types. *)
Infix "⇒" := arrow (at level 80).

(** A typing context will be a finite list of types. *)
Definition Ctx := list Ty.

Reserved Notation " x ∈ s " (at level 70, s at level 10).

#[template]
Inductive In {A : Type} (x : A) : list A -> Type :=
| here {xs} : x ∈ (x :: xs)
| there {y xs} : x ∈ xs -> x ∈ (y :: xs)
where " x ∈ s " := (In x s).
Derive Signature for In.
Arguments here {A x xs}.
Arguments there {A x y xs} _.

(** The [In] inductive family represents _proofs_ of membership of an element in a list. *)

Example in_ex_1 : In 1 [1; 2].
Proof. todo. Defined.

Example in_ex_2 : In 1 [4; 1].
Proof. todo. Defined.

Example notin {A} (x : A) : In x [] -> False.
Proof. intros Hin. todo. Qed.

Example in_ex_3 : In 3 [3] := here.

Example in_ex_4 : In 3 [0; 1; 3] := todo.

(** As you can see, the shape of proofs of [In] actually tells us the _index_ of the 
  element in the list. *)

(** From this, we can define a type of expressions, with variables drawn from 
    a context, and of a given type *)

Inductive Expr : Ctx -> Ty -> Set :=
| tt {Γ} : Expr Γ unit
(* The [tt] constructor of the [unit] type lives in any context *)
| var {Γ} {t} : In t Γ -> Expr Γ t
(* To form a variable, we must be able to give its index in the context *)
| abs {Γ} {t u} : Expr (t :: Γ) u -> Expr Γ (t ⇒ u)
(* λ-Abstraction is made only of a body of type [u] which has access to a new
   variable of type [t] at index 0 in the context, and builds a term of type [t => u] *)
| app {Γ} {t u} : Expr Γ (t ⇒ u) -> Expr Γ t -> Expr Γ u.
(* Application takes two terms in context [Γ], the first must be of function type 
  [t ⇒ u] and the second a term of type [t]. It builds a term of type [u]. *)
Derive Signature NoConfusion NoConfusionHom for Expr.

(** These are just the standard typing rules of simply-typed lambda calculus.
  So [t : Expr Γ ty] is equivalent to [Γ |- t : ty]: [Expr] represents typing derivations
  rather than just arbitrary terms. *)

(** Let's look at the so-called "de Bruijn" encoding of variables. The identity function
  on the unit type can be built using: *)

Example id_unit : Expr [] (unit ⇒ unit) := abs (var here).

(** Printing all type annotations: *)
Check eq_refl : id_unit = @abs nil unit unit (@var [unit] unit (@here _ unit nil)).

Example free_var_unit : Expr [unit] unit := var here.

(** The constant unit function: (fun _ : unit => tt). *)

Example constant_unit : Expr [] (unit ⇒ unit) := todo.

(** The following predicate [All P l] holds only if each and every element [x] of [l] has
  a proof of [P x], *)
#[template]
Inductive All {A} (P : A -> Type) : list A -> Type :=
| all_nil : All P []
| all_cons {x xs} : P x -> All P xs -> All P (x :: xs).
Arguments all_nil {A} {P}.
Arguments all_cons {A P x xs} _ _.
Derive Signature NoConfusion NoConfusionHom for All.

Section MapAll.
  Context  {A} {P Q : A -> Type} (f : forall x, P x -> Q x).

  (** [All] is just a regular inductive familiy, we can hence write programs
    by pattern-matching on it. Here we show that if [P x -> Q x] for all [x],
    then [All P l -> All Q l] for all [l].
    
    It is a variant of the [map] function, this time on [All] instead of [list] or [vec]. *)
  Equations map_all {l : list A} : All P l -> All Q l :=
  map_all all_nil := all_nil;
  map_all (all_cons p ps) := all_cons (f _ p) (map_all ps).
End MapAll.

(** Assuming we have a proof the [All P xs] and that [x ∈ xs] ([In x xs]),
  then we can fetch the proof of [P x] from the first argument. *)

Equations lookup : forall {A P xs} {x : A}, All P xs -> x ∈ xs -> P x :=
  lookup (all_cons p _) here := p;
  lookup (all_cons _ ps) (there ins) := lookup ps ins.

(** This is the analogue of the safe lookup function on [vec] and [fin].
  Indeed, given that we have a proof of [x ∈ xs], we know that the list [xs]
  cannot be empty, and hence the [all_nil] case does not need to be considered. 
  
  We can similarly replace a proof/term of type [P x] inside an [All P xs] if [x ∈ xs]:
  *)

Equations update : forall {A P xs} {x : A}, All P xs -> x ∈ xs -> P x -> All P xs :=
  update all pos proor := todo.

(** One should start thinking that [P x] might not just be "proofs" but 
  arbirarily indexed data. Indeed, what we will store in the [All] container
  will be "values" for our evaluator, and not proofs of some proposition. *)

(** Our evaluator will build well-typed values from well-typed terms, hence
  [Val] is indexed by [Ty]. However, values will be closed, so no context indexes [Val]. *)
Inductive Val : Ty -> Set :=
| val_tt : Val unit
(* It is clear that [tt] should be a closed value. *)
| val_closure {Γ t u} : Expr (t :: Γ) u -> All Val Γ -> Val (t ⇒ u).
(* For function types, any lambda abstraction will be a value, assuming
  we get values for all its free variables in [Γ]. This list of values is 
  called an environment: *)
Derive Signature NoConfusion NoConfusionHom for Val.

Definition Env (Γ : Ctx) : Set := All Val Γ.

Example Env_1 : Env [unit] := all_cons val_tt all_nil.
  (* [0th variable ↦ tt]. *)

(** To perform evaluation of an expression typable in context [Γ], one
  will need to provide an environment of the same type. That is, 
  a dependently-typed list of values for each type in [Γ].

  What we are building here are called "closures", which pair together a 
  function body and its environment: for each free variable of the body
  we have a value. *)

Example closure_1 : Val (unit ⇒ unit) :=
  val_closure free_var_unit all_nil.
(** This represents the empty closure [((λ x : unit. x), []] *)

Example closure_2 : Val (unit ⇒ unit) :=
  val_closure (Γ:=[unit]) (t:=unit) (u:=unit) (var (there here)) (all_cons val_tt all_nil).
(** This represents the closure [((λ x : unit. y), [y := tt]]. *)

(* Should contain just [tt] and the identity on unit closure  *)  
Example Env_2 : Env [unit; unit ⇒ unit] := todo.



(** Our evaluator is a function from environments for Γ to values of type A.
  (Ignore the argument (n : nat) for now).
  Morally, taking an expression with free variables in Γ, it tries to evaluate 
  it to produce a value. When facing a λ-expression, it simply stops and produces
  a closure using the current environment. At applications, it can unpack such
  closures for the function part and continue evaluation of the bodies, assuming
  the argument also evaluates to a value. 
  
  Dependent pattern-matching is used to ensure that from a well-typed term
  of type [t] we always produce a value of the same type [t]: our evaluator is type-preserving
  "by construction". In addition, thanks to the indexing by [Γ], we also know that at the
  variable case, we will _always_ find a corresponding value in the environment. *)

 Equations eval : ∀ (n : nat) {Γ t} (e : Expr Γ t), Env Γ -> option (Val t) :=
 eval 0 _               E := None;
 eval (S k) tt          E := Some val_tt;
 eval (S k) (var x)     E := Some (lookup E x);
                           (* Here (E : Env Γ) and (x : t ∈ Γ) and we must produce a [Val t] *)
 eval (S k) (abs be)    E := Some (val_closure be E);
                           (* Here we get the current environment which contains values for all free 
                             variables in Γ, and can just build a closure together with the body of the abstraction.*)
 eval (S k) (app fe xe) E with eval k fe E, eval k xe E := 
   { | Some (val_closure be E') | Some xv := eval k be (all_cons xv E') ;
     | _ | _ := None }.
(* The application case is the most interesting:
  First we evaluate the function expression and argument expressions, which, if they succeed,
  provides a (function) value of type [Val (t1 ⇒ t)] and an argument value [xv : Val t1] (the types must match, statically).
  The only way to introduce a value in [Val (t1 ⇒ t)] is by building a closure [b, e]
  where [b : Expr (t1 :: Γ) t] and [E : Env Γ].
  This gives us all the ingredients to extend the environment [E] to produce an [Env (t1 :: Γ)]
  and pursue the evaluation with the body [be]. *)

(** [eval n Γ t e E] takes an expression with free variables 
 in [Γ] and type [t], along with an environment for [Γ] and produces (optionally) values in [t]. *)
 
 (** * Fuel *) (**

 Here we are using a common idiom in Coq when we don't know how to prove the 
 termination of a function: we make it structurally recursive on an additional 
 argument [n] and when this reaches 0 we return an "out of domain" exception (here [None]).
 The [n] argument acts as an amount of gas or fuel that the function is allowed 
 to spend and which must decrease at each recursive call for the function to be accepted
 by Coq. It actually limits the longest depth of allowed recursive calls -- the
 analogy with blockchain gas which  counts exactly the cost of all instructions 
 of the program breaks down here.
 
 That is why our evaluator is partial, i.e., it returns only _optionally_ a resulting value.
 Remark that simply-typed lambda calculus is strongly normalizing, so in principle we could
 also define this program by well-founded recursion on the proof of normalization. This is
 simply beyond the scope of this example. Note also, on the other hand,
 that we could extend the language here  with imperative features like mutable references 
 that can lead to non-termination, and the evaluator would be fine with that, see 
 http://mattam82.github.io/Coq-Equations/examples/Examples.definterp.html for that example.
  
 *)

(** We can check that evaluation actually computes the right values: 
  we know already that it will have the right type. *)  
Definition app_id_tt : Expr [] unit := app (abs (var here)) tt.
(* (fun x => x) tt *)

Eval compute in eval 10 app_id_tt all_nil.
(* Some val_tt *)

(* We can also evaluate closures *)
Definition app_id_tt' : Expr [unit] (unit ⇒ unit) := abs (var (there here)).
Eval compute in eval 10 app_id_tt' (all_cons val_tt all_nil).
(* (fun x => x) tt *)

(** Exercise: extend the base types with booleans and the expression language
  with the constructors of booleans and the (well-typed) conditional (if .. then .. else). 
  Adapt the evaluator accordingly. *)

Module MonadicEvaluator.

(** ** Monadic version *) (**
  
  The treatment of the error cases and the environment passing is quite explicit here.
  We can abstract on this by using an error monad combined with a reader monad for the environment.

  Said differently, we will now write the evaluator as a _monadic_ program, producing
  a computation that takes a (well-typed) environment and returns optionally a value.
  The monad we are dealing with is defined as [M Γ A], and we will provide a few combinators on it: *)
  Definition M (Γ : Ctx) (A : Type) : Type :=
    Env Γ -> option A.

  (** The [bind] operation chains two [M] computations, the first produces a value of type A
  while the second expects a value in [A] to produce a computation producing [B]'s. 
  The whole composition hence produces B's. In case the first computation fails (with [None]),
  the whole computation fails. *)
Equations bind : ∀ {Γ A B}, M Γ A → (A → M Γ B) → M Γ B :=
  bind m f γ := match m γ with
              | None => None
              | Some x => f x γ
              end.
Infix ">>=" := bind (at level 20, left associativity).

(** The trivial [ret] combinator turns a value in [A] into a computation that returns it
  and does not look at the environment [γ]. *)
Equations ret : ∀ {Γ A}, A → M Γ A :=
  ret a γ := Some a.

(** The [getEnv] computation just returns the enviroment it is passed as argument *)
Equations getEnv : ∀ {Γ}, M Γ (Env Γ) :=
  getEnv γ := Some γ.

(** The [usingEnv] combinator take an environment for [Γ], a computation expecting 
  an environment for [Γ] and produces a computation expecting an environment for [Γ']:
  it simply ignores that last environment and uses the given one. *)
Equations usingEnv : ∀ {Γ Γ' A}, Env Γ → M Γ A → M Γ' A :=
  usingEnv γ m γ' := m γ.

(** Finally, [timeout] is the computation that always fails. *)
Equations timeout : ∀ {Γ A}, M Γ A :=
  timeout _ := None.

(** Our evaluator can now be written as a _computation_-producing function, 
  and hide the abstraction on the environment and the error cases behind those
  simple combinators. *)
 Equations eval : ∀ (n : nat) {Γ t} (e : Expr Γ t), M Γ (Val t) :=
  eval 0 _               := timeout; (* a.k.a, out-of-fuel *)
  eval (S k) tt          := ret val_tt; (* No need to look at the environment *)
  eval (S k) (var x)     := getEnv >>= fun E => ret (lookup E x);
                  (* Here (E : Env Γ) and (x : t ∈ Γ) and we must produce a [Val t] *)
  eval (S k) (abs be)    := getEnv >>= fun E => ret (val_closure be E);
  (* Here we get the current environment which contains values for all free 
    variables in Γ, and can just build a closure together with the body of the abstraction.*)
  eval (S k) (app fe xe) :=
    eval k fe >>= λ{ | val_closure be E => 
   (* This "pattern-matching lambda" syntax allows to build an 
      anonymous function by pattern-matching.
      Here it has a single case *) 
    eval k xe >>= fun xv => 
    (* We change the enviroment of evaluation explicitely here to the one we want. *)
    usingEnv (all_cons xv E) (eval k be)}.

End MonadicEvaluator.

(** * Exercise:*)
(** add a boolean type and a well-typed [if then else] construction
  to this language. 

  <<   
    b : bool
    t : τ 
    f : τ
    -------------
    if b then t else f : τ
  >>

  The constructors [true] and [false] should be values.

  Exercise: define the negation [negb] function on booleans and show/test
  that evaluating [negb true] evaluates to the [true] value.
*)


Require Import ssreflect.
Set Asymmetric Patterns.

Axiom todo : forall {A}, A.
Ltac todo := apply: todo.

(** *** Inductive types with parameters. *)
    
(**  The most basic example is that of pairs, i.e. cartesian products:
*)

(** ** Pairs *)

Inductive prod (A B : Type) : Type :=
| pair (fst : A) (snd : B).
Arguments pair {A B}.

(** Using only pattern-matching, we can define their projections: *)

Definition first {A B : Type} (p : prod A B) : A :=
  match p with
  | pair a b => a
  end.

Definition second {A B : Type} (p : prod A B) : B :=
  match p with
  | pair a b => b
  end.

Check (pair 2 3) : prod nat nat.
Eval compute in (first (pair 2 3)).

(** ** A common recursive type with parameters: lists. *)

Inductive list A : Type :=
| nil : list A
| cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A}.

Notation "[]" := nil.
Notation "x :: xs" := (cons x xs).

Check cons 3 nil : list nat.

(** The induction principle is derived as for nat, just parameterizing over
  the type [A]. *)

Check fun (A : Type) (P : list A -> Type) (f : P [])
    (f0 : forall (a : A) (l : list A), P l -> P (a :: l)) =>
    fix F (l : list A) : P l :=
    match l as l0 return (P l0) with
    | [] => f
    | y :: l0 => f0 y l0 (F l0)
    end.

(** Regular recursive functions can also be directly defined using fix+match, e.g: *)

Fixpoint rev_aux {A} (l acc : list A) {struct l} : list A :=
  match l with
  | [] => acc
  | x :: xs => rev_aux xs (x :: acc)
  end.

(** The [{struct l}] annotation can be inferred by Coq, trying each argument in turn. *)


(** ** Infinite trees *)

(**  More elaborate types can be defined inductively, e.g. with infinite branching.
*)

Inductive tree (A:Type) : Type :=
| Leaf : tree A
| Node : A -> (nat -> tree A) -> tree A.
Arguments Leaf {A}.
Arguments Node {A}.

(** Note how the recursive call to [map_tree] is on [ts x]: 
    as [ts] is a subterm of [t], all calls to [ts] are as well. *)

Fixpoint map_tree {A B} (t : tree A) (f : A -> B) : tree B :=
  match t with
  | Leaf => Leaf
  | Node a ts => Node (f a) (fun x => map_tree (ts x) f)
  end.

(** Sigma types. 

  The theory of Coq does not have a primitive notion of sigma-types
  or dependent pairs. They are rather derived using an inductive scheme.

  A dependent pair is like a cartesian product, except the second component's 
  type might depend on the first component.

*)

Inductive sigT (A : Type) (B : A -> Type) : Type :=
| existT (a : A) (b : B a) : sigT A B.
Arguments sigT {A}.
Arguments existT {A B}.
Notation "{ x : A  & P }" := (@sigT A (fun x => P)) : type_scope.

(** We can again define the projections using pattern-matching: *)
Definition projT1 {A B} (p : @sigT A B) : A :=
  match p with
  | existT a b => a
  end.

(** The second projection is special as it involves a dependent elimination,
    as we have seen in the example of the induction principle for natural numbers. *)

Definition projT2 {A B} (p : @sigT A B) : B (projT1 p) :=
  match p as p' return B (projT1 p') with
  | existT a b => b
  end.

(** Let's walk through the type-checking of this term. 

  We set the [return] clause of the pattern-matching to 
  [λ p', B (projT1 p')], so when typechecking the first and 
  only branch [existT a b => b], we expect the right-hand-side
  to have type [(λ p', B (projT1 p')) (existT a b) ≡ B (projT1 (existT a b)) ≡ B a].
  This is exactly the type of [b] in this branch.

  This phenomenon of dependent elimination allowing the type of branches to vary
  is crucial for logical reasoning. 
  
  Recall the elimination principle for natural numbers. 
  Suppose we want to prove [P n] for some natural number [n]. By dependent pattern-matching,
  we can split this problem in two cases, one for [P 0] and one for [P (S n')].
  The proofs of both cases will fit in the two branches of a dependent pattern-matching on [n]
  with return clause [λ n', P n']. *)

(* A dependent pair type can be used to model "dynamic" values, as a pair of a type
  and a value in this type: *)

Definition Dyn := {A : Set & A}.  
Definition nat_dyn (n : nat) : Dyn := existT nat n.

(** It is also at the basis of the representation of structures in type theory, e.g.:
    a type with a binary operation that is associative could be modeled as:
*)

Definition magma := {A : Type & {op : A -> A -> A & forall x y z, op (op x y) z = op x (op y z) }}.

(** We can then extract the various components using iterated projections (exercise!) *)

Definition magma_carrier (m : magma) : Type := todo.
Definition magma_op (m : magma) : todo := todo.
Definition magma_op_assoc (m : magma) : todo := todo.

(** Dependent elimination can also be used independently of induction principles. 
    For example we can define the following type [unit_or_nat b] which is [unit] when 
    the boolean [b] is [true], and [nat] otherwise: *)

Definition unit_or_nat (b : bool) : Type := 
  match b with
  | true => unit
  | false => nat
  end.

(** Using dependent elimination, we can then depend a value of type [unit_or_nat b] for 
    any [b]: *)

Definition unit_or_nat_witness (b : bool) : unit_or_nat b :=
  match b as b' return unit_or_nat b' with
  | true => (* This should have type [unit_or_nat true ≡ unit], not much choice here! *)
    tt
  | false => (* This one should be [unit_or_nat false ≡ nat] *)
    42
  end.

(** This type allows us to construct a meaningful example of a dependent pair:  *)

Definition bool_or_nat_pair : sigT (fun b => unit_or_nat b) :=
  existT true tt.

Definition bool_or_nat_pair_2 : sigT (fun b => unit_or_nat b) :=
  existT false 0.
  
(** These two objects pack a boolean value and depending on it being [true] or [false],
    the second projection will either be a value of type [unit] or [nat]. 
    Applying the second projection hence makes this dependency apparent: *)

Check projT2 bool_or_nat_pair : unit_or_nat (projT1 bool_or_nat_pair).
Check projT2 bool_or_nat_pair : unit.
Eval compute in projT2 bool_or_nat_pair.
Eval compute in projT2 bool_or_nat_pair_2.

(** We will come back to the use of dependent elimination throughout this lecture, 
  but first we will focus on the notion of propositions in Coq, represented by the
  sort [Prop]. *)

(** ** Logical connectives

  The logical connectives of the [Prop] sort can be defined inductively. *)

(** The trivial proposition. The equivalent to the [unit] type in [Type] *)
Inductive True : Prop := I.

(** The empty/void proposition *)
Inductive False : Prop := .

(** The elimnator of [False] allows to inhabit any type: ex falso quodlibet *)

Check False_rect : forall {A}, False -> A.

(** Indeed, there is no case to consider as [False] has no constructors. *)

(** Conjunction has a single constructor with two arguments: *)

Inductive and (A:Prop) (B:Prop) : Prop :=
| conj : A -> B -> and A B.

(** It is simply a propositional version of the cartesian product type. 
    Projections can be defined just as easily in the proof mode (usually preferred
    for witnessing propositions): *)

Example and_left A B : and A B -> A.
Proof.
  move=> [a b]. by exact a.
Qed.

(** Under the hood, the proof is still using the primitive [match] construct:*)

Definition and_right A B : and A B -> B :=
  fun p => match p with conj a b => b end.

(**
  Disjunction is an inductive with two constructors.
*)

Inductive or (A:Prop) (B:Prop) : Prop :=
| or_introl : A -> or A B
| or_intror : B -> or A B.
Arguments or_introl {A B}.
Arguments or_intror {A B}.

Definition or_eq : or True False := or_introl I.

(* We can use the derived eliminator to write proofs as well *)
Definition or_P_P (P : Prop) (p : or P P) : P := or_ind P P P (fun p => p) (fun p => p) p.

(*
Inductive eq {A} (a : A) : A -> Prop :=
 eq_refl : eq a a. 

Infix "=" := eq : type_scope.
*)

(** The [eq] inductive models propositional equality:
    - it includes convertibility, e.g. *)

Check (eq_refl _ : 3+2 = 5).

(** - equalities can also be proven by induction, contrary to "convertibility", which
    cannot even be stated in the theory (there are no type and proof terms for ≡) *)

Lemma add_0_r n : n + 0 = n.
Proof.
  elim: n => [|n'] /= //.
  by move=> H; rewrite H.
Qed.

(** Equality is reflexive, symmetric and transitive (exercise!), so it is an equivalence relation. *)

Definition eq_sym {A} (x y : A) : x = y -> y = x :=
  fun e => match e in eq _ y' return y' = x with
          | eq_refl => 
            (* [(fun y' _ => y' = x) x eq_refl ≡ (x = x)] *)
            eq_refl
          end.

Lemma eq_sym_tactic {A} (x y : A) : x = y -> y = x.
Proof. elim. reflexivity. Qed.

Example eq_trans {A} (x y z : A) : x = y -> y = z -> x = z.
Proof. todo. Qed.

(** The eliminator for equality allows do derive the Leibniz substitution principle: *)

Definition leibniz {A} (P : A -> Type) (x y : A) : x = y -> P x -> P y :=



  fun e => match e in _ = y' as e' return P x -> P y' with
            | eq_refl => (* Should have type [(λ (y' : A) (e' : eq x y'), P x -> P y') x (eq_refl x)]
                    which is equivalent to [P x -> P x] *)
                    fun (p : P x) => p
            end.

(** This means that we can transport values from one type to another if we can show they are equal.
    This is at the core of the [rewrite] tactic.

    Computationally, we can see that [leibniz] does not do much: 
    apart from matching on the equality proof [e], it just returns an identity function.
    The interesting part is only happening at the level of types.
*)

(** *** Simple indexed inductive types. *)

(**
  Dependent elimination can be understood more easily on indexed inductive types.
  Here we define a new inductive type [is_true : bool -> Type] with a single constructor of
  type [is_true true]. This means that there is no way to build a value of [is_true false]
  (in a consistent context). *)

Inductive is_true : bool -> Type := 
| is_true_intro : is_true true.
    
(** The eliminator: *)
  
Check fun (P : forall b : bool, is_true b -> Type) (f : P true is_true_intro)
        (b : bool) (i : is_true b) =>
    match i as i0 in (is_true b0) return (P b0 i0) with
    | is_true_intro => f
    end.
  
(** The elimator tells us that to prove a property on arbitrary [b] and [is_true b] values, 
    we only need to provide one branch [f : P true is_true_intro]. So we can actually 
    prove the property that given an object of type [is_true b] for any [b], we can 
    derive that [b = true].
  *)
    
Definition is_true_eq_true {b} : is_true b -> b = true :=
  fun p => match p in is_true b' return b' = true with
           | is_true_intro => 
  (* Here the branch should have type[(fun b' (p : is_true b') => b' = true) true is_true_intro ≡ (true = true)] *)
            eq_refl true
  end.

(** We can also define inductive relations using indexed inductive types:
  here the list membership predicate [In] which tells if some element appears in a list. *)

Inductive In {A} : A -> list A -> Prop :=
| here {x xs} : In x (x :: xs)
| there {x y xs} : In x xs -> In x (y :: xs).

(** The proof terms are derivation trees for this inductive relation: *)
Definition example_1 : In 1 (1 :: 2 :: nil) := here.
Definition example_2 : In 2 (1 :: 2 :: nil) := there here.

(** We will study how they can be how to dependently eliminate them in the last part of the lecture.
  For now we can assume: *)

Lemma in_empty {A} (x : A) : In x [] -> False.
Proof. move=> H; now inversion H. Qed.

(** ** Two new sigma-types / dependent pairs *)

(** * Subset types: *)

(* 
Inductive sig (A : Type) (P : A -> Prop) : Type :=
| exist (x : A) (p : P x) : sig A P.
Notation "{ x : A | P }" := (sig A (fun x : A => P)) : type_scope.
Arguments exist {A}.
 *)
(** Subset types have their first component a computational object 
    (some t : T, where T : Type) and second component a proof about
    this object (some (p : P t : Prop).. *)

Definition some_nat : {x : nat | x = 0} :=
  exist (fun x => x = 0) 0 (eq_refl 0).

(** We can also project these components using [proj1_sig] and [proj2_sig] 
    defined in the standard library. *)

Check proj1_sig : forall (A : Type) (P : A -> Prop), {x : A | P x} -> A.
Check proj2_sig : forall (A : Type) (P : A -> Prop) (p : {x : A | P x}), P (proj1_sig p).

(** * Existential types in [Prop] *)

Inductive ex (A:Type)(P:A->Prop) : Prop :=
| ex_intro : forall (x:A), P x -> ex A P.   
Arguments ex_intro {A} {P}.

(** Mimick the definition from the standard library *)
Notation "'exists' x .. y , p" := (@ex _ (fun x => .. (@ex _ (fun y => p)) ..))
 (at level 200, x binder, right associativity,
  format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
 : type_scope.

Definition some_nat_in_a_list : ex nat (fun x => In x (1 :: 2 :: nil)) :=
  ex_intro 1 here.

(** This is a special form of sigma-types where the first component is computational
 (e.g. a [nat]) and the second is a proof, but the whole existential is also a proposition
 (in [Prop]). As we will see, we cannot project from it to get back the witness, indeed: *)
 
Fail Definition ex_witness {A P} (e : exists x : A, P x) : A :=
  match e return A with
  | ex_intro x p => x
  end.

Lemma ex_proof l : (exists x : nat, In x l) -> l <> [].
Proof.
  move=> [x Hx]. (* allowed since the goal is in Prop *)
  (* Here we dependently eliminate the [In x l] proof, producing two cases: *)
  elim: {l x} Hx => [x xs | x y xs xinxs _].
  all:discriminate.  
Qed.

(** The eliminator for [or]:

  Note that the elimination sort is restricted here, [P] has to be in [Prop].
  We will come back to this in a minute! *)
 
  Check fun (A B P : Prop) (f : A -> P) (f0 : B -> P) (o : or A B) =>
  match o with
  | or_introl x => f x
  | or_intror x => f0 x
  end.

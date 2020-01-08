(** In these exercises we will practice equations by working with
    different implementations of vectors and matrices. The exercises
    are marked with stars, where 1 star exercises are the simplest
    and exercises with more start are more complicated.

    In order to complete some of the exercises you may need to define
    your own additional definitions/lemmas. *)
From Equations Require Import Equations.
From Coq Require Import Logic.FunctionalExtensionality.

Axiom todo : forall {A}, A.

(** Recall our definition of [vec] as an inductive type. *)

Inductive vec (A:Type) : nat -> Type :=
  | nil : vec A 0
  | cons : forall n, A -> vec A n -> vec A (S n).

Arguments nil {A}.
Arguments cons {A n}.

(** We derive [Signature] for [vec] here, so that the equations
    plugin will not reprove this every time it is needed. *)

Derive Signature for vec.

(** We will be using the following notations for convenience. *)

Notation "x :: v" := (cons x v).
Notation "[ ]" := nil.
Notation "[ x ]" := (cons x nil).
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) .. )).

(** Recall our definitions of [head], [tail] and [decompose]. *)

Equations head {A n} (v : vec A (S n)) : A :=
head (x :: _) := x.

Equations tail {A n} (v : vec A (S n)) : vec A n :=
tail (_ :: v) := v.

Equations decompose {A n} (v : vec A (S n)) : v = cons (head v) (tail v) :=
decompose (x :: v) := eq_refl.

(** * Exercise, 2 star: *)(** Finish the following proof that a vector with
    zero elements is [nil]. *)

Equations vec0_is_nil {A} (v : vec A 0) : v = nil :=
  vec0_is_nil v := todo.

(** * Exercise, 3 star: *)(** Finish the definition of [rev], the function
    which reverses a vector. *)

Equations rev {A n} (v : vec A n) : vec A n :=
  rev _ := todo.

(** * Exercise, 1 star: *)(** Show that [rev] satisfies the examples [rev_0]
    and [rev_3] below. *)

Example rev_0 : rev (@nil nat) = nil.
Proof.
Admitted.

Example rev_3 : rev [0;1;2] = [2;1;0].
Proof.
Admitted.

(** * Exercise, 3 star: *)(** Prove that [rev] is an involution [rev_involution]. *)

Lemma rev_involution {A n} (v : vec A n) : rev (rev v) = v.
Proof.
Admitted.

(** We can implement the type [fin n] of numbers strictly less than
    [n : nat] with the following inductive definition. *)

Inductive fin : nat -> Set :=
  | f0 : forall n, fin (S n)
  | fS : forall n, fin n -> fin (S n).

Derive Signature for fin.

Arguments f0 {n}.
Arguments fS {n}.

(** For example, [fin 3] has the following inhabitants: *)

Check f0 : fin 3.
Check fS f0 : fin 3.
Check fS (fS f0) : fin 3.

(** But [fS (fS (fS f0))] is not an inhabitant of [fin 3]: *)

Fail Check fS (fS (fS f0)) : fin 3.

(** The following definition [fvec] is an alternative way to define a
    vector data type. *)

Definition fvec (A:Type) (n : nat) : Type := fin n -> A.

(** The head of an [fvec] is given by the element at [f0]. *)

Definition fhead {A:Type} {n} (v : fvec A (S n)) : A := v f0.

(** The definition [ftail] gives the tail of an [fvec]. *)

Definition ftail {A} {n} (v : fvec A (S n)) (f : fin n) : A := v (fS f).

(** Notice that the following check succeeds. *)

Check @ftail : forall A n, fvec A (S n) -> fvec A n.

(** * Exercise, 2 star: *)(** Finish the following definition of [fnil], which
    is the [fvec A 0] corresponding to [nil : vec A 0]. *)

Equations fnil {A:Type} (f : fin 0) : A := ?.

(** The following check should succeed. *)

Check @fnil : forall A, fvec A 0.

(** * Exercise, 2 star: *)(** Finish the following definition of [fcons], which
    is the [fvec A (S n)] corresponding to [cons : vec A (S n)]. *)

Equations fcons {A:Type} {n} (x : A) (v : fvec A n) (f : fin (S n)) : A := ?

(** The following check should succeed. *)

Check @fcons : forall A n, A -> fvec A n -> fvec A (S n).

(** * Exercise, 1 star: *)(** To test your implementation of [fnil] and [fcons],
    prove the examples [fidx_0], [fidx_1], [fidx_2]. *)

Example fidx_0 : (fcons 0 (fcons 1 (fcons 2 fnil))) f0 = 0.
Proof.
Admitted.

Example fidx_1 : (fcons 0 (fcons 1 (fcons 2 fnil))) (fS f0) = 1.
Proof.
Admitted.

Example fidx_2 : (fcons 0 (fcons 1 (fcons 2 fnil))) (fS (fS f0)) = 2.
Proof.
Admitted.

(** * Exercise, 2 star: *)(** Finish the definition of [idx], which is the
    function for indexing a [vec], i.e. [idx v f] is the element at
    index [f] in vector [v]. *)

Equations idx {A n} (v : vec A n) (f : fin n) : A := ?

(** Notice that [@idx A n] is a function from [vec A n] to [fvec A n]. *)

Check @idx : forall A n, vec A n -> fvec A n.

(** * Exercise, 1 star: *)(** To test, prove the examples
    [idx_0], [idx_1], [idx_2]. *)

Example idx_0 : idx [0;1;2] f0 = 0.
Proof.
Admitted.

Example idx_1 : idx [0;1;2] (fS f0) = 1.
Proof.
Admitted.

Example idx_2 : idx [0;1;2] (fS (fS f0)) = 2.
Proof.
Admitted.

(** * Exercise, 3 star: *)(** Finish [unidx], the inverse of [idx]. It is the
    unique function satisfying the Lemmas [unidx_idx] and [idx_unidx]. *)

Equations unidx {A:Type} {n} (v : fvec A n) : vec A n := ?

(** * Exercise, 3 star: *)(** Finish the following Lemma [unidx_idx]. *)

Lemma unidx_idx
  : forall {A n} (v : vec A n), unidx (idx v) = v.
Proof.
Admitted.

(** * Exercise, 3 star: *)(** Finish Lemma [idx_unidx']. *)

Lemma idx_unidx'
  : forall {A n} (v : fvec A n) (f : fin n), idx (unidx v) f = v f.
Proof.
Admitted.

(** * Exercise, 2 star: *)(** Finish Lemma [idx_unidx].
    Hint: Look at the imports in the top of this file. *)

Lemma idx_unidx
  : forall {A n} (v : fvec A n), idx (unidx v) = v.
Proof.
Admitted.

(** * Exercise, 3 star: *)(** The Lemmas [idx_unidx] and [unidx_idx] show that
    there is a bijective correspondence between [vec A n] and [fvec A n].
    Finish the examples [nil_to_fnil], [cons_to_fcons], [fnil_to_nil]
    and [fcons_to_cons] to show that your implementation of [fnil] and
    [fcons] corresponds to [nil] and [cons], respectively, under this
    bijective correspondence. *)

Lemma nil_to_fnil : forall A, idx (@nil A) = fnil.
Proof.
Admitted.

Lemma cons_to_fcons
  : forall {A n} (x : A) (v : vec A n), idx (cons x v) = fcons x (idx v).
Proof.
Admitted.

Lemma fnil_to_nil A : unidx (@fnil A) = nil.
Proof.
Admitted.

Lemma fcons_to_cons
  : forall {A n} (x : A) (v : fvec A n), unidx (fcons x v) = cons x (unidx v).
Proof.
Admitted.

(** We define a matrix [mtx] as a vector of vectors. *)

Definition mtx (A:Type) (m n : nat) : Type := vec (vec A n) m.

(** We think of [mtx A m n] as an m by n matrix. For example: *)

Definition mtx_test : mtx nat 2 3 := [[1; 2; 3];
                                      [4; 5; 6]].

(** Similarly, an [fmtx] is an fvector of fvectors. *)

Definition fmtx (A:Type) (m n : nat) : Type := fvec (fvec A n) m.

(** * Exercise, 2 star: *)(** Finish the following definition of [midx]. It is
    supposed to satisfy that [midx M f g] is the matrix entry at (f,g). *)

Definition midx {A m n} (M : mtx A m n) (f : fin m) (g : fin n) : A.
Admitted.

(** * Exercise, 1 star: *)(** Test your definition of [midx] by finishing the
    examples [midx_0_0], [midx_0_1], [midx_1_1], [midx_1_2]. *)

Example midx_0_0 : midx mtx_test f0 f0 = 1.
Proof.
Admitted.

Example midx_0_1 : midx mtx_test f0 (fS f0) = 2.
Proof.
Admitted.

Example midx_1_1 : midx mtx_test (fS f0) (fS f0) = 5.
Proof.
Admitted.

Example midx_1_2 : midx mtx_test (fS f0) (fS (fS f0)) = 6.
Proof.
Admitted.

(** Notice that [@midx A m n] is a function
    from [mtx A m n] to [fmtx A m n]. *)

Check @midx : forall A m n, mtx A m n -> fmtx A m n.

(** * Exercise, 3 star: *)(** Finish the definition of [unmidx], the inverse
    function of [midx], satisfying Lemmas [unmidx_midx] and [midx_unmidx]. *)

Equations unmidx {A m n} (f : fmtx A m n) : mtx A m n := ?

(** * Exercise, 4 star: *)(** Prove Lemma [unmidx_midx]. *)

Lemma unmidx_midx
  : forall {A m n} (M : mtx A m n), unmidx (midx M) = M.
Proof.
Admitted.

(** * Exercise, 4 star: *)(** Prove Lemma [midx_unmidx']. *)

Lemma midx_unmidx'
  : forall {A m n} (M : fmtx A m n) (f : fin m), midx (unmidx M) f = M f.
Proof.
Admitted.

(** * Exercise, 2 star: *)(** Prove Lemma [midx_unmidx]. *)

Lemma midx_unmidx
  : forall {A m n} (M : fmtx A m n), midx (unmidx M) = M.
Proof.
Admitted.

(** * Exercise, 2 star: *)(** Finish definition [transpose_fmtx] to compute
    the transpose of an [fmtx]. *)

Definition transpose_fmtx {A m n} (M : fmtx A m n) : fmtx A n m.
Admitted.

(** * Exercise, 2 star: *)(** Show that [transpose_fmtx] is correct by proving
    Lemma [transpose_fmtx_is_transpose]. *)

Lemma transpose_fmtx_is_transpose
  : forall {A m n} (M : fmtx A m n) (f : fin m) (g : fin n),
      transpose_fmtx M g f =  M f g.
Proof.
Admitted.

(** * Exercise, 4 star: *)(** Define the transpose of an [mtx]. Consider the
    strong relationship [unmidx_midx], [midx_unmidx] we have between
    [mtx] and [fmtx]. Name your definition [transpose_mtx]. *)

(** Implement [transpose_mtx : forall {A m n}, mtx A m n -> mtx n m]
    below here. *)



(** * Exercise, 4 star: *)(** Show that your [transpose_mtx] definition is
    correct by proving Lemma [transpose_mtx_is_transpose]. *)

Lemma transpose_mtx_is_transpose
  : forall {A m n} (M : mtx A m n) (f : fin m) (g : fin n),
      midx (transpose_mtx M) g f =  midx M f g.
Proof.
Admitted.

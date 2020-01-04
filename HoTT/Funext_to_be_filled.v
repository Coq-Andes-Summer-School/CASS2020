Set Universe Polymorphism.

From Coq Require Import ssreflect ssrfun ssrbool.

Require Import HoTT.

Definition pw_eq A (B : A -> Type) (f g : forall x, B x) := forall x, f x = g x.

Infix "f == g" := (pw_eq _ _ f g) (at level 50). 

Definition weak_funext := forall A (B : A -> Type) (f g : forall x, B x),
  f == g -> f = g.

Definition retract_of A B := {f : A -> B & {g : B -> A & forall x, g (f x) = x}}.

Definition lemma1 A (B : A -> Type) (f : forall x, B x) :
  retract_of {g : forall x, B x & f == g} (forall x, {y : B x & f x = y}).
Proof.
Admitted.

Definition lemma2 (wf: weak_funext) A (B : A -> Type) (f : forall x, B x) :
  IsContr (forall x, {y : B x & f x = y}).
Proof.
Admitted.

Definition lemma3 A (B : A -> Type) (f : forall x, B x)
           (wf : weak_funext) : wf A B f f (fun x => refl _) = refl _ ->
                                forall g (h: f == g), apD10 (wf _ _ f g h) = h.
Proof.
Admitted.

Definition lemma4 
           (wf : weak_funext) : {wf' : forall A B (f g: forall x:A, B x), f == g -> f = g &
                                 forall A B f, wf' A B f f (fun x => refl _) = refl _}.
Proof.
Admitted.

Definition weak_is_strong (wf : weak_funext) : Funext.
Proof.
  move => A B f g. unshelve eapply isequiv_adjointify.
  - exact (π1 (lemma4 wf) A B f g). 
  - move => []. exact (π2 (lemma4 wf) A B f).
  - apply lemma3. exact (π2 (lemma4 wf) A B f).
Defined. 
  
  

  
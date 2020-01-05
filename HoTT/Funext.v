Set Universe Polymorphism.

From Coq Require Import ssreflect ssrfun ssrbool.

From CASS.HoTT Require Import HoTT.

Definition pw_eq A (B : A -> Type) (f g : forall x, B x) := forall x, f x = g x.

Infix "f == g" := (pw_eq _ _ f g) (at level 50). 

Definition weak_funext := forall A (B : A -> Type) (f g : forall x, B x),
  f == g -> f = g.

Definition retract_of A B := {f : A -> B & {g : B -> A & forall x, g (f x) = x}}.

Definition lemma1 A (B : A -> Type) (f : forall x, B x) :
  retract_of {g : forall x, B x & f == g} (forall x, {y : B x & f x = y}).
Proof.
  unshelve eexists; [| unshelve eexists].
  - move => X x. exists (π1 X x). exact (π2 X x).
  - move => F. exists (fun x => π1 (F x)). move => x. exact (π2 (F x)).
  - by move => [X Y]. 
Defined.

Definition IsContr_sing A (x:A) : IsContr ({y : A & x = y}).
Proof.
  exists (x;refl _). move => X.
  apply path_sigma_uncurried; cbn.
  exists (π2 X). rewrite transport_paths_r. symmetry. apply concat_pV.
Defined.

Definition lemma2 (wf: weak_funext) A (B : A -> Type) (f : forall x, B x) :
  IsContr (forall x, {y : B x & f x = y}).
Proof.
  unshelve eexists.
  - move => x. by exists (f x). 
  - move => F. apply wf. move => x. exact (π2 (IsContr_sing _ (f x)) (F x)).
Defined.

Definition Iscontr_retract_of A B : retract_of A B -> IsContr B -> IsContr A.
Proof.
  move => [f [g e]] [cB XB]. 
  exists (g cB). move => a. rewrite (XB (f a)). apply e.
Defined. 

Definition lemma3 A (B : A -> Type) (f : forall x, B x)
           (wf : weak_funext) : wf A B f f (fun x => refl _) = refl _ ->
                                forall g (h: f == g), apD10 (wf _ _ f g h) = h.
Proof.
  move => wf_refl g h.
  pose (X := (g;h) : {g : forall x, B x & f == g}).
  assert (e : (f; fun x => refl _) = X).
  pose (Iscontr_retract_of _ _ (lemma1 _ _ f) (lemma2 wf _ _ f)).
  eapply concat; [symmetry |]; apply (π2 i).
  change (apD10 (wf A B f (π1 X) (π2 X)) = π2 X).
  rewrite <- e; cbn. rewrite wf_refl. reflexivity. 
Defined.

Definition lemma4 
           (wf : weak_funext) : {wf' : forall A B (f g: forall x:A, B x), f == g -> f = g &
                                 forall A B f, wf' A B f f (fun x => refl _) = refl _}.
Proof.
  unshelve eexists.
  - move => A B f g e. eapply concat. apply (wf A B f f (fun x => refl _))^.
    apply (wf _ _ _ _ e).
  - move => A B f. cbn. apply concat_Vp.
Defined.

Definition weak_is_strong (wf : weak_funext) : Funext.
Proof.
  move => A B f g. unshelve eapply isequiv_adjointify.
  - exact (π1 (lemma4 wf) A B f g). 
  - move => []. exact (π2 (lemma4 wf) A B f).
  - apply lemma3. exact (π2 (lemma4 wf) A B f).
Defined. 
  
  

  

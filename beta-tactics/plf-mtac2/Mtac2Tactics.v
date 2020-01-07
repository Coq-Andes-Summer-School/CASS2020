From Coq Require Import omega.Omega.
From Mtac2 Require Import Mtac2.
Import T.

Definition open {A} (x: A) : M Type :=
  (mfix1 go (d: dyn) : M Type :=
    mmatch d return M Type with
        | [? T1 T2 f] @Dyn (T1 -> T2) f =>
          e <- M.evar T1;
          go (Dyn (f e))
        | [? T1 T2 f] @Dyn (forall x:T1, T2 x) f =>
          e <- M.evar T1;
          go (Dyn (f e))
        | [? p] @Dyn Prop p => @M.ret Type p
        | [? p] @Dyn Type p => M.ret p
   end
  )%MC (Dyn x).


Definition RemoveEvars {A} (value: A) : Exception. constructor. Qed.

Definition open_and_match {T} (c: T) : dyn -> M bool:=
  (mfix1 go (d : dyn) : M bool :=
    mmatch d return M bool with
    | [? T1 T2 f] @Dyn (forall x:T1, T2 x) f =>
        M.nu Generate mNone (fun x: T1=>go (Dyn (f x)))
    | [? T' x] @Dyn T' x =>
      mtry
        T <- open c;
        b <- M.bunify T T' UniCoq;
        M.raise (RemoveEvars b)
      with [? b] RemoveEvars b => M.ret b : M bool end
    end)%MC.

(** [intros_until patt] takes a "pattern" (a
function taking the unknowns of the term) and
introduces all of the hypotheses until it reaches
one that matches. *) 
Definition intros_until {A} (patt : A) : tactic :=
    mfix0 f : gtactic unit:=
      match_goal with
      | [[? T P |- forall x:T, P x ]] =>
        mif M.nu Generate mNone (fun x : T =>open_and_match patt (Dyn x)) then
          idtac
        else
          introsn 1 &> f
      end.


Definition find_concl {T} (c: T)  : mlist Hyp -> M dyn :=
  (mfix1 f (l : mlist Hyp) : M dyn :=
    match l with
    | (@ahyp A' x d) :m: l' =>
      mif open_and_match c (Dyn x) then
        M.ret (Dyn x)
      else f l'
    | _ => M.raise NotFound
    end)%MC.

Definition select_concl {T: Type} (c: T) : M dyn :=
  M.hyps >>= find_concl c.

(** [select_and patt f] calls continuation [f] with
the hypothesis that matches the [patt]ern. *)
Definition select_and {T: Type} (patt: T) (f: forall {A}, A -> tactic) : tactic :=
  (d <- select_concl patt;
  dcase d as e in f e)%tactic.



Definition generalize_matching {T} (P: T) : tactic :=
  select_and P (@T.move_back).

Definition name_it : forall {T} (P: T) (n: unit -> unit), tactic :=
  (fun {T} P n=>M.get_binder_name n >>=
      fun k=>(generalize_matching P &> T.intro_simpl (TheName k)))%tactic. 

(** [check_goal patt] checks if the goal matches pattern [patt]. *)
Mtac Do New Exception DoesntMatchGoal.
Definition check_goal {T} (patt: T) : tactic := fun g=>
  (match g with
    Metavar' gs_open _ _ ev =>
    mif open_and_match patt (Dyn ev) then
      T.idtac g
    else
      M.raise DoesntMatchGoal
 end)%MC.

(** [has_goals n] is a selector to check the produced number of goals
matches that [n]. *)
Definition NthGoalsException (got expected: nat) : Exception.
Proof. constructor. Qed.

Definition has_goals {A} (n: nat) : T.selector A := fun l=>
  let expected := rcbv n in
  let got := rcbv (mlength l) in
  if Nat.eqb got expected then
    M.ret l
  else
    M.raise (NthGoalsException got expected).

(** [nth_last n t] executes [t] on the [n]-th last subgoal. *)
Definition nth_last {A} n (t : gtactic A) : T.selector A := fun l =>
  let n := dreduce (minus, mlength) (mlength l-n) in
  T.S.nth n (fun _=>t) l.

(** These are just shortcuts for common tactics *)
Definition inversion1 : tactic :=
  (A <- M.evar _; intro_base Generate (fun x:A=>inversion x))%tactic.

Definition rewrite1r {A} (x: A) : tactic :=
  trewrite RightRewrite [m: Dyn x].

Definition rewrite1l {A} (x: A) : tactic :=
  trewrite LeftRewrite [m: Dyn x].

Definition rewrite1r_in {A B} (eq: A) (hyp: B) : tactic :=
  trewrite_in RightRewrite eq [m: Dyn hyp].

Definition rewrite1l_in {A B} (eq: A) (hyp: B) : tactic :=
  trewrite_in LeftRewrite eq [m: Dyn hyp].

Ltac induction1 := induction 1.
Definition induction1 := T.ltac "induction1" [m:].

Ltac mclear a := clear a.
Definition tclear {A} (x: A) := T.ltac "mclear" [m: Dyn x].

Ltac mapply_in a b := apply a in b.
Definition tapply_in {A B} (a: A) (b: B) := T.ltac "mapply_in" [m: Dyn a | Dyn b].

Ltac momega := omega.
Definition tomega := T.ltac "momega" [m:].

Ltac Medestruct e := edestruct e.
Definition edestruct {A} (x: A) : tactic := T.ltac "Medestruct" [m: Dyn x].

Definition to_hyps : mlist dyn -> M (mlist Hyp) :=
  M.map (fun d=>(dcase d as v in M.ret (ahyp v mNone))%MC).

Definition find_hyp {A} (x: A) : mlist Hyp -> M bool :=
  M.fold_right (fun h (b:bool)=>
                  if b then M.ret b
                  else
                    mmatch h return M bool with
                    | [? o] ahyp x o => M.ret true
                    | _ => M.ret false
                    end) false.

Definition clear_except (l: mlist dyn) : tactic :=
  l <- to_hyps l;
  (mfix1 f (hps: mlist Hyp) : gtactic unit :=
    match hps with
    | [m:] => T.idtac
    | (ahyp x _ :m: hps') =>
      mif find_hyp x l then
        f hps'
      else
        T.try (tclear x) &> (f hps')
    end) =<< M.hyps.

Module notations.

Tactic Notation "▷" uconstr(t):= (mrun t).

Notation "◎ T : t" := (check_goal T &> t) (at level 40).

Notation "'rename' P 'as' n" := (name_it P (fun n=>n)) (at level 0).

End notations.

Section examples.
Import notations.
Local Example ex_intros_until: forall n, (False -> {p : nat & p = n}) -> True.
MProof.
  intros_until (fun x y=> {p: x & y p}).
Abort.

Local Example ex_find_concl: forall n, (False -> {p : nat & p = n}) -> True.
MProof.
  intros.
  select_and (fun x y=> {p: x & y p}) (fun _ x=>M.print_term x;; idtac)%tactic.
Abort.

Local Example ex_rename: forall n, (False -> {p : nat & p = n}) -> True.
MProof.
  intros.
  rename (fun x y=> {p: x & y p}) as H.
Abort.

End examples.

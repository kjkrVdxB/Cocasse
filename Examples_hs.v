Require Import Cast Decidable Showable List.

Local Open Scope string_scope.

Definition x_not_ok := 1.
           
Definition x_good : {n:nat | n < 10} := ? 5.

Eval compute in x_good.

Eval compute in x_good.1.

Definition x_bad : {n:nat | n < 10} := ? 15.

Eval compute in x_bad.

Eval compute in x_bad.1.


Definition g (x: {n:nat | n > 0}) := 1.

Eval compute in g (? 0).


Definition client (x: nat) := g (? x).

Extraction Language Haskell.
Extract Constant failed_cast =>
     "Prelude.error ""Cast has failed""".
Extraction "test.hs" client.

(** ** A more involved example: casting lists *)

Definition cast_list (A: Type) `{Showable A} (P : A -> Prop) 
  (dec : forall a, Decidable (P a)): 
    list A -> list {a : A | P a} := map ?.

Notation "?::" := (cast_list _ _ _).

Definition list_of_3: list {n:nat | n = 3} := ?:: (3 :: 2 :: 1 :: nil).

Eval compute in list_of_3.


Definition top_succ : nat -> {n:nat | n < 10} := ?> S.


Eval compute in top_succ 6.

Eval compute in top_succ 9.



Definition foo (x: {n:nat | n > 0 }) := x.1.

Extraction foo.

Definition gee := <? foo.
Extraction gee.


Definition f_inc : 
  (nat -> nat) -> forall n : nat, {m:nat | (n <= m)} := ??>.

Eval compute in f_inc S 3.

Eval compute in f_inc (fun _ => O) 3.


Inductive ilist : nat -> Set :=
 | Nil : ilist O
 | Cons : forall n, nat -> ilist n -> ilist (S n).

Fixpoint build_list (n: nat) : ilist n :=
 match n with
   | O => Nil
   | S m => Cons _ O (build_list m)
 end.

Instance show_ilist n  : Showable (ilist n) := {| show := fun _ => not_implemented|}.

Definition non_empty_build: forall n:nat,  {_: ilist n | n > 0 } := 
  ??> build_list.

Eval compute in non_empty_build 2.

Eval compute in non_empty_build 0.

Definition build_pos : ∀ x: {n: nat | n > 0 }, ilist (x.1) :=
 fun n => build_list (n.1).

Definition build_pos' : forall n: nat, ilist n := <?? build_pos.

Eval compute in build_pos' 2.

Opaque eq_rect.

Eval compute in build_pos' 0.
(* EXAMPLE MIXING CAST/PROVEN *)
Definition Peq : nat -> Prop := fun n => n = n.

Definition wrap : nat ->  { n : nat | Peq n /\ (n=10)} :=
  fun n => ? n.

Eval compute in ((wrap 11) .1).
Eval compute in ((wrap 10) .1).


(* need to do this refactoring to be able to define hh *)
Definition IsNat (n:nat) := {m:nat | n = m}.

Definition h (x:{n:nat | n > 0}) : IsNat x.1 := ? x.1.
Definition hh := <?? h.

Eval compute in hh (S O).
Eval compute in hh O.
Eval cbn in hh O.
Eval cbv in hh O.


(* end hide *)

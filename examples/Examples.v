(******************************************************)
(*                    Cocasse                         *)
(* A library for Gradual Certified Programming in Coq *)
(* Authors: Nicolas Tabareau and Eric Tanter          *)
(******************************************************)

(* Add LoadPath "." as Casts. *)

Require Export Unicode.Utf8_core.
Require Import Cast DecSSR Showable List ExtrOcamlString.

Local Open Scope string_scope.

(* Starting with some simple examples *) 

Definition x_not_ok := 1.
           
Definition x_good : {n:nat | n <= 10} := ? 5.

Eval compute in x_good.

Eval compute in x_good.1.

Definition x_bad : {n:nat | n <= 10} := ? 15.

Eval compute in x_bad.

Eval compute in x_bad.1.

Definition g (x: {n:nat | n <= 5}) := 1.

Eval compute in g (? 6).


Definition client (x: nat) := g (? x).

(* Extraction to OCaml *)
Extraction Language OCaml.
Extract Constant failed_cast => "(let f _ s = failwith (String.concat """" ([""Cast has failed because of ""]@ (List.map (String.make 1) s))) in f)".
Extraction Inline failed_cast.

Extraction "test.ml" client.

(* Example combining proven prop with unproven one *)

Definition Peq : nat -> Prop := fun n => n = n.

Fail Definition wrap : nat ->  { n : nat | Peq n /\ (n=10)} :=
  fun n => ? n.

Fail Eval compute in ((wrap 11) .1).
Fail Eval compute in ((wrap 10) .1).


(* Casting lists *)

Definition cast_list (A: Type) `{Show A} (P : A -> Decidable) : 
    list A -> list {a : A | P a} := map (fun a => ? a).

Notation "?::" := (cast_list _ _).

Fail Definition list_of_3: list {n:nat | n = 3} := ?:: (3 :: 2 :: 1 :: nil).

Fail Eval compute in list_of_3.


(* strengthening the range of S *)

Fail Definition top_succ : nat -> {n:nat | n < 10} := ?> S.

Fail Eval compute in top_succ 6.

Fail Eval compute in top_succ 9.


(* function with rich argument, condition is lost upon extraction *)

Definition foo (x: {n:nat | n > 0 }) := x.1.

Extraction foo.

(* weakening the domain to protect before extraction *)

Fail Definition gee := <? foo.

Fail Extraction gee.


(* strengthening the range with dependency *)

Fail Definition f_inc : 
  (nat -> nat) -> forall n : nat, {m:nat | (n <= m)} := ??>.

Fail Eval compute in f_inc S 3.

Fail Eval compute in f_inc (fun _ => O) 3.


(* length-indexed lists *)

Inductive ilist : nat -> Set :=
 | Nil : ilist O
 | Cons : forall n, nat -> ilist n -> ilist (S n).

Fixpoint build_list (n: nat) : ilist n :=
 match n with
   | O => Nil
   | S m => Cons _ O (build_list m)
 end.

(* casting build_list to pretend it always returns non empty lists *)

Fail Definition non_empty_build: forall n:nat,  {_: ilist n | n > 0 } := 
  ??> build_list.

Fail Eval compute in non_empty_build 2.

Fail Eval compute in non_empty_build 0.

Definition build_pos : ∀ x: {n: nat | n > 0 }, ilist (x.1) :=
 fun n => build_list (n.1).

Fail Definition build_pos' : forall n: nat, ilist n := <?? build_pos.

Fail Eval compute in build_pos' 2.

Opaque eq_rect.

Fail Eval compute in build_pos' 0.



(* Example weakening domain *)

Definition IsNat (n:nat) := {m:nat | n = m}.

(* Definition h (x:{n:nat | n > 0}) : IsNat x.1 := ? x.1.
Definition hh := <?? h.

Eval compute in hh (S O).
Eval compute in hh O.
Eval cbn in hh O.
Eval cbv in hh O. *)

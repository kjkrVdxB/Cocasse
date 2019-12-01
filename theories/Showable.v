(******************************************************)
(*                    Cocasse                         *)
(* A library for Gradual Certified Programming in Coq *)
(* Authors: Nicolas Tabareau and Éric Tanter          *)
(******************************************************)

                                                 
Require Import String.

(* The Show structure for values convertible to strings, similar to the Haskell Show class *)

Structure Show := ShowPack { type : Type; get_show : type -> string }.

Coercion type : Show >-> Sortclass.

Definition show (e : Show) : type e -> string :=
  let 'ShowPack _ the_show := e in the_show.

Arguments show {e} obj : simpl never.

Local Open Scope string_scope.

(* Default Instance *)

Definition not_implemented := "not implemented".

Canonical Structure show_default (A : Type) := ShowPack A (fun _ => not_implemented).

(* Instance for nat *)
Canonical Structure show_nat := ShowPack nat
  (fix _show_nat n :=
       match n with
         | O => "O"
         | S n0 => "S (" ++ _show_nat n0 ++ ")"
       end).

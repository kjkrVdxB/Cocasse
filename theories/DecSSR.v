From mathcomp
     Require Import ssreflect ssrbool eqtype.
Require Import Bool Le.

Structure Decidable := Pack { prop : Prop; dec : decidable prop }.

Coercion prop : Decidable >-> Sortclass.

Definition dec_bool (t : bool) : decidable (Is_true t).
  by case: t; [ left | right ].
Defined.

Canonical DecBool (t : bool) := Pack (Is_true t) (dec_bool t).

Structure EqDecidable := PackEq { type : Type; eq_dec : forall a b : type, decidable (a = b) }.

Definition Decidable_eq_bool : forall (x y : bool), decidable (eq x y).
intros. destruct x, y; try (left; done); try (right; intro H; inversion H).
Defined.

Canonical dec_eq_bool_can := PackEq bool Decidable_eq_bool.

Definition Decidable_eq_nat : forall (x y : nat), decidable (eq x y).
induction x.
- destruct y.
 + left ;reflexivity.
 + right; intro H; inversion H.
- induction y.
  + right; intro H; inversion H.
  + case (IHx y). intro H. left. exact (f_equal S H).
    intro H; right. intro e. inversion e. apply (H H1).
Defined.

Canonical dec_eq_nat_can := PackEq nat Decidable_eq_nat.

(* Instances for list *)

Definition Decidable_eq_list : forall (HA: EqDecidable) 
  (x y: list (type HA)), decidable (eq x y).
intros HA. induction x.
- destruct y.
  + left; reflexivity.
  + right; intro H; inversion H.
- induction y.
  + right; intro H; inversion H.
  + case (eq_dec HA a a0); intro H. 
    * case (IHx y); intro Hl.
      left. rewrite H. rewrite Hl. reflexivity.
      right. rewrite H. unfold not in *. 
      intro Hc. inversion Hc. exact (Hl H1).
    * right. unfold not in *. 
      intro Hc. inversion Hc. exact (H H1).
Defined.

Canonical eqdec_list_can (HA: EqDecidable) 
          := PackEq (list (type HA)) (Decidable_eq_list HA).

Definition dec_le_nat : forall (x y : nat), decidable (x <= y).
induction x.
- destruct y.
  + left. done.
  + left. apply le_S, le_0_n.
- induction y.
  + right.  apply le_Sn_0.
  + case (IHx y). intro H. left. exact (le_n_S _ _ H).
    intro H; right. intro. apply H. exact (le_S_n _ _ H0).
Defined.
    
Canonical Structure dec_le_nat_can (x y : nat) : Decidable := Pack (x <= y) (dec_le_nat x y).


Definition Decidable_eq_option : forall (HA: EqDecidable) 
  (x y: option (type HA)), decidable (eq x y).
intros. destruct x; destruct y.
- case (eq_dec HA t t0); intro H.
  + left. rewrite H. reflexivity.
  + right. unfold not in *. intro Hc. inversion Hc. 
    exact (H H1).
- right. unfold not. intro Hc. inversion Hc.
- right. unfold not. intro Hc. inversion Hc.
- left. reflexivity.
Defined.

Definition Decidable_or (HP : Decidable)
        (HQ : Decidable) : decidable (HP \/ HQ).
destruct HP. destruct dec0.
- exact (left (or_introl p)).
- destruct HQ. destruct dec0.
  + exact (left (or_intror p)).
  + apply right. intro H. case H; auto.
Defined.
    
Canonical Structure dec_or_can (A B : Decidable) : Decidable := Pack (A \/ B) (Decidable_or A B).

Definition Decidable_implies (HP : Decidable) (HQ : Decidable) : decidable (HP -> HQ).
destruct HQ. destruct dec0.
- exact (left (fun _ => p)).
- destruct HP. destruct dec0.
  + apply right. intro H. exact (n (H p)).
  + apply left. intro p. destruct (n0 p).
Defined.

Canonical Structure dec_implies_can (HP : Decidable) (HQ : Decidable) := Pack (HP -> HQ) (Decidable_implies _ _).

Canonical Structure dec_eq_option_can (HA: EqDecidable) := PackEq (option (type HA)) (Decidable_eq_option _).

Canonical Structure dec_true_can := Pack True (left I).

Canonical Structure dec_false_can := Pack False (right (fun x => x)).

Canonical Structure dec_prove_can (P : Prop) (p : P) := Pack P (left p).

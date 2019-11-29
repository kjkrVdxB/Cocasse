From mathcomp
     Require Import ssreflect ssrbool eqtype.
Require Import Bool Le.

Structure Decidable := Pack { prop : Prop; dec : decidable prop }.

Coercion prop : Decidable >-> Sortclass.

Definition dec_bool (t : bool) : decidable (Is_true t).
  by case: t; [ left | right ].
Defined.

Canonical DecBool (t : bool) := Pack (Is_true t) (dec_bool t).

Definition dec_or (A B : Decidable) : decidable (A \/ B).
  case: A=> A decA.  
  case: B=> B decB.
  simpl.
  case: decA=> a.
  left.
  left.
  done.
Admitted.

Canonical Structure dec_or_can (A B : Decidable) : Decidable := Pack (A \/ B) (dec_or A B).

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

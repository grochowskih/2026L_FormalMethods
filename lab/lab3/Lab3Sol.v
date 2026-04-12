(* Zadanko 1 *)
Lemma addProperty : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros.
  induction n.
  trivial.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

(* Zadanko 2 *)
Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros.
  induction n.
  trivial.
  simpl.
  rewrite IHn.
  apply addProperty.
Qed.


(* Zadanko 3 *)
Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros.
  assert (n + m = m + n).
    { apply add_comm.
    }
  rewrite H.
  reflexivity.
Qed.

(* Zadanko 4 *)
Fixpoint monus (n m : nat) : nat :=
  match n, m with
  | 0, _ => 0
  | S x, 0 => S n
  | S x , S y => monus x y
  end.
 
Theorem monus_n_n_is_zero: forall (n : nat), monus n n = 0.
Proof.
  intros.
  induction n.
  trivial.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

(* Zadanko 5 *)
Fixpoint double (n : nat) : nat :=
  match n with
  | 0 => 0
  | S x => S (S (double x))
  end.

Theorem nTimes : forall (n : nat), double n = n + n.
Proof.
  intros.
  induction n.
  trivial.
  simpl.
  rewrite IHn.
  rewrite (addProperty n n).
  trivial.
Qed.




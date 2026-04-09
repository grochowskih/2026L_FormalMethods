(* Kod z poprzedniego tygodnia *)

Require Import Coq.Arith.Arith.
Definition divMod (n x : nat) := exists (t : nat), n = t * x.
Theorem swap: forall (k n p : nat), n = k * p -> divMod n k.
Proof.
  intros.
  unfold divMod.
  exists p.
  rewrite Nat.mul_comm.
  rewrite H.
  trivial.
Qed.

(* divMod - model relacji : n w relacji z x \Leftrightarrow \exists t : nat n = t * x *)

Definition rel1 (n m : nat) := exists (k : nat), n + k = m.

Require Import Lia.
Theorem rel1IsRefl: forall (n : nat), rel1 n n.
Proof.
  intros.
  unfold rel1.
  exists 0.
  trivial.
  lia.
Qed.

Theorem rel1Fact2: forall (n m y : nat), rel1 n m /\ rel1 m y -> rel1 n y.
Proof.
  intros.
  destruct H.
  (*unfold rel1.
  unfold rel1 in H.
  unfold rel1 in H0.*)
  unfold rel1 in *.
  (* Wydobywamy to co istnieje w zalozeniach *)
  destruct H.
  destruct H0.
  exists (x + x0).
  lia.
  (*rewrite <- H0.
  rewrite <- H.
  lia.*)
Qed.

Check list.
Print list.

Definition head (l : list nat) : nat :=
  match l with
  | nil => 0
  | cons x rest => x
  end.
  
Definition duzeL (l1 l2 : list nat) := head l1 = head l2.

(* Relacja duzeL jest relacja rownowaznosci, dowod na Lab *)
Check duzeL.
Search (nat -> nat -> Prop).

Print Nat.le.
Print le.









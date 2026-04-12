(* Zadanko 1 *)
Theorem adt: forall (x y : bool), x = true /\ y = true -> andb x y = true.
Proof.
  intros.
  destruct H.
  rewrite H.
  rewrite H0.
  simpl.
  reflexivity.
Qed.

(* Zadanko 2 *)
Theorem assocConj: forall P Q R : Prop,  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros.
  destruct H.
  destruct H0.
  split.
  split.
  apply H. apply H0. apply H1.
Qed.

Theorem commProp: forall (P Q : Prop), P /\ Q -> Q /\ P.
Proof.
  intros.
  destruct H.
  split.
  apply H0.
  apply H.
Qed.

(* Zadanko 3 *)
Theorem ogt: forall (x y : bool), (orb x y) = true -> x = true \/ y = true.
Proof.
  intros.
  destruct x.
  left.
  reflexivity.
  destruct y.
  right.
  reflexivity.
  discriminate.
Qed.

(* Zadanko 4 *)
Require Import ZArith.
Theorem zMultZ : forall (x y : Z), (x * y = 0)%Z -> (x = 0)%Z \/ (y = 0)%Z.
Proof.
  intros.
  destruct x.
  left.
  trivial.
  destruct y.
  right.
  trivial.
  discriminate.
  discriminate.
  destruct y.
  right.
  trivial.
  discriminate.
  discriminate.
Qed.

(* Zadanko 6 *)
Require Import Lia.
Definition Even (n : nat) := exists (k : nat), n = 2*k.

Lemma sixIsEven : Even 6.
Proof.
  unfold Even.
  exists 3.
  simpl.
  reflexivity.
Qed.

(* Zadanko 7*)
Theorem mb4gE: forall (n : nat), (exists (k : nat), n = 4 * k) -> Even n.
Proof.
  intros.
  destruct H.
  unfold Even.
  exists (2 * x).
  lia.
Qed.

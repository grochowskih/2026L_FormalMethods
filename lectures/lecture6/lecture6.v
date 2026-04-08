(* Modelowanie zdan logicznych *)

Inductive z3 := z | o | t.
Check z3.
Check (2 + 2 = 4).
Theorem latwe: 2 + 2 = 4.
Proof.
  trivial.
Qed.

(* Koniunkcja w zalozeni *)
Theorem thm1: forall (n m : nat), n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros.
  destruct H.
  rewrite H.
  rewrite H0.
  trivial.
Qed.
Theorem thm1b: forall (n m : nat), n = 0 -> m = 0 -> n + m =0.
Proof.
  intros.
  symmetry in H.
  rewrite -> H0.
  rewrite <- H.
  trivial.
Qed.

(* Lemat pomocniczy *)
Lemma tmp: forall (x y : nat), x + y = 0 -> x = 0.
Proof.
  intros.
  destruct x.
  trivial.
  discriminate.
Qed.
(* Koniunkcja w tezie *)
Theorem othrsd: forall (n m : nat), n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros.
  split.
  apply (tmp n m H).
  rewrite (tmp n m H) in H.
  simpl in H.
  rewrite H.
  reflexivity.
Qed.

Check mult_n_O.

(* Alternatywa w zalozeniu *)
Theorem easyMult: forall (n m : nat), n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros.
  destruct H.
  rewrite H.
  simpl.
  trivial.
  rewrite H.
  trivial.
  simpl.
  symmetry.
  trivial.
Qed.

(* Alternatywa w tezie *)
Theorem zOrP: forall (n : nat), n = 0 \/ n = S (pred n).
Proof.
  intros.
  destruct n.
  left. (* Poazujemy lewa czesc w alternatywie *)
  trivial.
  right. (* Pokazujemy prawa czesc w alternatywie *)
  simpl.
  trivial.
Qed.

(* Exist *)
Theorem exampleEx: exists (k : nat), 5 = k + 2.
Proof.
  exists 3. (* Wskaz co chcesz podstawic za k *)
  trivial.
Qed.
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









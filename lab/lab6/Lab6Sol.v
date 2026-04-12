(* Zadanko 1 *)
Definition relR (x y : nat) := x + 2 = y.
Theorem relRIsPartial: forall (x y z : nat), relR x y /\ relR x z -> y = z.
Proof.
  intros.
  destruct H.
  unfold relR in *.
  rewrite <- H.
  rewrite <- H0.
  trivial.
Qed.

(* Zadanko 2 *)
Definition head (l : list nat) : nat :=
  match l with
  | nil => 0
  | cons x rest => x
  end.
  
Definition duzeL (l1 l2 : list nat) := head l1 = head l2.

Lemma reflH: forall (l1 : list nat), head l1 = head l1.
Proof.
  intros.
  trivial.
Qed.

(* To mozna oczywiscie krocej, przypomnienie taktyk po prostu *)
Lemma symHd: forall (l1 l2 : list nat), duzeL l1 l2 -> duzeL l2 l1.
Proof.
  intros.
  destruct l1.
  destruct l2.
  trivial.
  unfold duzeL in *.
  symmetry.
  apply H.
  unfold duzeL in *.
  rewrite <- H.
  trivial.
Qed.

Lemma trnsHd: forall (l1 l2 l3 : list nat), duzeL l1 l2 /\ duzeL l2 l3 -> duzeL l1 l3.
Proof.
  intros.
  destruct H.
  unfold duzeL in *.
  rewrite H.
  rewrite H0.
  trivial.
Qed.

(* Zadanko 3 *)
Definition lenRel (l1 l2 : list nat) := length l1 = length l2.

Lemma lenRelRefl: forall (l1 : list nat), lenRel l1 l1.
Proof.
  intros.
  unfold lenRel.
  trivial.
Qed.
Lemma lenRelSym: forall (l1 l2 : list nat), lenRel l1 l2 -> lenRel l2 l1.
Proof.
  intros.
  unfold lenRel in *.
  rewrite H.
  trivial.
Qed.
Lemma lenRelTr: forall (l1 l2 l3 : list nat), lenRel l1 l2 /\ lenRel l2 l3 -> lenRel l1 l3.
Proof.
  intros.
  destruct H.
  unfold lenRel in *.
  rewrite H. rewrite H0.
  trivial.
Qed.

(* Zadanko 4 *)
Inductive pairsNat : Type := pair (x : nat) (y : nat).
Definition fst (p : pairsNat) : nat :=
  match p with
  | pair x y => x
  end.
Definition eqPr (p1 p2 : pairsNat) := fst p1 = fst p2.
Lemma eqPrRefl: forall (p1 : pairsNat), eqPr p1 p1.
Proof.
  intros.
  unfold eqPr.
  trivial.
Qed.
Lemma eqPrSym: forall (p1 p2 : pairsNat), eqPr p1 p2 -> eqPr p2 p1.
Proof.
  intros.
  unfold eqPr in *.
  rewrite H.
  trivial.
Qed.
Lemma eqPrTrn: forall (p1 p2 p3 : pairsNat), eqPr p1 p2 /\ eqPr p2 p3 -> eqPr p1 p3.
Proof.
  intros.
  destruct H.
  unfold eqPr in *.
  rewrite H.
  rewrite H0.
  trivial.
Qed.


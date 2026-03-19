(* Przypomnienie z poprzedniego tygodnia *)

(* Dla kazdych dwoch x, y : bool, jesli andb x y = orb x y -> x = y *)

Theorem andbEqOrb : forall (x y : bool), (andb x y) = (orb x y) -> x = y.
Proof.
  intros.
  destruct x.
  destruct y.
  reflexivity.
  discriminate.
  destruct y.
  discriminate.
  trivial.
Qed.

(* Dowody indukcyjne - typ nat *)

Theorem zeroIsNeutralRightAdd: forall (n : nat), n + 0 = n.
Proof.
  intro n.
  induction n. (* Indukcja po n *)
  trivial.
  simpl.
  rewrite -> IHn.
  reflexivity.
Qed.
  
(* Jeszcze jeden dowod indukcyjny *)

Search (nat -> nat -> nat).

Theorem sAndPlus: forall (x : nat), S x = x + 1.
Proof.
  intros.
  induction x.
  unfold Nat.add.
  reflexivity.
  simpl.
  rewrite <- IHx. (* -> IHx *)
  reflexivity.
Qed.

(* Taktyka assert *)
Theorem easyTauto: forall (p q : bool), orb q (orb p (negb p)) = true.
Proof.
  intros.
  assert (orb p (negb p) = true).
    {
      destruct p.
      trivial.
      trivial.
    }
    rewrite H.
    destruct q.
    trivial.
    trivial.
Qed.

  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
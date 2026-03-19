(* Zadanko 1 - zrobione globalnie *)

(* Zadanko 2 *)

Theorem negIsTwoident: forall (x : bool), negb (negb x) = x.
Proof.
  intro x.
  destruct x.
  trivial.
  trivial.
Qed.

(* Zadanko 3 *)
Theorem identIsTwoident: forall (t : Type), forall (f : t -> t), (forall (x : t), f x = x) -> (forall (x : t), f (f x) = x).
Proof.
  intros.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.

(* Zadanko 4 *)
Theorem identForBool: forall (f: bool -> bool), (forall (x : bool), f x = x) -> (forall (x : bool), f (f x) = x).
Proof.
  intro f.
  intro zalozenie.
  apply (identIsTwoident bool f zalozenie).
Qed.




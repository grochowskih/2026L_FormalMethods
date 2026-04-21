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

(* Zadanko 5 *)
Inductive ints : Type := plus (n : nat) | minus (n : nat).
(* konstruktor plus modeluje, że każda liczba naturalna jest liczba calkowta, a minus, ze kazda liczba przeciwna *)
(* do liczby naturalnej jest liczba calkowita *)

Definition absHelp (x : ints) : nat :=
  match x with
  | plus n => n
  | minus n => n
  end.
  
Theorem absNatDec : forall (x : ints), (Nat.leb) 0 (absHelp x) = true.
Proof.
  intro x.
  destruct x.
  simpl.
  reflexivity.
  trivial.
Qed.

(* Zadanko 6 *)
Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros.
  destruct b.
  destruct c.
  reflexivity.
  discriminate.
  destruct c.
  discriminate.
  reflexivity.
Qed. 



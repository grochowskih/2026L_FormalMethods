(* Plik z kodami do Listy 1 z Rocq *)
(* Typ ints i funkcja absHelp *)

Inductive ints : Type := plus (n : nat) | minus (n : nat).
(* konstruktor plus modeluje, że każda liczba naturalna jest liczba calkowta, a minus, ze kazda liczba przeciwna *)
(* do liczby naturalnej jest liczba calkowita *)

Definition absHelp (x : ints) : nat :=
  match x with
  | plus n => n
  | minus n => n
  end.

(* Typ quadPolyNat i funkcja zwracajaca, czy funkcja jest stala *)
Inductive quadPolyNat : Type := coeffs (a b c : nat).

Definition isConst (poly : quadPolyNat) : bool :=
  match poly with
  | coeffs 0 0 _ => true
  | _ => false
  end.

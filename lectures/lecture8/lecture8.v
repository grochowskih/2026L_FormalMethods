(* Fibonacci rekuirencyjny *)

Fixpoint fibRec (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | S (S x as p) => fibRec (p) + fibRec (x)
  end.
  
(* Fibonacci Rekurencyjny Liniowy *)
Fixpoint fibRecLinTmp (n a b : nat) : nat :=
  match n with
  | 0 => a
  | 1 => b
  | S (S x as p) => fibRecLinTmp p b (a+b)
  end.
  
(* Plik z kodami do Listy 1 z Coq *)
(* Typy i funkcje do zrozumienia konstrukcji if-than-else *)

Inductive twoSym : Type := xo | yo.
Inductive twoSym2 : Type := yy | xx.
Inductive triSym : Type := iks.

Definition ex1 (x : twoSym) : nat :=
  if x then 0 else 1.

Eval compute in ex1 xo.
Eval compute in ex1 yo.

Definition ex2 (x : twoSym2) : nat :=
  if x then 0 else 1.

Eval compute in ex2 xx.
Eval compute in ex2 yy.


Definition ex3 (x : triSym) : nat :=
  if x then 0.

Eval compute in ex3 igrek.
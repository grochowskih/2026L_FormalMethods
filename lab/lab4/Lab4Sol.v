(* Zadanko 1 - Trzy przykladowe listy *)
(* [1,2,3], [0,4,7,1], [1] *)

Definition lst1 : list nat := cons 1 (cons 2 (cons 3 nil)).
Definition lst3 : list nat := cons 1 nil.
Definition lst2 : list nat := 0 :: 4 :: 7 :: 1 :: nil.
Print lst2.
Print lst1.
Print lst3.

Fixpoint concatLists (l1 l2 : list nat) : list nat :=
  match l1 , l2 with
  | nil , l2 => l2
  | cons x rest , l2 => cons x (concatLists rest l2)
  end.

Fixpoint reverse (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x rest => concatLists (reverse rest) (cons x nil)
  end.
  
Eval compute in reverse lst1.
Eval compute in reverse lst2.

(* x :: rest   ->  sklej (odwroc rest) [x] *)

Inductive binTrVal := Leaf (x : nat) | Node (y : nat) (lft : binTrVal) (rght : binTrVal).

Definition exTr : binTrVal := Node 4 (Node 0 (Leaf 1) (Leaf 2)) (Leaf 0).

Fixpoint countZeros (tr : binTrVal) : nat :=
  match tr with
  | Leaf 0 => 1
  | Leaf _ => 0
  | Node 0 lft rght => 1 + countZeros lft + countZeros rght
  | Node _ lft rght => countZeros lft + countZeros rght
  end.
  
Eval compute in countZeros exTr.
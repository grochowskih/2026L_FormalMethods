Inductive natList := Nill | conss (x : nat) (rest : natList).

(* Definicja listy [1,2,4] *)
Definition exL : natList := conss 1 (conss 2 (conss 4 Nill)).

(* Lista: [7, 1] *)
Definition exL2 : natList := conss 7 (conss 1 Nill).

(* Funkcja ktora obliczy dlugosc listy *)
Fixpoint lenList (l : natList) : nat :=
  match l with
  | Nill => 0
  | conss x rest => 1 + (lenList rest)
  end.
  
Eval compute in lenList exL2.

(* Konktatenacja dwoch list: concatLists *)
(* [1,2,4] [7,1] -> [1,2,4,7,1] *)

Fixpoint concatLists (l1 l2 : natList) : natList :=
  match l1 , l2 with
  | Nill , l2 => l2
  | conss x rest , l2 => conss x (concatLists rest l2)
  end.
  
Eval compute in concatLists exL exL2.
  
(* Ten dowod przeprowadzimy indukcyjnie *)
Theorem thm: forall (l1 l2 : natList), lenList (concatLists l1 l2) = lenList l1 + lenList l2.
Proof.
  intros.
  induction l1.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl1.
  trivial.
Qed.
  
  
(* Binary Tree with leaves *)
Inductive binTree := Leaf | Node (lft : binTree) (rght : binTree).

(* Nasze przykladowe drzewo z wykladu *)
Definition exTr : binTree := Node (Node Leaf Leaf) Leaf.

(* funkcja liczaca liczbe lisci w drzewie *)
Fixpoint numLeaves (tr : binTree) : nat :=
  match tr with
  | Leaf => 1
  | Node lft rght => (numLeaves lft) + (numLeaves rght)
  end.
  
  
Eval compute in numLeaves exTr.

(* Funkcja liczaca liczbe wezlow w drzewie *)
Fixpoint numNodes (tr : binTree) : nat :=
  match tr with
  | Leaf => 0
  | Node lft rght => 1 + (numNodes lft) + (numNodes rght)
  end.
  
Eval compute in numNodes exTr.

Require Import Lia.
Theorem lvsnds: forall (tr : binTree), numLeaves tr = numNodes tr + 1.
Proof.
  intros.
  induction tr.
  unfold numLeaves.
  unfold numNodes.
  simpl.
  trivial.
  trivial.
  simpl.
  rewrite IHtr1.
  rewrite IHtr2.
  trivial.
  lia.
Qed.

(* Liczby rzeczywiste *)
Require Import Reals.

(* R - typ modelujacy liczby rzeczywiste *)

(* Udowodnimy pewne twierdzenie dla R *)
Theorem multReals: forall (x y z k : R), (x + y + z)%R = k -> (2 * k)%R = (2 * (x + y + z)%R)%R.
Proof.
  intros.
  rewrite -> H.
  trivial.
Qed.
  
  
  
  
  
  
  
  
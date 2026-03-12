(* Wyklad 2 *)
(* Typ z3 *)

Inductive z3 := zero | jeden | dwa.

Definition invEl (x : z3) : z3 :=
  match x with
  | zero => zero
  | jeden => dwa 
  | dwa => jeden
  end.
  
Definition addz3 (x y : z3) : z3 :=
  match x , y with
  | zero , _ => y
  | _ , zero => x
  | jeden , dwa => zero
  | jeden , jeden => dwa
  | dwa , dwa => jeden
  | dwa , jeden => zero
  end.
  
 
(* Nowosci *)

(* Chcemy pokazac, ze dla kazdego x in Z3, x + invEl(x) = 0 *)
Theorem goodInv: forall (x : z3), addz3 x (invEl x) = zero.
Proof.
intro x. (* Ustalmy x *)
destruct x. (* Rozbijmy na przypadki *)
unfold invEl. (* Rozpakujmy definicje invEl *)
unfold addz3.
reflexivity. (* Ze zwrotonosc *)
simpl. (* wykonaj uproszczenia *)
reflexivity. 
trivial.
Qed.

(* Dla kazdych a, b in Z3, jesli (addz3 a b) = zero, to invEl (addz3 a b) = 0*)
 
Theorem zeroGivesZero: forall (a b : z3), (addz3 a b) = zero -> invEl (addz3 a b) = zero.
Proof.
  intros.
  rewrite -> H.
  (*simpl.
  reflexivity.*)
  trivial.
Qed.

Lemma zeroPlusZeroIsZero: addz3 zero zero = zero.
Proof.
  trivial.
Qed.

Lemma zeroGivesZeroEasier: invEl zero = zero.
Proof.
  apply (zeroGivesZero zero zero zeroPlusZeroIsZero).
  (*apply (zeroGivesZero zero zero).
  apply zeroPlusZeroIsZero.*)
Qed.

(* Dowody dla bool *)
Search (bool -> bool -> bool).
Print andb.

Theorem trueImpliesTrue: forall (a b : bool), andb a b = true -> a = true.
Proof.
  intros.
  destruct a.
  trivial.
  unfold andb in H.
  discriminate.
Qed.

Check (forall (a b : bool), andb a b = true -> a = true).
(* Prop - specjalny typ do "twierdzen" *)
 
 
 
 
 
 
 
 
 
 
 
 
 
 
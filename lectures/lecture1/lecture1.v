(* Wyklad 1 *)

(* type Bool : true | false *)
Inductive Boole := truee | falsee.

Check truee . (* Sprawdzamy typ wyrazenia truee *)
Definition orr (x : Boole) (y : Boole) : Boole :=
  match x , y with
  | truee , _ => truee
  | falsee , truee => truee 
  | falsee , falsee => falsee
  end.
  
Eval compute in orr truee falsee .
Eval compute in orr falsee truee .
Check orr truee .

(* type nat : zeroo | suc (n : nat) *)
Inductive OwnNat := zeroo | suc (n : OwnNat) .

(* Przyklady wyrazen i sprawdzenie typow *)
Check zeroo .
Check suc zeroo .
Check suc (suc zeroo) .

Definition two : OwnNat := suc (suc zeroo).

Fixpoint addd (x : OwnNat) (y : OwnNat) : OwnNat :=
  match x , y with
  | zeroo , y => y
  | suc n , y => suc (addd n y)
  end.
  
Eval compute in addd zeroo two.
Eval compute in addd two two .
  

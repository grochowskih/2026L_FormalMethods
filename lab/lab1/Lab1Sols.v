(* Zadanko 1 *)

Inductive z3 := z | o | t. 
Definition invEl (x : z3) : z3 :=
  match x with
  | z => z
  | o => t
  | t => o
  end.
  
(* Zadanko 2 - quadPolyNat *)

Inductive quadPolyNat := coeffs (a : nat) (b : nat) (c : nat) .

(* 7x^2 + 9x + 1 *)
Definition poly1 : quadPolyNat := coeffs 7 9 1 .
(* 4x + 1 *)
Definition poly2 : quadPolyNat := coeffs 0 4 1 .
(* 0 *)
Definition poly3 : quadPolyNat := coeffs 0 0 0 .

(* Zadanko 3 - evalPoly *)
Definition evalPoly (w : quadPolyNat) (x : nat) : nat :=
  match w , x with
  | coeffs a b c , x => a * x * x + b * x + c
  end.
  
Eval compute in evalPoly poly1 2 .
Inductive Boole := true | false.
  
Definition isQuad (w : quadPolyNat) : Boole := 
  match w with
  | coeffs 0 _ _ => false 
  | _ => true
  end.
  
(* Zadanko 4 *)

Inductive ints := natInt (x : nat) | minusNatInt (y : nat) .
Definition fajw : ints := natInt 5 .
Definition majnusFajw : ints := minusNatInt 5.
Definition ziro1 : ints := natInt 0.
Definition ziro2 : ints := minusNatInt 0.

(* Zadnako 5 *)

Definition absHelp (x : ints) : nat :=
  match x with
  | natInt a => a
  | minusNatInt a => a
  end.
  
Eval compute in absHelp majnusFajw .
  
Definition absPlus (x : ints) (y : ints) : nat := (absHelp x) + (absHelp y).

Eval compute in absPlus fajw majnusFajw .

Definition absPlus2 (x : ints) (y : ints) : nat :=
  match x , y with
  | natInt a , natInt b => a + b
  | natInt a , minusNatInt b => a + b
  | minusNatInt a , natInt b => a + b
  | minusNatInt a , minusNatInt b => a + b
  end.
  
Eval compute in absPlus2 fajw majnusFajw .

(* Zadanko 6 - analiza kodu zrodlowego dolaczonego do Lab *)
(* Zadanko 8 - Pojawilo sie tez w Lab3 *)






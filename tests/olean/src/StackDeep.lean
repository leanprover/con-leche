module
prelude

public noncomputable section

inductive N : Type where
  | z
  | s (n : N)

def add (n m : N) : N := N.rec (motive := fun _ => N) m (fun _ ih => N.s ih) n

inductive Same {α : Type} (a : α) : α → Prop where
  | refl : Same a a

def c0 : N := .s N.z
def c1 : N := add c0 c0
def c2 : N := add c1 c1
def c3 : N := add c2 c2
def c4 : N := add c3 c3
def c5 : N := add c4 c4
def c6 : N := add c5 c5
def c7 : N := add c6 c6
def c8 : N := add c7 c7
def c9 : N := add c8 c8
def c10 : N := add c9 c9
def c11 : N := add c10 c10
def c12 : N := add c11 c11
def c13 : N := add c12 c12
def c14 : N := add c13 c13

set_option maxRecDepth 1000000 in
/-- A comparison that recurses once per `s`: 2^14 levels deep, overflowing a small thread stack. -/
theorem deep : Same (add c14 N.z) c14 := @Same.refl N c14

end

/- End-to-end test: indexed recursors beyond the tutorial's coverage.

   `VecB` is a recursive, Nat-indexed non-Prop family; `headOfTwo`'s
   defeq check forces an iota reduction whose index arguments are
   `succ`-applications, exercising the canonical-index certificate on
   non-variable index expressions.  `Even` adds a Prop-valued indexed
   family whose proof term chains two iota-typed constructors. -/

--#export VecB.headOfTwo_eq Even.four

inductive VecB : Nat → Type where
  | nil : VecB Nat.zero
  | cons : (n : Nat) → Bool → VecB n → VecB (Nat.succ n)

noncomputable def VecB.headOfTwo (v : VecB (Nat.succ (Nat.succ Nat.zero))) : Bool :=
  VecB.rec (motive := fun _ _ => Bool) true (fun _ b _ _ => b) v

def VecB.two : VecB (Nat.succ (Nat.succ Nat.zero)) :=
  VecB.cons (Nat.succ Nat.zero) true
    (VecB.cons Nat.zero false VecB.nil)

theorem VecB.headOfTwo_eq : Eq (VecB.headOfTwo VecB.two) true :=
  Eq.refl true

inductive Even : Nat → Prop where
  | zero : Even Nat.zero
  | plus2 : (n : Nat) → Even n → Even (Nat.succ (Nat.succ n))

theorem Even.four :
    Even (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) :=
  Even.plus2 (Nat.succ (Nat.succ Nat.zero)) (Even.plus2 Nat.zero Even.zero)

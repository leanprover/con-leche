--#export InModelMutualIdx.even_two InModelMutualIdx.odd_pos InModelMutualIdx.p_of_q InModelMutualIdx.q_base InModelMutualIdx.r_of_s InModelMutualIdx.size_example

/- End-to-end test: INDEXED mutual inductive blocks modelled IN-PROCESS
   (task #200, B2).  The tag constructors carry the members' index
   telescopes (`tag.m : ∀ p⃗ ı⃗_m, tag p⃗`), the auxiliary family is
   indexed by the tag, the recursor models take the index arguments
   before the major, and the iota statements carry the constructors'
   and the recursive fields' index expressions.

   Four shapes: a `Prop` pair over `Nat` (`Even`/`Odd`; `odd_pos`
   eliminates by mutual induction into a Prop motive over the index), a
   data pair with a recursor-spelled size function (`Tm`/`Args`, with a
   constructor at a shifted index so the index is not promoted to a
   parameter; `size_example`'s `rfl` forces iota through both model
   recursors at the indices), a
   pair whose members have DIFFERENT index telescopes (`P : Nat → Prop`,
   `Q : Nat → Bool → Prop`), and a pair with a universe-polymorphic index
   (`R`/`S` over `α : Type u`, so the tag's universe is inferred as
   `max 1 (u+1)`). -/

namespace InModelMutualIdx

mutual
inductive Even : Nat → Prop where
  | zero : Even 0
  | succ : ∀ n, Odd n → Even (n + 1)
inductive Odd : Nat → Prop where
  | succ : ∀ n, Even n → Odd (n + 1)
end

theorem even_two : Even 2 := .succ 1 (.succ 0 .zero)

theorem odd_pos : ∀ n, Odd n → 0 < n := fun n h =>
  Odd.rec (motive_1 := fun _ _ => True) (motive_2 := fun n _ => 0 < n)
    trivial (fun _ _ _ => trivial) (fun n _ _ => Nat.succ_pos n) h

-- `lam` keeps `n` a genuine index (Lean would otherwise promote a
-- uniform index to a parameter, for the whole block)
mutual
inductive Tm : Nat → Type where
  | var : ∀ n, Fin n → Tm n
  | lam : ∀ n, Tm (n + 1) → Tm n
  | app : ∀ n, Tm n → Args n → Tm n
inductive Args : Nat → Type where
  | nil : ∀ n, Args n
  | cons : ∀ n, Tm n → Args n → Args n
end

noncomputable def Tm.size (n : Nat) (t : Tm n) : Nat :=
  Tm.rec (motive_1 := fun _ _ => Nat) (motive_2 := fun _ _ => Nat)
    (fun _ _ => 1) (fun _ _ ih => ih + 1) (fun _ _ _ ih1 ih2 => ih1 + ih2 + 1)
    (fun _ => 0) (fun _ _ _ ih1 ih2 => ih1 + ih2) t

theorem size_example :
    Tm.size 0 (Tm.lam 0 (Tm.app 1 (Tm.var 1 ⟨0, Nat.zero_lt_one⟩)
      (Args.cons 1 (Tm.var 1 ⟨0, Nat.zero_lt_one⟩) (Args.nil 1)))) = 4 :=
  rfl

mutual
inductive P : Nat → Prop where
  | mk : ∀ n, Q (n + 1) true → P n
inductive Q : Nat → Bool → Prop where
  | mk : ∀ n b, P n → Q (n + 1) b
  | base : ∀ n, Q n false
end

theorem q_base : Q 3 false := .base 3
theorem p_of_q (n : Nat) (h : Q (n + 1) true) : P n := .mk n h

mutual
inductive R (α : Type u) : α → Prop where
  | mk : ∀ a, S α a a → R α a
inductive S (α : Type u) : α → α → Prop where
  | refl : ∀ a, S α a a
  | step : ∀ a b, R α a → S α b a
end

theorem r_of_s {α : Type u} (a : α) : R α a := .mk a (.refl a)

end InModelMutualIdx

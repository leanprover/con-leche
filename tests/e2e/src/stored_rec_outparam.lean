--#export SRO.Conv.use SRO.WithAuto.use SRO.WithOpt.use
/- Task #431: blocks whose stored recursor differs from con-leche's
generated one by binder annotations only.  The official kernel strips a
top-level `outParam`/`optParam`/`autoParam` from the domain of every
local it creates (parameters, fields — the minor premises' binders and
the rules' λ-binders); con-leche's generator keeps them.  The STORED
recursor is installed once it is definitionally equal to the generated
one, binder by binder.  Target and verdict: accept. -/
namespace SRO

class Conv (α : Type) (β : outParam Type) where
  conv : α → β

instance : Conv Nat Bool := ⟨fun n => n == 0⟩

noncomputable def Conv.use : Bool := Conv.rec (motive := fun _ => Bool) (fun f => f 3) (inferInstance : Conv Nat Bool)

structure WithAuto (n : Nat) where
  val : Nat
  pf : val = n := by rfl

noncomputable def WithAuto.use : Nat := WithAuto.rec (motive := fun _ => Nat) (fun v _ => v) (⟨2, rfl⟩ : WithAuto 2)

structure WithOpt where
  a : Nat
  b : Nat := 7

noncomputable def WithOpt.use : Nat := WithOpt.rec (motive := fun _ => Nat) (fun a b => a + b) ⟨1, 2⟩

end SRO

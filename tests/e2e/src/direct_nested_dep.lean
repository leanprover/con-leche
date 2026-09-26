--#export Dep.use

/- End-to-end control for a CROSS-BLOCK dependency: `Box` is a
   structure, `Dep` a two-constructor sum whose `wrap` field is a
   `Box`, and both install through the block install (`checkBlock`). -/

structure Box (α : Type) where
  val : α

inductive Dep (α : Type) where
  | wrap : Box α → Dep α
  | none : Dep α

def Dep.get {α : Type} (d : Dep α) (fallback : α) : α :=
  match d with
  | .wrap b => b.val
  | .none => fallback

theorem Dep.use (a b : Nat) :
    Eq (Dep.get (Dep.wrap (Box.mk a)) b) a := rfl

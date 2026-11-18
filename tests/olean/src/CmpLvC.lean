-- Task #607: a hole and a definition whose level parameters the solution names otherwise.
prelude
import Init.Prelude
universe u
def idu (α : Sort u) (a : α) : α := a
axiom h {α : Sort u} (a : α) : Eq (idu α a) a

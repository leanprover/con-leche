-- Task #607: CmpLvC's constants at other level-parameter names: accepted.
prelude
import Init.Prelude
universe w
def idu (α : Sort w) (a : α) : α := a
theorem h {α : Sort w} (a : α) : Eq (idu α a) a := rfl

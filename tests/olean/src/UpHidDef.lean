-- con-leche's own (task #384, the converse of UpKindDefOpqSol): a
-- definition whose value the module hides (not `@[expose]`), so that an
-- importer at the exported level sees only the axiom Lean exports for it.
module
prelude

public import Init.Data.Nat.Basic

public section

def n : Nat := 17

end

module
prelude

/- Task #424: a module that declares the kind-pinned `Lean.reduceBool`
   (the checker reads its stored kind) as an opaque constant, whose value
   its exported part hides: an importer reads the assumption of its
   statement there.  The home presents what the exported file says, so
   the module is declined wherever its parts are all read (modular, in
   isolation, its own worker); the merged read, which reads every private
   part, accepts it.  Lean accepts the module. -/

public section

inductive Bool : Type where
  | false : Bool
  | true : Bool

opaque Lean.reduceBool : Bool → Bool := fun b => b

end

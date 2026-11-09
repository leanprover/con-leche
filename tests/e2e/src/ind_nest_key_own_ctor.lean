--#export T.mk T.rec
/- A nested key `K T T.base` whose parameter mentions the block's own constructor.  The container's
   fields do not read that parameter, so it survives only in the key, which official checks at the
   end, in the environment holding the whole block (`tc.check(nested, …)`, `inductive.cpp`).  The
   declaration goes straight to the kernel: the elaborator has no `T.base` yet at that point. -/
import Lean
open Lean Elab Command

structure K (A : Type) (a : A) where
  v : A

elab "mk_block" : command => do
  let T := mkConst `T
  let base := mkConst `T.base
  let key := mkApp2 (mkConst ``K) T base
  let d : Declaration := .inductDecl [] 0
    [{ name := `T, type := mkSort 1, ctors := [
        { name := `T.base, type := T },
        { name := `T.mk, type := .forallE `x key T .default }] }] false
  liftCoreM <| addDecl d
mk_block

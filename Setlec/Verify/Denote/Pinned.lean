import Setlec.Verify.Denote
import Setlec.Verify.EnvPreds

/-!
# The pinned basis constants' direct valuations

`pinnedDirectT` — what a reserved basis constant denotes to in the
declarative layer, where it denotes to a bare `BConst` built-in.

Relocated verbatim from `Setlec/TTVerify/EnvTT.lean` (task #148, T1):
the definition is `V`-free — it is a table from the checker's reserved
names to `Setlec/TT/Const.lean`'s built-ins — so it belongs where both
verification lanes can import it.  The level-parameter names it reads
are `Setlec/Verify/EnvPreds.lean`'s `uN`/`vN`/`u1N` (the `uN`/`vN`/
`u1N` restatements that stood beside it were the same relocation's
fourth item).
-/

namespace Setlec.TTVerify

open Setlec.TT

/-- What a reserved basis constant denotes to, where it denotes to a
bare built-in.  `none` for the four the layer derives rather than
carries (see the section note).

**Three entries were wrong until the basis install elaborated them**
(task #119, `DESIGN.md` §8.2's defect, in its "unproved definition"
form).  `Empty` is stored *level-monomorphically* (`levelParams = []`),
so its valuation may not read the assignment at all — its level is
fixed by its pinned type, `Sort 1`.  `Empty.rec` binds **one** level
where the layer's `emptyRec` takes two, the first being `Empty`'s own.
And `PUnit.rec` binds `u_1, u` — motive level *second* in the layer's
order and named `u_1`, not `v`.

Each would have been caught only here, because `val_params` is what
they violate and nothing before the install asserts it for a basis
constant.  That is the house rule's point exactly (`Setlec/TT/DESIGN.md`
§3.1): a definition is a conjecture until a consumer elaborates it. -/
def pinnedDirectT (n : Name) (ψ : Name → Nat) : Option VExpr :=
  if n = natName then some (.const .nat [])
  else if n = natZeroName then some (.const .natZero [])
  else if n = natSuccName then some (.const .natSucc [])
  else if n = natName.str "rec" then some (.const .natRec [ψ uN])
  else if n = psigmaName then some (.const .psigma [ψ uN, ψ vN])
  else if n = psigmaMkName then some (.const .psigmaMk [ψ uN, ψ vN])
  else if n = punitName then some (.const .punit [ψ uN])
  else if n = punitUnitName then some (.const .punitUnit [ψ uN])
  else if n = punitName.str "rec" then
    some (.const .punitRec [ψ uN, ψ u1N])
  else if n = emptyName then some (.const .empty [1])
  else if n = emptyName.str "rec" then
    some (.const .emptyRec [1, ψ uN])
  else if n = quotName then some (.const .quot [ψ uN])
  else if n = quotMkName then some (.const .quotMk [ψ uN])
  else if n = quotLiftName then some (.const .quotLift [ψ uN, ψ vN])
  else if n = quotIndName then some (.const .quotInd [ψ uN])
  else if n = quotSoundName then some (.const .quotSound [ψ uN])
  else none

end Setlec.TTVerify

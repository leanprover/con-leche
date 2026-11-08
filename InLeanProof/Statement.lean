module

public import InLeanProof.ToCL
public import InLeanProof.Fields

/-!
# The simulation theorem's statement (task #451)

**The target.**  If the kernel environment `E` is related to a con-leche
environment `L` (`EnvRel`, `InLeanProof/AddDeclProof.lean`: what InLean reads
off `E` is what con-leche reads off `L`, entry by entry and table by table,
and the projection bodies InLean builds are in range), `L` carries
con-leche's fold invariant (`EnvModelOk`, `ConLeche/Model/Fold.lean`), and
InLean accepts a safe declaration `d` that is not a non-standard axiom, at
con-leche's axiom policy (`theoremConfig`), then some extension of `L` is
related to the new environment and carries the invariant.  `AddDeclSound`
(`InLeanProof/AddDeclProof.lean`, beside its proof and the relation, whose
parts are defined downstream of this file) states it.
`no_false_of_addDeclSound` follows: InLean never adds a safe constant whose
type reads as `False` (`SafeConst`; every such constant of `E` but `sorryAx`
reads as a constant of `L`, `EnvRel.reads`).

**Why "some `L`".**  con-leche's environment is a list, in installation
order; a `Kernel.Environment` is a map.  The statement holds for every
installation order of its groups.

**The axiom policy.**  `sorryAx` is a constant of `E` (the elaborator needs
it), and con-leche installs nothing for it: at con-leche's policy InLean hides
it (`FEnv.sees`), so any use declines, and the relation asks nothing of it.
Unsafe and `partial` constants are not about the theorem either: a safe check
does not see them (`FEnv.sees`), and the relation asks that `L` hold none.

**The install is con-leche's own.**  The extension is what master's accepted
step makes of the records InLean's added constants read as (`toDecl`):
`Env.pushDelta (declConstants d) (declTables d)`.  The install data
(capabilities, firing modes, projection tables) is what con-leche computes
from the records; InLean reads the same data off Lean's entries at use
(`InLean/FEnv.lean`), and the relation says the two agree.

**The range bound.**  InLean's cutoffs read Lean's cached fields, which the
stop-gap axioms (`InLeanProof/MkDataAxioms.lean`) describe only in range, so
the statement is about terms in range: a premise on `d` (`DeclRangeOk`).  The
terms of the constants InLean sees in the environment are in range through
the relation (`StoredT` in its entries, and the projection bodies' range).  `Expr.RangeOk` is what C's constructors enforce, so every term that
exists at runtime has it; it is not an axiom about all `Expr`s, and must not
be one (`Expr.bvar (2^20)` exists in the logic).

**The environment's own operations** are a premise (`EnvLaws`): core's
`Kernel.Environment.find?`/`add` go through `PersistentHashMap`'s `partial`
`findAux`/`insertAux`, which no proof can unfold.
-/

public section

namespace InLeanProof

open Lean

/-- The constants the theorem is about: con-leche checks no unsafe
declaration and no `partial` definition. -/
@[expose] def SafeConst : Lean.ConstantInfo → Prop
  | .defnInfo v => v.safety = .safe
  | ci => ci.isUnsafe = false

/-! ## In range -/

/-- A declaration's terms are in range. -/
@[expose] def DeclRangeOk : Declaration → Prop
  | .axiomDecl v => Expr.RangeOk v.type
  | .defnDecl v => Expr.RangeOk v.type ∧ Expr.RangeOk v.value
  | .thmDecl v => Expr.RangeOk v.type ∧ Expr.RangeOk v.value
  | .opaqueDecl v => Expr.RangeOk v.type ∧ Expr.RangeOk v.value
  | .mutualDefnDecl _ => True
  | .quotDecl => True
  | .inductDecl _ _ types _ =>
    ∀ t ∈ types, Expr.RangeOk t.type ∧ ∀ c ∈ t.ctors, Expr.RangeOk c.type

/-! ## The premise and the configuration -/

/-- **The environment's laws** (a premise: core's map operations are
`partial`).  Adding a fresh name makes it found and changes no other
lookup; marking the quotient package changes no lookup. -/
@[expose] def EnvLaws : Prop :=
  (∀ (E : Kernel.Environment) (ci : Lean.ConstantInfo) (n : Name),
    E.find? ci.name = none →
      (InLean.addConst E ci).find? n = if n = ci.name then some ci else E.find? n) ∧
  (∀ (E E' : Kernel.Environment), E'.constants = E.constants → E'.find? = E.find?)

/-- **The standard axioms**: those con-leche's fold carries a model through
(`axiomStepPB_of`: `propext`, `Classical.choice`, `Quot.sound`, the
compiler-trust family) and `sorryAx`, which it installs as nothing.  At
con-leche's policy InLean declines any other axiom (`checkAxiomC`). -/
@[expose] def StdAxiomName (n : Name) : Prop :=
  n = InLean.propextName ∨ n = InLean.choiceName ∨ n = InLean.quotSoundName ∨
    n = InLean.trustCompilerName ∨ n = InLean.ofReduceNatName ∨ n = InLean.ofReduceBoolName ∨
    n = InLean.sorryAxName

/-- **The declarations the theorem is about** (maintainer's rulings,
2026-11-06 and 2026-11-08): every safe declaration that is not a
non-standard axiom.  A non-standard axiom is the user's assumption, as in
any kernel; an ok environment's axioms are part of its being ok
(`EnvModelOk` of what presents it). -/
@[expose] def SafeDecl : Declaration → Prop
  | .axiomDecl v => v.isUnsafe = false ∧ StdAxiomName v.name
  | .defnDecl v => v.safety = .safe
  | .thmDecl _ => True
  | .opaqueDecl v => v.isUnsafe = false
  | .mutualDefnDecl _ => False
  | .quotDecl => True
  | .inductDecl _ _ _ isUnsafe => isUnsafe = false

/-- The theorem's configuration: the verified mode, con-leche's axiom policy
(`coreAxioms` off: `sorryAx` is no constant, any use of it declines, and no
other constant may take its name; an axiom at a certified `Nat` operation's
name is refused), the `Nat` certificates checked.  Core runs with `uncertifiedNatOps` on, which
accepts a definition at a certified name whose certificate cannot be
checked: covered only where the environment already holds the certified
definitions (the prelude assumed good), an obligation of the
environment's being ok (DESIGN, O10). -/
@[expose] def theoremConfig : InLean.Config :=
  { mode := .verified, coreAxioms := false, uncertifiedNatOps := false }

end InLeanProof

module

public import InLeanProof.ToCL
public import InLeanProof.Fields

/-!
# The simulation theorem's statement (task #451)

**The target.**  If a con-leche environment `L` *presents* the kernel
environment `E` — `L` is what con-leche's install makes of `E`'s
declaration groups, read as its records (`toDecl`), in some order, and every
safe constant of `E` but `sorryAx` reads as a constant of `L` — and `L`
carries con-leche's fold invariant (`EnvModelOk`, `ConLeche/Model/Fold.lean`),
and InLean accepts a safe declaration `d` that is not a non-standard axiom, at
con-leche's axiom policy (`theoremConfig`), then some extension of `L`
presents the new environment and carries the invariant (maintainer's ruling,
2026-11-08).
`AddDeclSound` (`InLeanProof/AddDeclProof.lean`, beside its proof) states it,
with InLean's relation to `L` (`RelatesI`: O4's `EnvPresI` and the projection
bodies' range) as a further premise and conclusion: `Presents` reads only
names and types, and the simulation needs the readers' agreement, which is
not a consequence of `Presents` (a `Presents` environment may install an
unsafe constant InLean hides).  `no_false_of_addDeclSound` — InLean never adds
a safe constant whose type reads as `False` — follows.

**Why "some `L` presenting `E`".**  con-leche's environment is a list, in
installation order; a `Kernel.Environment` is a map.  The statement holds
for every installation order of its groups.

**The axiom policy.**  `sorryAx` is a constant of `E` (the elaborator needs
it), and con-leche installs nothing for it: at con-leche's policy InLean hides
it (`FEnv.sees`), so any use declines, and `Presents` asks nothing of it.
Unsafe and `partial` constants are not about the theorem either: a safe check
does not see them (`FEnv.sees`), and con-leche's install has none.

**The install is con-leche's own.**  `L` is `installAll ds`: master's
`Env.pushDelta (declConstants d) (declTables d)` folded over the records
`ds`.  The install data (capabilities, firing modes, projection tables) is
what con-leche computes from the records; InLean reads the same data off
Lean's entries at use (`InLean/FEnv.lean`).

**The range bound.**  InLean's cutoffs read Lean's cached fields, which the
stop-gap axioms (`InLeanProof/MkDataAxioms.lean`) describe only in range, so
the statement is about terms in range: a premise on `E` and `d`, a conclusion
on `E'`.  `Expr.RangeOk` is what C's constructors enforce, so every term that
exists at runtime has it; it is not an axiom about all `Expr`s, and must not
be one (`Expr.bvar (2^20)` exists in the logic).

**The environment's own operations** are a premise (`EnvLaws`): core's
`Kernel.Environment.find?`/`add` go through `PersistentHashMap`'s `partial`
`findAux`/`insertAux`, which no proof can unfold.
-/

public section

namespace InLeanProof

open Lean

/-! ## Presenting an environment -/

/-- `cs` is one of `E`'s declaration groups, read as the record `d`. -/
@[expose] def ReadsGroup (E : Kernel.Environment) (cs : List Lean.ConstantInfo)
    (d : ConLeche.Declaration) : Prop :=
  (∀ ci ∈ cs, E.find? ci.name = some ci) ∧ toDecl cs = some d

/-- **con-leche's install of a list of records**, in order: each record's
constants and tables pushed (`Env.pushDelta`, `declConstants`, `declTables`). -/
@[expose] def installAll (ds : List ConLeche.Declaration) : ConLeche.Env :=
  ds.foldl (fun L d => L.pushDelta (ConLeche.declConstants d) (ConLeche.declTables d))
    ConLeche.Env.empty

/-- The constants the theorem is about: con-leche checks no unsafe
declaration and no `partial` definition. -/
@[expose] def SafeConst : Lean.ConstantInfo → Prop
  | .defnInfo v => v.safety = .safe
  | ci => ci.isUnsafe = false

/-- **`L` presents `E`**: `L` is con-leche's install of records that each
read a declaration group of `E`, and every safe constant of `E` but `sorryAx`
(present on Lean's side only: con-leche installs nothing for it) reads as a
constant of `L` (its name and its type). -/
@[expose] def Presents (E : Kernel.Environment) (L : ConLeche.Env) : Prop :=
  ∃ ds : List ConLeche.Declaration,
    (∀ d ∈ ds, ∃ cs, ReadsGroup E cs d) ∧ L = installAll ds ∧
    ∀ n ci, E.find? n = some ci → SafeConst ci → n ≠ InLean.sorryAxName →
      ∃ c ∈ L.consts, toName n = c.name ∧ toExprC ci.type = some c.toConstantVal.type

/-! ## In range -/

/-- A constant's terms are in range. -/
@[expose] def ConstRangeOk : Lean.ConstantInfo → Prop
  | .axiomInfo v => Expr.RangeOk v.type
  | .defnInfo v => Expr.RangeOk v.type ∧ Expr.RangeOk v.value
  | .thmInfo v => Expr.RangeOk v.type ∧ Expr.RangeOk v.value
  | .opaqueInfo v => Expr.RangeOk v.type ∧ Expr.RangeOk v.value
  | .quotInfo v => Expr.RangeOk v.type
  | .inductInfo v => Expr.RangeOk v.type
  | .ctorInfo v => Expr.RangeOk v.type
  | .recInfo v => Expr.RangeOk v.type ∧ ∀ r ∈ v.rules, Expr.RangeOk r.rhs

/-- Every constant of `E` is in range. -/
@[expose] def EnvRangeOk (E : Kernel.Environment) : Prop :=
  ∀ n ci, E.find? n = some ci → ConstRangeOk ci

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

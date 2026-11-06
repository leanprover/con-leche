module

public import InLeanProof.ToCL
public import InLeanProof.Fields
public import ConLeche.Model.Fold
public import ConLeche.Model.Capstone

/-!
# The simulation theorem's statement (task #451)

**The target.**  If a con-leche environment `L` *presents* the kernel
environment `E` — `L` is what con-leche's install makes of `E`'s
declaration groups, read as its records (`toDecl`), in some order, and every
safe constant of `E` reads as a constant of `L` — and `L` carries con-leche's
fold invariant (`EnvModelOk`, `ConLeche/Model/Fold.lean`), and InLean accepts
a safe declaration `d` at the theorem's configuration, then some extension
of `L` presents the new environment and carries the invariant.
`AddDeclSound` states it; it is not proved (the obligations are in DESIGN.md,
"TASK #451 — restart on master").  What it gives is proved:
`no_false_of_addDeclSound` — InLean never adds a safe constant whose type
reads as `False`.

**Why "some `L` presenting `E`".**  con-leche's environment is a list, in
installation order; a `Kernel.Environment` is a map.  The statement holds
for every installation order of its groups.

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
read a declaration group of `E`, and every safe constant of `E` reads as a
constant of `L` (its name and its type). -/
@[expose] def Presents (E : Kernel.Environment) (L : ConLeche.Env) : Prop :=
  ∃ ds : List ConLeche.Declaration,
    (∀ d ∈ ds, ∃ cs, ReadsGroup E cs d) ∧ L = installAll ds ∧
    ∀ n ci, E.find? n = some ci → SafeConst ci →
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

/-- **The declarations the theorem is about** (maintainer's ruling,
2026-11-06): every safe declaration but an axiom.  An axiom is the user's
assumption, as in any kernel; an ok environment's axioms are part of its
being ok (`EnvModelOk` of what presents it). -/
@[expose] def SafeDecl : Declaration → Prop
  | .axiomDecl _ => False
  | .defnDecl v => v.safety = .safe
  | .thmDecl _ => True
  | .opaqueDecl v => v.isUnsafe = false
  | .mutualDefnDecl _ => False
  | .quotDecl => True
  | .inductDecl _ _ _ isUnsafe => isUnsafe = false

/-- The theorem's configuration: the verified mode, the official axiom policy
(core's: it decides only `sorryAx`'s visibility and what an axiom at a
certified `Nat` operation's name may be, neither of which a non-axiom
declaration over a model-carrying environment meets), the `Nat`
certificates checked.  Core runs with `uncertifiedNatOps` on, which
accepts a definition at a certified name whose certificate cannot be
checked: covered only where the environment already holds the certified
definitions (the prelude assumed good), an obligation of the
environment's being ok (DESIGN, O10). -/
@[expose] def theoremConfig : InLean.Config :=
  { mode := .verified, coreAxioms := true, uncertifiedNatOps := false }

/-! ## The target -/

universe w

/-- **The simulation theorem** (target; not proved). -/
@[expose] def AddDeclSound (V : Type w) [ConLeche.SetTheory V] : Prop :=
  EnvLaws →
  ∀ (E E' : Kernel.Environment) (d : Declaration) (L : ConLeche.Env),
    SafeDecl d → DeclRangeOk d → EnvRangeOk E →
    Presents E L → ConLeche.Model.EnvModelOk V L →
    InLean.addDecl E d theoremConfig = .ok E' →
    ∃ L', EnvRangeOk E' ∧ Presents E' L' ∧ ConLeche.Model.EnvModelOk V L' ∧
      ∃ new, L'.consts = new ++ L.consts

/-! ## What the target gives -/

/-- **No proof of `False`**: under the target, InLean never adds a safe
constant whose type reads as `False` to a presented environment with a
model. -/
theorem no_false_of_addDeclSound (V : Type w) [ConLeche.SetTheory V] (hS : AddDeclSound V)
    (hlaws : EnvLaws) {E E' : Kernel.Environment} {d : Declaration} {L : ConLeche.Env}
    (hd : SafeDecl d) (hdr : DeclRangeOk d) (hE : EnvRangeOk E) (hP : Presents E L)
    (hM : ConLeche.Model.EnvModelOk V L)
    (h : InLean.addDecl E d theoremConfig = .ok E')
    {n : Name} {ci : Lean.ConstantInfo} (hci : E'.find? n = some ci) (hsafe : SafeConst ci)
    (hfalse : toExprC ci.type = some (.const ConLeche.falseName [])) : False := by
  obtain ⟨L', -, ⟨ds, -, -, hread⟩, hM', -⟩ := hS hlaws E E' d L hd hdr hE hP hM h
  obtain ⟨c, hc, -, hty⟩ := hread n ci hci hsafe
  obtain ⟨mp⟩ := hM'.nonempty
  rw [hfalse] at hty
  exact ConLeche.Model.no_constant_of_False mp c hc (Option.some.inj hty).symm

end InLeanProof

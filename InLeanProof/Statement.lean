module

public import InLeanProof.ToCL
public import InLeanProof.Fields
public import ConLeche.Model.Fold
public import ConLeche.Model.Capstone

/-!
# The simulation theorem's statement (task #451, lane F)

**The target.**  If a con-leche environment `L` *presents* the kernel
environment `E` (every safe constant of `E` is in `L`, read through
`toCL`, and nothing else is) and carries con-leche's fold invariant
(`EnvModelOk`: the graded set model, `ConLeche/Model/Fold.lean`), and
InLean accepts a safe declaration `d` at the theorem's configuration,
then some extension of `L` presents the new environment and carries the
invariant.  (Every term in range; see below.)  `AddDeclSound` states it; it is not proved yet (the lane F
record in DESIGN.md lists the obligations).  What it gives is proved:
`no_false_of_addDeclSound` — InLean never adds a safe constant whose
type reads as `False`.

**Why "some `L` presenting `E`" and not a function of `E`.**  con-leche's
environment is a list, in installation order, and its invariant is
about that list; a `Kernel.Environment` is a map.  The statement holds
for every list that presents the map.

**Install data.**  `L`'s inductive entries carry con-leche's install
data (`IndCaps`, recursor rule data, projection tables), which a
`Lean.ConstantInfo` does not: presentation fixes the names, levels,
types, values, counts and rule right-hand sides, and leaves the install
data to the invariant (`EnvModelOk` holds of `L` only if its install
data is the installer's).

**The range bound.**  InLean's cutoffs read Lean's cached fields, which the
stop-gap axioms (`InLeanProof/MkDataAxioms.lean`) describe only in range, so
the statement is about terms in range: a premise on `E` and `d`, a conclusion on
`E'`.  This costs no strength in use: `Expr.RangeOk` is what C's constructors
enforce, so every term that exists at runtime has it.  It is not an axiom about
all `Expr`s, and it must not be one (`Expr.bvar (2^20)` exists in the logic).
Inside a run, the terms InLean builds stay in range: instantiation at closed
substitutions cannot grow an index, `abstract` writes a poison checked at its
call sites (`InLean.abstractChecked`), and the generator's output is checked
(`IC.constInRange`); the obligations table in DESIGN.md records the proofs.

**The environment's own operations** are a premise (`EnvLaws`): core's
`Kernel.Environment.find?`/`add` go through `PersistentHashMap`'s
`partial` `findAux`/`insertAux`, which no proof can unfold (the
opaque-surface audit, `scripts/inlean_opaque_audit.lean`).
-/

public section

namespace InLeanProof

open Lean

/-! ## Reading constants -/

/-- A constant's name, levels and type, read. -/
@[expose] def ReadsCV (v : ConstantVal) (cv : ConLeche.ConstantVal) : Prop :=
  toName v.name = cv.name ∧ v.levelParams.map toName = cv.levelParams ∧
    toExprC v.type = some cv.type

@[expose] def toHint : ReducibilityHints → ConLeche.ReducibilityHint
  | .opaque => .opaque
  | .abbrev => .abbrev
  | .regular h => .regular h.toNat

/-- One recursor rule, read. -/
@[expose] def RuleReads (r : RecursorRule) (cr : ConLeche.RecRule) : Prop :=
  toName r.ctor = cr.ctor ∧ r.nfields = cr.nfields ∧ toExprC r.rhs = some cr.rhs

/-- The kind-specific part of a presentation: values (definitions),
counts (constructors, recursors) and rule right-hand sides; theorems
and opaques without their values (con-leche stores neither). -/
@[expose] def KindPresents : Lean.ConstantInfo → ConLeche.ConstantInfo → Prop
  | .axiomInfo _, c => ∃ cv, c = .axiomInfo cv
  | .defnInfo v, c => ∃ cv val, c = .defnInfo cv val (toHint v.hints) ∧ toExprC v.value = some val
  | .thmInfo _, c => ∃ cv, c = .thmInfo cv
  | .opaqueInfo _, c => ∃ cv, c = .axiomInfo cv
  | .quotInfo _, _ => True
  | .inductInfo _, c => ∃ cv caps, c = .indInfo cv caps
  | .ctorInfo v, c => ∃ cv, c = .ctorInfo cv v.numParams v.numFields
  | .recInfo v, c => ∃ cv rules,
      c = .recInfo cv (v.numParams + v.numMotives + v.numMinors + v.numIndices)
        (v.numParams + v.numMotives + v.numMinors) rules ∧
      v.rules.length = rules.length ∧ ∀ p ∈ v.rules.zip rules, RuleReads p.1 p.2

/-- `c` presents `ci`. -/
@[expose] def ConstPresents (ci : Lean.ConstantInfo) (c : ConLeche.ConstantInfo) : Prop :=
  ReadsCV ci.toConstantVal c.toConstantVal ∧ KindPresents ci c

/-- The constants the theorem is about: con-leche checks no unsafe
declaration and no `partial` definition. -/
@[expose] def SafeConst : Lean.ConstantInfo → Prop
  | .defnInfo v => v.safety = .safe
  | ci => ci.isUnsafe = false

/-- **`L` presents `E`**: every safe constant of `E` is in `L`, and every
constant of `L` presents one of `E`. -/
@[expose] def Presents (E : Kernel.Environment) (L : ConLeche.Env) : Prop :=
  (∀ n ci, E.find? n = some ci → SafeConst ci → ∃ c ∈ L.consts, ConstPresents ci c) ∧
  (∀ c ∈ L.consts, ∃ n ci, E.find? n = some ci ∧ ConstPresents ci c)

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

/-- The declarations the theorem is about. -/
@[expose] def SafeDecl : Declaration → Prop
  | .axiomDecl v => v.isUnsafe = false
  | .defnDecl v => v.safety = .safe
  | .thmDecl _ => True
  | .opaqueDecl v => v.isUnsafe = false
  | .mutualDefnDecl _ => False
  | .quotDecl => True
  | .inductDecl _ _ _ isUnsafe => isUnsafe = false

/-- The theorem's configuration: the verified mode, con-leche's axiom
policy, no Nat-operation stopgap. -/
@[expose] def theoremConfig : InLean.Config :=
  { mode := .verified, coreAxioms := false, uncertifiedNatOps := false }

/-! ## The target -/

universe w

/-- **The simulation theorem** (target; not proved). -/
@[expose] def AddDeclSound (V : Type w) [ConLeche.SetTheory V] : Prop :=
  EnvLaws →
  ∀ (E E' : Kernel.Environment) (d : Declaration) (L : ConLeche.Env),
    SafeDecl d → DeclRangeOk d → EnvRangeOk E →
    Presents E L → ConLeche.Model.EnvModelOk V .verified L →
    InLean.addDecl E d theoremConfig = .ok E' →
    ∃ L', EnvRangeOk E' ∧ Presents E' L' ∧ ConLeche.Model.EnvModelOk V .verified L' ∧
      ∃ new, L'.consts = new ++ L.consts

/-! ## What the target gives -/

theorem ConstPresents.type {ci : Lean.ConstantInfo} {c : ConLeche.ConstantInfo}
    (h : ConstPresents ci c) : toExprC ci.toConstantVal.type = some c.toConstantVal.type :=
  h.1.2.2

/-- **No proof of `False`**: under the target, InLean never adds a safe
constant whose type reads as `False` to a presented environment with a
model. -/
theorem no_false_of_addDeclSound (V : Type w) [ConLeche.SetTheory V] (hS : AddDeclSound V)
    (hlaws : EnvLaws) {E E' : Kernel.Environment} {d : Declaration} {L : ConLeche.Env}
    (hd : SafeDecl d) (hdr : DeclRangeOk d) (hE : EnvRangeOk E) (hP : Presents E L)
    (hM : ConLeche.Model.EnvModelOk V .verified L)
    (h : InLean.addDecl E d theoremConfig = .ok E')
    {n : Name} {ci : Lean.ConstantInfo} (hci : E'.find? n = some ci) (hsafe : SafeConst ci)
    (hfalse : toExprC ci.toConstantVal.type = some (.const ConLeche.falseName [])) : False := by
  obtain ⟨L', -, hP', hM', -⟩ := hS hlaws E E' d L hd hdr hE hP hM h
  obtain ⟨c, hc, hpres⟩ := hP'.1 n ci hci hsafe
  obtain ⟨mp⟩ := hM'.nonempty
  have hty : c.toConstantVal.type = .const ConLeche.falseName [] := by
    have := hpres.type
    rw [hfalse] at this
    exact (Option.some.inj this).symm
  exact ConLeche.Model.no_constant_of_False mp c hc hty

end InLeanProof

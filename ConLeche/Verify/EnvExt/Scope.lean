module

public import ConLeche.Kernel.CoreDefs

public section

/-!
# Env extension, part 1: the scope and the agreement hypothesis

PRIMREC's member tie needs: a pure kernel run whose input mentions only
constants of a SCOPE answers the same in any two environments that
agree on the scope (the extension lemma is the special case "the
smaller environment and a later one").  The audit (DESIGN.md, ENVEXT)
sorts the knot's `Env.find?` reads into four kinds; this file states
the hypothesis that covers each:

* **S** (a name the run holds): the scope predicate `N` holds of every
  constant, projection struct name and fvar annotation of every term
  the run touches (`Sc N`), and the environments agree on `N`
  (`Agree.find`);
* **C** (names read out of stored info): stored info of a scoped name
  is scoped (`Agree.closed`, `CiSc`), and a rule's η bit is the lookup's
  verdict (`Agree.etaRule`), so the η constructor it fabricates at is
  the rule's own;
* **D** (derived names): `N` is closed under `projTableName` and
  `projFnName` (`Agree.table`, `Agree.projFn`);
* **F** (the literal guards' and the unit test's names, read whatever
  the input): a LITERAL is scoped only with the names it implicitly
  reads (`litNames`, as `Expr.constsResolve` has it), so a guard read
  with a literal in hand agrees; the `Nat` trio and `PUnit`/`PUnit.rec`
  are scoped together (`Agree.natMate`, `Agree.punitMate`: pinned
  basis blocks install atomically); a stored certified `Nat`
  operation's guard names are scoped (`Agree.natOp`); and the one read
  with no literal in hand (the `Nat` operations' fast path) is
  monotone (`Agree.natLit`), which the one-directional currency
  (`Ok.lean`) absorbs.  No name is in scope merely for being looked
  up: a base environment need not be past the prelude.

It then proves `Sc` closed under every term operation the knot uses,
and every fuel-free reader of `Kernel/CoreDefs.lean` and
`Kernel/PropRead.lean` congruent across the two environments.
-/

namespace ConLeche.EnvExt

open ConLeche

/-- The `Nat` literal's names: the basis trio. -/
@[expose] def natLitNames : List Name := [natName, natZeroName, natSuccName]

/-- **The names a literal implicitly reads** (`Expr.constsResolve`'s
literal clauses): a `Nat` literal the trio, a string literal the trio
and the seven string-support names. -/
@[expose] def litNames : Literal → List Name
  | .natVal _ => natLitNames
  | .strVal _ => litGuardNames

/-- **Scoped by `N`**: every constant, projection struct name and
(hereditarily) fvar annotation satisfies `N`, and every literal's
implicit names (`litNames`) do. -/
@[expose] def Sc (N : Name → Prop) : Expr → Prop
  | .bvar _ => True
  | .fvar _ ty => Sc N ty
  | .sort _ => True
  | .const n _ => N n
  | .app f a => Sc N f ∧ Sc N a
  | .lam ty b _ => Sc N ty ∧ Sc N b
  | .forallE ty b _ => Sc N ty ∧ Sc N b
  | .letE t v b => Sc N t ∧ Sc N v ∧ Sc N b
  | .lit l => ∀ n ∈ litNames l, N n
  | .proj s _ e => N s ∧ Sc N e

section ScSimp
variable {N : Name → Prop}

@[simp] theorem sc_bvar {i : Nat} : Sc N (.bvar i) := by simp [Sc]
@[simp] theorem sc_fvar {i : Nat} {ty : Expr} : Sc N (.fvar i ty) ↔ Sc N ty := by simp [Sc]
@[simp] theorem sc_sort {u : Level} : Sc N (.sort u) := by simp [Sc]
@[simp] theorem sc_const {n : Name} {us : List Level} : Sc N (.const n us) ↔ N n := by
  simp [Sc]
@[simp] theorem sc_app {f a : Expr} : Sc N (.app f a) ↔ Sc N f ∧ Sc N a := by simp [Sc]
@[simp] theorem sc_lam {ty b : Expr} {m : BinderMeta} :
    Sc N (.lam ty b m) ↔ Sc N ty ∧ Sc N b := by simp [Sc]
@[simp] theorem sc_forallE {ty b : Expr} {m : BinderMeta} :
    Sc N (.forallE ty b m) ↔ Sc N ty ∧ Sc N b := by simp [Sc]
@[simp] theorem sc_letE {t v b : Expr} :
    Sc N (.letE t v b) ↔ Sc N t ∧ Sc N v ∧ Sc N b := by simp [Sc]
@[simp] theorem sc_lit {l : Literal} : Sc N (.lit l) ↔ ∀ n ∈ litNames l, N n := by simp [Sc]
@[simp] theorem sc_proj {s : Name} {i : Nat} {e : Expr} :
    Sc N (.proj s i e) ↔ N s ∧ Sc N e := by simp [Sc]

end ScSimp

/-- A stored rule's scoped parts: its constructor name, its right-hand
side and a nested rule's stored parameter instantiations. -/
@[expose] def RuleSc (N : Name → Prop) (rl : RecRule) : Prop :=
  N rl.ctor ∧ Sc N rl.rhs ∧
    ∀ lvls pins, rl.fire = .nested lvls pins → ∀ p ∈ pins, Sc N p

/-- **The parts of a stored constant the knot reads**, scoped: every
type; a definition's value; a recursor's rules; a projection table's
bodies.  (A theorem's value is never read; an inductive's η
constructor is read only through a rule's η bit, `Agree.etaRule`.) -/
@[expose] def CiSc (N : Name → Prop) : ConstantInfo → Prop
  | .axiomInfo cv => Sc N cv.type
  | .defnInfo cv v _ => Sc N cv.type ∧ Sc N v
  | .thmInfo cv _ => Sc N cv.type
  | .indInfo cv _ => Sc N cv.type
  | .ctorInfo cv _ _ => Sc N cv.type
  | .recInfo cv _ _ rules => Sc N cv.type ∧ ∀ rl ∈ rules, RuleSc N rl
  | .projInfo tbl => ∀ b ∈ tbl.bodies.toList, Sc N b

/-- **The agreement hypothesis** between the environment a run was made
in (`E₁`) and another one (`E₂`), relative to a scope `N`. -/
structure Agree (N : Name → Prop) (E₁ E₂ : Env) : Prop where
  /-- the two environments agree on the scope -/
  find : ∀ {n : Name}, N n → E₂.find? n = E₁.find? n
  /-- stored info of a scoped name is scoped -/
  closed : ∀ {n : Name} {ci : ConstantInfo}, N n → E₁.find? n = some ci → CiSc N ci
  /-- a stored rule's η bit is the lookup's own verdict (`RecCtorsStored`'s
  third clause, at the scope): the η rescue fabricates at the η
  constructor, which is then the rule's -/
  etaRule : ∀ {n : Name} {cv : ConstantVal} {mI rP : Nat} {rules : List RecRule}, N n →
    E₁.find? n = some (.recInfo cv mI rP rules) →
    ∀ rl ∈ rules, rl.eta = true → recRuleEtaOf E₁.find? n rl.ctor = true
  /-- a scoped constant's projection table name is scoped -/
  table : ∀ {T : Name}, N T → N (projTableName T)
  /-- a scoped constant's projection-function names are scoped -/
  projFn : ∀ {T : Name} (j : Nat), N T → N (projFnName T j)
  /-- the pinned `Nat` trio is scoped together (the `Nat` basis block
  installs its three names at once) -/
  natMate : ∀ {n : Name}, n ∈ natLitNames → N n → ∀ m ∈ natLitNames, N m
  /-- `PUnit.rec` is scoped with `PUnit` (the unit test reads both) -/
  punitMate : N punitName → N punitRecName
  /-- a stored certified `Nat` operation's guard names are scoped: the
  trio, and the `Bool` constructors of the comparisons
  (`natOpGuard`, which the operation's install established) -/
  natOp : ∀ {c : Name}, N c → natOpStored E₁ c = true → (c ∈ natOpNames ∨ c ∈ natDivModNames) →
    (∀ m ∈ natLitNames, N m) ∧
      ((c = natBeqName ∨ c = natBleName) → N boolTrueName ∧ N boolFalseName)
  /-- the `Nat` literal guard is monotone from `E₁` to `E₂` (the later
  environment keeps the earlier one's basis) -/
  natLit : natLitSupported E₁ = true → natLitSupported E₂ = true

namespace Agree

variable {N : Name → Prop} {E₁ E₂ : Env} (H : Agree N E₁ E₂)
include H

theorem natMate' {n : Name} (hn : n ∈ natLitNames) (h : N n) :
    N natName ∧ N natZeroName ∧ N natSuccName :=
  ⟨H.natMate hn h _ (by simp [natLitNames]), H.natMate hn h _ (by simp [natLitNames]),
    H.natMate hn h _ (by simp [natLitNames])⟩

/-- The closure fact at `E₂`. -/
theorem closed₂ {n : Name} {ci : ConstantInfo} (hn : N n) (h : E₂.find? n = some ci) :
    CiSc N ci :=
  H.closed hn (by rw [← H.find hn]; exact h)

/-- Projection-table lookups of a scoped name agree. -/
theorem findProj? {T : Name} (hT : N T) (i : Nat) :
    E₂.findProj? T i = E₁.findProj? T i := by
  unfold Env.findProj?; rw [H.find (H.table hT)]

end Agree

end ConLeche.EnvExt

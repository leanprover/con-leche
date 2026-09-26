module

public import ConLeche.Kernel.Core

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
* **F** (fixed names): `N` holds of `envExtFixedNames`
  (`Agree.fixed`).

It then proves `Sc` closed under every term operation the knot uses,
and every fuel-free reader of `Kernel/CoreDefs.lean` and
`Kernel/PropRead.lean` congruent across the two environments.
-/

namespace ConLeche.EnvExt

open ConLeche

/-- **Scoped by `N`**: every constant, projection struct name and
(hereditarily) fvar annotation satisfies `N`.  Literals are scoped
unconditionally: the names a literal implicitly reads are fixed ones
(`envExtFixedNames`). -/
@[expose] def Sc (N : Name → Prop) : Expr → Prop
  | .bvar _ => True
  | .fvar _ ty => Sc N ty
  | .sort _ => True
  | .const n _ => N n
  | .app f a => Sc N f ∧ Sc N a
  | .lam ty b _ => Sc N ty ∧ Sc N b
  | .forallE ty b _ => Sc N ty ∧ Sc N b
  | .letE t v b => Sc N t ∧ Sc N v ∧ Sc N b
  | .lit _ => True
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
@[simp] theorem sc_lit {l : Literal} : Sc N (.lit l) := by simp [Sc]
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

/-- **The fixed names** the knot looks up whatever the input: the unit
test's `PUnit`/`PUnit.rec`, the two literal guards' ten names, `And`'s
projection table (the `And` rescue), and the `Bool` constructors the
structural comparisons produce. -/
@[expose] def envExtFixedNames : List Name :=
  [punitName, punitRecName, projTableName andName, boolTrueName, boolFalseName] ++
    litGuardNames

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
  /-- the fixed names are scoped -/
  fixed : ∀ n ∈ envExtFixedNames, N n

namespace Agree

variable {N : Name → Prop} {E₁ E₂ : Env} (H : Agree N E₁ E₂)
include H

theorem fixed_punit : N punitName := H.fixed _ (by simp [envExtFixedNames])
theorem fixed_punitRec : N punitRecName := H.fixed _ (by simp [envExtFixedNames])
theorem fixed_andTable : N (projTableName andName) :=
  H.fixed _ (by simp [envExtFixedNames])
theorem fixed_boolTrue : N boolTrueName := H.fixed _ (by simp [envExtFixedNames])
theorem fixed_boolFalse : N boolFalseName := H.fixed _ (by simp [envExtFixedNames])
theorem fixed_lit {n : Name} (h : n ∈ litGuardNames) : N n :=
  H.fixed _ (by simp [envExtFixedNames, h])
theorem fixed_nat : N natName := H.fixed_lit (by simp [litGuardNames])
theorem fixed_natZero : N natZeroName := H.fixed_lit (by simp [litGuardNames])
theorem fixed_natSucc : N natSuccName := H.fixed_lit (by simp [litGuardNames])
theorem fixed_string : N stringName := H.fixed_lit (by simp [litGuardNames])
theorem fixed_stringOfList : N stringOfListName := H.fixed_lit (by simp [litGuardNames])
theorem fixed_list : N listName := H.fixed_lit (by simp [litGuardNames])
theorem fixed_listNil : N listNilName := H.fixed_lit (by simp [litGuardNames])
theorem fixed_listCons : N listConsName := H.fixed_lit (by simp [litGuardNames])
theorem fixed_char : N charName := H.fixed_lit (by simp [litGuardNames])
theorem fixed_charOfNat : N charOfNatName := H.fixed_lit (by simp [litGuardNames])

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

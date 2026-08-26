import Setlec.Kernel.Checker
import Setlec.Verify.Level
import Setlec.Verify.EnvWF
import Setlec.TT.Judgment

/-!
# Denotation of kernel expressions into the declarative type theory

`denote cval env φ d e` maps a kernel `Expr` to a `Setlec.TT.VExpr`.
It is **the structural transpose of `Setlec/Model/Interp.lean`'s
`interpExpr`**, clause for clause, and the reader should hold the two
side by side: everything below is `interpExpr` with the set-theoretic
universe `V` replaced by the syntax `VExpr` and set-level operations
replaced by the corresponding term formers.

| `interpExpr` | `denote` |
|---|---|
| `some (univ (u.eval φ))` | `some (.sort (u.eval φ))` |
| `some (ρ idx)` | `some (.bvar (d - 1 - idx))` |
| `cval n (Level.substFn φ ps us)` | *the same*, at `TConstVal` |
| `piC A fun x => …` | `.pi ⟦ty⟧ ⟦body opened⟧` |
| `lamC A fun x => …` | `.lam ⟦ty⟧ ⟦body opened⟧` |
| `SetTheory.app vf va` | `.app ⟦f⟧ ⟦a⟧` |
| `sfst`/`ssnd` | *see "The projection gap"* |
| `natLitVal zv sv n` | `natLitT ⟦zero⟧ ⟦succ⟧ n` |

Three points where the transpose is worth stating rather than reading
off the table.

## The free-variable valuation collapses

`interpExpr` carries `ρ : Nat → V` because a set has no notion of
"variable": the interpretation of an opened binder has to be handed the
member it stands for, and `updV` extends `ρ` at the binder's own depth.
Here the opened binder *is* a variable, and which one it is is
determined by its own `fvar` index together with the current depth —
`fvar d` opened at depth `d` becomes de Bruijn index `0` under one
binder, `1` under two, i.e. `.bvar (d' - 1 - d)` at depth `d'`.  So
`ρ` and `updV` have no counterpart: the leaf clause computes what the
valuation would have stored.  Correspondingly the counterpart of
`FvarsOk` (which constrains `ρ`) is `CtxOk` (which constrains the de
Bruijn context `Δ`); see `Setlec/TTVerify/EnvTT.lean`.

## Delta is `rfl`, because `denote` never delta-reduces either

`denote` does *not* unfold a constant: like `interpExpr` it reads the
constant's value out of a valuation `cval`, and the environment
invariant (`EnvTT.defn_eq`) records that a definition's valuation is
the denotation of its body.  A delta step in the checker is therefore
an *equation between denotations that already holds*, not a rule of the
type theory — which is the concrete sense in which the reduction
strategy drops out of the consistency argument.

(`Setlec/TT/DESIGN.md` §2.1 describes the denotation as unfolding
constants by well-founded recursion on the environment.  Carrying a
valuation instead is the same thing done the way the set model already
does it: the recursion on the environment becomes the *incremental
construction of the valuation* as declarations install, which is
exactly `EnvModel`'s existing induction and needs no new termination
argument.  Task #119 follows the set model here, by direction.)

## `let` denotes to its zeta reduct

`interpExpr`'s `letE` clause interprets the body opened at the value's
interpretation, i.e. the zeta reduct; `denote` does the same, by
substituting `⟦value⟧` for the opened binder.  `VExpr.letE` and its
`HasType.letE` rule are therefore *not* used by this bridge — they
become relevant only when the checker stops zeta-expanding at
annotation time (task #117), and the two are interderivable through
`HasType.zeta` in any case.

## The projection gap (task #119, open)

`interpExpr` reads a `.proj` node with the *untyped* set operations
`sfst`/`ssnd`.  The type theory has no untyped projection: its
`psigmaFst`/`psigmaSnd` are constants applied to the pair's type
arguments `A` and `B`, and a `.proj` node does not carry them — the
checker recovers them at *use* time, by whnf-ing the subject's inferred
type (`Setlec/Kernel/Core.lean`, the `.proj` clause of `annotateBody`).
A denotation that is a function of the expression alone therefore
cannot emit them, and a *relational* denotation is not an option
either: the defeq claim of the fuel induction needs both sides denoted
by the *same* function, or the two existentials do not meet.

So `denote` is `none` on `.proj`, and the bridge covers exactly the
stored terms with no first-class projection node.  This is not a
coverage decision, it is an open obligation; see the module's `TODO`
below and the report for task #119.  The fix is one clause here plus a
projection former in `Setlec/TT/Syntax.lean` (interpreted by
`sfst`/`ssnd`, exactly as this file's table would then read), which is
the same shape the set model already has.
-/

set_option linter.unusedVariables false

namespace Setlec.TTVerify

open Setlec.TT

/-- A valuation of the environment's constants by *terms* of the
declarative type theory — level-polymorphically, each constant being a
function of the level-parameter assignment.  The exact transpose of
`Setlec.ConstVal V = Name → (Name → Nat) → V`. -/
abbrev TConstVal := Name → (Name → Nat) → VExpr

/-- The term of a `Nat` literal: the `Nat.succ` valuation iterated on
the `Nat.zero` valuation.  Transpose of `natLitVal`.

Note that this is *unary and never evaluated*: nothing in the bridge
computes it, and the literal fast paths are discharged by lemma
families proved by meta-level induction on the literal (task #119, the
`Nat` interface), never by exhibiting a derivation of the size of the
numeral. -/
def natLitT (zv sv : VExpr) : Nat → VExpr
  | 0 => zv
  | n + 1 => .app sv (natLitT zv sv n)

/-- The character-list part of a string literal's constructor form.
Transpose of `charListVal`. -/
def charListT (nilV consV ofNatV zv sv : VExpr) : List Char → VExpr
  | [] => nilV
  | c :: cs =>
    .app (.app consV (.app ofNatV (natLitT zv sv c.toNat)))
      (charListT nilV consV ofNatV zv sv cs)

/-- The stored level-parameter list of a constant (`[]` when absent).
Transpose of `Setlec.Env.levelParamsAt`; restated here because
`Setlec/TTVerify/*` does not import the set model. -/
def levelParamsAt (env : Env) (n : Name) : List Name :=
  match env.find? n with
  | some ci => ci.toConstantVal.levelParams
  | none => []

/-- The term of a `String` literal: the denotation of its constructor
form (`strLitToConstructor`), written out — each constant valued
exactly as the `.const` clause values it on that form.  Transpose of
`strLitVal`. -/
def strLitT (cval : TConstVal) (env : Env) (φ : Name → Nat) (s : String) :
    VExpr :=
  .app (cval stringOfListName (Level.substFn φ [] []))
    (charListT
      (.app (cval listNilName
          (Level.substFn φ (levelParamsAt env listNilName) [.zero]))
        (cval charName (Level.substFn φ [] [])))
      (.app (cval listConsName
          (Level.substFn φ (levelParamsAt env listConsName) [.zero]))
        (cval charName (Level.substFn φ [] [])))
      (cval charOfNatName (Level.substFn φ [] []))
      (cval natZeroName (Level.substFn φ [] []))
      (cval natSuccName (Level.substFn φ [] []))
      s.toList)

/-- Denote an expression under constant valuation `cval`, level
assignment `φ` and binder depth `d`.  Clause for clause the transpose
of `Setlec.interpExpr`; see the module docstring, in particular for the
absent free-variable valuation, for `letE`, and for the open `.proj`
obligation. -/
def denote (cval : TConstVal) (env : Env) (φ : Name → Nat) :
    (d : Nat) → Expr → Option VExpr
  | _, .sort u => some (.sort (u.eval φ))
  | d, .fvar idx _ _ => some (.bvar (d - 1 - idx))
  | _, .const n us =>
    match env.find? n with
    | some ci =>
      if us.length = ci.toConstantVal.levelParams.length then
        some (cval n (Level.substFn φ ci.toConstantVal.levelParams us))
      else none
    | none => none
  | d, .forallE n ty body m =>
    match denote cval env φ d ty with
    | none => none
    | some A =>
      match denote cval env φ (d + 1) (body.instantiate1 (.fvar d n ty)) with
      | none => none
      | some B => some (.pi A B)
  | d, .lam n ty body m =>
    match denote cval env φ d ty with
    | none => none
    | some A =>
      match denote cval env φ (d + 1) (body.instantiate1 (.fvar d n ty)) with
      | none => none
      | some b => some (.lam A b)
  | d, .app f a =>
    match denote cval env φ d f, denote cval env φ d a with
    | some vf, some va => some (.app vf va)
    | _, _ => none
  | d, .letE n ty val body =>
    -- a `let` is its body at the value: open the binder at index `d`
    -- (exactly as the binder clauses do) and substitute the value's
    -- denotation for it, which is the zeta reduct `body[val]`
    match denote cval env φ d val with
    | none => none
    | some xv =>
      match denote cval env φ (d + 1) (body.instantiate1 (.fvar d n ty)) with
      | none => none
      | some b => some (b.inst xv)
  | d, .proj _ i e =>
    -- TODO (task #119): the pair's type arguments are not on the node.
    -- Needs a projection former in `Setlec/TT/Syntax.lean`, interpreted
    -- by `sfst`/`ssnd` exactly as the set model reads this clause; see
    -- "The projection gap" above.
    none
  | _, .lit (.natVal n) =>
    -- guarded exactly like the checker's literal paths
    if natLitSupported env then
      some (natLitT (cval natZeroName (Level.substFn φ [] []))
        (cval natSuccName (Level.substFn φ [] [])) n)
    else none
  | _, .lit (.strVal s) =>
    if strLitSupported env then some (strLitT cval env φ s) else none
  | _, _ => none
termination_by _ e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-- Denotation of a closed expression (as they appear in declarations).
Transpose of `interpClosed`. -/
def denoteClosed (cval : TConstVal) (env : Env) (φ : Name → Nat)
    (e : Expr) : Option VExpr :=
  denote cval env φ 0 e

/-! ## Clause equations

`denote` is defined by well-founded recursion on `Expr.sizeB` (like
`interpExpr`), so its clauses are not definitional; these are the
rewrite rules every consumer uses. -/

@[simp] theorem denote_sort (cval : TConstVal) (env : Env) (φ : Name → Nat)
    (d : Nat) (u : Level) :
    denote cval env φ d (.sort u) = some (.sort (u.eval φ)) := by
  rw [denote]

@[simp] theorem denote_fvar (cval : TConstVal) (env : Env) (φ : Name → Nat)
    (d idx : Nat) (n : Name) (ty : Expr) :
    denote cval env φ d (.fvar idx n ty) = some (.bvar (d - 1 - idx)) := by
  rw [denote]

theorem denote_const (cval : TConstVal) (env : Env) (φ : Name → Nat)
    (d : Nat) (n : Name) (us : List Level) :
    denote cval env φ d (.const n us) =
      match env.find? n with
      | some ci =>
        if us.length = ci.toConstantVal.levelParams.length then
          some (cval n (Level.substFn φ ci.toConstantVal.levelParams us))
        else none
      | none => none := by
  rw [denote]

theorem denote_app (cval : TConstVal) (env : Env) (φ : Name → Nat)
    (d : Nat) (f a : Expr) :
    denote cval env φ d (.app f a) =
      match denote cval env φ d f, denote cval env φ d a with
      | some vf, some va => some (.app vf va)
      | _, _ => none := by
  rw [denote]

theorem denote_forallE (cval : TConstVal) (env : Env) (φ : Name → Nat)
    (d : Nat) (n : Name) (ty body : Expr) (m : BinderMeta) :
    denote cval env φ d (.forallE n ty body m) =
      match denote cval env φ d ty with
      | none => none
      | some A =>
        match denote cval env φ (d + 1) (body.instantiate1 (.fvar d n ty)) with
        | none => none
        | some B => some (.pi A B) := by
  rw [denote]

theorem denote_lam (cval : TConstVal) (env : Env) (φ : Name → Nat)
    (d : Nat) (n : Name) (ty body : Expr) (m : BinderMeta) :
    denote cval env φ d (.lam n ty body m) =
      match denote cval env φ d ty with
      | none => none
      | some A =>
        match denote cval env φ (d + 1) (body.instantiate1 (.fvar d n ty)) with
        | none => none
        | some b => some (.lam A b) := by
  rw [denote]

theorem denote_letE (cval : TConstVal) (env : Env) (φ : Name → Nat)
    (d : Nat) (n : Name) (ty val body : Expr) :
    denote cval env φ d (.letE n ty val body) =
      match denote cval env φ d val with
      | none => none
      | some xv =>
        match denote cval env φ (d + 1) (body.instantiate1 (.fvar d n ty)) with
        | none => none
        | some b => some (b.inst xv) := by
  rw [denote]

@[simp] theorem denote_proj (cval : TConstVal) (env : Env) (φ : Name → Nat)
    (d : Nat) (T : Name) (i : Nat) (e : Expr) :
    denote cval env φ d (.proj T i e) = none := by
  rw [denote]

@[simp] theorem denote_bvar (cval : TConstVal) (env : Env) (φ : Name → Nat)
    (d i : Nat) : denote cval env φ d (.bvar i) = none := by
  rw [denote] <;> simp

theorem denote_natLit (cval : TConstVal) (env : Env) (φ : Name → Nat)
    (d n : Nat) :
    denote cval env φ d (.lit (.natVal n)) =
      (if natLitSupported env then
        some (natLitT (cval natZeroName (Level.substFn φ [] []))
          (cval natSuccName (Level.substFn φ [] [])) n)
      else none) := by
  rw [denote]

theorem denote_strLit (cval : TConstVal) (env : Env) (φ : Name → Nat)
    (d : Nat) (s : String) :
    denote cval env φ d (.lit (.strVal s)) =
      (if strLitSupported env then some (strLitT cval env φ s) else none) := by
  rw [denote]

end Setlec.TTVerify

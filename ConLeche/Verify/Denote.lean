import ConLeche.Kernel.Checker
import ConLeche.Verify.Level
import ConLeche.Verify.EnvWF
import ConLeche.VExpr.Const

/-!
# Denotation of kernel expressions into the erased term language

`denote cval env φ d e` maps a kernel `Expr` to a `ConLeche.VExpr.VExpr`.

**Provenance note (task #209).**  This function was written as the
front half of a *declarative* verification lane: a typing judgment
`HasType` over `VExpr` with a model above it.  That lane is gone
(tasks #148, #190, #209) and `denote` survives as the semantics
tier's reading of a stored term.  The design rationale below names
rules of the deleted judgment where that is what decided a clause's
shape; those names no longer resolve to anything in the tree, and are
kept because the *reasons* still bind — see DESIGN.md's task #209
section.
It is **the structural transpose of `ConLeche/Model/Interp.lean`'s
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
| `sfst ve`/`ssnd ve` | `.proj i ⟦e⟧` (the former, task #119) |
| `natLitVal zv sv n` | `natLitT ⟦zero⟧ ⟦succ⟧ n` |
| `letE` ↦ its zeta reduct | `.letE ⟦ty⟧ ⟦val⟧ ⟦body⟧` (**structural**) |

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
Bruijn context `Δ`).

## Delta is `rfl`, because `denote` never delta-reduces either

`denote` does *not* unfold a constant: like `interpExpr` it reads the
constant's value out of a valuation `cval`, and the environment
invariant (`EnvTT.defn_eq`) records that a definition's valuation is
the denotation of its body.  A delta step in the checker is therefore
an *equation between denotations that already holds*, not a rule of the
type theory — which is the concrete sense in which the reduction
strategy drops out of the consistency argument.

(An early design described the denotation as unfolding
constants by well-founded recursion on the environment.  Carrying a
valuation instead is the same thing done the way the set model already
does it: the recursion on the environment becomes the *incremental
construction of the valuation* as declarations install, which is
exactly `EnvModel`'s existing induction and needs no new termination
argument.  Task #119 follows the set model here, by direction.)

## Why `denote` is structural, including at `let`

**Every clause maps a constructor to a constructor.**  That is not
cosmetic, and the `letE` clause is where it was decided.  The principle
to preserve, if any clause is ever tempted to compute:

> **A structural `denote` is what keeps the bridge's substitution
> metatheory small.**

The accounting the retired lane's record did: four lemmas, where
a computing `denote` needs lifting to commute with instantiation and
with itself, and four becomes six and keeps going.

`interpExpr`'s `letE` clause interprets the *zeta reduct* — the body
opened at the value's interpretation — and the obvious transpose was to
substitute `⟦value⟧` into the denoted body, i.e. emit `b.inst xv`.
That was the original choice here and it is **withdrawn**: a `denote`
that performs a substitution forces the bridge's own metatheory to
prove that lifting commutes with instantiation, and then that lifting
commutes with lifting, and the swamp `ConLeche/VExpr/Subst.lean` is proud
of avoiding (lean4lean's 123 syntactic lemmas) reappears one layer
down.  The shift lemma (`ConLeche/Verify/Denote/Shift.lean`) is where this
showed up concretely: with `b.inst xv` its `letE` case needs two
commutation lemmas; with `.letE A xv b` it is structural and needs
none.

So a `let` denotes to `VExpr.letE`, and a consumer that wants the
reduct gets it from a premise-free zeta equation.  The cost is one
rule application at the zeta clause of `whnfCore`; the saving is that
the reading keeps the property the term language advertises — its
substitution metatheory stays small.

(The clause also denotes the type annotation, which `interpExpr` does
not read.  A substituting `letE` rule needs it, and stored terms carry no `letE`
today — the checker zeta-expands at annotation time — so nothing is
lost until task #117 lands, at which point the checker's own `letE`
rule supplies exactly this premise.)

## Projections, and why the layer grew a former for them

`interpExpr` reads a `.proj` node with the *untyped* set operations
`sfst`/`ssnd`.  The layer originally had no untyped projection: its
`psigmaFst`/`psigmaSnd` were constants applied to the pair's type
arguments `A` and `B`, which a `.proj` node does not carry — the
checker recovers them at *use* time, by whnf-ing the subject's inferred
type (`ConLeche/Kernel/Core.lean`, the `.proj` clause of `annotateBody`).
A denotation that is a function of the expression alone cannot emit
them, and a *relational* denotation is not an option either: the defeq
claim of the fuel induction needs both sides denoted by the *same*
function, or the two existentials do not meet.

So the term language gained `VExpr.proj` (task #119;
`ConLeche/VExpr/Syntax.lean`), a former carrying exactly what the
checker's node carries, whose typing read `A` and `B` off the
premise.  This clause is then the plain transpose of `interpExpr`'s,
`i < 2` guard included, and the alphabet came out *smaller*:
`psigmaFst` and `psigmaSnd` are derivable from the former and left
`BConst`.
-/

set_option linter.unusedVariables false

namespace ConLeche.Verify

open ConLeche.VExpr

/-- A valuation of the environment's constants by *terms* of the
declarative type theory — level-polymorphically, each constant being a
function of the level-parameter assignment.  The exact transpose of
`ConLeche.ConstVal V = Name → (Name → Nat) → V`. -/
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
Transpose of `ConLeche.Env.levelParamsAt`; restated here because
`ConLeche/TTVerify/*` does not import the set model. -/
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

/-- The tower projection's `VExpr` spelling (task #175 wiring W3):
`.proj 0 ∘ (.proj 1)^i` — the erase image of the P reading's `projAV`
(`SetBase/TowerLeaf.lean`), interpreting to `projS i` on the tuple
tier's carriers.  Depends only on the index. -/
def projNV : Nat → VExpr → VExpr
  | 0, e => .proj 0 e
  | i + 1, e => projNV i (.proj 1 e)

/-- Denote an expression under constant valuation `cval`, level
assignment `φ` and binder depth `d`.  Clause for clause the transpose
of `ConLeche.interpExpr`; see the module docstring, in particular for the
absent free-variable valuation, for `letE`, and for the open `.proj`
obligation. -/
def denote (cval : TConstVal) (env : Env) (φ : Name → Nat) :
    (d : Nat) → Expr → Option VExpr
  | _, .sort u => some (.sort (u.eval φ))
  | d, .fvar idx _ => some (.bvar (d - 1 - idx))
  | _, .const n us =>
    match env.find? n with
    | some ci =>
      if us.length = ci.toConstantVal.levelParams.length then
        some (cval n (Level.substFn φ ci.toConstantVal.levelParams us))
      else none
    | none => none
  | d, .forallE ty body m =>
    match denote cval env φ d ty with
    | none => none
    | some A =>
      match denote cval env φ (d + 1) (body.instantiate1 (.fvar d ty)) with
      | none => none
      | some B => some (.pi A B)
  | d, .lam ty body m =>
    match denote cval env φ d ty with
    | none => none
    | some A =>
      match denote cval env φ (d + 1) (body.instantiate1 (.fvar d ty)) with
      | none => none
      | some b => some (.lam A b)
  | d, .app f a =>
    match denote cval env φ d f, denote cval env φ d a with
    | some vf, some va => some (.app vf va)
    | _, _ => none
  | d, .letE ty val body =>
    -- structural: a `let` denotes to the layer's own `letE`, *not* to
    -- its zeta reduct.  See "Why `denote` is structural" above.
    match denote cval env φ d ty, denote cval env φ d val with
    | some A, some xv =>
      match denote cval env φ (d + 1) (body.instantiate1 (.fvar d ty)) with
      | none => none
      | some b => some (.letE A xv b)
    | _, _ => none
  | d, .proj sn i e =>
    -- the transpose of `interpExpr`'s clause, `i < 2` guard included
    -- on the pair side; a tower-backed entry (task #175 wiring W3)
    -- reads field `i` by the uniform iterated spelling instead — the
    -- entry key consumed at the reading, never carried in the syntax
    match denote cval env φ d e with
    | none => none
    | some ve =>
      match env.findProj? sn i with
      | some _ => some (projNV i ve)
      | none => if i < 2 then some (.proj i ve) else none
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
    (d idx : Nat) (ty : Expr) :
    denote cval env φ d (.fvar idx ty) = some (.bvar (d - 1 - idx)) := by
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
    (d : Nat) (ty body : Expr) (m : BinderMeta) :
    denote cval env φ d (.forallE ty body m) =
      match denote cval env φ d ty with
      | none => none
      | some A =>
        match denote cval env φ (d + 1) (body.instantiate1 (.fvar d ty)) with
        | none => none
        | some B => some (.pi A B) := by
  rw [denote]

theorem denote_lam (cval : TConstVal) (env : Env) (φ : Name → Nat)
    (d : Nat) (ty body : Expr) (m : BinderMeta) :
    denote cval env φ d (.lam ty body m) =
      match denote cval env φ d ty with
      | none => none
      | some A =>
        match denote cval env φ (d + 1) (body.instantiate1 (.fvar d ty)) with
        | none => none
        | some b => some (.lam A b) := by
  rw [denote]

theorem denote_letE (cval : TConstVal) (env : Env) (φ : Name → Nat)
    (d : Nat) (ty val body : Expr) :
    denote cval env φ d (.letE ty val body) =
      match denote cval env φ d ty, denote cval env φ d val with
      | some A, some xv =>
        match denote cval env φ (d + 1) (body.instantiate1 (.fvar d ty)) with
        | none => none
        | some b => some (.letE A xv b)
      | _, _ => none := by
  rw [denote]

theorem denote_proj (cval : TConstVal) (env : Env) (φ : Name → Nat)
    (d : Nat) (T : Name) (i : Nat) (e : Expr) :
    denote cval env φ d (.proj T i e) =
      match denote cval env φ d e with
      | none => none
      | some ve =>
        match env.findProj? T i with
        | some _ => some (projNV i ve)
        | none => if i < 2 then some (.proj i ve) else none := by
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

end ConLeche.Verify

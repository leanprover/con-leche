module

import ConLeche.Kernel.Env
import ConLeche.Kernel.ExprOps
import ConLeche.Kernel.Basis
public import ConLeche.Kernel.StdAxioms
import ConLeche.Kernel.Core

@[expose] public section

/-!
# Reading lean4export ndjson files: the shared scaffolding

The lean4export NDJSON format (version 3.x, see `format_ndjson.md` in
the lean4export repository) is a sequence of JSON objects: an initial
`meta` object, then name/level/expression table entries (keys
`in`/`il`/`ie` give the table index) interleaved with declarations.
Index 0 of the name table is `Name.anonymous`, index 0 of the level
table is `Level.zero`; both are implicit.  Indices need not be dense or
in order (hand-crafted arena tests have gaps), so the tables are maps;
entries are resolved eagerly when inserted, so a later re-binding of an
index cannot retroactively change anything built earlier.

**This file is the representation-free half** — the pieces the parse
proper is written against and would otherwise duplicate:

* `canonLevel`/`canonExpr`/`ConstantInfo.canon`, the level-parameter
  canonicalization the basis and prelude matching compare up to;
* `FrontendError`, the taint sentinel and the error monad `M`;
* `taintSummary`, the driver's decline message.

The stream's **grammar** is not here: since task #256 the dialect has
one recogniser, `ConLeche/Frontend/Scan/{Types,Fast}.lean` (the syntax
records and the byte scanner), and the `Lean.Json` DOM this file used
to read records out of is gone from the checking path.

**The parse proper is `ConLeche/Frontend/ExportC.lean`** (task #171): it
reads the stream *directly* to `ExprC` — no arena, no conversion
detour.  Until task #172 this file also held a second parse into an
interned arena (`State`, `parseExport`, `parseExportStream`,
producing `DeclP` over a `WFStore`); that went with the interned
representation.

Declaration kinds the checker cannot represent yet map to
`FrontendError.unsupported`, which the driver turns into the arena's
"declined" exit code — as opposed to malformed input, which is a hard
error.
-/

namespace ConLeche.Frontend

/-- Rename level parameters (for basis-block matching up to
level-parameter names). -/
def canonLevel (m : Name → Name) : Level → Level
  | .zero => .zero
  | .succ u => .succ (canonLevel m u)
  | .max u v => .max (canonLevel m u) (canonLevel m v)
  | .imax u v => .imax (canonLevel m u) (canonLevel m v)
  | .param n => .param (m n)

/-- Erase binder names *and binder annotations* and rename level
parameters: the alpha/renaming canonical form used to match a parsed
inductive block against a pinned basis block (Lean's exports use
auto-bound universe names and hygienic binder names, both semantically
irrelevant).

Task #142, pin-side normalization: the parser already maps every
stream binder to `.default`, and both sides of every
`ConstantInfo.canon` comparison go through here, so erasing the
annotation here is what kept the two sides consistent while the pinned
literals still carried the real `BinderInfo`s of their `Init.Prelude`
signatures.  Since task #203 the pin builder
(`ConLeche/Kernel/Basis/Builder.lean`) emits `.anonymous` at `.default`
and the parser emits `.anonymous` too, so the name/annotation erasure
here is the identity on both sides; what this canonical form still
*does* is rename level parameters and reset `pw` (the pin side is
annotated, the stream side is at the parse placeholder). -/
def canonExpr (m : Name → Name) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar idx ty => .fvar idx (canonExpr m ty)
  | .sort u => .sort (canonLevel m u)
  | .const n us => .const n (us.map (canonLevel m))
  | .app f a => .app (canonExpr m f) (canonExpr m a)
  | .lam ty b _ => .lam (canonExpr m ty) (canonExpr m b) ⟨.never⟩
  | .forallE ty b _ =>
      .forallE (canonExpr m ty) (canonExpr m b) ⟨.never⟩
  | .letE ty v b => .letE (canonExpr m ty) (canonExpr m v)
      (canonExpr m b)
  | .lit l => .lit l
  | .proj s i e => .proj s i (canonExpr m e)

/-- The level-parameter renaming a constant's own parameter list
induces: the `i`-th parameter becomes `⟨i⟩`, anything else is left
alone. -/
def canonNameMap (ps : List Name) : Name → Name := fun n =>
  match ps.findIdx? (fun p => p == n) with
  | some i => .num .anonymous i
  | none => n

/-- Canonical form of a constant's common data (name kept, level
parameters numbered, type renamed). -/
def ConstantVal.canon (cv : ConstantVal) : ConstantVal :=
  { cv with
    levelParams := (List.range cv.levelParams.length).map (.num .anonymous ·),
    type := canonExpr (canonNameMap cv.levelParams) cv.type }

/-- Canonical form of a stored constant for basis matching. -/
def ConstantInfo.canon (ci : ConstantInfo) : ConstantInfo :=
  let ps := ci.toConstantVal.levelParams
  let m : Name → Name := canonNameMap ps
  let cv : ConstantVal := ConstantVal.canon ci.toConstantVal
  match ci with
  | .axiomInfo _ => .axiomInfo cv
  | .defnInfo _ v hint => .defnInfo cv (canonExpr m v) hint
  | .thmInfo _ v => .thmInfo cv (canonExpr m v)
  | .indInfo _ _ => .indInfo cv {}
  | .ctorInfo _ nP nF => .ctorInfo cv nP nF
  | .recInfo _ mI rP rules => .recInfo cv mI rP
      (rules.map fun r => { r with rhs := canonExpr m r.rhs })
  -- table entries never occur in parsed input; identity keeps the
  -- match total
  | .projInfo e => .projInfo e

/-! ### Comparing canonical forms in lockstep (task #226)

Three places ask "is this parsed record the same declaration as that
pinned one, up to level-parameter names?" — the `Quot.sound` axiom and
the quotient records against the `quot` basis pin, a block against one
of the five basis pins, and any record under a built-in prelude name
against the prelude's copy (`ExportC.lean`, `DeclC.sameCanon`).  Each
used to build `ConstantInfo.canon` of BOTH sides and compare the
results.  That is `O(tree)` on the stream side, because `canonExpr`
rebuilds every node: `tests/e2e/tower_axiom.ndjson`,
`tower_quot.ndjson` and `tower_prelude.ndjson` — a depth-60 shared
tower (`2^60` nodes unshared) under `Quot.sound`, under `Quot` and
under `Bool` — exhaust memory on it.

The `canonEq*` functions below are the SPECIFICATIONS, spelled exactly
that way; the `*Fast` twins beside them descend both terms **together**
and stop at the first disagreement, and are swapped in by `@[csimp]`.
Wherever the two sides agree they have the pin's shape, so the walk is
bounded by the PIN's tree size — a few dozen nodes — however large the
stream side; where they disagree it stops there.  Same verdict on
every input; only the work changes.

The **name pre-filter of task #215 stays in front** of the block
comparison: `canon` renames only level parameters, so a block can match
a pin only when its members' names are the pin's, member for member,
and that test is a handful of `Name` comparisons. -/

/-- Lockstep twin of `canonExpr m a == canonExpr m' b`
(`canonExprEqFast_iff`). -/
def canonExprEqFast (m m' : Name → Name) : Expr → Expr → Bool
  | .bvar i, .bvar j => i == j
  | .fvar i t, .fvar j t' => i == j && canonExprEqFast m m' t t'
  | .sort u, .sort v => canonLevel m u == canonLevel m' v
  | .const n us, .const n' us' =>
      n == n' && us.map (canonLevel m) == us'.map (canonLevel m')
  | .app f a, .app f' a' =>
      canonExprEqFast m m' f f' && canonExprEqFast m m' a a'
  | .lam t b _, .lam t' b' _ =>
      canonExprEqFast m m' t t' && canonExprEqFast m m' b b'
  | .forallE t b _, .forallE t' b' _ =>
      canonExprEqFast m m' t t' && canonExprEqFast m m' b b'
  | .letE t v b, .letE t' v' b' =>
      canonExprEqFast m m' t t' && canonExprEqFast m m' v v' &&
        canonExprEqFast m m' b b'
  | .lit l, .lit l' => l == l'
  | .proj s i e, .proj s' i' e' =>
      s == s' && i == i' && canonExprEqFast m m' e e'
  | _, _ => false

/-- **The agreement for expressions.**  `canonExpr` preserves every
node's constructor (it rewrites only levels, and resets the binder
metadata to the same constant on both sides), so the two canonical
forms are equal iff the originals agree constructor by constructor
down to their leaves — which is what the descent tests. -/
theorem canonExprEqFast_iff (m m' : Name → Name) :
    ∀ a b : Expr, canonExprEqFast m m' a b = true ↔ canonExpr m a = canonExpr m' b := by
  intro a
  induction a with
  | bvar i => intro b; cases b <;> simp [canonExprEqFast, canonExpr]
  | fvar i t ih =>
    intro b; cases b <;> simp [canonExprEqFast, canonExpr, Bool.and_eq_true, ih]
  | sort u => intro b; cases b <;> simp [canonExprEqFast, canonExpr]
  | const n us => intro b; cases b <;> simp [canonExprEqFast, canonExpr]
  | app f a ihf iha =>
    intro b; cases b <;>
      simp [canonExprEqFast, canonExpr, Bool.and_eq_true, ihf, iha]
  | lam t b m iht ihb =>
    intro c; cases c <;>
      simp [canonExprEqFast, canonExpr, Bool.and_eq_true, iht, ihb]
  | forallE t b m iht ihb =>
    intro c; cases c <;>
      simp [canonExprEqFast, canonExpr, Bool.and_eq_true, iht, ihb]
  | letE t v b iht ihv ihb =>
    intro c; cases c <;>
      simp [canonExprEqFast, canonExpr, Bool.and_eq_true, iht, ihv, ihb, and_assoc]
  | lit l => intro b; cases b <;> simp [canonExprEqFast, canonExpr]
  | proj s i e ih =>
    intro b; cases b <;>
      simp [canonExprEqFast, canonExpr, Bool.and_eq_true, ih, and_assoc]

/-- The common data of a canonical form is the canonical form of the
common data: `ConstantInfo.canon` rebuilds `toConstantVal` the same
way in every arm but the table one, which is the identity (a table
never occurs in parsed input).  The quotient records — parsed
`axiomInfo`s, pinned `indInfo`/`ctorInfo`/`recInfo`/`axiomInfo`s — are
compared at this projection. -/
theorem ConstantInfo.canon_toConstantVal :
    ∀ {ci : ConstantInfo}, (∀ t, ci ≠ .projInfo t) →
      (ConstantInfo.canon ci).toConstantVal = ConstantVal.canon ci.toConstantVal := by
  intro ci h
  cases ci <;> first | rfl | exact absurd rfl (h _)

/-- A `Bool` identity from the `= true` equivalence. -/
private theorem boolEq_of_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

/-- Two constants have the same canonical common data.  (`decide (· =
·)` is what `==` unfolds to at these `DecidableEq` types, so this is
the comparison the call sites used to spell inline.) -/
def ConstantVal.canonEq (cv cv' : ConstantVal) : Bool :=
  decide (ConstantVal.canon cv = ConstantVal.canon cv')

/-- `ConstantVal.canonEq` in lockstep.  The numbered level-parameter
lists are equal exactly when they are equally long. -/
def ConstantVal.canonEqFast (cv cv' : ConstantVal) : Bool :=
  cv.name == cv'.name && cv.levelParams.length == cv'.levelParams.length &&
    canonExprEqFast (canonNameMap cv.levelParams) (canonNameMap cv'.levelParams)
      cv.type cv'.type

theorem ConstantVal.canonEqFast_iff (cv cv' : ConstantVal) :
    ConstantVal.canonEqFast cv cv' = true ↔
      ConstantVal.canon cv = ConstantVal.canon cv' := by
  simp only [ConstantVal.canonEqFast, ConstantVal.canon, Bool.and_eq_true,
    beq_iff_eq, canonExprEqFast_iff, ConstantVal.mk.injEq, and_assoc]
  constructor
  · rintro ⟨hn, hl, ht⟩; exact ⟨hn, by rw [hl], ht⟩
  · rintro ⟨hn, hl, ht⟩
    exact ⟨hn, by simpa using congrArg List.length hl, ht⟩

@[csimp] theorem ConstantVal.canonEq_eq_canonEqFast :
    @ConstantVal.canonEq = @ConstantVal.canonEqFast := by
  funext cv cv'
  exact boolEq_of_iff (by
    simp only [ConstantVal.canonEq, decide_eq_true_eq, ConstantVal.canonEqFast_iff])

/-- Rule lists compared through the canonical form of each rule's
right-hand side (`ConstantInfo.canon`'s recursor arm). -/
def canonRulesEqFast (m m' : Name → Name) : List RecRule → List RecRule → Bool
  | [], [] => true
  | r :: rs, r' :: rs' =>
      ({ r with rhs := .bvar 0 } == { r' with rhs := .bvar 0 }) &&
        canonExprEqFast m m' r.rhs r'.rhs && canonRulesEqFast m m' rs rs'
  | _, _ => false

theorem canonRulesEqFast_iff (m m' : Name → Name) :
    ∀ rs rs' : List RecRule,
      canonRulesEqFast m m' rs rs' = true ↔
        rs.map (fun r => { r with rhs := canonExpr m r.rhs }) =
          rs'.map (fun r => { r with rhs := canonExpr m' r.rhs }) := by
  intro rs
  induction rs with
  | nil => intro rs'; cases rs' <;> simp [canonRulesEqFast]
  | cons r rs ih =>
    intro rs'; cases rs' with
    | nil => simp [canonRulesEqFast]
    | cons r' rs' =>
      cases r; cases r'
      simp only [canonRulesEqFast, Bool.and_eq_true, ih, List.map_cons,
        List.cons.injEq, beq_iff_eq, RecRule.mk.injEq, canonExprEqFast_iff]
      constructor <;> (intro h; simp_all)

/-- Two stored constants have the same canonical form. -/
def ConstantInfo.canonEq (ci ci' : ConstantInfo) : Bool :=
  decide (ConstantInfo.canon ci = ConstantInfo.canon ci')

/-- `ConstantInfo.canonEq` in lockstep. -/
def ConstantInfo.canonEqFast : ConstantInfo → ConstantInfo → Bool
  | .axiomInfo cv, .axiomInfo cv' => ConstantVal.canonEqFast cv cv'
  | .defnInfo cv v h, .defnInfo cv' v' h' =>
      ConstantVal.canonEqFast cv cv' &&
        canonExprEqFast (canonNameMap cv.levelParams)
          (canonNameMap cv'.levelParams) v v' && h == h'
  | .thmInfo cv v, .thmInfo cv' v' =>
      ConstantVal.canonEqFast cv cv' &&
        canonExprEqFast (canonNameMap cv.levelParams)
          (canonNameMap cv'.levelParams) v v'
  | .indInfo cv _, .indInfo cv' _ => ConstantVal.canonEqFast cv cv'
  | .ctorInfo cv nP nF, .ctorInfo cv' nP' nF' =>
      ConstantVal.canonEqFast cv cv' && nP == nP' && nF == nF'
  | .recInfo cv mI rP rules, .recInfo cv' mI' rP' rules' =>
      ConstantVal.canonEqFast cv cv' && mI == mI' && rP == rP' &&
        canonRulesEqFast (canonNameMap cv.levelParams)
          (canonNameMap cv'.levelParams) rules rules'
  | .projInfo t, .projInfo t' => t == t'
  | _, _ => false

theorem ConstantInfo.canonEqFast_iff (ci ci' : ConstantInfo) :
    ConstantInfo.canonEqFast ci ci' = true ↔
      ConstantInfo.canon ci = ConstantInfo.canon ci' := by
  cases ci <;> cases ci' <;>
    simp [ConstantInfo.canonEqFast, ConstantInfo.canon, ConstantInfo.toConstantVal,
      Bool.and_eq_true, ConstantVal.canonEqFast_iff, canonExprEqFast_iff,
      canonRulesEqFast_iff, and_assoc]

@[csimp] theorem ConstantInfo.canonEq_eq_canonEqFast :
    @ConstantInfo.canonEq = @ConstantInfo.canonEqFast := by
  funext ci ci'
  exact boolEq_of_iff (by
    simp only [ConstantInfo.canonEq, decide_eq_true_eq, ConstantInfo.canonEqFast_iff])

/-- Two blocks are the same, member for member, up to the canonical
form. -/
def canonEqList (xs ys : List ConstantInfo) : Bool :=
  decide (xs.map ConstantInfo.canon = ys.map ConstantInfo.canon)

/-- `canonEqList` in lockstep. -/
def canonEqListFast : List ConstantInfo → List ConstantInfo → Bool
  | [], [] => true
  | x :: xs, y :: ys => ConstantInfo.canonEqFast x y && canonEqListFast xs ys
  | _, _ => false

theorem canonEqListFast_iff :
    ∀ xs ys : List ConstantInfo,
      canonEqListFast xs ys = true ↔
        xs.map ConstantInfo.canon = ys.map ConstantInfo.canon := by
  intro xs
  induction xs with
  | nil => intro ys; cases ys <;> simp [canonEqListFast]
  | cons x xs ih =>
    intro ys; cases ys with
    | nil => simp [canonEqListFast]
    | cons y ys =>
      simp [canonEqListFast, Bool.and_eq_true, ConstantInfo.canonEqFast_iff, ih]

@[csimp] theorem canonEqList_eq_canonEqListFast :
    @canonEqList = @canonEqListFast := by
  funext xs ys
  exact boolEq_of_iff (by
    simp only [canonEqList, decide_eq_true_eq, canonEqListFast_iff])

inductive FrontendError where
  | parseError (line : Nat) (msg : String)
  | unsupported (what : String)

/-- Internal sentinel: a declaration-level expression lookup hit a
tainted entry.  Backstop only — `processLine`'s read-only pre-scan
(`declRecordScan`) skips tainted declarations before any parsing, so
this should be unreachable; if it fires anyway it is converted to a
decline at the record level (the pre-change behavior). -/
def taintSentinel : String := "\x00uses-skipped-axiom"

/-! ### The tree-size budget, retired at task #215

The frontend used to cap a declaration's *unshared tree size*
(`declTreeSizeBudget = 2^25`, `CON_LECHE_TREE_BUDGET`, `sizeSentinel`,
`budgetedName`, the per-entry `sizes` counter).  It existed because
four record kinds were read by **unmemoized** tree walks, and a
heavily DAG-shared declaration would have unfolded them into billions
of nodes — Mathlib's `ModularCurve.JZeroGoodReductionSpecialization_alt`
is a 5 038-entry DAG whose recursor rule is 38 795 167 nodes unshared,
and it is the record that hit the cap in practice.

Task #215 removed the reasons instead of the declarations:

* the **basis-pin match** selects its candidate by *name* first
  (`ExportC.lean`), so `canonExpr` runs only on a block whose members
  are named exactly as one of the five pins';
* `Expr.renameConsts` and the `Expr.instantiate1` inside
  `openPisAtFvars` are **memoized DAG walks**, swapped in by
  `@[csimp]` in `ConLeche/Kernel/ExprOps.lean` — kernel-checked
  against the pure definitions, so no proof and no trust point moved.

What replaces the cap is a **gate, not a limit**: the adversarial
DAG-tower fixtures in `tests/e2e` put a shared tower of depth 60
(about `2^60` nodes unshared, 60 entries as a DAG) into every record
kind the frontend reads.  An unmemoized walk over one of them never
finishes, so the fixture fails and names the walker — which is what a
regression should do, rather than telling a user with a legitimate
declaration "no".  User ruling, 2026-09-07: *"delete it if it is
unlikely to help (and we know such DAGs appear in practice)."* -/

abbrev M := Except String

/-- The taint skips WITHOUT the total: per-root counts and the first
few skipped names.  Used where the caller already states the count
(the declined verdict line). -/
def taintDetail (skips : Array (Name × Name)) : String :=
  let perRoot := toleratedAxiomNames.filterMap fun r =>
    match skips.foldl (fun c p => if p.2 == r then c + 1 else c) 0 with
    | 0 => none
    | c => some s!"{c} via {r}"
  let names := (skips.toList.take 8).map (fun p => s!"{p.1}")
  let more := if skips.size > 8 then ", …" else ""
  s!"{String.intercalate "; " perRoot}; first skipped: {String.intercalate ", " names}{more}"

/-- Diagnostic summary of the taint skips: total, per-root counts, and
the first few skipped names. -/
def taintSummary (skips : Array (Name × Name)) : String :=
  s!"skipped {skips.size} declarations that use a tolerated axiom ({taintDetail skips})"

end ConLeche.Frontend

module

public import ConLeche.Kernel.Env

@[expose] public section

/-!
# The level-parameter canonical form the pinned blocks are matched up to

A stream's `Nat` block and the checker's pinned one are the same
declaration when they agree up to the names Lean's exporter picks
freely: binder names, binder infos and level-parameter names (the
first two never reach an `Expr`; this form renames the third).
This module is that canonical form and the lockstep comparisons built
on it.

It sits in the KERNEL because the matching does (task #293): the
decoder emits the file's records and nothing else, and it is
`checkDecl` that recognises a block as one of the five pinned basis
blocks, and a `#QUOT` record (or the `Quot.sound` axiom record) as the
pinned quotient package's.  Until then this lived in
`ConLeche/Frontend/Export.lean`, beside the parser that did the
matching.
-/

namespace ConLeche

/-- Rename level parameters (for basis-block matching up to
level-parameter names). -/
def canonLevel (m : Name → Name) : Level → Level
  | .zero => .zero
  | .succ u => .succ (canonLevel m u)
  | .max u v => .max (canonLevel m u) (canonLevel m v)
  | .imax u v => .imax (canonLevel m u) (canonLevel m v)
  | .param n => .param (m n)

/-- Rename level parameters throughout a term: the canonical form used
to match a parsed inductive block against a pinned basis block up to
level-parameter names (Lean's exports use auto-bound universe names,
which are semantically irrelevant).  Binder names and binder infos
need no erasing: `Expr` has no slot for either (the parser drops them,
tasks #142 and #203). -/
def canonExpr (m : Name → Name) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar idx ty => .fvar idx (canonExpr m ty)
  | .sort u => .sort (canonLevel m u)
  | .const n us => .const n (us.map (canonLevel m))
  | .app f a => .app (canonExpr m f) (canonExpr m a)
  | .lam ty b => .lam (canonExpr m ty) (canonExpr m b)
  | .forallE ty b =>
      .forallE (canonExpr m ty) (canonExpr m b)
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
  | .thmInfo _ => .thmInfo cv
  | .indInfo _ _ => .indInfo cv {}
  | .ctorInfo _ nP nF => .ctorInfo cv nP nF
  | .recInfo _ mI rP isK rules => .recInfo cv mI rP
      isK (rules.map fun r => { r with rhs := canonExpr m r.rhs })

/-! ### Comparing canonical forms in lockstep (task #226)

Two places ask "is this record the same declaration as that pinned
one, up to level-parameter names?" — the `Quot.sound` axiom record and
the four quotient records against the `quot` basis pin, and a block
against one of the five basis pins.  Both are `checkDecl`'s since task
#293 (`pinCopyOk`, `quotPinHit`, `ConLeche/Kernel/Basis.lean`); a
third, the built-in prelude's dedupe, went with that task.  Each used
to build `ConstantInfo.canon` of BOTH sides and compare the results.
That is `O(tree)` on the stream side, because `canonExpr` rebuilds
every node: `tests/e2e/tower_axiom.ndjson` and `tower_quot.ndjson` — a
depth-60 shared tower (`2^60` nodes unshared) under `Quot.sound` and
under `Quot` — exhaust memory on it.

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
  | .lam t b, .lam t' b' =>
      canonExprEqFast m m' t t' && canonExprEqFast m m' b b'
  | .forallE t b, .forallE t' b' =>
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
  | lam t b iht ihb =>
    intro c; cases c <;>
      simp [canonExprEqFast, canonExpr, Bool.and_eq_true, iht, ihb]
  | forallE t b iht ihb =>
    intro c; cases c <;>
      simp [canonExprEqFast, canonExpr, Bool.and_eq_true, iht, ihb]
  | letE t v b iht ihv ihb =>
    intro c; cases c <;>
      simp [canonExprEqFast, canonExpr, Bool.and_eq_true, iht, ihv, ihb, and_assoc]
  | lit l => intro b; cases b <;> simp [canonExprEqFast, canonExpr]
  | proj s i e ih =>
    intro b; cases b <;>
      simp [canonExprEqFast, canonExpr, Bool.and_eq_true, ih, and_assoc]

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
  | .thmInfo cv, .thmInfo cv' => ConstantVal.canonEqFast cv cv'
  | .indInfo cv _, .indInfo cv' _ => ConstantVal.canonEqFast cv cv'
  | .ctorInfo cv nP nF, .ctorInfo cv' nP' nF' =>
      ConstantVal.canonEqFast cv cv' && nP == nP' && nF == nF'
  | .recInfo cv mI rP isK rules, .recInfo cv' mI' rP' isK' rules' =>
      ConstantVal.canonEqFast cv cv' && mI == mI' && rP == rP' && isK == isK' &&
        canonRulesEqFast (canonNameMap cv.levelParams)
          (canonNameMap cv'.levelParams) rules rules'
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

/-! ## Pointer-first equality of what an install pushes -/

/-- Element-wise comparison of two lists by `f`. -/
def listBeqBy {α : Type} (f : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && listBeqBy f as bs
  | _, _ => false

theorem eq_of_listBeqBy {α : Type} {f : α → α → Bool} (hf : ∀ a b, f a b = true → a = b) :
    ∀ {l l' : List α}, listBeqBy f l l' = true → l = l'
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [listBeqBy, Bool.and_eq_true] at h
    rw [hf a b h.1, eq_of_listBeqBy hf h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [listBeqBy] at h

/-- `ConstantVal` equality, the type by `Expr`'s pointer-first `==`. -/
def ConstantVal.beqP (a b : ConstantVal) : Bool :=
  a.name == b.name && a.levelParams == b.levelParams && a.type == b.type

theorem ConstantVal.eq_of_beqP {a b : ConstantVal} (h : a.beqP b = true) : a = b := by
  obtain ⟨n, l, t⟩ := a
  obtain ⟨n', l', t'⟩ := b
  simp only [ConstantVal.beqP, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  rfl

/-- `RecRuleFire` equality, the pins by `Expr`'s `==`. -/
def RecRuleFire.beqP : RecRuleFire → RecRuleFire → Bool
  | .plain, .plain => true
  | .nested l p, .nested l' p' => l == l' && p == p'
  | _, _ => false

theorem RecRuleFire.eq_of_beqP {a b : RecRuleFire} (h : a.beqP b = true) : a = b := by
  cases a <;> cases b <;> simp_all [RecRuleFire.beqP]

/-- `RecRule` equality, the right-hand side by `Expr`'s `==`. -/
def RecRule.beqP (a b : RecRule) : Bool :=
  a.ctor == b.ctor && a.nfields == b.nfields && a.fire.beqP b.fire && a.rhs == b.rhs

theorem RecRule.eq_of_beqP {a b : RecRule} (h : a.beqP b = true) : a = b := by
  obtain ⟨c, n, f, r⟩ := a
  obtain ⟨c', n', f', r'⟩ := b
  simp only [RecRule.beqP, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨rfl, rfl⟩, hf⟩, rfl⟩ := h
  rw [RecRuleFire.eq_of_beqP hf]

/-- **`ConstantInfo` equality, pointer-first**: every `Expr` by its
memoised `==` (`Expr.beqMemo`), the rest by its decidable equality. -/
def ConstantInfo.beqP : ConstantInfo → ConstantInfo → Bool
  | .axiomInfo v, .axiomInfo v' => v.beqP v'
  | .defnInfo v e h, .defnInfo v' e' h' => v.beqP v' && e == e' && decide (h = h')
  | .thmInfo v, .thmInfo v' => v.beqP v'
  | .indInfo v c, .indInfo v' c' => v.beqP v' && decide (c = c')
  | .ctorInfo v a b, .ctorInfo v' a' b' => v.beqP v' && a == a' && b == b'
  | .recInfo v a b isK rs, .recInfo v' a' b' isK' rs' =>
    v.beqP v' && a == a' && b == b' && isK == isK' && listBeqBy RecRule.beqP rs rs'
  | _, _ => false

theorem ConstantInfo.eq_of_beqP {a b : ConstantInfo} (h : a.beqP b = true) : a = b := by
  cases a <;> cases b <;> simp only [ConstantInfo.beqP, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, reduceCtorEq] at h
  · rw [ConstantVal.eq_of_beqP h]
  · obtain ⟨⟨hv, rfl⟩, rfl⟩ := h; rw [ConstantVal.eq_of_beqP hv]
  · rw [ConstantVal.eq_of_beqP h]
  · obtain ⟨hv, rfl⟩ := h; rw [ConstantVal.eq_of_beqP hv]
  · obtain ⟨⟨hv, rfl⟩, rfl⟩ := h; rw [ConstantVal.eq_of_beqP hv]
  · obtain ⟨⟨⟨⟨hv, rfl⟩, rfl⟩, rfl⟩, hr⟩ := h
    rw [ConstantVal.eq_of_beqP hv, eq_of_listBeqBy (fun _ _ => RecRule.eq_of_beqP) hr]

/-- **`ProjTable` equality, pointer-first**: the bodies by `Expr`'s
`==`, the rest by value. -/
def ProjTable.beqP (a b : ProjTable) : Bool :=
  a.structName == b.structName && a.levelParams == b.levelParams &&
    a.numParams == b.numParams && a.ctor == b.ctor && a.numFields == b.numFields &&
    a.structSort == b.structSort && a.bodies == b.bodies

theorem ProjTable.eq_of_beqP {a b : ProjTable} (h : a.beqP b = true) : a = b := by
  obtain ⟨_, _, _, _, _, _, _⟩ := a
  obtain ⟨_, _, _, _, _, _, _⟩ := b
  simp only [ProjTable.beqP, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h
  rfl

end ConLeche

module

public import ConLeche.Cached.CheckerC

@[expose] public section

/-!
# The stored install of an inductive block (task #431)

The parallel install pushes an inductive block **as the input stores
it**: every constant the checked install pushes is read syntactically
off the block's records (`storedInstall`), and nothing is generated or
inferred — no positivity walk, no recursor generation, no field sort.
The block's checked install runs later, as a job of the check phase
(`BlockCheck`, `ConLeche/Verify/Cached/Defer.lean`), and compares what
it pushes with what this install pushed, pointer-first
(`ConstantInfo.beqP`, `ProjTable.beqP`); a difference is an internal
error naming the block (exit 3: this reading is wrong, the stream is
not).  So this file is unverified: nothing about the reading is proved,
the job's comparison is what the fold's step is taken from.

What is read, and from where (the checked install's own functions on
the same inputs wherever one exists):
* the formers: each stored constant at its stored type, with
  `blockCapsAt` at official's `is_rec` (`blockRawRec`) and the result
  sort read off member 0's syntactic telescope.  A former whose stored
  type is not a syntactic telescope ending in a sort (a def-headed
  former, #195) is not read: `storedReadable` is `false` and the block
  is installed checked, inline;
* the constructors as declared (`consSumCtorsF`'s records);
* the recursors: each record at its stored type, its stored right-hand
  sides, its rules' metadata by `tgtStoredRules` at the record's major —
  a member's (the member's parameter count and constructors) or an
  outside container's (`targetCtorsOf`, the firing data read off the
  stored major domain opened at the recursor's prefix, as the
  generator's class reading opens it);
* the projection tables: the bodies by substitution
  (`structProjBodiesC`), the guards **lazily** (`ProjTable.guards`): a
  thunk that infers the fields' sorts, from a fresh memo, at the
  formers' environment, as the checked install's constructor stage
  does (`checkStructFieldSortsIFA`).  Only a `Prop`-declared
  structure's `.proj` uses and the job's comparison force it.
-/

namespace ConLeche

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
  a.ctor == b.ctor && a.nfields == b.nfields && a.ctorParams == b.ctorParams &&
    a.fire.beqP b.fire && a.rhs == b.rhs && a.k == b.k && a.eta == b.eta

theorem RecRule.eq_of_beqP {a b : RecRule} (h : a.beqP b = true) : a = b := by
  obtain ⟨c, n, p, f, r, k, e⟩ := a
  obtain ⟨c', n', p', f', r', k', e'⟩ := b
  simp only [RecRule.beqP, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, hf⟩, rfl⟩, rfl⟩, rfl⟩ := h
  rw [RecRuleFire.eq_of_beqP hf]

/-- **`ConstantInfo` equality, pointer-first**: every `Expr` by its
memoised `==` (`Expr.beqMemo`), the rest by its decidable equality. -/
def ConstantInfo.beqP : ConstantInfo → ConstantInfo → Bool
  | .axiomInfo v, .axiomInfo v' => v.beqP v'
  | .defnInfo v e h, .defnInfo v' e' h' => v.beqP v' && e == e' && decide (h = h')
  | .thmInfo v, .thmInfo v' => v.beqP v'
  | .indInfo v c, .indInfo v' c' => v.beqP v' && decide (c = c')
  | .ctorInfo v a b, .ctorInfo v' a' b' => v.beqP v' && a == a' && b == b'
  | .recInfo v a b rs, .recInfo v' a' b' rs' =>
    v.beqP v' && a == a' && b == b' && listBeqBy RecRule.beqP rs rs'
  | _, _ => false

theorem ConstantInfo.eq_of_beqP {a b : ConstantInfo} (h : a.beqP b = true) : a = b := by
  cases a <;> cases b <;> simp only [ConstantInfo.beqP, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, reduceCtorEq] at h
  · rw [ConstantVal.eq_of_beqP h]
  · obtain ⟨⟨hv, rfl⟩, rfl⟩ := h; rw [ConstantVal.eq_of_beqP hv]
  · rw [ConstantVal.eq_of_beqP h]
  · obtain ⟨hv, rfl⟩ := h; rw [ConstantVal.eq_of_beqP hv]
  · obtain ⟨⟨hv, rfl⟩, rfl⟩ := h; rw [ConstantVal.eq_of_beqP hv]
  · obtain ⟨⟨⟨hv, rfl⟩, rfl⟩, hr⟩ := h
    rw [ConstantVal.eq_of_beqP hv, eq_of_listBeqBy (fun _ _ => RecRule.eq_of_beqP) hr]

/-- **`ProjTable` equality, pointer-first**: the bodies by `Expr`'s
`==`, the guards by value (forcing both thunks). -/
def ProjTable.beqP (a b : ProjTable) : Bool :=
  a.structName == b.structName && a.levelParams == b.levelParams &&
    a.numParams == b.numParams && a.ctor == b.ctor && a.numFields == b.numFields &&
    a.structSort == b.structSort && a.bodies == b.bodies && a.guards.get == b.guards.get

theorem ProjTable.eq_of_beqP {a b : ProjTable} (h : a.beqP b = true) : a = b := by
  obtain ⟨_, _, _, _, _, _, _, g⟩ := a
  obtain ⟨_, _, _, _, _, _, _, g'⟩ := b
  simp only [ProjTable.beqP, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, hg⟩ := h
  rw [Thunk.ext hg]

end ConLeche

namespace ConLeche.Cached

open ConLeche

/-! ## The reading -/

variable (mode : CheckMode)

/-- Member 0's result sort and every member's stored type a syntactic
telescope ending in a sort at its parameter and index count. -/
def storedSorts (p : BlockParts) : Option Level :=
  let ss := p.members.map fun ms =>
    match ms.cvT.type.stripPis (p.nP + ms.nIdx) with
    | some (_, .sort s) => some s
    | _ => none
  if ss.all (·.isSome) then ss.head?.join else none

/-- **The blocks the stored install reads**: a recognised block that is
no pinned basis block, at its declared parameter count, every former
at a syntactic telescope.  Any other block (a basis block, a shapeless
one, a def-headed former) is installed checked, inline. -/
def storedReadable (block : List ConstantInfo) (nP : Nat) : Bool :=
  (basisPinHit block).isNone && indParamsOk nP block &&
    match blockParts? nP block with
    | some p => (storedSorts p).isSome
    | none => false

/-- A recursor record's major, as `tgtStoredRules` reads it: a member
(its parameter count and constructors), or an outside container at the
levels and parameters of the stored major domain opened at the
recursor's prefix. -/
def storedMajor (fe : FEnv) (p : BlockShape) (rc : RecShape) : Option TargetMajor :=
  if h : rc.tgt < p.k then
    let ms := p.members[rc.tgt]'(by simpa [BlockShape.k] using h)
    some { ind := ms.cvT.name, lvls := [], ds := [], nPc := p.nP, nIdx := ms.nIdx,
           ctors := ms.ctors, member := some rc.tgt }
  else do
    let (_, body) ← openPisAtFvars rc.mI rc.cvR.type 0
    let .forallE dom _ := body | none
    let .const I us := dom.getAppFn | none
    let (nPc, ctors) ← targetCtorsOf fe I
    some { ind := I, lvls := us, ds := dom.getAppArgs.take nPc, nPc := nPc, nIdx := 0,
           ctors := ctors, member := none }

/-- The recursors' records, in the block's order. -/
def storedRecs (fe₂ : FEnv) (p : BlockShape) : Nat → List RecShape → Option (List ConstantInfo)
  | _, [] => some []
  | r, rc :: rest => do
    let M ← storedMajor fe₂ p rc
    let rs ← storedRecs fe₂ p (r + 1) rest
    some (.recInfo rc.cvR (p.majorIdxAt r) (p.rulePrefixAt r)
      (tgtStoredRules fe₂.find? rc.cvR (p.rulePrefixAt r) M (rc.rules.map (·.rhs))) :: rs)

/-- **A structure's guard levels, inferred on first use**: the fields'
sorts at the formers' environment `fe₁`, from a fresh memo, by the
constructor stage's own walk; `[]` where the walk fails (the block's
checked install then fails at the same walk, and the job reports it). -/
def storedGuards (fe₁ : FEnv) (p : BlockShape) (c : ConstantVal × Nat) : List Level :=
  let run : CheckCM (List Level) := do
    flushC
    let cq ← unwrapOr (openPisAtFvarsF p.nP c.1.type 0) (.internal "stored guards")
    let xq ← unwrapOr (openPisAtFvarsF c.2 cq.2 p.nP) (.internal "stored guards")
    checkStructFieldSortsIFA (sharedOpsC mode fe₁) fe₁ p.isProp p.large p.resSort p.nP
      xq.1.toArray (xq.2.getAppArgs.drop p.nP) c.2
  match run {} with
  | .ok (sorts, _) => structProjGuards c.1.type p.nP c.2 sorts
  | .error _ => []

/-- The projection tables, member by member in block order, at every
structure-like member (one constructor, no index). -/
def storedTables (fe₁ : FEnv) (p : BlockShape) : List MemberShape → Option (List ProjTable)
  | [] => some []
  | ms :: rest => do
    let rs ← storedTables fe₁ p rest
    match ms.ctors with
    | [c] =>
      if ms.nIdx == 0 then
        let bodies ← structProjBodiesC ms.cvT.name p.nP c.2 c.1.type
        some (⟨ms.cvT.name, p.lps, p.nP, c.1.name, c.2, p.resSort, bodies,
          Thunk.mk fun _ => storedGuards mode fe₁ p c⟩ :: rs)
      else some rs
    | _ => some rs

/-- **The stored install of a block** at the view `W`: the constants it
pushes (formers, constructors, recursors, in the checked install's push
order) and its tables (in install order); `none` where the reading
fails. -/
def storedInstall (W : FEnv) (block : List ConstantInfo) (nP : Nat) :
    Option (List ConstantInfo × List ProjTable) := do
  let p₀ ← blockParts? nP block
  let s0 ← storedSorts p₀
  let p := p₀.toBlockShape.withSort s0
  let isRec := blockRawRec p₀
  let formers := (p.members.zipIdx).map fun (ms, i) =>
    ConstantInfo.indInfo ms.cvT (blockCapsAt p i isRec)
  let ctors := p.members.flatMap fun ms => ms.ctors.map fun c => ConstantInfo.ctorInfo c.1 p.nP c.2
  let fe₁ := FEnv.pushAll formers W
  let fe₂ := FEnv.pushAll ctors fe₁
  let recs ← storedRecs fe₂ p 0 p.recs
  let tbls ← storedTables mode fe₁ p p.members
  some (formers ++ ctors ++ recs, tbls)

end ConLeche.Cached

module

public import ConLeche.Cached.CheckerC

@[expose] public section

/-!
# The stored install of an inductive block (task #431)

The install phase pushes an inductive block **as the input stores
it**: every constant the checked install pushes is read off the block's
records (`storedInstall`), and nothing is generated — no positivity
walk, no recursor generation; the one inference is the structures'
field sorts (their projection tables' guards), the one reduction a
def-headed former's telescope.  The block's checked install runs
later, as a job of the check phase
(`DeferredCheck`, `ConLeche/Verify/Cached/Defer.lean`), and compares what
it pushes with what this install pushed, pointer-first
(`ConstantInfo.beqP`, `ProjTable.beqP`); a difference is an internal
error naming the block (exit 3: this reading is wrong, the stream is
not).  So this file is unverified: nothing about the reading is proved,
the job's comparison is what the fold's step is taken from.

Every inductive block is installed this way (task #431 cont. 5): a
block matching a basis pin as the pin's constants, a block the
recogniser does not read as nothing, every other block by the reading
below.  What is read, and from where (the checked install's own
functions on the same inputs wherever one exists):
* the formers: each at its telescope, with `blockCapsAt` at official's
  `is_rec` (`blockRawRec`) and member 0's result sort.  The telescope is
  the stored type where that is a syntactic telescope ending in a sort,
  else (a def-headed former, #195) the reduced telescope official's
  `whnf` loop reads, as the checked install computes it (`storedTele`) —
  the binders the stored recursor shows; the sort is on no record;
* the constructors as declared (`consSumCtorsF`'s records);
* the recursors: each record at its stored type, its stored right-hand
  sides, its rules' metadata by `tgtStoredRules` at the record's major —
  a member's (the member's parameter count and constructors) or an
  outside container's (`targetCtorsOf`, the firing data read off the
  stored major domain opened at the recursor's prefix, as the
  generator's class reading opens it);
* the projection tables: the bodies by substitution
  (`structProjBodiesC`), the guards (`ProjTable.guards`, the fields'
  sorts) inferred here, at install, from a fresh memo at the formers'
  environment, by the checked install's constructor-stage walk
  (`checkStructFieldSortsIFA`, `storedGuards`) — the one inference of
  this install besides a def-headed former's telescope.  The table,
  guards included, is a value in the environment's table map like the
  checked install's; no part of it is deferred.

Where a part cannot be read, it is pushed at its record as declared
(a former, a recursor's rules) or left out (a table): the block is one
the checked install rejects, and its job reports it; the pushes keep the
slots the prediction made for the block filled.
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
`==`, the rest by value. -/
def ProjTable.beqP (a b : ProjTable) : Bool :=
  a.structName == b.structName && a.levelParams == b.levelParams &&
    a.numParams == b.numParams && a.ctor == b.ctor && a.numFields == b.numFields &&
    a.structSort == b.structSort && a.bodies == b.bodies && a.guards == b.guards

theorem ProjTable.eq_of_beqP {a b : ProjTable} (h : a.beqP b = true) : a = b := by
  obtain ⟨_, _, _, _, _, _, _, g⟩ := a
  obtain ⟨_, _, _, _, _, _, _, g'⟩ := b
  simp only [ProjTable.beqP, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h
  rfl

end ConLeche

namespace ConLeche.Cached

open ConLeche

/-! ## The reading -/

variable (mode : CheckMode)

/-- **A former's telescope, as the checked install computes it** (task
#195's `checkSumTeleF`, without its checks): the stored type where it
is a syntactic telescope of `n` binders ending in a sort; else the
telescope official's `whnf` loop reads (`whnfTelescope` at the view,
from a fresh memo), closed — the reduced form the stored recursor's
binders show.  `none` where the loop does not reach a sort (the checked
install rejects the block there). -/
def storedTele (W : FEnv) (cv : ConstantVal) (n : Nat) : Option (ConstantVal × Level) :=
  match cv.type.stripPis n with
  | some (_, .sort s) => some (cv, s)
  | _ =>
    let run : CheckCM (List Expr × Level) := do
      flushC
      whnfTelescope (sharedOpsC mode W) W.env 0 n cv.type
    match run {} with
    | .ok ((bs, s), _) => some ({ cv with type := closeTelescope bs 0 (.sort s) }, s)
    | .error _ => none

/-- The members' formers at their telescopes (`storedTele`), each at its
record as declared where its telescope cannot be read, and member 0's
result sort (the recogniser's placeholder where it cannot be read). -/
def storedFormers (W : FEnv) (p : BlockParts) : List ConstantVal × Level :=
  let ts := p.members.map fun ms => (ms.cvT, storedTele mode W ms.cvT (p.nP + ms.nIdx))
  (ts.map fun (cv, t?) => (t?.map (·.1)).getD cv,
    match ts.head? with
    | some (_, some (_, s)) => s
    | _ => p.resSort)

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

/-- The recursors' records, in the block's order; a recursor whose major
cannot be read keeps its rules as declared (the checked install rejects
the block there). -/
def storedRecs (fe₂ : FEnv) (p : BlockShape) : Nat → List RecShape → List ConstantInfo
  | _, [] => []
  | r, rc :: rest =>
    let rules := match storedMajor fe₂ p rc with
      | some M => tgtStoredRules fe₂.find? rc.cvR (p.rulePrefixAt r) M (rc.rules.map (·.rhs))
      | none => rc.rules
    .recInfo rc.cvR (p.majorIdxAt r) (p.rulePrefixAt r) rules :: storedRecs fe₂ p (r + 1) rest

/-- **A structure's guard levels**: the fields'
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
structure-like member (one constructor, no index); none where the
bodies cannot be built (the checked install rejects the block there). -/
def storedTables (fe₁ : FEnv) (p : BlockShape) : List MemberShape → List ProjTable
  | [] => []
  | ms :: rest =>
    let rs := storedTables fe₁ p rest
    match ms.ctors with
    | [c] =>
      if ms.nIdx == 0 then
        match structProjBodiesC ms.cvT.name p.nP c.2 c.1.type with
        | some bodies =>
          ⟨ms.cvT.name, p.lps, p.nP, c.1.name, c.2, p.resSort, bodies,
            storedGuards mode fe₁ p c⟩ :: rs
        | none => rs
      else rs
    | _ => rs

/-- **The stored install of a block** at the view `W`: the constants it
pushes (formers, constructors, recursors, in the checked install's push
order) and its tables (in install order).  Total: a block matching a
basis pin pushes the pin's constants, a block the recogniser does not
read pushes nothing (the checked install's pushes and the prediction's
skeleton, `declCSkels`, in both cases), and every other block its
reading, each part at its record as declared where the reading fails —
the blocks the checked install rejects, which its job reports. -/
def storedInstall (W : FEnv) (block : List ConstantInfo) (nP : Nat) :
    List ConstantInfo × List ProjTable :=
  match basisPinHit block with
  | some kind => (kind.declsA, [])
  | none =>
    match blockParts? nP block with
    | none => ([], [])
    | some p₀ =>
      let (cvTs, s0) := storedFormers mode W p₀
      let p := p₀.toBlockShape.withSort s0
      let isRec := blockRawRec p₀
      let formers := (cvTs.zipIdx).map fun (cv, i) => ConstantInfo.indInfo cv (blockCapsAt p i isRec)
      let ctors := p.members.flatMap fun ms =>
        ms.ctors.map fun c => ConstantInfo.ctorInfo c.1 p.nP c.2
      let fe₁ := FEnv.pushAll formers W
      let fe₂ := FEnv.pushAll ctors fe₁
      (formers ++ ctors ++ storedRecs fe₂ p 0 p.recs, storedTables mode fe₁ p p.members)

end ConLeche.Cached

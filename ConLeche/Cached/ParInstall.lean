module

public import ConLeche.Cached.Installed
import ConLeche.Cached.KnotCongr
/- `withPtrEq` is `public` but not `@[expose]`; the slot check below is
*defined* through it and `slotIs_spec` needs its body (`k ()`), which
`import all` makes visible in this module only (the `Init.Util`
exception CLAUDE.md lists). -/
import all Init.Util

/-!
# The parallel install's commit step (task #329)

Phase A (`annotDeclStep`, `ConLeche/Cached/Installed.lean`) installs
every record from a fresh memo state, so a record's install is a
function of the index it sees and the record alone.  The parallel
install runs that function on worker threads, each at a **worker view**
instead of the serial index, and an in-order commit thread pushes the
results into the serial index while it extends the serial fold's
accepting run (`InstallRun`) one record at a time — the run the driver
returns is the serial fold's whatever the schedule.

* **The worker view** (`workerView B S v`) is an `FEnv` with an empty
  index and the frozen base layer `B` (`FBase`,
  `ConLeche/Kernel/FEnv.lean`) visible below the counter `v`: the
  predicted name of every slot of the stream, each answering from the
  task of the record that installs it.  It is built once, before the
  workers start, from the names the records will install.
* **The invariant** (`ViewAgrees B S fe`): the view at the serial index's
  counter answers every lookup as the serial index does.  It holds at
  the empty index (`ViewAgrees.empty`), and a commit keeps it when the
  slot it fills is the one `B` predicted for that counter and the
  slot's task delivers the very constant pushed (`ViewAgrees.push`,
  checked by `slotIs`, a pointer comparison at run time).
* **The commit step of a value record** (`valueStep_commit`): a
  definition's, theorem's or opaque's install at the view, by the
  congruence of the cached core in `find?` (`coreKnotI_congr`,
  `ConLeche/Cached/KnotCongr.lean`), IS the serial step's: same
  constant, same pending check.  A failing record fails with the serial
  step's error (`valueStep_commit_error`).  Every other record — a
  block, an axiom, a basis block, a pinned declaration — pushes a list
  of constants, each checked against its slot (`ViewAgrees.pushAll`);
  that its install at the view is the serial step is
  `installStep_commit` (`ConLeche/Cached/ViewCongr.lean`).

Nothing here mentions a schedule, a thread or a promise: the lemmas
are about values, and what a task delivers is a value (`Task.get` is
logically a projection).  The driver is `Main.lean`'s.

**Why proofs sit in the implementation tier.**  The driver carries the
serial fold's accepting run and needs these lemmas to extend it; the
file is self-contained (the cached checker and `KnotCongr`, nothing
from the theory) — the exception CLAUDE.md makes for a self-contained
verification living with the implementation.  It opens one
`@[expose] public section` like the rest of the tier: the driver runs
its definitions.
-/

@[expose] public section

namespace ConLeche.Cached

open ConLeche

variable {mode : CheckMode}

/-! ## The install halves read the index only through `find?` -/

/-- `annotConstantValC` reads its index through `find?` alone (the
duplicate guard, the knot, `constsResolveFC`). -/
theorem annotConstantValC_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) :
    annotConstantValC mode fe₁ = annotConstantValC mode fe₂ := by
  funext cv
  unfold annotConstantValC
  simp only [coreKnotI_congr hfe, constsResolveFC_congr hfe, hfe]

/-- `annotValC` reads its index through `find?` alone (the knot and
`constsResolveFC`), so it is congruent in the index: phase B's
annotation of a theorem's value at the prefix view is the annotation
at the environment the view names. -/
theorem annotValC_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) :
    annotValC mode fe₁ = annotValC mode fe₂ := by
  funext cvA value
  unfold annotValC
  simp only [coreKnotI_congr hfe, constsResolveFC_congr hfe]

/-- Phase A's value install reads its index through `find?` alone. -/
theorem annotValueC_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) :
    annotValueC mode fe₁ = annotValueC mode fe₂ := by
  funext cv value
  unfold annotValueC
  simp only [annotConstantValC_congr hfe, annotValC_congr hfe]

/-! ## The index below its counter -/

/-- Every index entry was installed below the counter: what the serial
index satisfies by construction (it is only ever pushed onto), and what
makes a push's lookup the old lookup but for the pushed name. -/
def IdxBelow (fe : FEnv) : Prop :=
  fe.ovl = [] ∧
    ∀ (n : Name) (c : Nat) (ci : ConstantInfo), fe.idx[n]? = some (c, ci) → c < fe.visibleBelow

theorem IdxBelow.mkFEnv_empty : IdxBelow (mkFEnv Env.empty) := by
  unfold IdxBelow
  refine ⟨rfl, ?_⟩
  intro n c ci h
  simp [mkFEnv, mkFEnvGo, Env.empty] at h

theorem IdxBelow.push {fe : FEnv} (h : IdxBelow fe) (ci : ConstantInfo) :
    IdxBelow (fe.push ci) := by
  unfold IdxBelow at h ⊢
  refine ⟨h.1, ?_⟩
  intro n c ci' hl
  simp only [FEnv.push, Std.HashMap.getElem?_insert] at hl ⊢
  split at hl
  · cases hl; omega
  · exact Nat.lt_succ_of_lt (h.2 n c ci' hl)

/-- **A push answers the pushed name and leaves every other lookup
alone** (below the counter nothing else changes). -/
theorem IdxBelow.find?_push {fe : FEnv} (h : IdxBelow fe) (ci : ConstantInfo) (n : Name) :
    (fe.push ci).find? n = if ci.name = n then some ci else fe.find? n := by
  unfold IdxBelow at h
  have hov : (fe.push ci).ovl = [] := h.1
  simp only [FEnv.find?, hov, h.1]
  simp only [FEnv.push, Std.HashMap.getElem?_insert, beq_iff_eq]
  by_cases hn : ci.name = n
  · simp [hn]
  · simp only [hn, ↓reduceIte]
    cases hl : fe.idx[n]? with
    | none => rfl
    | some p =>
      obtain ⟨c, ci'⟩ := p
      have hc := h.2 n c ci' hl
      simp only [Nat.lt_succ_of_lt hc, hc, ↓reduceIte]

/-! ## The base index, the worker view, and the invariant -/

/-- The base index of a parallel install: each predicted name with its
counter, the record that installs it, and its position among that
record's installed constants. -/
abbrev BaseIdx := Std.HashMap Name (Nat × Nat × Nat)

/-- The records' tasks: record `k`'s installed constants, `none` if the
task was dropped unresolved. -/
abbrev Slots := Array (Task (Option (Array ConstantInfo)))

/-- **The worker view at counter `v`**: no constants of its own, the
base visible below `v`.  A worker installs record `r` at
`workerView B S vis_r`, where `vis_r` is the counter the prediction
gives it. -/
def workerView (B : BaseIdx) (S : Slots) (v : Nat) : FEnv :=
  ⟨⟨[]⟩, {}, v, ⟨B, S, v⟩, []⟩

theorem workerView_find? (B : BaseIdx) (S : Slots) (v : Nat) (n : Name) :
    (workerView B S v).find? n = FBase.find? ⟨B, S, v⟩ n := by
  simp [workerView, FEnv.find?]

/-- No two names share a counter in the base: what the builder
guarantees (`buildBase_inj`), and what lets a commit fill exactly one
slot. -/
def BaseInj (B : BaseIdx) : Prop :=
  ∀ (n₁ n₂ : Name) (c : Nat) (x₁ x₂ : Nat × Nat),
    B[n₁]? = some (c, x₁) → B[n₂]? = some (c, x₂) → n₁ = n₂

/-- **The invariant of the commit thread**: the worker view at the
serial index's counter answers every lookup as the serial index does. -/
def ViewAgrees (B : BaseIdx) (S : Slots) (fe : FEnv) : Prop :=
  ∀ n, (workerView B S fe.visibleBelow).find? n = fe.find? n

/-- At the empty index nothing is visible on either side. -/
theorem ViewAgrees.empty (B : BaseIdx) (S : Slots) : ViewAgrees B S (mkFEnv Env.empty) := by
  unfold ViewAgrees
  intro n
  rw [workerView_find?]
  simp only [FBase.find?, mkFEnv, mkFEnvGo, Env.empty, FEnv.find?,
    Std.HashMap.getElem?_empty]
  split <;> simp

/-- The slot's constant: position `j` of record `k`'s task. -/
def slotGet (S : Slots) (k j : Nat) : Option ConstantInfo :=
  if h : k < S.size then
    match (S[k]).get with
    | some cs => cs[j]?
    | none => none
  else none

/-- **The slot check**: position `j` of record `k`'s task is `ci`.  At
run time a pointer comparison — the task delivers the very object the
record's install reports — and only on a mismatch the
structural comparison, which is what it means logically
(`slotIs_spec`). -/
def slotIs (S : Slots) (k j : Nat) (ci : ConstantInfo) : Bool :=
  match slotGet S k j with
  | some ci' => withPtrEq ci' ci (fun _ => decide (ci' = ci)) (fun h => by simp [h])
  | none => false

theorem slotIs_spec {S : Slots} {k j : Nat} {ci : ConstantInfo}
    (h : slotIs S k j ci = true) : slotGet S k j = some ci := by
  unfold slotIs at h
  split at h
  · rename_i ci' hget
    have h' : decide (ci' = ci) = true := h
    rw [hget, of_decide_eq_true h']
  · exact absurd h Bool.false_ne_true

/-- **A commit's slot check**: the base predicted `ci`'s name at the
counter `v`, and that slot's task delivers `ci`. -/
def slotOk (B : BaseIdx) (S : Slots) (v : Nat) (ci : ConstantInfo) : Bool :=
  match B[ci.name]? with
  | some (c, k, j) => c == v && slotIs S k j ci
  | none => false

theorem slotOk_spec {B : BaseIdx} {S : Slots} {v : Nat} {ci : ConstantInfo}
    (h : slotOk B S v ci = true) :
    ∃ k j, B[ci.name]? = some (v, k, j) ∧ slotGet S k j = some ci := by
  unfold slotOk at h
  split at h
  · rename_i c k j hB
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hs⟩ := h
    exact ⟨k, j, hB, slotIs_spec hs⟩
  · exact absurd h Bool.false_ne_true

theorem FBase.find?_eq (B : BaseIdx) (S : Slots) (v : Nat) (n : Name) :
    FBase.find? ⟨B, S, v⟩ n =
      match B[n]? with
      | some (c, k, j) => if c < v then slotGet S k j else none
      | none => none := by
  simp only [FBase.find?]
  cases B[n]? with
  | none => rfl
  | some p => obtain ⟨c, k, j⟩ := p; rfl

/-- **A checked commit keeps the invariant.** -/
theorem ViewAgrees.push {B : BaseIdx} {S : Slots} {fe : FEnv} (hB : BaseInj B)
    (hidx : IdxBelow fe) (h : ViewAgrees B S fe) {ci : ConstantInfo}
    (hok : slotOk B S fe.visibleBelow ci = true) :
    ViewAgrees B S (fe.push ci) := by
  obtain ⟨k, j, hslot, hget⟩ := slotOk_spec hok
  unfold ViewAgrees at h ⊢
  unfold BaseInj at hB
  intro n
  rw [hidx.find?_push, workerView_find?, FBase.find?_eq]
  have hv : (fe.push ci).visibleBelow = fe.visibleBelow + 1 := rfl
  rw [hv]
  by_cases hn : ci.name = n
  · subst hn
    simp [hslot, hget]
  · simp only [hn, ↓reduceIte]
    rw [← h n, workerView_find?, FBase.find?_eq]
    cases hl : B[n]? with
    | none => rfl
    | some p =>
      obtain ⟨c, k', j'⟩ := p
      have hc : c ≠ fe.visibleBelow := fun hc =>
        hn (hB _ _ _ _ _ hslot (hc ▸ hl))
      simp only
      by_cases hlt : c < fe.visibleBelow
      · simp [hlt, Nat.lt_succ_of_lt hlt]
      · have : ¬ c < fe.visibleBelow + 1 := by omega
        simp [hlt, this]

/-! ## A commit of several constants

A block, an axiom, a basis block or a pinned declaration pushes a list
of constants; each fills its predicted slot. -/

/-- The slot checks of a list of constants pushed from counter `v` on. -/
def slotsOk (B : BaseIdx) (S : Slots) : Nat → List ConstantInfo → Bool
  | _, [] => true
  | v, ci :: L => slotOk B S v ci && slotsOk B S (v + 1) L

theorem IdxBelow.pushAll {fe : FEnv} (h : IdxBelow fe) :
    ∀ L : List ConstantInfo, IdxBelow (FEnv.pushAll L fe)
  | [] => h
  | ci :: L => IdxBelow.pushAll (h.push ci) L

/-- **Checked commits of several constants keep the invariant.** -/
theorem ViewAgrees.pushAll {B : BaseIdx} {S : Slots} (hB : BaseInj B) :
    ∀ (L : List ConstantInfo) {fe : FEnv}, IdxBelow fe → ViewAgrees B S fe →
      slotsOk B S fe.visibleBelow L = true → ViewAgrees B S (FEnv.pushAll L fe)
  | [], _, _, h, _ => h
  | ci :: L, fe, hidx, h, hok => by
    simp only [slotsOk, Bool.and_eq_true] at hok
    exact ViewAgrees.pushAll hB L (hidx.push ci) (ViewAgrees.push hB hidx h hok.1) hok.2

/-! ## The base builder -/

/-- Insert the slots from `i` on, each name at its counter unless an
earlier slot already holds it (a duplicate name keeps its first slot;
the serial step rejects the duplicate, and the commit's slot check
fails before that).  A slot is `(name, record, position)`. -/
def buildBaseGo (slots : Array (Name × Nat × Nat)) : (i : Nat) → BaseIdx → BaseIdx
  | i, m =>
    if h : i < slots.size then
      let s := slots[i]
      buildBaseGo slots (i + 1) (m.insertIfNew s.1 (i, s.2))
    else m
  termination_by i => slots.size - i

/-- **The base index of the predicted slots**, in counter order. -/
def buildBase (slots : Array (Name × Nat × Nat)) : BaseIdx :=
  buildBaseGo slots 0 {}

/-- What the builder keeps: every entry names its own slot. -/
private def SlotsOf (slots : Array (Name × Nat × Nat)) (m : BaseIdx) : Prop :=
  ∀ (n : Name) (c : Nat) (x : Nat × Nat),
    m[n]? = some (c, x) → ∃ h : c < slots.size, slots[c].1 = n

private theorem buildBaseGo_slots (slots : Array (Name × Nat × Nat)) :
    ∀ (i : Nat) (m : BaseIdx), SlotsOf slots m → SlotsOf slots (buildBaseGo slots i m)
  | i, m, hm => by
    unfold buildBaseGo
    split
    · rename_i hi
      refine buildBaseGo_slots slots (i + 1) _ ?_
      unfold SlotsOf at hm ⊢
      intro n c x hl
      rw [Std.HashMap.getElem?_insertIfNew] at hl
      split at hl
      · rename_i hk
        cases hl
        obtain ⟨hk, -⟩ := hk
        exact ⟨hi, by simpa using hk⟩
      · exact hm n c x hl
    · exact hm
  termination_by i => slots.size - i

/-- **The builder's base is counter-injective.** -/
theorem buildBase_inj (slots : Array (Name × Nat × Nat)) : BaseInj (buildBase slots) := by
  have h := buildBaseGo_slots slots 0 {} (by unfold SlotsOf; intro n c x hl; simp at hl)
  unfold SlotsOf at h
  unfold BaseInj
  intro n₁ n₂ c x₁ x₂ h₁ h₂
  obtain ⟨hc, rfl⟩ := h n₁ c x₁ h₁
  obtain ⟨-, rfl⟩ := h n₂ c x₂ h₂
  rfl

/-! ## What a worker installs, and the commit step -/

/-- **A worker's install of a value record at the view `W`**: the
constant the serial step pushes and the pending check it records, or
its error; `none` for every other kind (they are installed at the
commit thread).  The memo state is dropped here — nothing of it
crosses to the commit. -/
def valueStep (mode : CheckMode) (W : FEnv) : Declaration →
    Option (Except CheckError (ConstantInfo × ValueGroup))
  | .defnDecl cv value hint =>
    if natOpNames.contains cv.name || natDivModNames.contains cv.name then none
    else some (match annotValueC mode W cv value {} with
      | .ok (r, _) => .ok (.defnInfo r.1 r.2.2 hint, ⟨.defn, r.1, r.2.2⟩)
      | .error e => .error e)
  | .thmDecl cv value =>
    some (match annotConstantValC mode W cv ({} : CState).flushed with
      | .ok (r, _) => .ok (.thmInfo r.1 value, ⟨.thm, r.1, value⟩)
      | .error e => .error e)
  | .opaqueDecl cv value =>
    if reduceOpNames.contains cv.name then none
    else some (match annotValueC mode W cv value {} with
      | .ok (r, _) => .ok (.axiomInfo r.1, ⟨.opaque, r.1, r.2.2⟩)
      | .error e => .error e)
  | _ => none

/-- The serial step at a value record, unfolded: what `annotStepC`
computes from a fresh state when `valueStep` has a verdict. -/
private theorem annotStepC_value {pins : List NatOpPinSet} {i : Nat} {fe W : FEnv}
    {pend : Array PendingCheck} {pd : Declaration}
    (hfe : W.find? = fe.find?) {r : Except CheckError (ConstantInfo × ValueGroup)}
    (h : valueStep mode W pd = some r) :
    (match annotStepC mode pins i fe pend pd {} with
      | .ok ((fe', pend'), _) => Except.ok (fe', pend')
      | .error e => .error e) =
      (r.map fun (ci, vg) => (fe.push ci, pend.push ⟨vg, i, fe.visibleBelow⟩)) := by
  have hflush : (flushC : CheckCM Unit) {} = .ok ((), ({} : CState).flushed) := rfl
  cases pd with
  | defnDecl cv value hint =>
    by_cases hnat : (natOpNames.contains cv.name || natDivModNames.contains cv.name) = true
    · simp only [valueStep, hnat, ↓reduceIte] at h
      exact nomatch h
    · simp only [valueStep, hnat, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h
      simp only [annotStepC, hnat, Bool.false_eq_true, ↓reduceIte,
        annotValueC_congr (mode := mode) hfe, bind, StateT.bind, pure, StateT.pure]
      cases annotValueC mode fe cv value {} <;> rfl
  | thmDecl cv value =>
    simp only [valueStep, Option.some.injEq] at h
    subst h
    simp only [annotStepC, annotConstantValC_congr (mode := mode) hfe, bind, StateT.bind,
      pure, StateT.pure, hflush, Except.bind]
    cases annotConstantValC mode fe cv ({} : CState).flushed <;> rfl
  | opaqueDecl cv value =>
    by_cases hred : reduceOpNames.contains cv.name = true
    · simp only [valueStep, hred, ↓reduceIte] at h
      exact nomatch h
    · simp only [valueStep, hred, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h
      simp only [annotStepC, hred, Bool.false_eq_true, ↓reduceIte,
        annotValueC_congr (mode := mode) hfe, bind, StateT.bind, pure, StateT.pure]
      cases annotValueC mode fe cv value {} <;> rfl
  | axiomDecl _ => exact nomatch h
  | basisDecl _ => exact nomatch h
  | quotDecl _ _ => exact nomatch h
  | indDecl _ _ => exact nomatch h

/-- **The commit step**: a value record a worker installed at the view
whose lookups are the serial index's is the serial fold's step — the
constant the worker reports pushed, its pending check recorded at the
serial counter. -/
theorem valueStep_commit {pins : List NatOpPinSet} {B : BaseIdx} {S : Slots} {i : Nat}
    {fe : FEnv} {pend : Array PendingCheck} {pd : Declaration} {ci : ConstantInfo}
    {vg : ValueGroup} (hag : ViewAgrees B S fe) (hand : andPinOk pd = true)
    (h : valueStep mode (workerView B S fe.visibleBelow) pd = some (.ok (ci, vg))) :
    annotDeclStep mode pins (i, fe, pend) pd =
      .ok (i + 1, fe.push ci, pend.push ⟨vg, i, fe.visibleBelow⟩) := by
  have hs := annotStepC_value (pins := pins) (i := i) (pend := pend) (funext hag) h
  unfold annotDeclStep
  simp only [hand, ↓reduceIte]
  revert hs
  cases annotStepC mode pins i fe pend pd {} with
  | error e => intro hs; simp [Except.map] at hs
  | ok p =>
    obtain ⟨⟨fe', pend'⟩, s'⟩ := p
    intro hs
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    rfl

/-- A failing worker's install is the serial step's failure, with the
same error at the same position. -/
theorem valueStep_commit_error {pins : List NatOpPinSet} {B : BaseIdx} {S : Slots}
    {i : Nat} {fe : FEnv} {pend : Array PendingCheck} {pd : Declaration} {e : CheckError}
    (hag : ViewAgrees B S fe) (hand : andPinOk pd = true)
    (h : valueStep mode (workerView B S fe.visibleBelow) pd = some (.error e)) :
    annotDeclStep mode pins (i, fe, pend) pd = .error (e, i) := by
  have hs := annotStepC_value (pins := pins) (i := i) (pend := pend) (funext hag) h
  unfold annotDeclStep
  simp only [hand, ↓reduceIte]
  revert hs
  cases annotStepC mode pins i fe pend pd {} with
  | error e' => intro hs; cases hs; rfl
  | ok p => intro hs; simp [Except.map] at hs

end ConLeche.Cached

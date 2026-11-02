module

public import ConLeche.Cached.Installed
import ConLeche.Verify.Cached.KnotCongr
/- `withPtrEq` is `public` but not `@[expose]`; the slot check below is
*defined* through it and `slotIs_spec` needs its body (`k ()`), which
`import all` makes visible in this module only (the `Init.Util`
exception CLAUDE.md lists). -/
public import ConLeche.Util.PtrEq

/-!
# The parallel install's commit step (task #329)

Phase A (`installDeclStep`, `ConLeche/Cached/Installed.lean`) installs
every record from a fresh memo state, so a record's install is a
function of the index it sees and the record alone.  The parallel
install runs that function on worker threads, each at a **worker view**
instead of the serial index, and an in-order commit thread pushes each
record's constants into the serial index while it extends the serial
fold's accepting run (`InstallRun`) one record at a time — the run the
driver returns is the serial fold's whatever the schedule.

* **The worker view** (`workerView B S v`) is an `FEnv` with an empty
  index and the frozen base layer `B` (`FBase`,
  `ConLeche/Kernel/FEnv.lean`) visible below the counter `v`: the
  predicted name of every constant of the stream, each answering from
  the slot of the record that installs it.  It is built once, before
  the workers start, from the names the records will install.
* **The invariant** (`ViewAgrees B S fe`): the view at the serial index's
  counter answers every lookup as the serial index does.  It holds at
  the empty index (`ViewAgrees.empty`), and a commit keeps it when every
  constant it pushes fills the slot `B` predicted for its counter and
  that slot delivers the very constant pushed (`ViewAgrees.pushAll`,
  checked by `slotsOk`, pointer comparisons at run time, which the
  installer evaluates after publishing its slot).
* **The commit step of a value record** (`valueStep_commit`): a
  definition's, theorem's or opaque's install at the view, by the
  congruence of the cached core in `find?` (`coreKnotI_congr`,
  `ConLeche/Verify/Cached/KnotCongr.lean`), IS the serial step's: same
  constant, same pending check.  A failing record fails with the serial
  step's error (`valueStep_commit_error`).  Every other record — a
  block, an axiom, a basis block, a pinned declaration — goes through
  the cached checker's own step at the view; that its install there is
  the serial step is `installStep_commit`
  (`ConLeche/Verify/Cached/ViewCongr.lean`), which covers both kinds.

Nothing here mentions a schedule, a thread or a promise: the lemmas
are about values, and what a task delivers is a value (`Task.get` is
logically a projection).  The driver is `ConLeche/Driver/ParInstall.lean`'s.

**Why this is `Verify/Cached`, not `Cached`.**  The driver carries the
serial fold's accepting run and needs these lemmas to extend it; the
file is self-contained (the cached checker and `KnotCongr`, nothing
from the theory).  During task #329 this file sat in the `Cached` tier
under CLAUDE.md's self-contained-verification exception, because the
then-implementation driver (`Main.lean`) could not import `Verify/*`;
the maintainer's 2026-10-08 ruling lets the driver import `Verify/*`,
so it moved back here.  It keeps its `@[expose] public section` (not
the Verify tier's usual plain `public section`): `workerView` and
`valueStep` are `unfold`ed and `simp`-rewritten by
`ConLeche/Verify/Cached/ViewCongr.lean`'s own proofs
(`installStep_commit`'s case split), which needs their bodies exposed,
not just their statements visible.
-/

@[expose] public section

namespace ConLeche.Cached

open ConLeche

variable {mode : CheckMode}

/-! ## The install halves read the index only through `find?` -/

/-- `installHeaderC` reads its index through `find?` alone (the
duplicate guard, the knot, `constsResolveFC`). -/
theorem installHeaderC_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) :
    installHeaderC fe₁ = installHeaderC fe₂ := by
  funext cv
  unfold installHeaderC
  simp only [constsResolveFC_congr hfe, hfe, strLitSupportedF_congr hfe]

/-- `installValueGuardsC` reads its index through `find?` alone (the knot and
`constsResolveFC`), so it is congruent in the index: phase B's
guards on a theorem's value at the prefix view are the guards at the
environment the view names. -/
theorem installValueGuardsC_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) :
    installValueGuardsC fe₁ = installValueGuardsC fe₂ := by
  funext cv value
  unfold installValueGuardsC
  simp only [constsResolveFC_congr hfe, strLitSupportedF_congr hfe]

/-- Phase A's value install reads its index through `find?` alone. -/
theorem installGuardsC_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) :
    installGuardsC fe₁ = installGuardsC fe₂ := by
  funext cv value
  unfold installGuardsC
  simp only [installHeaderC_congr hfe, installValueGuardsC_congr hfe]

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

theorem IdxBelow.pushTable {fe : FEnv} (h : IdxBelow fe) (t : ProjTable) :
    IdxBelow (fe.pushTable t) := h

theorem IdxBelow.pushTables :
    ∀ (Q : List ProjTable) {fe : FEnv}, IdxBelow fe → IdxBelow (FEnv.pushTables Q fe)
  | [], _, h => h
  | t :: Q, _, h => IdxBelow.pushTables Q (h.pushTable t)

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
record's installed constants — sharded by name hash (`baseGet?`,
`ConLeche/Kernel/FEnv.lean`), one map per shard. -/
abbrev BaseIdx := Array (Std.HashMap Name (Nat × Nat × Nat))

/-- The records' slots: record `k`'s installed constants and projection
tables, each in install order, deferred. -/
abbrev Slots := Array (Thunk (Array ConstantInfo × List ProjTable))

/-- **The worker view at counter `v`**: no constants or tables of its
own, the base visible below `v`.  A worker installs record `r` at
`workerView B S vis_r`, where `vis_r` is the counter the prediction
gives it. -/
def workerView (B : BaseIdx) (S : Slots) (v : Nat) : FEnv :=
  ⟨⟨[], []⟩, {}, v, ⟨B, S, v⟩, [], {}⟩

theorem workerView_find? (B : BaseIdx) (S : Slots) (v : Nat) (n : Name) :
    (workerView B S v).find? n = FBase.find? ⟨B, S, v⟩ n := by
  simp [workerView, FEnv.find?]

theorem workerView_rawTable? (B : BaseIdx) (S : Slots) (v : Nat) (T : Name) :
    (workerView B S v).rawTable? T = FBase.findTable? ⟨B, S, v⟩ T := by
  simp [workerView, FEnv.rawTable?]

/-- No two names share a counter in the base: what the builder
guarantees (`buildBase_inj`), and what lets a commit fill exactly one
slot. -/
def BaseInj (B : BaseIdx) : Prop :=
  ∀ (n₁ n₂ : Name) (c : Nat) (x₁ x₂ : Nat × Nat),
    baseGet? B n₁ = some (c, x₁) → baseGet? B n₂ = some (c, x₂) → n₁ = n₂

/-- **The invariant of the commit thread**: the worker view at the
serial index's counter answers every constant lookup as the serial
index does, and every raw table lookup (`FEnv.rawTable?`) — so every
table lookup too (`FEnv.findTable?` is the raw lookup gated by the
constant lookup). -/
structure ViewAgrees (B : BaseIdx) (S : Slots) (fe : FEnv) : Prop where
  find : ∀ n, (workerView B S fe.visibleBelow).find? n = fe.find? n
  raw : ∀ T, (workerView B S fe.visibleBelow).rawTable? T = fe.rawTable? T

/-- At the empty index nothing is visible on either side. -/
theorem ViewAgrees.empty (B : BaseIdx) (S : Slots) : ViewAgrees B S (mkFEnv Env.empty) := by
  constructor
  · intro n
    rw [workerView_find?]
    simp only [FBase.find?, mkFEnv, mkFEnvGo, Env.empty, FEnv.find?,
      Std.HashMap.getElem?_empty]
    split <;> simp [baseGet?]
  · intro T
    rw [workerView_rawTable?]
    simp only [FBase.findTable?, mkFEnv, mkFEnvGo, mkTblsGo, Env.empty, FEnv.rawTable?,
      Std.HashMap.getElem?_empty]
    split <;> simp [baseGet?]

/-- The slot's constant: position `j` of record `k`'s task. -/
def slotGet (S : Slots) (k j : Nat) : Option ConstantInfo :=
  if h : k < S.size then (S[k]).get.1[j]? else none

/-- The slot's tables: record `k`'s task's. -/
def slotTables (S : Slots) (k : Nat) : Option (List ProjTable) :=
  if h : k < S.size then some (S[k]).get.2 else none

/-- **The slot check**: position `j` of record `k`'s slot is `ci`.  At
run time a pointer comparison — the slot delivers the very object the
record's install reports — and only on a mismatch the
structural comparison, which is what it means logically
(`slotIs_spec`). -/
def slotIs (S : Slots) (k j : Nat) (ci : ConstantInfo) : Bool :=
  match slotGet S k j with
  | some ci' => ConLeche.withPtrEq ci' ci (fun _ => decide (ci' = ci)) (fun h => by simp [h])
  | none => false

theorem slotIs_spec {S : Slots} {k j : Nat} {ci : ConstantInfo}
    (h : slotIs S k j ci = true) : slotGet S k j = some ci := by
  unfold slotIs at h
  split at h
  · rename_i ci' hget
    have h' : decide (ci' = ci) = true := h
    rw [hget, of_decide_eq_true h']
  · exact absurd h Bool.false_ne_true

/-- **The table slot check**: record `k`'s slot delivers the tables `Q`
— a pointer comparison at run time, as `slotIs`. -/
def slotTablesIs (S : Slots) (k : Nat) (Q : List ProjTable) : Bool :=
  match slotTables S k with
  | some Q' => withPtrEq Q' Q (fun _ => decide (Q' = Q)) (fun h => by simp [h])
  | none => false

theorem slotTablesIs_spec {S : Slots} {k : Nat} {Q : List ProjTable}
    (h : slotTablesIs S k Q = true) : slotTables S k = some Q := by
  unfold slotTablesIs at h
  split at h
  · rename_i Q' hget
    have h' : decide (Q' = Q) = true := h
    rw [hget, of_decide_eq_true h']
  · exact absurd h Bool.false_ne_true

/-- **A commit's slot check**: the base predicted `ci`'s name at the
counter `v`, and that slot's task delivers `ci` and the record's tables
`Q`. -/
def slotOk (B : BaseIdx) (S : Slots) (Q : List ProjTable) (v : Nat) (ci : ConstantInfo) :
    Bool :=
  match baseGet? B ci.name with
  | some (c, k, j) => c == v && slotIs S k j ci && slotTablesIs S k Q
  | none => false

theorem slotOk_spec {B : BaseIdx} {S : Slots} {Q : List ProjTable} {v : Nat}
    {ci : ConstantInfo} (h : slotOk B S Q v ci = true) :
    ∃ k j, baseGet? B ci.name = some (v, k, j) ∧ slotGet S k j = some ci ∧
      slotTables S k = some Q := by
  unfold slotOk at h
  split at h
  · rename_i c k j hB
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, hs⟩, ht⟩ := h
    exact ⟨k, j, hB, slotIs_spec hs, slotTablesIs_spec ht⟩
  · exact absurd h Bool.false_ne_true

theorem FBase.find?_eq (B : BaseIdx) (S : Slots) (v : Nat) (n : Name) :
    FBase.find? ⟨B, S, v⟩ n =
      match baseGet? B n with
      | some (c, k, j) => if c < v then slotGet S k j else none
      | none => none := by
  simp only [FBase.find?]
  cases baseGet? B n with
  | none => rfl
  | some p => obtain ⟨c, k, j⟩ := p; rfl

theorem FBase.findTable?_eq (B : BaseIdx) (S : Slots) (v : Nat) (T : Name) :
    FBase.findTable? ⟨B, S, v⟩ T =
      match baseGet? B T with
      | some (c, k, _) =>
        if c < v then (slotTables S k).bind (ProjTable.lastOf? T) else none
      | none => none := by
  simp only [FBase.findTable?, slotTables]
  cases baseGet? B T with
  | none => rfl
  | some p =>
    obtain ⟨c, k, j⟩ := p
    simp only
    split
    · split <;> simp
    · rfl

/-- **A checked push keeps the constant half of the invariant.** -/
theorem ViewAgrees.find_push {B : BaseIdx} {S : Slots} {fe : FEnv} (hB : BaseInj B)
    (hidx : IdxBelow fe) (h : ∀ n, (workerView B S fe.visibleBelow).find? n = fe.find? n)
    {Q : List ProjTable} {ci : ConstantInfo}
    (hok : slotOk B S Q fe.visibleBelow ci = true) :
    ∀ n, (workerView B S (fe.push ci).visibleBelow).find? n = (fe.push ci).find? n := by
  obtain ⟨k, j, hslot, hget, -⟩ := slotOk_spec hok
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
    cases hl : baseGet? B n with
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

/-! ## A commit of several constants and tables

A block, an axiom, a basis block or a pinned declaration pushes a list
of constants, each filling its predicted slot, and a block its tables:
every table names one of the record's own constants (the structure it
belongs to), and travels in that record's slot. -/

/-- The slot checks of a list of constants pushed from counter `v` on,
each slot also delivering the record's tables `Q`. -/
def slotsOk (B : BaseIdx) (S : Slots) (Q : List ProjTable) : Nat → List ConstantInfo → Bool
  | _, [] => true
  | v, ci :: L => slotOk B S Q v ci && slotsOk B S Q (v + 1) L

/-- **A commit's checks**: every constant fills its slot (`slotsOk`), and
every table belongs to one of the record's constants. -/
def commitOk (B : BaseIdx) (S : Slots) (v : Nat) (L : List ConstantInfo)
    (Q : List ProjTable) : Bool :=
  slotsOk B S Q v L && Q.all (fun t => L.any (·.name == t.structName))

theorem IdxBelow.pushAll {fe : FEnv} (h : IdxBelow fe) :
    ∀ L : List ConstantInfo, IdxBelow (FEnv.pushAll L fe)
  | [] => h
  | ci :: L => IdxBelow.pushAll (h.push ci) L

theorem pushAll_visibleBelow : ∀ (L : List ConstantInfo) (fe : FEnv),
    (FEnv.pushAll L fe).visibleBelow = fe.visibleBelow + L.length
  | [], _ => rfl
  | ci :: L, fe => by
    show (FEnv.pushAll L (fe.push ci)).visibleBelow = _
    rw [pushAll_visibleBelow L (fe.push ci)]
    simp only [FEnv.push, List.length_cons]
    omega

/-- Checked pushes keep the constant half of the invariant. -/
theorem ViewAgrees.find_pushAll {B : BaseIdx} {S : Slots} (hB : BaseInj B)
    {Q : List ProjTable} :
    ∀ (L : List ConstantInfo) {fe : FEnv}, IdxBelow fe →
      (∀ n, (workerView B S fe.visibleBelow).find? n = fe.find? n) →
      slotsOk B S Q fe.visibleBelow L = true →
      ∀ n, (workerView B S (FEnv.pushAll L fe).visibleBelow).find? n =
        (FEnv.pushAll L fe).find? n
  | [], _, _, h, _ => h
  | ci :: L, fe, hidx, h, hok => by
    simp only [slotsOk, Bool.and_eq_true] at hok
    exact ViewAgrees.find_pushAll hB L (hidx.push ci)
      (ViewAgrees.find_push hB hidx h hok.1) hok.2

/-- The slot checks place every pushed constant at its counter, its slot
delivering the tables. -/
theorem slotsOk_mem {B : BaseIdx} {S : Slots} {Q : List ProjTable} :
    ∀ {v : Nat} {L : List ConstantInfo}, slotsOk B S Q v L = true →
      ∀ ci ∈ L, ∃ c k j, baseGet? B ci.name = some (c, k, j) ∧ v ≤ c ∧
        c < v + L.length ∧ slotTables S k = some Q
  | _, [], _, _, hm => nomatch hm
  | v, ci :: L, hok, cj, hm => by
    simp only [slotsOk, Bool.and_eq_true] at hok
    rcases List.mem_cons.mp hm with rfl | hm
    · obtain ⟨k, j, hB, -, hQ⟩ := slotOk_spec hok.1
      exact ⟨v, k, j, hB, Nat.le_refl _, by simp, hQ⟩
    · obtain ⟨c, k, j, hB, h1, h2, hQ⟩ := slotsOk_mem hok.2 cj hm
      exact ⟨c, k, j, hB, by omega, by simp only [List.length_cons]; omega, hQ⟩

/-- The slot checks fill every counter of the range: the name at a
counter in it is a pushed constant's. -/
theorem slotsOk_cover {B : BaseIdx} {S : Slots} {Q : List ProjTable} :
    ∀ {v : Nat} {L : List ConstantInfo}, slotsOk B S Q v L = true →
      ∀ c, v ≤ c → c < v + L.length → ∃ ci ∈ L, ∃ k j, baseGet? B ci.name = some (c, k, j)
  | _, [], _, c, h1, h2 => by simp at h2; omega
  | v, ci :: L, hok, c, h1, h2 => by
    simp only [slotsOk, Bool.and_eq_true] at hok
    by_cases hc : c = v
    · subst hc
      obtain ⟨k, j, hB, -⟩ := slotOk_spec hok.1
      exact ⟨ci, List.mem_cons_self, k, j, hB⟩
    · obtain ⟨cj, hm, k, j, hB⟩ :=
        slotsOk_cover hok.2 c (by omega) (by simp only [List.length_cons] at h2; omega)
      exact ⟨cj, List.mem_cons_of_mem _ hm, k, j, hB⟩

/-- `lastOf?` finds nothing exactly when no table carries the name. -/
theorem lastOf?_eq_none {T : Name} :
    ∀ {Q : List ProjTable}, ProjTable.lastOf? T Q = none ↔ ∀ t ∈ Q, t.structName ≠ T
  | [] => by simp [ProjTable.lastOf?]
  | t :: Q => by
    have ih := lastOf?_eq_none (T := T) (Q := Q)
    simp only [ProjTable.lastOf?, List.mem_cons, forall_eq_or_imp]
    cases hl : ProjTable.lastOf? T Q with
    | some r => simp only [reduceCtorEq, false_iff]; intro ⟨_, h⟩; exact absurd (ih.2 h) (by simp [hl])
    | none =>
      have := ih.1 hl
      by_cases hT : t.structName = T
      · simp [hT]
      · simpa [hT] using this

/-- **A checked commit keeps the invariant**: the record's constants
pushed, then its tables. -/
theorem ViewAgrees.commit {B : BaseIdx} {S : Slots} (hB : BaseInj B) {fe : FEnv}
    (hidx : IdxBelow fe) (h : ViewAgrees B S fe) {L : List ConstantInfo}
    {Q : List ProjTable} (hok : commitOk B S fe.visibleBelow L Q = true) :
    ViewAgrees B S (FEnv.pushTables Q (FEnv.pushAll L fe)) := by
  simp only [commitOk, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    beq_iff_eq] at hok
  obtain ⟨hsl, hQL⟩ := hok
  have hvb : (FEnv.pushTables Q (FEnv.pushAll L fe)).visibleBelow =
      fe.visibleBelow + L.length := by
    rw [FEnv.visibleBelow_pushTables, pushAll_visibleBelow]
  constructor
  · intro n
    rw [FEnv.find?_pushTables, ← ViewAgrees.find_pushAll hB L hidx h.find hsl n,
      hvb, pushAll_visibleBelow]
  · intro T
    -- a table of the record names one of its constants, at a counter of
    -- the commit's range
    have hQr : ∀ t ∈ Q, t.structName = T → ∃ c k j, baseGet? B T = some (c, k, j) ∧
        fe.visibleBelow ≤ c ∧ c < fe.visibleBelow + L.length := by
      intro t ht hT
      obtain ⟨ci, hci, hn⟩ := hQL t ht
      obtain ⟨c, k, j, hBc, h1, h2, -⟩ := slotsOk_mem hsl ci hci
      exact ⟨c, k, j, by rw [← hT, ← hn]; exact hBc, h1, h2⟩
    rw [hvb, FEnv.rawTable?_pushTables, FEnv.rawTable?_pushAll, ← h.raw T,
      workerView_rawTable?, workerView_rawTable?, FBase.findTable?_eq, FBase.findTable?_eq]
    cases hl : baseGet? B T with
    | none =>
      have hQn : ProjTable.lastOf? T Q = none := by
        rw [lastOf?_eq_none]
        intro t ht hT
        obtain ⟨c, k, j, hBT, -⟩ := hQr t ht hT
        rw [hBT] at hl; exact nomatch hl
      simp [hQn]
    | some p =>
      obtain ⟨c, k, j⟩ := p
      simp only
      by_cases hc : c < fe.visibleBelow
      · have hQn : ProjTable.lastOf? T Q = none := by
          rw [lastOf?_eq_none]
          intro t ht hT
          obtain ⟨c', k', j', hBT, h1, -⟩ := hQr t ht hT
          rw [hBT] at hl
          cases hl
          omega
        simp [hQn, hc, Nat.lt_of_lt_of_le hc (Nat.le_add_right _ _)]
      · by_cases hc' : c < fe.visibleBelow + L.length
        · obtain ⟨ci, hci, k', j', hBci⟩ := slotsOk_cover hsl c (by omega) hc'
          have hn : ci.name = T := hB _ _ _ _ _ hBci hl
          obtain ⟨c₁, k₁, j₁, hB₁, -, -, hQ⟩ := slotsOk_mem hsl ci hci
          rw [hn, hl] at hB₁
          cases hB₁
          simp only [hc', hc, ↓reduceIte, hQ, Option.bind_some]
          cases ProjTable.lastOf? T Q <;> rfl
        · have hQn : ProjTable.lastOf? T Q = none := by
            rw [lastOf?_eq_none]
            intro t ht hT
            obtain ⟨c', k', j', hBT, -, h2⟩ := hQr t ht hT
            rw [hBT] at hl
            cases hl
            omega
          simp [hQn, hc, hc']

/-! ## The base builder

The base is built one shard per task, each from the predicted slots
that fall in it, in counter order (a duplicate name keeps its first
slot; the serial step rejects the duplicate, so the install that pushes
it fails, and an install that fails is committed as the rejection
without a slot check).  Nothing below depends on the sharding or on the
order: every entry the builder inserts names its own slot
(`SlotsOf`), and that alone makes the base counter-injective
(`buildBase_inj`).  A slot is `(name, record, position)`. -/

/-- What the builder keeps: every entry names its own slot. -/
def SlotsOf (slots : Array (Name × Nat × Nat)) (m : Std.HashMap Name (Nat × Nat × Nat)) :
    Prop :=
  ∀ (n : Name) (c : Nat) (x : Nat × Nat),
    m[n]? = some (c, x) → ∃ h : c < slots.size, slots[c].1 = n

/-- Insert the slots at the counters `cs` (offset by `off`), in order,
each name at its counter unless the shard already holds it. -/
def shardInsert (slots : Array (Name × Nat × Nat)) (off : Nat) (cs : Array Nat)
    (m : Std.HashMap Name (Nat × Nat × Nat)) : Std.HashMap Name (Nat × Nat × Nat) :=
  cs.foldl (fun m i =>
    match slots[off + i]? with
    | some s => m.insertIfNew s.1 (off + i, s.2)
    | none => m) m

theorem SlotsOf.empty (slots : Array (Name × Nat × Nat)) : SlotsOf slots {} := by
  intro n c x hl; simp at hl

theorem SlotsOf.shardInsert {slots : Array (Name × Nat × Nat)} {m : Std.HashMap Name (Nat × Nat × Nat)}
    (hm : SlotsOf slots m) (off : Nat) (cs : Array Nat) :
    SlotsOf slots (ConLeche.Cached.shardInsert slots off cs m) := by
  unfold ConLeche.Cached.shardInsert
  rw [← Array.foldl_toList]
  generalize cs.toList = l
  induction l generalizing m with
  | nil => exact hm
  | cons i l ih =>
    simp only [List.foldl_cons]
    apply ih
    split
    · rename_i s hs
      intro n c x hl
      rw [Std.HashMap.getElem?_insertIfNew] at hl
      split at hl
      · rename_i hk
        cases hl
        obtain ⟨hk, -⟩ := hk
        rw [Array.getElem?_eq_some_iff] at hs
        obtain ⟨hlt, hs⟩ := hs
        exact ⟨hlt, by rw [hs]; simpa using hk⟩
      · exact hm n c x hl
    · exact hm

/-- **A base whose shards all keep `SlotsOf` is counter-injective.** -/
theorem baseInj_of_slotsOf {slots : Array (Name × Nat × Nat)} {B : BaseIdx}
    (h : ∀ m ∈ B, SlotsOf slots m) : BaseInj B := by
  have hget : ∀ n c x, baseGet? B n = some (c, x) → ∃ h : c < slots.size, slots[c].1 = n := by
    intro n c x hl
    unfold baseGet? at hl
    split at hl
    · rename_i m hm
      exact h m (Array.mem_of_getElem? hm) n c x hl
    · exact absurd hl (by simp)
  unfold BaseInj
  intro n₁ n₂ c x₁ x₂ h₁ h₂
  obtain ⟨hc, rfl⟩ := hget n₁ c x₁ h₁
  obtain ⟨-, rfl⟩ := hget n₂ c x₂ h₂
  rfl

/-- One shard of the base: the slots the chunks put in shard `s`, chunk
by chunk (`offs[t]` is chunk `t`'s first counter, `buckets[t][s]` the
chunk-relative counters of its slots in shard `s`). -/
def buildShard (slots : Array (Name × Nat × Nat)) (offs : Array Nat)
    (buckets : Array (Array (Array Nat))) (s : Nat) : Std.HashMap Name (Nat × Nat × Nat) :=
  (Array.range buckets.size).foldl (fun m t =>
    shardInsert slots (offs[t]?.getD 0) ((buckets[t]?.bind (·[s]?)).getD #[]) m) {}

theorem buildShard_slotsOf (slots : Array (Name × Nat × Nat)) (offs : Array Nat)
    (buckets : Array (Array (Array Nat))) (s : Nat) :
    SlotsOf slots (buildShard slots offs buckets s) := by
  unfold buildShard
  rw [← Array.foldl_toList]
  generalize (Array.range buckets.size).toList = l
  suffices ∀ m, SlotsOf slots m → SlotsOf slots (l.foldl (fun m t =>
      shardInsert slots (offs[t]?.getD 0) ((buckets[t]?.bind (·[s]?)).getD #[]) m) m) from
    this _ (SlotsOf.empty slots)
  induction l with
  | nil => intro m hm; exact hm
  | cons t l ih => intro m hm; exact ih _ (hm.shardInsert _ _)

/-- A built shard, with the evidence that it is `buildShard` of some
shard number: what a shard task returns.  The driver builds it and marks
it persistent on the task's own thread (so that the runtime's resolution
of the task, which marks a task's result under its global lock, finds
nothing left to mark), and uses the mark's result; the evidence is what
lets the base be counter-injective (`buildBase_inj`) whatever the task
delivered. -/
abbrev BuiltShard (slots : Array (Name × Nat × Nat)) (offs : Array Nat)
    (buckets : Array (Array (Array Nat))) : Type :=
  { m : Std.HashMap Name (Nat × Nat × Nat) // ∃ s, m = buildShard slots offs buckets s }

/-- **A base of built shards is counter-injective.** -/
theorem buildBase_inj {slots : Array (Name × Nat × Nat)} {offs : Array Nat}
    {buckets : Array (Array (Array Nat))} (shards : Array (BuiltShard slots offs buckets)) :
    BaseInj (shards.map (·.1)) := by
  apply baseInj_of_slotsOf (slots := slots)
  intro m hm
  simp only [Array.mem_map] at hm
  obtain ⟨⟨m', s, rfl⟩, -, rfl⟩ := hm
  exact buildShard_slotsOf slots offs buckets s

/-! ## What a worker installs, and the commit step -/

/-- **A worker's install of a value record at the view `W`**: the
constant the serial step pushes and the pending check it records, or
its error; `none` for every other kind (`installStep` installs those
with the cached checker's own step, at the same view).  The memo state
is dropped here — nothing of it crosses to the commit. -/
def valueStep (W : FEnv) : Declaration →
    Option (Except CheckError (ConstantInfo × ValueGroup))
  | .defnDecl cv value hint =>
    if natOpNames.contains cv.name || natDivModNames.contains cv.name then none
    else some (match installGuardsC W cv value {} with
      | .ok (_, _) => .ok (.defnInfo cv value hint, ⟨.defn, cv, value⟩)
      | .error e => .error e)
  | .thmDecl cv value =>
    some (match installHeaderC W cv ({} : CState).flushed with
      | .ok (_, _) => .ok (.thmInfo cv, ⟨.thm, cv, value⟩)
      | .error e => .error e)
  | .opaqueDecl cv value =>
    if reduceOpNames.contains cv.name then none
    else some (match installGuardsC W cv value {} with
      | .ok (_, _) => .ok (.axiomInfo cv, ⟨.opaque, cv, value⟩)
      | .error e => .error e)
  | _ => none

/-- The serial step at a value record, unfolded: what `installStepC`
computes from a fresh state when `valueStep` has a verdict. -/
private theorem installStepC_value {pins : List NatOpPinSet} {i : Nat} {fe W : FEnv}
    {pend : Array PendingCheck} {pd : Declaration}
    (hfe : W.find? = fe.find?) {r : Except CheckError (ConstantInfo × ValueGroup)}
    (h : valueStep W pd = some r) :
    (match installStepC mode pins i fe pend pd {} with
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
      simp only [installStepC, hnat, Bool.false_eq_true, ↓reduceIte,
        installGuardsC_congr hfe, bind, StateT.bind, pure, StateT.pure]
      cases installGuardsC fe cv value {} <;> rfl
  | thmDecl cv value =>
    simp only [valueStep, Option.some.injEq] at h
    subst h
    simp only [installStepC, installHeaderC_congr hfe, bind, StateT.bind,
      pure, StateT.pure, hflush, Except.bind]
    cases installHeaderC fe cv ({} : CState).flushed <;> rfl
  | opaqueDecl cv value =>
    by_cases hred : reduceOpNames.contains cv.name = true
    · simp only [valueStep, hred, ↓reduceIte] at h
      exact nomatch h
    · simp only [valueStep, hred, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h
      simp only [installStepC, hred, Bool.false_eq_true, ↓reduceIte,
        installGuardsC_congr hfe, bind, StateT.bind, pure, StateT.pure]
      cases installGuardsC fe cv value {} <;> rfl
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
    (h : valueStep (workerView B S fe.visibleBelow) pd = some (.ok (ci, vg))) :
    installDeclStep mode pins (i, fe, pend) pd =
      .ok (i + 1, fe.push ci, pend.push ⟨vg, i, fe.visibleBelow⟩) := by
  have hs := installStepC_value (mode := mode) (pins := pins) (i := i) (pend := pend) (funext hag.find) h
  unfold installDeclStep
  simp only [hand, ↓reduceIte]
  revert hs
  cases installStepC mode pins i fe pend pd {} with
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
    (h : valueStep (workerView B S fe.visibleBelow) pd = some (.error e)) :
    installDeclStep mode pins (i, fe, pend) pd = .error (e, i) := by
  have hs := installStepC_value (mode := mode) (pins := pins) (i := i) (pend := pend) (funext hag.find) h
  unfold installDeclStep
  simp only [hand, ↓reduceIte]
  revert hs
  cases installStepC mode pins i fe pend pd {} with
  | error e' => intro hs; cases hs; rfl
  | ok p => intro hs; simp [Except.map] at hs

end ConLeche.Cached

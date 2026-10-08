module

public import ConLeche.Cached.Installed
import ConLeche.Verify.Cached.KnotCongr
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
  slot of the record that installs it.  It is built once, before the
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
  `ConLeche/Verify/Cached/KnotCongr.lean`), IS the serial step's: same
  constant, same pending check.  A failing record fails with the serial
  step's error (`valueStep_commit_error`).  Every other record — a
  block, an axiom, a basis block, a pinned declaration — pushes a list
  of constants, each checked against its slot (`ViewAgrees.pushAll`);
  that its install at the view is the serial step is
  `installStep_commit` (`ConLeche/Verify/Cached/ViewCongr.lean`).

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
record's installed constants — sharded by name hash (`baseGet?`,
`ConLeche/Kernel/FEnv.lean`), one map per shard. -/
abbrev BaseIdx := Array (Std.HashMap Name (Nat × Nat × Nat))

/-- The records' slots: record `k`'s installed constants, deferred. -/
abbrev Slots := Array (Thunk (Array ConstantInfo))

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
    baseGet? B n₁ = some (c, x₁) → baseGet? B n₂ = some (c, x₂) → n₁ = n₂

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
  split <;> simp [baseGet?]

/-- The slot's constant: position `j` of record `k`'s task. -/
def slotGet (S : Slots) (k j : Nat) : Option ConstantInfo :=
  if h : k < S.size then (S[k]).get[j]? else none

/-- **The slot check**: position `j` of record `k`'s slot is `ci`.  At
run time a pointer comparison — the slot delivers the very object the
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
  match baseGet? B ci.name with
  | some (c, k, j) => c == v && slotIs S k j ci
  | none => false

theorem slotOk_spec {B : BaseIdx} {S : Slots} {v : Nat} {ci : ConstantInfo}
    (h : slotOk B S v ci = true) :
    ∃ k j, baseGet? B ci.name = some (v, k, j) ∧ slotGet S k j = some ci := by
  unfold slotOk at h
  split at h
  · rename_i c k j hB
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hs⟩ := h
    exact ⟨k, j, hB, slotIs_spec hs⟩
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

/-! ## The serial index as a function of the slots

The commit thread does not push: the serial index after the first `k`
records is `prefixFe S k`, the empty index with the records' slots
pushed in order, which a builder thread computes beside the commit loop
(`ConLeche/Driver/ParInstall.lean`).  The commit loop carries its run
over `prefixFe S k`, a term only its proofs mention; what it needs per
record is that the record's slot IS the list its install pushed
(`selfOk`, checked by the installer). -/

/-- Record `k`'s slot, as a list. -/
def slotList (S : Slots) (k : Nat) : List ConstantInfo :=
  match S[k]? with
  | some t => t.get.toList
  | none => []

/-- **The serial index after the first `k` records' slots.** -/
def prefixFe (S : Slots) : Nat → FEnv
  | 0 => mkFEnv Env.empty
  | k + 1 => FEnv.pushAll (slotList S k) (prefixFe S k)

/-- A push of an array, one constant at a time, is `pushAll` of its list. -/
theorem foldl_push_eq_pushAll (a : Array ConstantInfo) (fe : FEnv) :
    a.foldl (fun fe ci => fe.push ci) fe = FEnv.pushAll a.toList fe := by
  rw [← Array.foldl_toList]
  generalize a.toList = l
  induction l generalizing fe with
  | nil => rfl
  | cons ci l ih => exact ih (fe.push ci)

/-- The builder's step: record `k`'s slot pushed. -/
def prefixStep (S : Slots) (k : Nat) (fe : FEnv) : FEnv :=
  match S[k]? with
  | some t => t.get.foldl (fun fe ci => fe.push ci) fe
  | none => fe

theorem prefixStep_eq (S : Slots) (k : Nat) :
    prefixStep S k (prefixFe S k) = prefixFe S (k + 1) := by
  unfold prefixStep
  show _ = FEnv.pushAll (slotList S k) (prefixFe S k)
  unfold slotList
  split
  · exact foldl_push_eq_pushAll _ _
  · rfl

theorem pushAll_visibleBelow : ∀ (L : List ConstantInfo) (fe : FEnv),
    (FEnv.pushAll L fe).visibleBelow = fe.visibleBelow + L.length
  | [], _ => rfl
  | ci :: L, fe => by
    show (FEnv.pushAll L (fe.push ci)).visibleBelow = _
    rw [pushAll_visibleBelow L (fe.push ci)]
    simp only [FEnv.push, List.length_cons]
    omega

/-- Two constants are the same: a pointer comparison at run time, the
structural one only when the pointers differ. -/
def ciSame (a b : ConstantInfo) : Bool :=
  withPtrEq a b (fun _ => decide (a = b)) (fun h => by simp [h])

theorem ciSame_spec {a b : ConstantInfo} (h : ciSame a b = true) : a = b := by
  have h' : decide (a = b) = true := h
  exact of_decide_eq_true h'

/-- Two lists of constants are the same (`ciSame` elementwise). -/
def listSame : List ConstantInfo → List ConstantInfo → Bool
  | [], [] => true
  | a :: as, b :: bs => ciSame a b && listSame as bs
  | _, _ => false

theorem listSame_spec : ∀ {as bs : List ConstantInfo}, listSame as bs = true → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [listSame, Bool.and_eq_true] at h
    rw [ciSame_spec h.1, listSame_spec h.2]
  | [], _ :: _, h => by simp [listSame] at h
  | _ :: _, [], h => by simp [listSame] at h

/-- **Record `k`'s slot is the list `L`** (the installer's check, after
publishing its slot). -/
def selfOk (S : Slots) (k : Nat) (L : List ConstantInfo) : Bool :=
  listSame (slotList S k) L

theorem selfOk_spec {S : Slots} {k : Nat} {L : List ConstantInfo}
    (h : selfOk S k L = true) : slotList S k = L :=
  listSame_spec h

/-! ## The base builder

The base is built one shard per task, each from the predicted slots
that fall in it, in counter order (a duplicate name keeps its first
slot; the serial step rejects the duplicate, and the commit's slot check
fails before that).  Nothing below depends on the sharding or on the
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
shard number: what a shard task returns (it is built and marked
multi-threaded on its own thread, so that the runtime's resolution of
the task — which marks a task's result under its global lock — finds
nothing left to mark). -/
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
      | .ok (r, _) => .ok (.thmInfo r.1, ⟨.thm, r.1, value⟩)
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

import Setlec.Kernel.ArenaWF

/-!
# The correct-by-construction interning arena (task #103)

`WFStore` bundles an `EStore` with its invariant `EStore.WF`
(`Setlec/Kernel/ArenaWF.lean`), making arena validity a property of the
*type* — the `Std.HashMap` pattern: downstream code never states, checks,
or threads a well-formedness hypothesis, because every value of the type
carries it.  The proof field is computationally irrelevant: the compiled
representation of `WFStore` is exactly that of `EStore` (the trivial
one-field-structure optimization), so the bundle is a zero-runtime-cost
wrapper.

The interning interface is lifted wholesale:
* `empty` / `ofRaw` — constructors (the latter seeds from a raw store
  together with a proof of its invariant);
* `intern` / `internL` / `internN` — single-node interning; the node's
  index references must be in range, supplied as (erased) hypotheses,
  or checked at runtime by the `intern?` / `internL?` / `internN?`
  variants (`O(children)` per node — a per-record guard, not a sweep);
* `internExpr` / `internExprFast` / `internLevel` / `internLevels` /
  `internBM` / `internName` — whole-tree interning, hypothesis-free;
* the eager derived-field reads (`bvarBoundD`, `fvarRangeD`,
  `lhasParamD`, `ehasParamD`, `readbackN`, `beqNameI`) with their
  exactness facts available *unconditionally* — no `WF` hypothesis at
  any call site.

Every op satisfies a definitional `*_raw`/`*_idx` equation exposing the
underlying `EStore` op, so the whole `ArenaWF`/`Verify` lemma library
applies to bundle results via `s.wf` (extraction is just the field).
-/

namespace Setlec

/-- An interning arena that is well-formed *by construction*: the raw
`EStore` together with its invariant.  The `wf` field is a `Prop`, so
the compiled representation is exactly `EStore`'s (zero runtime
cost). -/
structure WFStore where
  /-- The underlying raw arena. -/
  raw : EStore
  /-- The invariant.  Extraction: from a `WFStore`, `EStore.WF` holds
  definitionally, so every raw-level `WF`-hypothesis lemma applies. -/
  wf : raw.WF

namespace WFStore

/-- Two bundles with the same raw store are equal (proof
irrelevance). -/
protected theorem ext : ∀ {s t : WFStore}, s.raw = t.raw → s = t
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/-- The empty arena. -/
def empty : WFStore := ⟨.empty, EStore.empty_wf⟩

instance : Inhabited WFStore := ⟨empty⟩

@[simp] theorem empty_raw : empty.raw = EStore.empty := rfl

/-- Seed a bundle from a raw store whose invariant has been
established. -/
def ofRaw (st : EStore) (h : st.WF) : WFStore := ⟨st, h⟩

@[simp] theorem ofRaw_raw (st : EStore) (h : st.WF) :
    (ofRaw st h).raw = st := rfl

/-! ## Single-node interning

The node's child/level/name references must be indices of the arena;
the evidence is an erased hypothesis (the caller usually has it because
the indices came out of earlier interning into the same, append-only
arena), or is checked at runtime by the `?`-variants. -/

/-- Intern one expression node. -/
def intern (s : WFStore) (n : ENode)
    (hc : ∀ c ∈ n.children, c < s.raw.nodes.size)
    (hlv : ∀ u ∈ n.levels, u < s.raw.lnodes.size)
    (hnm : ∀ p ∈ n.names, p < s.raw.nnodes.size) : EIdx × WFStore :=
  let p := s.raw.intern n
  (p.1, ⟨p.2, EStore.intern_wf s.wf hc hlv hnm⟩)

@[simp] theorem intern_raw (s : WFStore) (n : ENode) (hc hlv hnm) :
    (s.intern n hc hlv hnm).2.raw = (s.raw.intern n).2 := rfl

@[simp] theorem intern_idx (s : WFStore) (n : ENode) (hc hlv hnm) :
    (s.intern n hc hlv hnm).1 = (s.raw.intern n).1 := rfl

/-- The interned node is stored at the returned index. -/
theorem intern_node (s : WFStore) (n : ENode) (hc hlv hnm) :
    (s.intern n hc hlv hnm).2.raw.nodes[(s.intern n hc hlv hnm).1]?
      = some n :=
  EStore.intern_node s.wf

/-- The returned index is in range of the extended arena. -/
theorem intern_lt (s : WFStore) (n : ENode) (hc hlv hnm) :
    (s.intern n hc hlv hnm).1 < (s.intern n hc hlv hnm).2.raw.nodes.size :=
  EStore.intern_lt_size s.wf

/-- Intern one level node. -/
def internL (s : WFStore) (n : LNode)
    (hc : ∀ c ∈ n.children, c < s.raw.lnodes.size) : LIdx × WFStore :=
  let p := s.raw.internL n
  (p.1, ⟨p.2, EStore.internL_wf s.wf hc⟩)

@[simp] theorem internL_raw (s : WFStore) (n : LNode) (hc) :
    (s.internL n hc).2.raw = (s.raw.internL n).2 := rfl

@[simp] theorem internL_idx (s : WFStore) (n : LNode) (hc) :
    (s.internL n hc).1 = (s.raw.internL n).1 := rfl

theorem internL_lt (s : WFStore) (n : LNode) (hc) :
    (s.internL n hc).1 < (s.internL n hc).2.raw.lnodes.size :=
  EStore.internL_lt_size s.wf

/-- Intern one name node. -/
def internN (s : WFStore) (n : NNode)
    (hc : ∀ c ∈ n.children, c < s.raw.nnodes.size) : NIdx × WFStore :=
  let p := s.raw.internN n
  (p.1, ⟨p.2, EStore.internN_wf s.wf hc⟩)

@[simp] theorem internN_raw (s : WFStore) (n : NNode) (hc) :
    (s.internN n hc).2.raw = (s.raw.internN n).2 := rfl

@[simp] theorem internN_idx (s : WFStore) (n : NNode) (hc) :
    (s.internN n hc).1 = (s.raw.internN n).1 := rfl

theorem internN_lt (s : WFStore) (n : NNode) (hc) :
    (s.internN n hc).1 < (s.internN n hc).2.raw.nnodes.size :=
  EStore.internN_lt_size s.wf

/-! ## Checked single-node interning

For callers whose child indices come from untrusted input (the export
parser reads them from translation tables): an `O(children)` runtime
range check per node replaces the deleted one-shot whole-store sweep
(the pre-#103 `wfB`). -/

/-- `intern` with the range side conditions checked at runtime. -/
def intern? (s : WFStore) (n : ENode) : Option (EIdx × WFStore) :=
  if h : n.children.all (· < s.raw.nodes.size)
      && n.levels.all (· < s.raw.lnodes.size)
      && n.names.all (· < s.raw.nnodes.size) then
    have h' : ((∀ c ∈ n.children, c < s.raw.nodes.size) ∧
        (∀ u ∈ n.levels, u < s.raw.lnodes.size)) ∧
        (∀ p ∈ n.names, p < s.raw.nnodes.size) := by
      simpa only [Bool.and_eq_true, List.all_eq_true,
        decide_eq_true_eq] using h
    some (s.intern n h'.1.1 h'.1.2 h'.2)
  else none

/-- `internL` with the range side condition checked at runtime. -/
def internL? (s : WFStore) (n : LNode) : Option (LIdx × WFStore) :=
  if h : n.children.all (· < s.raw.lnodes.size) then
    some (s.internL n (by
      simpa only [List.all_eq_true, decide_eq_true_eq] using h))
  else none

/-- `internN` with the range side condition checked at runtime. -/
def internN? (s : WFStore) (n : NNode) : Option (NIdx × WFStore) :=
  if h : n.children.all (· < s.raw.nnodes.size) then
    some (s.internN n (by
      simpa only [List.all_eq_true, decide_eq_true_eq] using h))
  else none

/-! ## Whole-tree interning (hypothesis-free) -/

/-- Intern a whole name bottom-up. -/
def internName (s : WFStore) (nm : Name) : NIdx × WFStore :=
  let p := s.raw.internName nm
  (p.1, ⟨p.2, (EStore.internName_spec s.wf nm).1⟩)

@[simp] theorem internName_raw (s : WFStore) (nm : Name) :
    (s.internName nm).2.raw = (s.raw.internName nm).2 := rfl

@[simp] theorem internName_idx (s : WFStore) (nm : Name) :
    (s.internName nm).1 = (s.raw.internName nm).1 := rfl

/-- Intern a whole level bottom-up. -/
def internLevel (s : WFStore) (l : Level) : LIdx × WFStore :=
  let p := s.raw.internLevel l
  (p.1, ⟨p.2, (EStore.internLevel_spec s.wf l).1⟩)

@[simp] theorem internLevel_raw (s : WFStore) (l : Level) :
    (s.internLevel l).2.raw = (s.raw.internLevel l).2 := rfl

@[simp] theorem internLevel_idx (s : WFStore) (l : Level) :
    (s.internLevel l).1 = (s.raw.internLevel l).1 := rfl

/-- Intern a list of levels. -/
def internLevels (s : WFStore) (ls : List Level) : List LIdx × WFStore :=
  let p := s.raw.internLevels ls
  (p.1, ⟨p.2, (EStore.internLevels_spec s.wf ls).1⟩)

@[simp] theorem internLevels_raw (s : WFStore) (ls : List Level) :
    (s.internLevels ls).2.raw = (s.raw.internLevels ls).2 := rfl

@[simp] theorem internLevels_idx (s : WFStore) (ls : List Level) :
    (s.internLevels ls).1 = (s.raw.internLevels ls).1 := rfl

/-- Intern binder metadata. -/
def internBM (s : WFStore) (m : BinderMeta) : IBinderMeta × WFStore :=
  let p := s.raw.internBM m
  (p.1, ⟨p.2, (EStore.internBM_spec s.wf m).1⟩)

@[simp] theorem internBM_raw (s : WFStore) (m : BinderMeta) :
    (s.internBM m).2.raw = (s.raw.internBM m).2 := rfl

@[simp] theorem internBM_idx (s : WFStore) (m : BinderMeta) :
    (s.internBM m).1 = (s.raw.internBM m).1 := rfl

/-- Intern a whole expression bottom-up. -/
def internExpr (s : WFStore) (e : Expr) : EIdx × WFStore :=
  let p := s.raw.internExpr e
  (p.1, ⟨p.2, (EStore.internExpr_spec s.wf e).1⟩)

@[simp] theorem internExpr_raw (s : WFStore) (e : Expr) :
    (s.internExpr e).2.raw = (s.raw.internExpr e).2 := rfl

@[simp] theorem internExpr_idx (s : WFStore) (e : Expr) :
    (s.internExpr e).1 = (s.raw.internExpr e).1 := rfl

/-- Intern a whole expression with the boundary codomain-chain fast
path (task #72). -/
def internExprFast (s : WFStore) (e : Expr) : EIdx × WFStore :=
  let p := s.raw.internExprFast e
  (p.1, ⟨p.2, by
    show (s.raw.internExprFast e).2.WF
    rw [EStore.internExprFast_eq s.wf e]
    exact (EStore.internExpr_spec s.wf e).1⟩)

@[simp] theorem internExprFast_raw (s : WFStore) (e : Expr) :
    (s.internExprFast e).2.raw = (s.raw.internExprFast e).2 := rfl

@[simp] theorem internExprFast_idx (s : WFStore) (e : Expr) :
    (s.internExprFast e).1 = (s.raw.internExprFast e).1 := rfl

/-- Pairs of an index and a bundle are equal when their computational
components are (proof irrelevance in the second slot). -/
theorem pair_ext {α : Type} {p q : α × WFStore} (h1 : p.1 = q.1)
    (h2 : p.2.raw = q.2.raw) : p = q := by
  obtain ⟨a, s⟩ := p
  obtain ⟨b, t⟩ := q
  cases h1
  cases WFStore.ext h2
  rfl

/-- On the bundle, the fast path *is* `internExpr` — with no
well-formedness hypothesis (it is in the type). -/
theorem internExprFast_eq_internExpr (s : WFStore) (e : Expr) :
    s.internExprFast e = s.internExpr e := by
  have h := EStore.internExprFast_eq s.wf e
  exact pair_ext (by simp [h]) (by simp [h])

/-! ## Denotation and round-trips (hypothesis-free) -/

/-- Read an interned index back as an `Expr` (spec-level; the
verification's denotation on the raw store). -/
abbrev denote (s : WFStore) : EIdx → Option Expr := s.raw.denote

/-- Read an interned level index back (spec-level). -/
abbrev denoteL (s : WFStore) : LIdx → Option Level := s.raw.denoteL

/-- Read an interned name index back (spec-level). -/
abbrev denoteN (s : WFStore) : NIdx → Option Name := s.raw.denoteN

/-- `internExpr` round-trips through the denotation. -/
theorem internExpr_denote (s : WFStore) (e : Expr) :
    (s.internExpr e).2.denote (s.internExpr e).1 = some e :=
  (EStore.internExpr_spec s.wf e).2.2

/-- Interning only extends the arena. -/
theorem internExpr_ext (s : WFStore) (e : Expr) :
    EStore.Ext s.raw (s.internExpr e).2.raw :=
  (EStore.internExpr_spec s.wf e).2.1

/-- `internLevel` round-trips through the denotation. -/
theorem internLevel_denoteL (s : WFStore) (l : Level) :
    (s.internLevel l).2.denoteL (s.internLevel l).1 = some l :=
  (EStore.internLevel_spec s.wf l).2.2

/-- `internName` round-trips through the denotation. -/
theorem internName_denoteN (s : WFStore) (nm : Name) :
    (s.internName nm).2.denoteN (s.internName nm).1 = some nm :=
  (EStore.internName_spec s.wf nm).2.2

/-- Canonicity: index equality is expression equality — with no
well-formedness hypothesis (it is in the type). -/
theorem denote_eq_iff (s : WFStore) {i j : EIdx} {a b : Expr}
    (ha : s.denote i = some a) (hb : s.denote j = some b) :
    i = j ↔ a = b :=
  EStore.denote_eq_iff s.wf ha hb

/-- Canonicity for names: name-index equality is name equality. -/
theorem denoteN_eq_iff (s : WFStore) {i j : NIdx} {a b : Name}
    (ha : s.denoteN i = some a) (hb : s.denoteN j = some b) :
    i = j ↔ a = b :=
  EStore.denoteN_eq_iff s.wf ha hb

/-! ## Eager derived-field reads with unconditional exactness -/

/-- The eager per-node loose-bvar bound (task #87). -/
@[inline] def bvarBoundD (s : WFStore) (e : EIdx) : Nat :=
  s.raw.bvarBoundD e

/-- The eager per-node fvar range (task #87). -/
@[inline] def fvarRangeD (s : WFStore) (e : EIdx) : Nat :=
  s.raw.fvarRangeD e

/-- The eager per-level-node has-param flag (task #87). -/
@[inline] def lhasParamD (s : WFStore) (u : LIdx) : Bool :=
  s.raw.lhasParamD u

/-- The eager per-node has-level-param flag (task #87). -/
@[inline] def ehasParamD (s : WFStore) (e : EIdx) : Bool :=
  s.raw.ehasParamD e

/-- `O(1)` interned-name readback (task #88). -/
@[inline] def readbackN (s : WFStore) (i : NIdx) : Option Name :=
  s.raw.readbackN i

/-- Memoized whole-tree readback of an interned expression
(pointer-shared, `O(DAG)`). -/
@[inline] def readbackI (s : WFStore) (e : EIdx) : Option Expr :=
  s.raw.readbackI e

/-- Alloc-free comparison of an interned name against a `Name`. -/
@[inline] def beqNameI (s : WFStore) (i : NIdx) (nm : Name) : Bool :=
  s.raw.beqNameI i nm

/-- The eager bound entry is exactly the spec bound of the
denotation. -/
theorem bvarBoundD_exact (s : WFStore) {i : EIdx} {x : Expr}
    (h : s.denote i = some x) : s.bvarBoundD i = x.bvarBound :=
  s.wf.bvarBoundD_exact i h

/-- A bound entry at or below the cursor certifies
`looseBVarsBounded` of the denotation. -/
theorem bvarBoundD_le (s : WFStore) {e : EIdx} {x : Expr} {d : Nat}
    (hx : s.denote e = some x) (hle : s.bvarBoundD e ≤ d) :
    x.looseBVarsBounded d = true :=
  s.wf.bvarBoundD_le hx hle

/-- The eager range entry is exactly the spec range of the
denotation. -/
theorem fvarRangeD_exact (s : WFStore) {i : EIdx} {x : Expr}
    (h : s.denote i = some x) : s.fvarRangeD i = x.fvarRange :=
  s.wf.fvarRangeD_exact i h

/-- The eager level has-param entry is exactly `hasParam` of the
denotation. -/
theorem lhasParamD_exact (s : WFStore) {u : LIdx} {x : Level}
    (h : s.denoteL u = some x) : s.lhasParamD u = x.hasParam :=
  s.wf.lhasParamD_exact u h

/-- The eager has-level-param entry is exactly `hasLevelParam` of the
denotation. -/
theorem ehasParamD_exact (s : WFStore) {i : EIdx} {x : Expr}
    (h : s.denote i = some x) : s.ehasParamD i = x.hasLevelParam :=
  s.wf.ehasParamD_exact i h

/-- The eager readback array agrees with the denotation
everywhere. -/
theorem readbackN_eq_denoteN (s : WFStore) (i : NIdx) :
    s.readbackN i = s.denoteN i :=
  s.wf.readbackN_eq_denoteN i

/-- `beqNameI` decides equality of the denotation. -/
theorem beqNameI_eq (s : WFStore) {i : NIdx} {nm a : Name}
    (h : s.denoteN i = some a) : s.beqNameI i nm = (a == nm) :=
  EStore.beqNameI_eq h

end WFStore

/-! ## The two-tier bundle (task #64)

While tier two is live the store satisfies the two-tier invariant
`EStore.TWF` but not the flag-off `EStore.WF`, so the enabled phase
gets its own bundle: `WFStore.enableTierTwo` moves into `TWFStore`,
tier-blind interning stays inside it, and `TWFStore.truncateTierTwo`
drops tier two wholesale and returns to `WFStore` — with every
tier-one observation untouched (`EStore.truncateTierTwo_*`,
`Setlec/Kernel/ArenaWF.lean`).  Like `WFStore`, the proof field is
erased: the compiled representation is exactly `EStore`. -/

/-- An arena in the tier-two phase: the raw `EStore` together with the
two-tier invariant `EStore.TWF`. -/
structure TWFStore where
  /-- The underlying raw arena. -/
  raw : EStore
  /-- The two-tier invariant. -/
  twf : raw.TWF

/-- Enable tier two (task #64): subsequent interns append to the
tier-two tables; tier one is frozen.  The raw op's guard (the tag
bound, checked once — validate-at-insertion) is what discharges the
invariant; on the impossible guard failure the store simply stays in
the verified flag-off regime. -/
def WFStore.enableTierTwo (s : WFStore) : TWFStore :=
  ⟨s.raw.enableTierTwo, EStore.enableTierTwo_twf s.wf.toTWF⟩

@[simp] theorem WFStore.enableTierTwo_raw (s : WFStore) :
    s.enableTierTwo.raw = s.raw.enableTierTwo := rfl

namespace TWFStore

/-- Two bundles with the same raw store are equal (proof
irrelevance). -/
protected theorem ext : ∀ {s t : TWFStore}, s.raw = t.raw → s = t
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/-- Drop tier two wholesale and return to the flag-off bundle
(task #64): `Array.shrink` keeps the tier-two arrays' capacity; every
tier-one observation is untouched. -/
def truncateTierTwo (s : TWFStore) : WFStore :=
  ⟨s.raw.truncateTierTwo, EStore.truncateTierTwo_wf s.twf⟩

@[simp] theorem truncateTierTwo_raw (s : TWFStore) :
    s.truncateTierTwo.raw = s.raw.truncateTierTwo := rfl

/-- Intern one expression node, tier-blind: the dispatcher appends to
whichever tier is active; the children may be indices of either
tier. -/
def intern (s : TWFStore) (n : ENode)
    (hc : ∀ c ∈ n.children, s.raw.Valid2 c)
    (hlv : ∀ u ∈ n.levels, u < s.raw.lnodes.size)
    (hnm : ∀ p ∈ n.names, p < s.raw.nnodes.size) : EIdx × TWFStore :=
  let p := s.raw.intern n
  (p.1, ⟨p.2, EStore.intern_twf s.twf hc hlv hnm⟩)

@[simp] theorem intern_raw (s : TWFStore) (n : ENode) (hc hlv hnm) :
    (s.intern n hc hlv hnm).2.raw = (s.raw.intern n).2 := rfl

@[simp] theorem intern_idx (s : TWFStore) (n : ENode) (hc hlv hnm) :
    (s.intern n hc hlv hnm).1 = (s.raw.intern n).1 := rfl

/-- The interned node is read back tier-blind at the returned index. -/
theorem intern_getNode (s : TWFStore) (n : ENode) (hc hlv hnm) :
    (s.intern n hc hlv hnm).2.raw.getNode (s.intern n hc hlv hnm).1
      = some n :=
  EStore.intern_getNode s.twf

/-- The returned index is a valid two-tier index of the extended
arena. -/
theorem intern_valid2 (s : TWFStore) (n : ENode) (hc hlv hnm) :
    (s.intern n hc hlv hnm).2.raw.Valid2 (s.intern n hc hlv hnm).1 :=
  EStore.intern_valid2 s.twf

/-- Intern one level node (levels are single-tier). -/
def internL (s : TWFStore) (n : LNode)
    (hc : ∀ c ∈ n.children, c < s.raw.lnodes.size) : LIdx × TWFStore :=
  let p := s.raw.internL n
  (p.1, ⟨p.2, EStore.internL_twf s.twf hc⟩)

@[simp] theorem internL_raw (s : TWFStore) (n : LNode) (hc) :
    (s.internL n hc).2.raw = (s.raw.internL n).2 := rfl

@[simp] theorem internL_idx (s : TWFStore) (n : LNode) (hc) :
    (s.internL n hc).1 = (s.raw.internL n).1 := rfl

/-- Intern one name node (names are single-tier). -/
def internN (s : TWFStore) (n : NNode)
    (hc : ∀ c ∈ n.children, c < s.raw.nnodes.size) : NIdx × TWFStore :=
  let p := s.raw.internN n
  (p.1, ⟨p.2, EStore.internN_twf s.twf hc⟩)

@[simp] theorem internN_raw (s : TWFStore) (n : NNode) (hc) :
    (s.internN n hc).2.raw = (s.raw.internN n).2 := rfl

@[simp] theorem internN_idx (s : TWFStore) (n : NNode) (hc) :
    (s.internN n hc).1 = (s.raw.internN n).1 := rfl

/-! ### Truncation is the identity on tier-one observations

The one theorem the eventual wiring consumes (task #64): dropping tier
two changes no tier-one read — node reads, derived reads, cons hits,
and the denotation are untouched. -/

/-- Truncation is invisible to the denotation, at every index. -/
theorem truncateTierTwo_denote (s : TWFStore) :
    ∀ i, s.truncateTierTwo.raw.denote i = s.raw.denote i :=
  EStore.truncateTierTwo_denote s.raw

/-- Truncation keeps the tier-one node table (so node reads, spine
walks, and cons hits are untouched). -/
theorem truncateTierTwo_nodes (s : TWFStore) :
    s.truncateTierTwo.raw.nodes = s.raw.nodes :=
  EStore.truncateTierTwo_nodes s.raw

@[inherit_doc truncateTierTwo_nodes]
theorem truncateTierTwo_cons (s : TWFStore) :
    s.truncateTierTwo.raw.cons = s.raw.cons :=
  EStore.truncateTierTwo_cons s.raw

/-- Truncation is the identity on `getNode` at tier-one indices. -/
theorem truncateTierTwo_getNode (s : TWFStore) {i : EIdx}
    (h : i < s.raw.nodes.size) :
    s.truncateTierTwo.raw.getNode i = s.raw.getNode i :=
  EStore.truncateTierTwo_getNode h

end TWFStore

/-- The enable/truncate round trip is the identity on the raw
tier-one tables — enabling only sets the flag, truncation only drops
tier two (which starts and ends empty on a `WFStore`). -/
theorem WFStore.enable_truncate_denote (s : WFStore) :
    ∀ i, s.enableTierTwo.truncateTierTwo.raw.denote i = s.raw.denote i :=
  fun i => (EStore.truncateTierTwo_denote _ i).trans
    (EStore.enableTierTwo_denote _ i)

end Setlec

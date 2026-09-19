module

-- `NestedOwnPinsRead` is a FALLBACK re-export: the cut-`0` bridge
-- (`denoteMeta_ownAt_component`) and the dummy-telescope kit this file
-- generalises are stated there, and this file's PUBLIC statements
-- mention both.  `NestedCopyRead` carries `AnnotTerm.instAll_mkPisAV`
-- and `instTeleP_length`, `StructData` carries `mkPisAV_inj`.
public import ConLeche.Model.Inductives.NestedOwnPinsRead
public import ConLeche.Model.Inductives.NestedCopyRead
import ConLeche.Model.Inductives.StructData
import ConLeche.Verify.Inductives.NestedCopyTele
import ConLeche.Verify.InstSpine
import ConLeche.Verify.InstList
import ConLeche.Verify.Inductives.NestedCopyInstU
import ConLeche.Model.Steps.CapsRows
public section

/-!
# A component AT A FIELD'S CUT, read (task #315 WIDE (3), lane LE)

`NestedOwnPinsRead.lean` bridges a container's own pin — a CLOSED term
at the parameter openers, cut `0` — from the syntactic spelling
`PinSyn.ownAt` to its reading.  This module is the same bridge at the
cut a CONSTRUCTOR FIELD sits at.

**What moves.**  A stored container's own-pin table holds whole pins,
which stand at the `nP` parameter openers and nothing else.  A rewritten
ordinary field's DOMAIN — the term K.69's recomputation names
(`ordTargetDom`, the owner's own reading of a container field) — stands
at those same openers *and* under the constructor's `l` EARLIER FIELD
BINDERS, and at a reflexive field under its own `Π`-tower as well.  So
the term has `cut = l (+ domPiDepth)` LOOSE bound variables where the
own-pin table's entries have none, and `denoteMeta` has no `bvar` arm:
a term with a loose bound variable does not read at all.  The reading
has to happen with those `cut` binders OPENED, and the bridge has to
carry the opening across the opener substitution.

**The route, and why it is a reduction and not a second copy of the
cut-`0` file.**  Wrap the cut-`cut` term in `cut` DUMMY binders
(`dummyPisM`, the existing `dummyPis` with the binder datum an
argument).  The wrapped term is bvar-closed and has the same `fvar`
leaves, so the cut-`0` bridge applies to it VERBATIM; the dummy tower
commutes with each of the three operations the spelling performs —
`Expr.abstractRange` (the cursor moves out by `cut`),
`Expr.instantiateLevelParams` (the binder datum is substituted, which
is why the kit is parametric in it) and `Expr.instSeq` (each cut moves
out by `cut`) — and `denoteMeta` on the wrapped term is the tower over
the opened body's reading, in both directions
(`denoteMeta_mkPisB_dummyPis` and its inversion here).  What the cut-`0`
bridge returns is then `AnnotTerm.instAll Ds 0` of a `mkPisAV`, which
`AnnotTerm.instAll_mkPisAV` splits into the tower and
`AnnotTerm.instAll Ds cut` of the body — and `mkPisAV_inj` reads the
body off.

So `denoteMeta_ownAt_component`'s 93 lines are NOT redone and the
`dummyPis` scope kit is NOT generalised to "live" binders: the live
binders are opened on BOTH sides by the same `Verify.openFvars`, and
the wrapper is what carries them across.  The one thing that had to be
generalised is the binder DATUM, because `instantiateLevelParams`
rewrites it (`Level.substPW`) and the dummy tower is under the level
instantiation on the spelled side.

**`instPisILP_read`'s `hDs`** (`NestedCopyRead.lean:94`) — the
constraint the pricing named as the hard one — is met unchanged: it
constrains the COMPONENTS `DsE`, not the term being read, and the
components are the reader's, scoped at the reader's own depth `dp`.
The cut does not touch them; it is the term that moves, and it moves
inside the wrapper, below the cut-`0` bridge's own `instPisILP_read`
call.  Nothing in this file calls `instPisILP_read` at all.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## The dummy telescope at an arbitrary binder datum -/

/-- **`dummyPis` with the binder datum an argument.**  The domains are
still the closed `Sort 0`; only the datum varies, and it has to,
because `Expr.instantiateLevelParams` rewrites a binder's datum
(`Level.substPW`) and the spelled side wraps the tower UNDER that
instantiation. -/
def dummyPisM (bm : ConLeche.BinderMeta) : Nat → List (Expr × ConLeche.BinderMeta)
  | 0 => []
  | n + 1 => (Expr.sort Level.zero, bm) :: dummyPisM bm n

/-- The dummy tower under one substitution: the domains are closed, so
only the body moves, and it moves to the cut below the whole tower. -/
theorem mkPisB_dummyPisM_instantiate1 (bm : ConLeche.BinderMeta) (v : Expr) :
    ∀ (n j : Nat) (y : Expr),
      (ConLeche.mkPisB (dummyPisM bm n) y).instantiate1 v j
        = ConLeche.mkPisB (dummyPisM bm n) (y.instantiate1 v (j + n))
  | 0, j, y => by
    show (ConLeche.mkPisB [] y).instantiate1 v j
      = ConLeche.mkPisB [] (y.instantiate1 v (j + 0))
    rw [mkPisB_nil, mkPisB_nil, Nat.add_zero]
  | n + 1, j, y => by
    show (ConLeche.mkPisB ((Expr.sort Level.zero, bm) :: dummyPisM bm n) y).instantiate1 v j
      = ConLeche.mkPisB ((Expr.sort Level.zero, bm) :: dummyPisM bm n)
          (y.instantiate1 v (j + (n + 1)))
    rw [mkPisB_cons, mkPisB_cons]
    show Expr.forallE ((Expr.sort Level.zero).instantiate1 v j)
        ((ConLeche.mkPisB (dummyPisM bm n) y).instantiate1 v (j + 1)) bm = _
    rw [mkPisB_dummyPisM_instantiate1 bm v n (j + 1) y,
      show j + 1 + n = j + (n + 1) from by omega]
    rfl

/-- The dummy tower under a whole spine: each cut moves out by the
tower's depth.  The length side condition is what the descending cuts
of `Expr.instSeq` need — at `t = 0` the list is already exhausted. -/
theorem instSeq_mkPisB_dummyPisM (bm : ConLeche.BinderMeta) :
    ∀ (as : List Expr) (t n : Nat) (y : Expr), as.length ≤ t + 1 →
      Expr.instSeq as t (ConLeche.mkPisB (dummyPisM bm n) y)
        = ConLeche.mkPisB (dummyPisM bm n) (Expr.instSeq as (t + n) y)
  | [], _, _, _, _ => rfl
  | a :: as, t, n, y, hlen => by
    show Expr.instSeq as (t - 1) ((ConLeche.mkPisB (dummyPisM bm n) y).instantiate1 a t) = _
    rw [mkPisB_dummyPisM_instantiate1]
    cases t with
    | zero =>
      obtain rfl : as = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      show ConLeche.mkPisB (dummyPisM bm n) (y.instantiate1 a (0 + n)) = _
      rfl
    | succ t =>
      have hih := instSeq_mkPisB_dummyPisM bm as t n (y.instantiate1 a (t + 1 + n))
        (by simpa using hlen)
      show Expr.instSeq as t (ConLeche.mkPisB (dummyPisM bm n)
        (y.instantiate1 a (t + 1 + n))) = _
      rw [hih]
      show _ = ConLeche.mkPisB (dummyPisM bm n)
        (Expr.instSeq as (t + 1 + n - 1) (y.instantiate1 a (t + 1 + n)))
      rw [show t + 1 + n - 1 = t + n from by omega]

/-- The dummy tower under a closing pass: the cursor moves out by the
tower's depth, and the closed domains are untouched. -/
theorem abstractRange_mkPisB_dummyPisM (bm : ConLeche.BinderMeta) :
    ∀ (n : Nat) (y : Expr) (d k c : Nat),
      Expr.abstractRange (ConLeche.mkPisB (dummyPisM bm n) y) d k c
        = ConLeche.mkPisB (dummyPisM bm n) (Expr.abstractRange y d k (c + n))
  | 0, y, d, k, c => by
    show Expr.abstractRange (ConLeche.mkPisB [] y) d k c
      = ConLeche.mkPisB [] (Expr.abstractRange y d k (c + 0))
    rw [mkPisB_nil, mkPisB_nil, Nat.add_zero]
  | n + 1, y, d, k, c => by
    show Expr.abstractRange (ConLeche.mkPisB
      ((Expr.sort Level.zero, bm) :: dummyPisM bm n) y) d k c
      = ConLeche.mkPisB ((Expr.sort Level.zero, bm) :: dummyPisM bm n)
          (Expr.abstractRange y d k (c + (n + 1)))
    rw [mkPisB_cons, mkPisB_cons]
    show Expr.forallE (Expr.abstractRange (Expr.sort Level.zero) d k c)
        (Expr.abstractRange (ConLeche.mkPisB (dummyPisM bm n) y) d k (c + 1)) bm = _
    rw [abstractRange_mkPisB_dummyPisM bm n y d k (c + 1),
      show c + 1 + n = c + (n + 1) from by omega]
    rfl

/-- The dummy tower under a level instantiation: the domains are
`Sort 0`, which no level substitution moves, and the binder DATUM is
substituted — which is the whole reason the kit carries it. -/
theorem instantiateLevelParams_mkPisB_dummyPisM (bm : ConLeche.BinderMeta)
    (ks : List Name) (us : List Level) :
    ∀ (n : Nat) (y : Expr),
      Expr.instantiateLevelParams ks us (ConLeche.mkPisB (dummyPisM bm n) y)
        = ConLeche.mkPisB (dummyPisM ⟨Level.substPW ks us bm.pw⟩ n)
            (Expr.instantiateLevelParams ks us y)
  | 0, y => by
    show Expr.instantiateLevelParams ks us (ConLeche.mkPisB [] y)
      = ConLeche.mkPisB [] (Expr.instantiateLevelParams ks us y)
    rw [mkPisB_nil, mkPisB_nil]
  | n + 1, y => by
    show Expr.instantiateLevelParams ks us
        (ConLeche.mkPisB ((Expr.sort Level.zero, bm) :: dummyPisM bm n) y)
      = ConLeche.mkPisB ((Expr.sort Level.zero, ⟨Level.substPW ks us bm.pw⟩)
          :: dummyPisM ⟨Level.substPW ks us bm.pw⟩ n) (Expr.instantiateLevelParams ks us y)
    rw [mkPisB_cons, mkPisB_cons]
    show Expr.forallE (Expr.instantiateLevelParams ks us (Expr.sort Level.zero))
        (Expr.instantiateLevelParams ks us (ConLeche.mkPisB (dummyPisM bm n) y))
        ⟨Level.substPW ks us bm.pw⟩ = _
    rw [instantiateLevelParams_mkPisB_dummyPisM bm ks us n y]
    rfl

/-- The wrapper adds no `fvar` leaf: its domains are closed sorts. -/
theorem fvarLeaves_mkPisB_dummyPisM (bm : ConLeche.BinderMeta) :
    ∀ (n : Nat) (y : Expr), (ConLeche.mkPisB (dummyPisM bm n) y).fvarLeaves = y.fvarLeaves
  | 0, y => by
    show (ConLeche.mkPisB [] y).fvarLeaves = y.fvarLeaves
    rw [mkPisB_nil]
  | n + 1, y => by
    show (ConLeche.mkPisB ((Expr.sort Level.zero, bm) :: dummyPisM bm n) y).fvarLeaves
      = y.fvarLeaves
    rw [mkPisB_cons]
    simp only [Expr.fvarLeaves, List.nil_append]
    exact fvarLeaves_mkPisB_dummyPisM bm n y

/-- The wrapper absorbs `n` loose bound variables. -/
theorem looseBVarsBounded_mkPisB_dummyPisM (bm : ConLeche.BinderMeta) :
    ∀ (n d : Nat) (y : Expr),
      y.looseBVarsBounded (d + n) = true →
        (ConLeche.mkPisB (dummyPisM bm n) y).looseBVarsBounded d = true
  | 0, d, y, h => by
    show Expr.looseBVarsBounded d (ConLeche.mkPisB [] y) = true
    rw [mkPisB_nil]; simpa using h
  | n + 1, d, y, h => by
    show Expr.looseBVarsBounded d
      (ConLeche.mkPisB ((Expr.sort Level.zero, bm) :: dummyPisM bm n) y) = true
    rw [mkPisB_cons]
    simp only [Expr.looseBVarsBounded, Bool.true_and]
    exact looseBVarsBounded_mkPisB_dummyPisM bm n (d + 1) y
      (by rw [show d + 1 + n = d + (n + 1) from by omega]; exact h)

/-- **The dummy tower reads as a tower over its body's OPENED
reading**, at an arbitrary binder datum: `denoteMeta` on a `∀` already
reads the body opened at the binder's own variable one depth up, and
the dummy domains plant exactly `Verify.openFvars`' openers. -/
theorem denoteMeta_mkPisB_dummyPisM {acval : Name → (Name → Nat) → AnnotTerm}
    {φ : Name → Nat} (bm : ConLeche.BinderMeta) :
    ∀ (n d : Nat) (y : Expr) (r : AnnotTerm),
      denoteMeta acval env φ (d + n)
          (Expr.instSeq (Verify.openFvars d n) (n - 1) y) = some r →
      ∃ pps : List (Nat × Nat × AnnotTerm), pps.length = n ∧
        denoteMeta acval env φ d (ConLeche.mkPisB (dummyPisM bm n) y) = some (mkPisAV pps r)
  | 0, _, _, _, h => ⟨[], rfl, h⟩
  | n + 1, d, y, r, h => by
    have hop : Expr.instSeq (Verify.openFvars d (n + 1)) (n + 1 - 1) y
        = Expr.instSeq (Verify.openFvars (d + 1) n) (n - 1)
            (y.instantiate1 (Expr.fvar d (.sort .zero)) n) := by
      rw [Verify.openFvars_succ]
      rfl
    rw [hop, show d + (n + 1) = d + 1 + n from by omega] at h
    obtain ⟨pps, hlen, hpps⟩ :=
      denoteMeta_mkPisB_dummyPisM bm n (d + 1)
        (y.instantiate1 (Expr.fvar d (.sort .zero)) n) r h
    refine ⟨(0, pwBit φ bm.pw, .sort (Level.eval φ Level.zero)) :: pps,
      by rw [List.length_cons, hlen], ?_⟩
    have hbody : (ConLeche.mkPisB (dummyPisM bm n) y).instantiate1
          (Expr.fvar d (.sort .zero))
        = ConLeche.mkPisB (dummyPisM bm n)
            (y.instantiate1 (Expr.fvar d (.sort .zero)) n) := by
      rw [mkPisB_dummyPisM_instantiate1, Nat.zero_add]
    show denoteMeta acval env φ d (ConLeche.mkPisB
      ((Expr.sort Level.zero, bm) :: dummyPisM bm n) y) = _
    rw [mkPisB_cons, denoteMeta_forallE, denoteMeta_sort, hbody, hpps]
    rfl

/-! ## The dummy tower's reading, INVERTED

`denoteMeta_mkPisB_dummyPis` (`NestedOwnPinsRead.lean`) builds the
tower's reading from the opened body's.  The bridge below needs the
other direction: the cut-`0` bridge hands back a reading OF the tower,
and the body's is what the consumer wants. -/

/-- **The dummy tower's reading determines its opened body's.**  The
converse of `denoteMeta_mkPisB_dummyPis`, at an arbitrary binder
datum: a `∀` reads its body already opened at the binder's own
variable, and the dummy domains plant exactly `Verify.openFvars`'
openers. -/
theorem denoteMeta_mkPisB_dummyPisM_inv {acval : Name → (Name → Nat) → AnnotTerm}
    {φ : Name → Nat} (bm : ConLeche.BinderMeta) :
    ∀ (n d : Nat) (y : Expr) (ea : AnnotTerm),
      denoteMeta acval env φ d (ConLeche.mkPisB (dummyPisM bm n) y) = some ea →
      ∃ (pps : List (Nat × Nat × AnnotTerm)) (r : AnnotTerm),
        pps.length = n ∧ ea = mkPisAV pps r ∧
        denoteMeta acval env φ (d + n)
          (Expr.instSeq (Verify.openFvars d n) (n - 1) y) = some r
  | 0, d, y, ea, h => by
    refine ⟨[], ea, rfl, rfl, ?_⟩
    rw [Nat.add_zero]
    show denoteMeta acval env φ d y = some ea
    exact h
  | n + 1, d, y, ea, h => by
    have h' : denoteMeta acval env φ d
        (Expr.forallE (Expr.sort Level.zero) (ConLeche.mkPisB (dummyPisM bm n) y) bm)
          = some ea := h
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv h'
    rw [mkPisB_dummyPisM_instantiate1, Nat.zero_add] at hba
    obtain ⟨pps, r, hlen, rfl, hbody⟩ :=
      denoteMeta_mkPisB_dummyPisM_inv bm n (d + 1)
        (y.instantiate1 (Expr.fvar d (Expr.sort Level.zero)) n) ba hba
    refine ⟨(0, pwBit φ bm.pw, ta) :: pps, r, by rw [List.length_cons, hlen], rfl, ?_⟩
    have hop : Expr.instSeq (Verify.openFvars d (n + 1)) (n + 1 - 1) y
        = Expr.instSeq (Verify.openFvars (d + 1) n) (n - 1)
            (y.instantiate1 (Expr.fvar d (.sort .zero)) n) := by
      rw [Verify.openFvars_succ]
      rfl
    rw [hop, show d + (n + 1) = d + 1 + n from by omega]
    exact hbody

/-! ## THE SUBSTITUTION LAW AT A FIELD'S CUT -/

/-- **A RECORDED TERM AT A FIELD'S CUT, SPELLED AT ANOTHER
INSTANTIATION, READS AS ITS RECORDED READING INSTANTIATED**
(task #315 WIDE (3), lane LE) — `denoteMeta_ownAt_component`'s twin at
cut `cut`.

`x` stands at the container's `nP` parameter openers (`hxlv`/`hidx`)
and under `cut` further binders it leaves LOOSE (`hxb`) — a
constructor's earlier fields, plus a reflexive field's own `Π`-tower.
Its recorded reading `rx` is therefore taken with those `cut` binders
OPENED (`hread`, `Verify.openFvars nP cut` at depth `nP + cut`).

The spelling closes `x` over the parameters AT THE CUT
(`Expr.abstractRange … 0 nP cut` — the cut is where the openers must
land, since abstracting at `0` would collide with the loose binders
below), substitutes the level arguments and re-opens at the components
`DsE` the reader was asked for, at the cut the spine's own depth adds
(`nP - 1 + cut`).  Read with the SAME `cut` binders opened, that is the
recorded reading with the components' readings substituted at the cut —
`AnnotTerm.instAll Ds cut`, which is the shape `CopyCtorShape`'s field
clauses are stated in.

This is `ordRootInst`'s (K.69) model-side law: the kernel's
`Expr.instantiateList … cut` at the reversed spine IS this `Expr.instSeq`
at the descending cuts (`Expr.instSpine_eq_instantiateList_at` with
`Expr.instSpine_eq_instSeq`), and the abstraction starting AT the cut is
the same correction K.69 records for the same reason. -/
theorem denoteMeta_ownAt_component_at {env : Env} (m : EnvModel V env) {ψ : Name → Nat}
    {lps : List Name} {lvls : List Level} {nP dp cut : Nat}
    {params DsE : List Expr} {Ds : List AnnotTerm} {x : Expr} {rx : AnnotTerm}
    (hplen : params.length = nP)
    (hidx : ∀ j, j < nP → ∃ ty, params[j]? = some (Expr.fvar j ty))
    (hxb : x.looseBVarsBounded cut = true)
    (hxlv : ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ params)
    (hDlen : DsE.length = nP)
    (hDs : ∀ a ∈ DsE, Expr.WScoped dp a ∧ a.looseBVarsBounded 0 = true)
    (hspine : DenoteMetaSpine m.acval env ψ dp DsE Ds)
    (hread : denoteMeta m.acval env (Level.substFn ψ lps lvls) (nP + cut)
      (Expr.instSeq (Verify.openFvars nP cut) (cut - 1) x) = some rx) :
    denoteMeta m.acval env ψ (dp + cut)
        (Expr.instSeq (Verify.openFvars dp cut) (cut - 1)
          (Expr.instSeq DsE (nP - 1 + cut)
            (Expr.instantiateLevelParams lps lvls (Expr.abstractRange x 0 nP cut))))
      = some (AnnotTerm.instAll Ds cut rx) := by
  classical
  -- the wrapped term: bvar-closed, the same `fvar` leaves
  have hXb : (ConLeche.mkPisB (dummyPisM default cut) x).looseBVarsBounded 0 = true :=
    looseBVarsBounded_mkPisB_dummyPisM default cut 0 x (by simpa using hxb)
  have hXlv : ∀ l ∈ (ConLeche.mkPisB (dummyPisM default cut) x).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ params := by
    intro l hl
    refine hxlv l ?_
    rw [fvarLeaves_mkPisB_dummyPisM] at hl
    exact hl
  -- the wrapped term's own reading: the tower over `rx`
  obtain ⟨pps, hppsLen, hXread⟩ :=
    denoteMeta_mkPisB_dummyPisM (acval := m.acval) (φ := Level.substFn ψ lps lvls)
      default cut nP x rx hread
  -- the cut-`0` bridge, at the wrapped term
  have h0 := denoteMeta_ownAt_component m hplen hidx hXb hXlv hDlen hDs hspine hXread
  -- the spelled side, rewritten into the tower over the cut-`cut` spelling
  have hZ : Expr.instSeq DsE (DsE.length - 1)
        (Expr.instantiateLevelParams lps lvls
          (Expr.abstractRange (ConLeche.mkPisB (dummyPisM default cut) x) 0 nP 0))
      = ConLeche.mkPisB (dummyPisM ⟨Level.substPW lps lvls (default : ConLeche.BinderMeta).pw⟩ cut)
          (Expr.instSeq DsE (nP - 1 + cut)
            (Expr.instantiateLevelParams lps lvls (Expr.abstractRange x 0 nP cut))) := by
    rw [abstractRange_mkPisB_dummyPisM, Nat.zero_add,
      instantiateLevelParams_mkPisB_dummyPisM, hDlen,
      instSeq_mkPisB_dummyPisM _ DsE (nP - 1) cut _ (by rw [hDlen]; omega)]
  rw [hZ] at h0
  -- the answer's tower, split
  have hsplit : AnnotTerm.instAll Ds 0 (mkPisAV pps rx)
      = mkPisAV (instTeleP Ds 0 pps) (AnnotTerm.instAll Ds cut rx) := by
    rw [AnnotTerm.instAll_mkPisAV, hppsLen, Nat.zero_add]
  rw [hsplit] at h0
  -- the tower's reading determines the opened body's
  obtain ⟨qs, r, hqsLen, heq, hbody⟩ :=
    denoteMeta_mkPisB_dummyPisM_inv (env := env) (acval := m.acval) (φ := ψ)
      ⟨Level.substPW lps lvls (default : ConLeche.BinderMeta).pw⟩ cut dp _ _ h0
  obtain ⟨-, rfl⟩ := mkPisAV_inj (by rw [instTeleP_length, hqsLen]; exact hppsLen) heq
  exact hbody

/-! ## THE KERNEL'S OWN SPELLING (`ordRootInst`, K.69) -/

/-- **Closing over the parameters and substituting the levels
commute.**  `Expr.abstractRange` replaces an `fvar` in range by a
`bvar`, dropping its annotation, and leaves everything else's shape
alone; `Expr.instantiateLevelParams` touches only sorts, constants'
level arguments and binder data.  `ordRootInst` (K.69) performs the two
in the order `abstractRange ∘ instantiateLevelParams`, and
`denoteMeta_ownAt_component_at` inherits the other order from the
cut-`0` bridge; this is what identifies them. -/
theorem abstractRange_instantiateLevelParams (ks : List Name) (us : List Level) :
    ∀ (e : Expr) (d k c : Nat),
      Expr.abstractRange (Expr.instantiateLevelParams ks us e) d k c
        = Expr.instantiateLevelParams ks us (Expr.abstractRange e d k c) := by
  intro e
  induction e with
  | bvar i => intro _ _ _; rfl
  | sort u => intro _ _ _; rfl
  | const n us' => intro _ _ _; rfl
  | lit l => intro _ _ _; rfl
  | fvar idx ty _ =>
    intro d k c
    show Expr.abstractRange (Expr.fvar idx (Expr.instantiateLevelParams ks us ty)) d k c = _
    by_cases h : d ≤ idx ∧ idx < d + k
    · rw [Expr.abstractRange, if_pos h, Expr.abstractRange, if_pos h]; rfl
    · rw [Expr.abstractRange, if_neg h, Expr.abstractRange, if_neg h]; rfl
  | app f a ihf iha =>
    intro d k c
    show Expr.abstractRange (Expr.app (Expr.instantiateLevelParams ks us f)
      (Expr.instantiateLevelParams ks us a)) d k c = _
    rw [Expr.abstractRange, ihf, iha]; rfl
  | lam ty b m ihty ihb =>
    intro d k c
    show Expr.abstractRange (Expr.lam (Expr.instantiateLevelParams ks us ty)
      (Expr.instantiateLevelParams ks us b) ⟨Level.substPW ks us m.pw⟩) d k c = _
    rw [Expr.abstractRange, ihty, ihb]; rfl
  | forallE ty b m ihty ihb =>
    intro d k c
    show Expr.abstractRange (Expr.forallE (Expr.instantiateLevelParams ks us ty)
      (Expr.instantiateLevelParams ks us b) ⟨Level.substPW ks us m.pw⟩) d k c = _
    rw [Expr.abstractRange, ihty, ihb]; rfl
  | letE ty v b ihty ihv ihb =>
    intro d k c
    show Expr.abstractRange (Expr.letE (Expr.instantiateLevelParams ks us ty)
      (Expr.instantiateLevelParams ks us v) (Expr.instantiateLevelParams ks us b)) d k c = _
    rw [Expr.abstractRange, ihty, ihv, ihb]; rfl
  | proj sn i x ih =>
    intro d k c
    show Expr.abstractRange (Expr.proj sn i (Expr.instantiateLevelParams ks us x)) d k c = _
    rw [Expr.abstractRange, ih]; rfl

/-- **THE BRIDGE AT `ordRootInst`'s OWN SPELLING** (task #315 WIDE (3),
lane LE): `denoteMeta_ownAt_component_at` with the kernel's bulk form
in place of the `instantiate1` fold.

K.69's `ordRootInst` writes the one substitution that carries a
root-era term into the block's scope as

    Expr.instantiateList
      (Expr.abstractRange (W.instantiateLevelParams lpsJ lvlsJ) 0 nPJ cut)
      ((pinG.getAppArgs.take nPJ).reverse) cut

— the KERNEL may not name `Expr.instSeq`, which lives in `Verify`
(`instantiateList_openers_eq_instSeq` carries the same note).  This is
that term read: the components are `DsE`, the abstraction starts AT the
cut, and the reading is the recorded one with the components' readings
substituted at the cut. -/
theorem denoteMeta_ordRootInst_read {env : Env} (m : EnvModel V env) {ψ : Name → Nat}
    {lps : List Name} {lvls : List Level} {nP dp cut : Nat}
    {params DsE : List Expr} {Ds : List AnnotTerm} {x : Expr} {rx : AnnotTerm}
    (hplen : params.length = nP)
    (hidx : ∀ j, j < nP → ∃ ty, params[j]? = some (Expr.fvar j ty))
    (hxb : x.looseBVarsBounded cut = true)
    (hxlv : ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ params)
    (hDlen : DsE.length = nP)
    (hDs : ∀ a ∈ DsE, Expr.WScoped dp a ∧ a.looseBVarsBounded 0 = true)
    (hspine : DenoteMetaSpine m.acval env ψ dp DsE Ds)
    (hread : denoteMeta m.acval env (Level.substFn ψ lps lvls) (nP + cut)
      (Expr.instSeq (Verify.openFvars nP cut) (cut - 1) x) = some rx) :
    denoteMeta m.acval env ψ (dp + cut)
        (Expr.instSeq (Verify.openFvars dp cut) (cut - 1)
          (Expr.instantiateList
            (Expr.abstractRange (Expr.instantiateLevelParams lps lvls x) 0 nP cut)
            DsE.reverse cut))
      = some (AnnotTerm.instAll Ds cut rx) := by
  have hbulk : Expr.instantiateList
        (Expr.abstractRange (Expr.instantiateLevelParams lps lvls x) 0 nP cut)
        DsE.reverse cut
      = Expr.instSeq DsE (nP - 1 + cut)
          (Expr.instantiateLevelParams lps lvls (Expr.abstractRange x 0 nP cut)) := by
    rw [← Expr.instSpine_eq_instantiateList_at, Expr.instSpine_eq_instSeq,
      abstractRange_instantiateLevelParams, hDlen]
    cases nP with
    | zero =>
      obtain rfl : DsE = [] := List.eq_nil_of_length_eq_zero hDlen
      rfl
    | succ n => rw [show cut + (n + 1) - 1 = n + 1 - 1 + cut from by omega]
  rw [hbulk]
  exact denoteMeta_ownAt_component_at m hplen hidx hxb hxlv hDlen hDs hspine hread

/-- **THE REWRITTEN DOMAIN, READ AT THE OPENERS, IN TERMS OF ITS
ARGUMENTS' READINGS** (task #315 WIDE (3), lane LE) — what the pin
half's `Eis` clause consumes.

A copy-field domain the owner's elimination REWROTE is headed by a
constant: the pin the rewrite planted (`replaceIfNested` always writes
one), or a member of the owner's own group.  Read at the owner's
parameter openers under the field's `cut` binders, such a domain is
that head's reading applied to its arguments' — and carried to the
block's scope by `ordRootInst`, it is the SAME head applied to those
readings INSTANTIATED at the components, position by position.

The head does not move (`AnnotTerm.instAll_eq_self` at `hfa`, which a
constant's value satisfies — `EnvModel.acval_inst_self`), which is
what makes the equation an equation between SPINES: the block's side's
index expressions are the owner's, `AnnotTerm.instAll Ds cut` applied. -/
theorem denoteMeta_ordRootInst_mkAppN_read {env : Env} (m : EnvModel V env) {ψ : Name → Nat}
    {lps : List Name} {lvls : List Level} {nP dp cut : Nat}
    {params DsE : List Expr} {Ds : List AnnotTerm}
    {J : Name} {lvlsJ : List Level} {es : List Expr}
    {fa : AnnotTerm} {Eis : List AnnotTerm}
    (hplen : params.length = nP)
    (hidx : ∀ j, j < nP → ∃ ty, params[j]? = some (Expr.fvar j ty))
    (hxb : (Expr.mkAppN (Expr.const J lvlsJ) es).looseBVarsBounded cut = true)
    (hxlv : ∀ l ∈ (Expr.mkAppN (Expr.const J lvlsJ) es).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ params)
    (hDlen : DsE.length = nP)
    (hDs : ∀ a ∈ DsE, Expr.WScoped dp a ∧ a.looseBVarsBounded 0 = true)
    (hspine : DenoteMetaSpine m.acval env ψ dp DsE Ds)
    (hhead : denoteMeta m.acval env (Level.substFn ψ lps lvls) (nP + cut)
      (Expr.const J lvlsJ) = some fa)
    (hfa : ∀ (y : AnnotTerm) (k : Nat), fa.inst y k = fa)
    (hargs : DenoteMetaSpine m.acval env (Level.substFn ψ lps lvls) (nP + cut)
      (es.map (Expr.instSeq (Verify.openFvars nP cut) (cut - 1))) Eis) :
    denoteMeta m.acval env ψ (dp + cut)
        (Expr.instSeq (Verify.openFvars dp cut) (cut - 1)
          (Expr.instantiateList
            (Expr.abstractRange (Expr.instantiateLevelParams lps lvls
              (Expr.mkAppN (Expr.const J lvlsJ) es)) 0 nP cut)
            DsE.reverse cut))
      = some (AnnotTerm.mkAppN fa (Eis.map (AnnotTerm.instAll Ds cut))) := by
  have hx : denoteMeta m.acval env (Level.substFn ψ lps lvls) (nP + cut)
      (Expr.instSeq (Verify.openFvars nP cut) (cut - 1)
        (Expr.mkAppN (Expr.const J lvlsJ) es))
      = some (AnnotTerm.mkAppN fa Eis) := by
    rw [ConLeche.instSeq_mkAppN_const]
    exact denoteMeta_mkAppN hargs hhead
  rw [denoteMeta_ordRootInst_read m hplen hidx hxb hxlv hDlen hDs hspine hx,
    AnnotTerm.instAll_mkAppN, AnnotTerm.instAll_eq_self hfa]

/-! ## THE TWO COPIES' INDEX EXPRESSIONS, RELATED -/

/-- **THE TWO COPIES OF ONE CONTAINER FIELD CARRY ONE INDEX SPINE, ONE
INSTANTIATION APART** (task #315 WIDE (3), lane LE) — the bridge and
K.69 composed, which is the equation the wide identification's pin half
asks `hslotOrd` for at the `ordF` guard.

The OWNER read its rewritten copy-field domain at its own parameter
openers and recorded the arguments' readings as `Eis₂`
(`hhead`/`hargs`, `denoteMeta_ordRootInst_mkAppN_read`'s own inputs).
The BLOCK read ITS copy of the same field — the term `Wb` — at the
block's openers and recorded `Eis₁` (`hreadB`).  K.69 (`hK69`, read as
a term equation by `nestedOrdNormOk_at_pi`) says `Wb` IS the owner's
domain at `ordRootInst`'s spelling; the bridge reads that spelling as
the owner's head applied to `Eis₂` with `AnnotTerm.instAll Ds cut`
applied POSITION BY POSITION, the head not moving.  So the two
readings are two `mkAppN`s of one arity, and `AnnotTerm.mkAppN_inj`
reads the spines off.

**Both sides' readings are premises, and that is the point.**  Neither
is derivable here: a copy's recorded index expressions are tied to its
own rewritten domain by the install that made it, and at this guard
that tie is carried by no clause on either model — the object the
lane's ledger names as step 2's remaining content.  What this theorem
settles is everything AFTER those two readings, so that when they
arrive the comparison is one application and not an argument. -/
theorem ordSpine_inst_of_reads {env : Env} (m : EnvModel V env) {ψ : Name → Nat}
    {lps : List Name} {lvls : List Level} {nP dp cut : Nat}
    {params DsE : List Expr} {Ds : List AnnotTerm}
    {J : Name} {lvlsJ : List Level} {es : List Expr} {Wb : Expr}
    {fa fb : AnnotTerm} {Eis₁ Eis₂ : List AnnotTerm}
    (hplen : params.length = nP)
    (hidx : ∀ j, j < nP → ∃ ty, params[j]? = some (Expr.fvar j ty))
    (hxb : (Expr.mkAppN (Expr.const J lvlsJ) es).looseBVarsBounded cut = true)
    (hxlv : ∀ l ∈ (Expr.mkAppN (Expr.const J lvlsJ) es).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ params)
    (hDlen : DsE.length = nP)
    (hDs : ∀ a ∈ DsE, Expr.WScoped dp a ∧ a.looseBVarsBounded 0 = true)
    (hspine : DenoteMetaSpine m.acval env ψ dp DsE Ds)
    (hhead : denoteMeta m.acval env (Level.substFn ψ lps lvls) (nP + cut)
      (Expr.const J lvlsJ) = some fa)
    (hfa : ∀ (y : AnnotTerm) (k : Nat), fa.inst y k = fa)
    (hargs : DenoteMetaSpine m.acval env (Level.substFn ψ lps lvls) (nP + cut)
      (es.map (Expr.instSeq (Verify.openFvars nP cut) (cut - 1))) Eis₂)
    (hK69 : Wb = Expr.instantiateList
      (Expr.abstractRange (Expr.instantiateLevelParams lps lvls
        (Expr.mkAppN (Expr.const J lvlsJ) es)) 0 nP cut)
      DsE.reverse cut)
    (hreadB : denoteMeta m.acval env ψ (dp + cut)
        (Expr.instSeq (Verify.openFvars dp cut) (cut - 1) Wb)
      = some (AnnotTerm.mkAppN fb Eis₁))
    (hlen : Eis₁.length = Eis₂.length) :
    fb = fa ∧ Eis₁ = Eis₂.map (AnnotTerm.instAll Ds cut) := by
  rw [hK69,
    denoteMeta_ordRootInst_mkAppN_read m hplen hidx hxb hxlv hDlen hDs hspine hhead hfa hargs
      (J := J) (lvlsJ := lvlsJ) (es := es)] at hreadB
  exact AnnotTerm.mkAppN_inj (Option.some.inj hreadB).symm
    (by rw [hlen, List.length_map])

end ConLeche.Model

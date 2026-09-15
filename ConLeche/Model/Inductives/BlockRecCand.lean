module

public import ConLeche.Model.Inductives.BlockRep
public import ConLeche.SetModel.UnionRec
public import ConLeche.Semantics.Tower.FixRecCoreI
public import ConLeche.Semantics.Tower.FixSquashI
public section

/-!
# The block's recursor candidate, over the datum (task #315, M3)

The uniform route's recursors are the projections of ONE chosen tuple
pinned by its ι equations (DESIGN §U.4, `Semantics/Tower/SigChainI.lean`).
The tuple's EXISTENCE is the block's union recursor at the frame's
motives and minors: this file defines that candidate over the datum
`BlockRep`, as data — the recursion kit's predecessor map, bound and
step (`kitPred`/`kitB`/`kitSt`), the union recursor at them
(`blockRecAt`), a member's value at a leaf frame of its recursor type
(`blockLeafV`: the frame's motives, minors, index values and major
read off by position), and the λ-tower over the recursor type's binder
data (`blockCand`).

The first of the kit's three obligations, **`PredsFrom`**
(`BlockRep.kitPred_from`), is proved here: the datum's `fibre` read at
the recursive positions — the value is `inj c j f⃗` with `f⃗` fitting
constructor `j`'s entries at `X` (`ChainFit`), the decode unique by
`mkInj`, a recursive field's value in its slot (the target member's
component of `X` at the tuple of the field's index expressions under
its telescope, `slotSet`), whose fold along a fitting telescope spine
lands in that component (`slotSet_fold_mem`), the tuple in the
target's index set because a family-space graph is empty off its
domain.  The bound's and the step's obligations (the motives' and
minors' typings at the frame), the candidate's typing and the
equations at the candidate are M3's remaining sessions (DESIGN §U.4
(f)); their consumer, `blockRecs` (`BlockRec.lean`), names them.

Conventions.  A union element is `tagged c i x` (`UnionRec.lean`):
class `c` = the member, `i` its index tuple, `x` the value.  The step
decodes `x` into member `c`'s constructor `j` and field spine `f⃗`
through `BlockRep.mkInj` (classical choice; the datum's `inj` stays
abstract).  Member `c`'s constructor `j` is the block's minor
`minorIdx c j` (the minors are in block order: member `0`'s
constructors, then member `1`'s, …).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule)

universe w

variable {V : Type w} [SetTheory V]

namespace BlockRepData

variable (d : BlockRepData V)

/-- The block's minor index of member `mm`'s constructor `j`. -/
@[expose] def minorIdx (mm j : Nat) : Nat :=
  ((List.range mm).map fun t => (d.ctorsM t).length).sum + j

/-- Field `i'`'s telescope. -/
@[expose] def teleAt (ψ : Name → Nat) (c j i' : Nat) : List (Nat × Nat × AnnotTerm) :=
  ((d.tlss c ψ).getD j []).getD i' []

/-- Field `i'`'s index expressions. -/
@[expose] def eisAt (ψ : Name → Nat) (c j i' : Nat) : List AnnotTerm :=
  ((d.Eiss c ψ).getD j []).getD i' []

/-- **The predecessor relation** on union elements: `tagged c i (inj c
j f⃗)` has, for each recursive field `i'` of constructor `j` and each
spine `b⃗` fitting the field's telescope, the predecessor at the target
member, at the tuple of the field's index expressions, with value the
field applied to the spine. -/
@[expose] def PredRel (ψ : Name → Nat) (ρp : Nat → V) (u v : V) : Prop :=
  ∃ (c : Nat) (i : V) (j : Nat) (fs : List V) (i' : Nat) (bs : List V),
    c < d.k ∧ j < (d.ctorsM c).length ∧ fs.length = ((d.Fss c ψ).getD j []).length ∧
    u = tagged c i (d.inj ψ c j fs) ∧
    i' ∈ recIdx ((d.rss c).getD j []) ((d.Fss c ψ).getD j []).length ∧
    SpineFit (consList (fs.take i') ρp) ((d.teleAt ψ c j i').map (·.2.2)) bs ∧
    v = tagged (d.tgts c j i')
      (d.tup ψ (d.tgts c j i')
        ((d.eisAt ψ c j i').map (interp V (consList bs (consList (fs.take i') ρp)))))
      (bs.foldl SetTheory.app (fs.getD i' pt))

/-- **The predecessor map**: the relation, separated off the carrier's
union. -/
@[expose] noncomputable def kitPred (ψ : Name → Nat) (ρp : Nat → V) (u : V) : V :=
  relPred (unionSet d.k (d.idx ψ ρp) (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp)))
    (d.PredRel ψ ρp) u

/-- **The bound**: at `tagged c i x`, motive `c` at the index spine of
`i` and at `x`. -/
@[expose] noncomputable def kitB (ψ : Name → Nat) (Ms : Nat → V) (u : V) : V :=
  SetTheory.app
    ((isOfW (d.uM (natIdx (sfst u)) ψ) (d.nIdxAt (natIdx (sfst u))) (sfst (ssnd u))).foldl
      SetTheory.app (Ms (natIdx (sfst u))))
    (ssnd (ssnd u))

/-- **The inductive hypotheses** of member `c`'s constructor `j` at
the field spine `f⃗`, from a choice `g` of the predecessors' values:
per recursive field, the λ-tower over its telescope of `g` at the
call's element. -/
@[expose] noncomputable def kitIhs (ψ : Name → Nat) (ρp : Nat → V) (ℓ c j : Nat) (fs : List V) (g : V) :
    List V :=
  (recIdx ((d.rss c).getD j []) ((d.Fss c ψ).getD j []).length).map fun i' =>
    lamTower ℓ (consList (fs.take i') ρp) (d.teleAt ψ c j i') fun σ' =>
      SetTheory.app g
        (tagged (d.tgts c j i')
          (d.tup ψ (d.tgts c j i') ((d.eisAt ψ c j i').map (interp V σ')))
          ((ConLeche.Semantics.frameIdx (d.teleAt ψ c j i').length σ').foldl SetTheory.app
            (fs.getD i' pt)))

/-- The value's constructor and fields, when it has them (unique by
`BlockRep.mkInj` at `w ≠ 0`). -/
@[expose] def Decodes (ψ : Name → Nat) (c : Nat) (x : V) : Prop :=
  ∃ (j : Nat) (fs : List V), j < (d.ctorsM c).length ∧
    fs.length = ((d.Fss c ψ).getD j []).length ∧ x = d.inj ψ c j fs

open Classical in
/-- **The step at a class and a value**: with `x = inj c j f⃗`, minor
`minorIdx c j` at the fields and the inductive hypotheses; junk
elsewhere. -/
@[expose] noncomputable def kitStAt (ψ : Name → Nat) (ρp : Nat → V) (ℓ : Nat) (ms : Nat → V) (c : Nat)
    (x g : V) : V :=
  if h : d.Decodes ψ c x then
    (Classical.choose (Classical.choose_spec h) ++
      d.kitIhs ψ ρp ℓ c (Classical.choose h) (Classical.choose (Classical.choose_spec h)) g).foldl
      SetTheory.app (ms (d.minorIdx c (Classical.choose h)))
  else empty

/-- **The step**: at `tagged c i x`, the step at class `c` and value
`x`. -/
@[expose] noncomputable def kitSt (ψ : Name → Nat) (ρp : Nat → V) (ℓ : Nat) (ms : Nat → V) (u g : V) : V :=
  d.kitStAt ψ ρp ℓ ms (natIdx (sfst u)) (ssnd (ssnd u)) g

/-- **The block's recursor at the frame's data**: the union recursor
of the carrier at the kit's predecessor map, bound and step, at class
`c`, index tuple `i`, value `x`. -/
@[expose] noncomputable def blockRecAt (ψ : Name → Nat) (ρp : Nat → V) (ℓ : Nat) (Ms ms : Nat → V)
    (c : Nat) (i x : V) : V :=
  unionRec ℓ (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp) (d.kitPred ψ ρp) (d.kitB ψ Ms)
    (d.kitSt ψ ρp ℓ ms) c i x

/-- **Member `mm`'s value at a leaf frame of its recursor type**
`(p⃗, M⃗, m⃗, ı⃗_mm, t)`: the union recursor at class `mm`, at the
parameter frame below the frame's `1 + nIdx + n + k` innermost
binders, with motive `c` at `σ (1 + nIdx + n + (k - 1 - c))`, minor
`J` at `σ (1 + nIdx + n - 1 - J)`, the index tuple of the `nIdx`
binders above the major, and the major `σ 0`. -/
@[expose] noncomputable def blockLeafV (ψ : Name → Nat) (ℓ mm : Nat) (σ : Nat → V) : V :=
  d.blockRecAt ψ (shiftE (1 + d.nIdxAt mm + d.nCtors + d.k) 0 σ) ℓ
    (fun c => σ (1 + d.nIdxAt mm + d.nCtors + (d.k - 1 - c)))
    (fun J => σ (1 + d.nIdxAt mm + d.nCtors - 1 - J))
    mm (d.tup ψ mm (ConLeche.Semantics.frameIdx (d.nIdxAt mm) (shiftE 1 0 σ))) (σ 0)

/-- **The candidate recursor of member `mm`**: the λ-tower over its
recursor type's binder data `rds` (at the elimination bit `ℓ`) whose
leaf is the union recursor at the frame. -/
@[expose] noncomputable def blockCand (ψ : Name → Nat) (ℓ : Nat) (rds : List (Nat × Nat × AnnotTerm))
    (mm : Nat) (ρ : Nat → V) : V :=
  lamTower ℓ ρ rds (d.blockLeafV ψ ℓ mm)

end BlockRepData

/-! ## Kit -/

/-- A recursive position's value in a fit lies in its slot at the
prefix. -/
theorem FitsFrom.rec_mem {rs : List Bool} {slot : Nat → (Nat → V) → V} :
    ∀ {i : Nat} {ρ : Nat → V} {Fs : List AnnotTerm} {as : List V}, FitsFrom rs slot i ρ Fs as →
      ∀ l, l < Fs.length → rs.getD (i + l) false = true →
        as.getD l pt ∈ˢ slot (i + l) (consList (as.take l) ρ)
  | _, _, [], _, _, l, hl, _ => absurd hl (Nat.not_lt_zero _)
  | _, _, _ :: _, [], h, _, _, _ => h.elim
  | i, ρ, _ :: _, a :: _, h, 0, _, hr => by
    rw [Nat.add_zero] at hr ⊢
    have h1 := h.1
    rw [if_pos hr] at h1
    simpa using h1
  | i, ρ, _ :: Fs, a :: as, h, l + 1, hl, hr => by
    have := FitsFrom.rec_mem (i := i + 1) (ρ := cons a ρ) (Fs := Fs) (as := as) h.2 l
      (by simpa using hl) (by rw [show i + 1 + l = i + (l + 1) from by omega]; exact hr)
    rw [show i + 1 + l = i + (l + 1) from by omega] at this
    simpa using this

/-- A family-space member is empty off its index set. -/
theorem app_famSpace_of_not_mem {w : Nat} {I X t : V} (hX : X ∈ˢ famSpace w I) (ht : ¬ t ∈ˢ I) :
    SetTheory.app X t = empty := by
  rw [← eq_graph_app_of_mem_piSet hX]
  exact app_graph_of_not_mem ht

/-- A family-space member's application is in `univ w` everywhere. -/
theorem app_famSpace_mem_univ {w : Nat} {I X : V} (hX : X ∈ˢ famSpace w I) (t : V) :
    SetTheory.app X t ∈ˢ (univ w : V) := by
  by_cases ht : t ∈ˢ I
  · exact famSpace_app hX ht
  · rw [app_famSpace_of_not_mem hX ht]; exact empty_mem_univ w

/-- An inhabited application of a family-space member is at an index. -/
theorem mem_idx_of_app_famSpace {w : Nat} {I X t y : V} (hX : X ∈ˢ famSpace w I)
    (hy : y ∈ˢ SetTheory.app X t) : t ∈ˢ I := by
  rcases Classical.em (t ∈ˢ I) with ht | ht
  · exact ht
  · exfalso
    rw [app_famSpace_of_not_mem hX ht] at hy
    exact not_mem_empty y hy

omit [SetTheory V] in
/-- A set recursive flag is within the kinds. -/
theorem rsOf_getD_true_lt {ks : List RecFieldKind} {i : Nat} (h : (rsOf ks).getD i false = true) :
    i < ks.length := by
  rcases Nat.lt_or_ge i ks.length with hi | hi
  · exact hi
  · exfalso
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa [rsOf] using hi)] at h
    exact nomatch h

/-! ## `PredsFrom` at the datum -/

namespace BlockRep

variable {m : EnvModel V env} {T : Name} {cvT cvR : ConstantVal} {mI rP : Nat}
  {rules : List RecRule} {d : BlockRepData V} {mm : Nat}
  (h : BlockRep m T cvT cvR mI rP rules d mm)
include h

/-- **The predecessors come from the argument tuple**: at any tuple `X`
in the tuple space, a value of `Φ X c` at an index tuple has every
`kitPred` predecessor in `X`'s union — the datum's `fibre` read at the
recursive positions. -/
theorem kitPred_from {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V (d.params ψ).reverse ρp)
    (hw : d.w ψ ≠ 0) :
    PredsFrom (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp) (d.kitPred ψ ρp) := by
  intro X hX _ c hc i hi x hx v hv
  obtain ⟨-, c', i', j, fs, i'', bs, hc', hj, hlen, heq, hi'', hbs, rfl⟩ := mem_relPred.mp hv
  obtain ⟨rfl, rfl, hxe⟩ := tagged_inj heq
  obtain ⟨j₂, fs₂, hj₂, hfit, hx₂⟩ := (h.fibre ψ ρp hρp X hX c hc i hi x).mp hx
  have hlen₂ : fs₂.length = ((d.Fss c ψ).getD j₂ []).length := hfit.1.length_eq
  obtain ⟨rfl, rfl⟩ := h.mkInj ψ hw c hc j fs j₂ fs₂ hj hj₂ hlen hlen₂ (hxe.symm.trans hx₂)
  obtain ⟨hi''F, hrec⟩ := mem_recIdx.mp hi''
  -- the field's value is in its slot at the prefix
  have hmem := hfit.1.rec_mem i'' hi''F (by rw [Nat.zero_add]; exact hrec)
  rw [Nat.zero_add] at hmem
  unfold BlockRepData.slotAt at hmem
  -- the target is a member
  have hi''K : i'' < (d.ksF c j).length := by
    have hj' : j < (d.ctorsM c).length := hj
    rw [BlockRepData.rss, rssOfK_getD hj'] at hrec
    exact rsOf_getD_true_lt hrec
  have htgt : d.tgts c j i'' < d.k := h.tgtsLt c j i'' hc hj hi''K
  have hXt := hX _ htgt
  have hXu : ∀ t, SetTheory.app (X (d.tgts c j i'')) t ∈ˢ (univ (d.w ψ) : V) :=
    fun t => app_famSpace_mem_univ hXt t
  have hval := slotSet_fold_mem hXu hmem hbs
  refine tagged_mem_unionSet htgt ?_ hval
  exact mem_idx_of_app_famSpace hXt hval

end BlockRep

end ConLeche.Model

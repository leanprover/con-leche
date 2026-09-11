module

public import ConLeche.Model.Inductives.MutualRecRead
public import ConLeche.Model.Inductives.MutualData
public import ConLeche.Model.Inductives.FixRecData
import ConLeche.Verify.Inductives.MutualInv
public section

/-!
# The mutual recursor stage's readings, from the run (task #278, M2.5a)

`FixRecData.lean` at a mutual block: member `mm`'s generated recursor
type (`mutualRecTy`, checked by `checkMutualRecTy`) read off the run.

The pieces, in the order the stage needs them:

* `MutualFormerFacts` / `formerReadsM_of` — the members' reading
  premises (`FormerReadsM`) from their `FormerData`s and their stored
  records;
* `MutualCtorFactsAt` / `mutualCtorReadsM_of` — the constructors'
  reading premises (`MutualCtorReadsM`) from their `MutualCtorDataI`
  facts and the classified kinds (`fixCtorReadsR_of` with a per-field
  TARGET member: the datum's recursive positions are `recIdxOf` of the
  kinds stripped of their targets, and the generated constructor's
  `recFields` is that list re-paired with them);
* `MutualRecData` / `mutualRecData_of` — the stored recursor type's
  reading package and its universe, the kernel's own sort inference
  through the claims' sort row.

`SumRecData` does NOT fit: its `len`/`read` are the ONE-motive shape
(`nP + n + nIdx + 2` binders, core `recConcAV n nIdx`), while a mutual
member's recursor carries `k` motives (`nP + k + n + nIdx + 1` binders,
core `mutualConcAV k n nIdx mm`) — the two coincide only at `k = 1`
(`recConcAV_eq_mutualConcAV`).  `MutualRecData` is the same six clauses
at that shape, with `SumRecData.cross`'s cons-crossing lemma repeated.

No cross-member parameter identification is needed for the READING:
`mutualRecTy` takes the parameter Πs from former `0` and the index Πs
from member `mm`, and the data names exactly those (`ppsOf 0`,
`ipsOf mm`).  The identification is what the later stages need to see
the prefix as member `mm`'s OWN parameter data; `mutualRdsAV_take_own`
is that step, from the hypothesis in the shape `mutualCrossChecks`
supports.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta
  MutualBlock MutualFormer MutualCtor4)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The recursive positions of a mutual constructor -/

/-- A `filterMap` whose function is a guarded `some` is a filter and a
map. -/
theorem filterMap_if_eq {α β : Type} (p : α → Bool) (g : α → β) :
    ∀ l : List α, l.filterMap (fun a => if p a then some (g a) else none)
      = (l.filter p).map g
  | [] => rfl
  | a :: l => by
    cases h : p a with
    | true => simp [h, filterMap_if_eq p g l]
    | false => simp [h, filterMap_if_eq p g l]

omit [SetTheory V] in
/-- **The generated constructor's recursive fields are the datum's
recursive positions, re-paired with their targets**: `mutualRecFieldsOf`
walks the kinds with their targets, `recIdxOf` the kinds alone. -/
theorem mutualRecFieldsOf_eq (ks : List (RecFieldKind × Nat)) :
    ConLeche.mutualRecFieldsOf ks
      = (ConLeche.recIdxOf (kindsOf ks)).map fun i => (i, tgtAt ks i) := by
  unfold ConLeche.mutualRecFieldsOf ConLeche.recIdxOf
  rw [kindsOf_length, ← filterMap_if_eq
    (fun i => (kindsOf ks).getD i RecFieldKind.ordinary == RecFieldKind.recursive ||
      (kindsOf ks).getD i RecFieldKind.ordinary == RecFieldKind.reflexive)
    (fun i => (i, tgtAt ks i))]
  congr 1
  funext i
  by_cases hi : i < ks.length
  · rw [show ks.getD i (RecFieldKind.ordinary, 0) = (kindAt ks i, tgtAt ks i) from rfl,
      kindsOf_getD hi]
    cases hk : kindAt ks i <;> simp
  · have h1 : ks.getD i (RecFieldKind.ordinary, 0) = (.ordinary, 0) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    have h2 : (kindsOf ks).getD i RecFieldKind.ordinary = .ordinary := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [kindsOf_length]; omega)]
      rfl
    rw [h1, h2]
    simp

/-! ## The members' reading premises -/

/-- **What the stage knows about one member after the formers' stage**:
its former is stored at the block's level parameters with the
generators' type, its telescope ends in its result sort, and its
parameter/index data are its `FormerData`. -/
structure MutualFormerFacts {env : Env} (m : EnvModel V env) (lps : List Name) (nP : Nat)
    (f : MutualFormer) (cvTa : ConstantVal) (s : Level)
    (pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)) (lvls : (Name → Nat) → List Nat) :
    Prop where
  find : ∃ caps : IndCaps, env.find? f.name = some (.indInfo cvTa caps)
  tty : cvTa.type = f.tty
  lps : cvTa.levelParams = lps
  strip : ∃ bs : List (Expr × BinderMeta),
    cvTa.type.stripPis (nP + f.nIdx) = some (bs, Expr.sort s)
  data : FormerData m cvTa (nP + f.nIdx) s pps lvls

/-- **The members' reading premises**, from their facts: the leaf is
the stored former's value, the parameter block the telescope's first
`nP` entries and the index block the rest. -/
theorem formerReadsM_of {m : EnvModel V env} {lps : List Name} {nP : Nat}
    {Tname : Nat → Name} {nIdxOf : Nat → Nat}
    {cvTaOf : Nat → ConstantVal} {sOf : Nat → Level}
    {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {lvlsOf : Nat → (Name → Nat) → List Nat}
    {formers : List MutualFormer}
    (hT : ∀ t, t < formers.length → Tname t = (formers.getD t default).name)
    (hI : ∀ t, t < formers.length → nIdxOf t = (formers.getD t default).nIdx)
    (hf : ∀ t, t < formers.length →
      MutualFormerFacts m lps nP (formers.getD t default) (cvTaOf t) (sOf t) (ppsOf t) (lvlsOf t))
    (ψ : Name → Nat) :
    FormerReadsM m ψ lps nP (fun t => m.acval (Tname t) ψ) nIdxOf
      (fun t => (ppsOf t ψ).take nP) (fun t => (ppsOf t ψ).drop nP) formers := by
  intro t ht
  obtain ⟨⟨caps, hfind⟩, htty, hlps, ⟨bs, hstrip⟩, hD⟩ := hf t ht
  obtain ⟨hCf, -, -, hCb, -⟩ := m.wf _ (ConLeche.Semantics.Env.find?_mem hfind)
  simp only [ConstantInfo.toConstantVal] at hCf hCb
  have hname : Tname t = (formers.getD t default).name := hT t ht
  have hidx : nIdxOf t = (formers.getD t default).nIdx := hI t ht
  have hstripS : ((formers.getD t default).tty.stripPis
      (nP + (formers.getD t default).nIdx)).isSome = true := by
    rw [← htty, hstrip]; rfl
  refine ⟨⟨.indInfo (cvTaOf t) caps, hfind, hlps⟩, by show m.acval (Tname t) ψ = _; rw [hname],
    hidx, by rw [← htty]; exact hCf, by rw [← htty]; exact hCb, ?_, hstripS,
    ⟨ppsOf t ψ, (sOf t).eval ψ, by rw [← htty]; exact hD.read ψ, by rw [hD.len ψ], rfl, rfl⟩⟩
  obtain ⟨⟨tbs, itele⟩, hq⟩ := Option.isSome_iff_exists.mp
    (ConLeche.stripPis_isSome_of_le (Nat.le_add_right _ _) hstripS)
  exact ⟨tbs, itele, hq⟩

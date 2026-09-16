module

public import ConLeche.Model.Inductives.NestedRecsStage
import ConLeche.Verify.Inductives.NestedRestoreKit
import ConLeche.Verify.Inductives.NestedRestoreOpen
import ConLeche.Verify.Inductives.MutualGrouped
import ConLeche.Model.Inductives.StructRecKit2
import ConLeche.Model.IndTowerRead
import ConLeche.Model.Inductives.StructData
import ConLeche.Model.Inductives.NestedCtorRead
import ConLeche.Model.Inductives.StructFrames
public section

/-!
# The restored recursor types' readings — the syntactic half (task #315, M7-2)

The `k + nPins` restored recursor types are `restoreNested` of the
auxiliary block's generated `mutualRecTy`s (DESIGN §U.1 (c) 7).  The
restore keeps every binder and every binder meta
(`rk_restoreNested_stripPis`), so the restored type is a syntactic
`∀`-telescope of the auxiliary's length whose residual is the
auxiliary's conclusion `motive_c ı⃗ t` (`mutualRecTy_stripPis`, the
Verify half), and its reading at ANY model is a Π-tower of that
length with the elimination datum's bits (`restoredRecTy_reading`).
The bookkeeping that names that length in the nested block model's
terms — `nCtorsT` at `nestedPc` is the auxiliary block's constructor
count, a pin class's index count is its copy's — is the second half
of this file.  The readings' FRAMES (`ReadingFramesT`) are the
semantic half, `NestedRecFrames.lean`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  NestedParts MutualBlock AuxStored ElimState NestedPin IndCaps fueledOps BinderMeta PropWhen
  RestoreTbl)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The reading of a restored telescope -/

/-- **A restored recursor type reads to a Π-tower of the auxiliary's
length with the elimination datum's bits**: at a model `m`, a type
`tyR = restoreNested R tyA` whose auxiliary `tyA` is a syntactic
`∀`-telescope of `N` binders with every meta `⟨pw⟩` and an
auxiliary-free residual, reads (whenever it reads) to
`mkPisAV rds conc` with `rds.length = N`, every entry's bits
`(0, pwBit φ pw)`, and — the type being closed — the domains closed at
their depths. -/
theorem restoredRecTy_reading {env : Env} (m : EnvModel V env) {φ : Name → Nat}
    {R : RestoreTbl} {nP N : Nat} (hnP : R.nP = nP) {tyA tyR : Expr}
    {cbs : List (Expr × BinderMeta)} {resid : Expr} {pw : PropWhen}
    (hstrip : tyA.stripPis (nP + N) = some (cbs, resid))
    (hmeta : ∀ x ∈ cbs, x.2 = (⟨pw⟩ : BinderMeta))
    (hfree : ∀ n ∈ R.auxNames, resid.mentionsConst n = false)
    (hres : ConLeche.restoreNested R tyA = .ok tyR)
    (hb : tyR.looseBVarsBounded 0 = true) (hfv : tyR.hasFvar = false)
    {ea : AnnotTerm} (hea : denoteMeta m.acval env φ 0 tyR = some ea) :
    ∃ (rds : List (Nat × Nat × AnnotTerm)) (conc : AnnotTerm),
      ea = mkPisAV rds conc ∧ rds.length = nP + N ∧
      (∀ e ∈ rds, e.1 = 0 ∧ e.2.1 = pwBit φ pw) ∧ DomsBelow 0 rds := by
  obtain ⟨cbs', hstrip', hmeta'⟩ := ConLeche.rk_restoreNested_stripPis hnP hstrip hres hfree
  have hlen' : cbs'.length = nP + N := ConLeche.Expr.stripPis_length _ hstrip'
  have htyR : tyR = ConLeche.mkPisB cbs' resid := ConLeche.stripPis_mkPisB _ hstrip'
  obtain ⟨fvs, o, hop⟩ := openPisAtFvars_of_stripPis_isSome (nP + N) (e := tyR) 0
    (by rw [hstrip']; rfl)
  obtain ⟨Γ, Rr, hpi, -, -⟩ := openPisAtFvars_denotePTele (nP + N) hop hea
  obtain ⟨rds, hst, -⟩ := stripPisAV_of_piTeleAV hpi
  obtain ⟨heq, hlen⟩ := stripPisAV_eq_mkPis hst
  refine ⟨rds, Rr, heq, hlen, ?_, ?_⟩
  · intro e he
    obtain ⟨k, hk⟩ := List.getElem?_of_mem he
    have hkl : k < rds.length := (List.getElem?_eq_some_iff.mp hk).1
    have hkl' : k < cbs'.length := by rw [hlen']; rw [hlen] at hkl; exact hkl
    obtain ⟨bm, hbm⟩ : ∃ bm, cbs'[k]? = some bm := ⟨_, List.getElem?_eq_getElem hkl'⟩
    have hea' : denoteMeta m.acval env φ 0 (ConLeche.mkPisB cbs' resid) = some ea := by
      rw [← htyR]; exact hea
    rw [← hlen'] at hst
    obtain ⟨h1, h2⟩ := stripPisAV_denoteMeta_mkPisB cbs' hea' hst k e bm hk hbm
    refine ⟨h1, ?_⟩
    rw [h2]
    have hbm2 : bm.2 = (⟨pw⟩ : BinderMeta) := by
      have hmap := congrArg (fun l => l[k]?) hmeta'
      simp only [List.getElem?_map, hbm, Option.map_some] at hmap
      cases hcb : cbs[k]? with
      | none =>
        rw [hcb] at hmap
        exact absurd hmap (by simp)
      | some x =>
        rw [hcb] at hmap
        simp only [Option.map_some, Option.some.injEq] at hmap
        rw [hmap]
        exact hmeta x (List.mem_of_getElem? hcb)
    rw [hbm2]
  · have hw : Expr.WScoped 0 tyR := Expr.WScoped.of_not_hasFvar hfv
    exact (stripPisAV_below hst (bvarsBelow_of_reading hw hb hea)).1

/-! ## Bookkeeping at the nested block model -/

section Bookkeeping

variable {p : NestedParts} {b : MutualBlock} {fms : List MutualFormerA} {f₀ : MutualFormerA}
  {ctorsA : List (ConstantVal × Nat)} {kinds : List (List (RecFieldKind × Nat))} {env : Env}
  {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {W : (Name → Nat) → Nat}
  {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
  {fvsPF : Nat → List Expr} {xrestF : Nat → Expr}
  {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
  {ctorsR : List (List (ConstantVal × Nat × Nat))}
  {dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {xFvsR : Nat → Nat → List Expr}
  {pinsS : List PinSyn}

local notation "D" => (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS)
local notation "PC" => (nestedPc (V := V) b ctorsA kinds p.k f₀.s dsF esF eissF tssF)

/-- The classes are the auxiliary block's members. -/
theorem nestedBlockModel_kT : (D).kT = p.k + pinsS.length := rfl

/-- The parameter count is the auxiliary block's. -/
theorem nestedBlockModel_nP : (D).nP = b.nP := rfl

/-- A pin class's constructor count is its copy's. -/
theorem nestedPc_ctors_length (q : Nat) : (PC q).ctors.length = (b.ownCtors (p.k + q)).length := by
  simp [nestedPc]

/-- **The minors' count at the nested block model is the auxiliary
block's constructor count**: the members' restored constructors are as
many as their auxiliary ones, the pins' are the copies', and the
auxiliary block is grouped. -/
theorem nestedBlockModel_nCtorsT
    (hlen : ∀ mm, mm < p.k → (ctorsR.getD mm []).length = (b.ownCtors mm).length)
    (hbk : b.k = p.k + pinsS.length)
    (hmem : b.ctors.all (fun c => c.member < b.k) = true) :
    (D).nCtorsT PC = b.ctors.length := by
  have hsum : ∀ n, n ≤ p.k + pinsS.length →
      ((List.range n).map fun c => ((D).ctorsT PC c).length).sum = b.ownOffset n := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.map_append, List.sum_append, ih (by omega),
        ConLeche.ownOffset_succ]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      congr 1
      by_cases hc : n < p.k
      · rw [BlockModel.ctorsT_of_mem hc]
        show ((ctorsR.getD n []).map fun c => (c.1, c.2.2)).length = _
        rw [List.length_map]
        exact hlen n hc
      · rw [BlockModel.ctorsT_of_pin hc]
        show (PC (n - p.k)).ctors.length = _
        rw [nestedPc_ctors_length, Nat.add_sub_cancel' (Nat.le_of_not_lt hc)]
  show ((List.range ((D).kT)).map fun c => ((D).ctorsT PC c).length).sum = _
  rw [nestedBlockModel_kT, hsum _ (Nat.le_refl _), ← hbk]
  exact ConLeche.ownOffset_k hmem

/-- A member class's index count is its former's. -/
theorem nestedBlockModel_nIdxT_mem {c : Nat} (hc : c < p.k) (hk : p.k ≤ fms.length) :
    (D).nIdxT c = (fms.getD c default).nIdx := by
  rw [BlockModel.nIdxT_of_mem hc]
  show ((fms.take p.k).map (·.nIdx)).getD c 0 = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take_of_lt hc,
    List.getElem?_eq_getElem (by omega), List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega)]
  rfl

local notation "PG" => NestedPinGroup (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀)
  (ctorsA := ctorsA) (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF)
  (dsF := dsF) (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
  (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)

/-- **A pin class's index count is its copy's**: the pin's recorded
index count is its container member's (`NestedPinGroup.pinNIdx`), and
the copy's index telescope is the container's instantiated at the
components (`NestedPinGroup.idx`), of the same length. -/
theorem nestedBlockModel_nIdxT_pin {env₂ : Env} {m : EnvModel V env₂} {q₀ kJ i : Nat}
    {dJ : BlockModel V} (G : PG m q₀ kJ dJ) (hi : i < kJ) {nIdx : Nat}
    (hlenP : ∀ ψ : Name → Nat, (ppsF (p.k + q₀ + i) ψ).length = b.nP + nIdx) :
    (D).nIdxT (p.k + (q₀ + i)) = nIdx := by
  have hk : (D).k = p.k := rfl
  rw [BlockModel.nIdxT_of_pin (by rw [hk]; omega), hk, Nat.add_sub_cancel_left, G.pinNIdx i hi]
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := G.rep i hi
  have h := congrArg List.length (G.idx i hi (fun _ => 0) i hi)
  rw [instTele_length, hI.IdsM_length] at h
  have hl : (blockIds b.nP ppsF (fun _ => 0) (p.k + q₀ + i)).length = nIdx := by
    show (((ppsF (p.k + q₀ + i) (fun _ => 0)).drop b.nP).map (·.2.2)).length = nIdx
    rw [List.length_map, List.length_drop, hlenP]
    omega
  rw [hl] at h
  exact h.symm

end Bookkeeping

end ConLeche.Model

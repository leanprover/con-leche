module

public import ConLeche.Model.BasisRep
public import ConLeche.Model.BasisBlocks

public section

/-!
# The pinned `PUnit` block's representation (task #280)

`PUnit.{u} : Sort u` has one field-free constructor, so its container
functor is the CONSTANT one whose every fibre is `unitSet = {pt}` and
whose sole injection is the point — the pin's own value, on the nose,
with no tagging.  The least fixed point of that functor is the
constant family again, which is the `PUnit` leaf.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps
  RecRule punitA punitUnitA punitRecA punitName punitUnitName uN u1N)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-- **The `PUnit` block's representation datum**: no parameters, no
indices, one field-free constructor, the constant functor with fibre
`unitSet` and the point as injection. -/
@[expose] noncomputable def punitRepData (env₀ : Env) : IndRepData V where
  nP := 0
  nIdx := 0
  resSort := .param uN
  isProp := (Level.isEquiv (.param uN) .zero == some true)
  large := true
  env₀ := env₀
  ctorsA := [(punitUnitA.toConstantVal, 0)]
  idxF := fun _ => []
  dsF := fun _ _ => []
  esF := fun _ _ => []
  srcsF := fun _ => []
  ksF := fun _ => []
  fvsPF := fun _ => []
  xFvsF := fun _ => []
  xrestF := fun _ => .const punitName [.param uN]
  eissF := fun _ _ => []
  tssF := fun _ _ => []
  pps := fun _ => []
  u := fun _ => 0
  Φ := fun ψ _ => lamR (Nat.max 0 (ψ uN + 1)) (lfpFamSpace V (ψ uN) unitSet)
    fun _ => lamR (ψ uN + 1) (unitSet : V) fun _ => unitSet
  inj := fun _ _ _ => pt

section

variable {env₀ : Env}

/-- The datum's index-tuple set is the unit set (no indices). -/
theorem punitRepData_idx (ψ : Name → Nat) (ρp : Nat → V) :
    (punitRepData (V := V) env₀).idx ψ ρp = unitSet := rfl

/-- The constant functor's fibre. -/
theorem punitRepData_fibre_eq (ψ : Name → Nat) (ρp : Nat → V) {X : V}
    (hX : X ∈ˢ famSpace (ψ uN) (unitSet : V)) {t : V} (ht : t ∈ˢ (unitSet : V)) :
    app (app ((punitRepData (V := V) env₀).Φ ψ ρp) X) t = unitSet := by
  show app (app (lamR (Nat.max 0 (ψ uN + 1)) (lfpFamSpace V (ψ uN) unitSet)
      (fun _ => lamR (ψ uN + 1) (unitSet : V) fun _ => unitSet)) X) t = _
  rw [app_lamR_pos (max_succ_ne_zero 0 (ψ uN)) (by rw [lfpFamSpace_eq]; exact hX),
    app_lamR_pos (Nat.succ_ne_zero (ψ uN)) ht]

/-- The constant family `i ↦ unitSet` is closed under the functor. -/
theorem punitRepData_closed (ψ : Name → Nat) (ρp : Nat → V) :
    IsClosedFam (ψ uN) (unitSet : V) ((punitRepData (V := V) env₀).Φ ψ ρp)
      (graph (fun _ => unitSet) unitSet) := by
  refine ⟨graph_mem_famSpace fun _ _ => unitSet_mem_univ _, fun i hi x hx => ?_⟩
  rw [punitRepData_fibre_eq (env₀ := env₀) ψ ρp
    (graph_mem_famSpace fun _ _ => unitSet_mem_univ _) hi] at hx
  rw [app_graph hi]
  exact hx

theorem punitRepData_mono (ψ : Name → Nat) (ρp : Nat → V) :
    MonoFam (ψ uN) (unitSet : V) ((punitRepData (V := V) env₀).Φ ψ ρp) := by
  intro X Y hX hY _ i hi
  rw [punitRepData_fibre_eq (env₀ := env₀) ψ ρp hX hi,
    punitRepData_fibre_eq (env₀ := env₀) ψ ρp hY hi]

theorem punitRepData_maps (ψ : Name → Nat) (ρp : Nat → V) :
    MapsFam (ψ uN) (unitSet : V) ((punitRepData (V := V) env₀).Φ ψ ρp) := by
  intro X hX
  show app (lamR (Nat.max 0 (ψ uN + 1)) (lfpFamSpace V (ψ uN) unitSet)
      (fun _ => lamR (ψ uN + 1) (unitSet : V) fun _ => unitSet)) X ∈ˢ _
  rw [app_lamR_pos (max_succ_ne_zero 0 (ψ uN)) (by rw [lfpFamSpace_eq]; exact hX)]
  rw [← lfpFamSpace_eq]
  exact lamR_mem fun _ _ => unitSet_mem_univ _

/-- **The least fixed point of the constant functor is the constant
family** — the `PUnit` leaf. -/
theorem punitRepData_lfp (ψ : Name → Nat) (ρp : Nat → V) :
    app (lfpFamSet (ψ uN) (unitSet : V) ((punitRepData (V := V) env₀).Φ ψ ρp)) pt
      = unitSet := by
  have hcl : ∃ L, IsClosedFam (ψ uN) (unitSet : V) ((punitRepData (V := V) env₀).Φ ψ ρp) L :=
    ⟨_, punitRepData_closed ψ ρp⟩
  refine Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · have := lfpFamSet_le (punitRepData_closed (env₀ := env₀) ψ ρp) pt pt_mem_unitSet x hx
    rwa [app_graph (pt_mem_unitSet (V := V))] at this
  · refine lfpFamSet_closed hcl (punitRepData_mono ψ ρp) pt pt_mem_unitSet x ?_
    rw [punitRepData_fibre_eq (env₀ := env₀) ψ ρp
      (by rw [← lfpFamSpace_eq]; exact lfpFamSet_mem_space V _ _ _) pt_mem_unitSet]
    exact hx

end

/-- **The pinned `PUnit` block is represented** — the obligation
`declStep_preserves_of_basis_rec_cons` owes at the `PUnit.rec` cons. -/
theorem indRepsHead_punitRec (mp : EnvModelM V μ env)
    (hP : env.find? punitName = some punitA)
    (hU : env.find? punitUnitName = some punitUnitA)
    (hfresh : env.find? punitRecA.name = none) :
    ∀ m₂ : EnvModel V ⟨punitRecA :: env.consts⟩,
      m₂.acval = acvalWith mp.base2.acval punitRecA.name
        (fun ψ => AnnotTerm.const .punitRec [ψ uN, ψ u1N]) →
      IndRepsHead env punitRecA m₂ := by
  intro m₂ hac cvR mI rP rules hc T hT
  injection hc with h1 h2 h3 h4
  subst h1 h2 h3 h4
  have hT' : T = punitName := by
    have h := hT
    simp only at h
    exact (Name.str.inj h).1.symm
  subst hT'
  -- the two pinned leaves at the extension
  have hPleaf : ∀ ψ : Name → Nat, m₂.acval punitName ψ = AnnotTerm.const .punit [ψ uN] := by
    intro ψ
    rw [hac, acvalWith_ne (by decide)]
    exact acval_basis_pinned (m := mp.base2) hP (by decide)
      (by simp +decide [ConLeche.Verify.pinnedStructT])
  have hUleaf : ∀ ψ : Name → Nat,
      m₂.acval punitUnitName ψ = AnnotTerm.const .punitUnit [ψ uN] := by
    intro ψ
    rw [hac, acvalWith_ne (by decide)]
    exact acval_basis_pinned (m := mp.base2) hU (by decide)
      (by simp +decide [ConLeche.Verify.pinnedStructT])
  have hPread : ∀ (ψ : Name → Nat) (d : Nat),
      denoteMeta m₂.acval ⟨punitRecA :: env.consts⟩ ψ d
        (Expr.const punitName [Level.param uN])
        = some (AnnotTerm.const .punit [ψ uN]) := by
    intro ψ d
    rw [hac]
    exact (denoteMeta_punitRec_leaves (m := mp.base2)
      (A := fun ψ => AnnotTerm.const .punitRec [ψ uN, ψ u1N]) ψ hP hU).1 d (.param uN)
  refine Or.inl ⟨_, _, punitRepData ⟨punitRecA :: env.consts⟩,
    ConLeche.Env.find?_cons_of_fresh hfresh hP, ?_⟩
  refine {
    strip := ⟨[], rfl⟩
    isProp := rfl
    mI := rfl
    rP := rfl
    rules := rfl
    former := ?_
    ctors := ?_
    idxRes := fun _ _ _ _ h => nomatch h
    uParams := fun _ _ _ => rfl
    paramsIff := fun _ _ _ _ _ => Iff.rfl
    chains := ?_
    functor := fun ψ ρp _ => ⟨?_, punitRepData_mono ψ ρp, punitRepData_maps ψ ρp,
      ⟨_, punitRepData_closed ψ ρp⟩⟩
    fibre := ?_
    leaf := ?_
    ctor := ?_
    mkZero := fun _ _ _ _ => rfl
    mkInj := ?_ }
  · -- the former's data
    refine ⟨fun ψ => ?_, (fun _ => rfl), (fun _ _ h => nomatch h), fun ψ ρ => ?_,
      (fun _ => trivial), fun ψ₁ ψ₂ h => ⟨rfl, h uN List.mem_cons_self⟩⟩
    · rw [show punitA.toConstantVal.type = Expr.sort (.param uN) from rfl, denoteMeta_sort]
      rfl
    · show WellDenotedV V ρ (AnnotTerm.sort (ψ uN))
      exact ⟨by rw [WellDenoted_sort]; trivial, by rw [AnnotValid_sort]; trivial⟩
  · -- the constructor's data
    intro j cA hj
    match j, hj with
    | 0, hj =>
      obtain rfl : cA = (punitUnitA.toConstantVal, 0) := (Option.some.inj hj).symm
      refine ⟨ConLeche.Env.find?_cons_of_fresh hfresh hU, rfl, ?_⟩
      refine {
        resid := ⟨[], [], rfl, rfl⟩
        read := fun ψ => ?_
        len := fun _ => rfl
        lenE := fun _ => rfl
        idxLen := rfl
        idxRead := fun _ => .nil
        bits := fun _ _ h => nomatch h
        okTy := fun ψ ρ => ?_
        below := fun _ => trivial
        belowE := fun _ _ h => nomatch h
        params := fun _ _ _ => ⟨rfl, rfl⟩
        srcLen := rfl
        srcBnd := fun _ h => nomatch h
        srcIdx := fun _ _ h => nomatch h
        srcProp := fun _ _ _ _ _ => trivial
        opened := ⟨(fun _ h => nomatch h), (fun _ _ h => nomatch h),
          (fun _ _ h => nomatch h), (fun _ _ h => nomatch h),
          fun _ h => absurd h (Nat.not_lt_zero _)⟩
        opens := ⟨_, rfl, rfl⟩
        ksLen := rfl
        xLen := rfl
        pLen := rfl
        xIdx := fun _ _ h => nomatch h
        pIdx := fun _ _ h => nomatch h
        idxEq := rfl
        domRead := fun _ _ _ h => nomatch h
        eissLen := fun _ => rfl
        eisRead := fun _ _ _ h => nomatch h
        eisLen := fun _ _ _ h => absurd h (Nat.not_lt_zero _)
        recEntry := fun _ _ _ h => absurd h (Nat.not_lt_zero _)
        eissParams := fun _ _ _ => rfl
        eissBelow := fun _ _ _ h => nomatch h
        ordNone := fun _ _ _ _ => rfl
        tssLen := fun _ => rfl
        tssNone := fun _ _ _ => rfl
        tssBits := fun _ _ _ h => nomatch h
        tssPiBits := fun _ _ _ h => nomatch h
        tssBelow := fun _ _ => trivial
        tssParams := fun _ _ _ => rfl
        reflOpen := fun _ _ _ h => nomatch h
        eisLenRefl := fun _ _ _ h => absurd h (Nat.not_lt_zero _)
        reflEntry := fun _ _ _ h => absurd h (Nat.not_lt_zero _) }
      · show denoteMeta m₂.acval ⟨punitRecA :: env.consts⟩ ψ 0
            (Expr.const punitName [Level.param uN]) = _
        rw [hPread ψ 0]
        show some (AnnotTerm.const .punit [ψ uN])
          = some (AnnotTerm.mkAppN (m₂.acval punitName ψ) [])
        rw [hPleaf ψ]
        rfl
      · show WellDenotedV V ρ (AnnotTerm.mkAppN (m₂.acval punitName ψ) [])
        rw [show AnnotTerm.mkAppN (m₂.acval punitName ψ) [] = m₂.acval punitName ψ from rfl,
          hPleaf ψ]
        exact ⟨by rw [WellDenoted_const]; trivial, by rw [AnnotValid_const]; trivial⟩
  · -- the chains
    intro ψ ρp _
    refine ⟨⟨trivial, trivial⟩, ?_, ?_⟩
    · intro X _ t _
      intro Fs hFs
      obtain rfl : Fs = [AnnotTerm.idxEqAV []] := by
        rcases List.mem_cons.mp hFs with h | h
        · exact h
        · exact nomatch h
      exact ⟨idxEqAV_wellDenoted (fun _ h => nomatch h),
        (fun _ => idxEqAV_mem_univ [] _ _), fun _ _ => trivial⟩
    · intro _ _ _ _ j hj
      match j, hj with
      | 0, _ => exact trivial
  · -- the functor's membership
    exact lamR_mem fun _ _ => lamR_mem fun _ _ => unitSet_mem_univ _
  · -- the fibre
    intro ψ ρp _ X hX t ht x
    rw [punitRepData_fibre_eq ψ ρp hX ht]
    constructor
    · intro hx
      exact ⟨0, [], Nat.zero_lt_one, ⟨rfl, trivial, fun _ h => nomatch h⟩, mem_unitSet hx⟩
    · rintro ⟨j, fs, -, -, rfl⟩
      exact pt_mem_unitSet
  · -- the leaf
    intro ψ ρ as is hsp₁ hsp₂
    obtain rfl : as = [] := List.length_eq_zero_iff.mp hsp₁.length_eq
    obtain rfl : is = [] := List.length_eq_zero_iff.mp hsp₂.length_eq
    show interp V ρ (m₂.acval punitName ψ)
      = app (lfpFamSet _ _ ((punitRepData (V := V) ⟨punitRecA :: env.consts⟩).Φ ψ
          (consList [] ρ))) (tupW 0 [])
    rw [hPleaf ψ, tupW_zero, punitRepData_lfp]
    rfl
  · -- the constructors
    intro j cA hj ψ ρ as fs hsp₁ hsp₂
    match j, hj with
    | 0, hj =>
      obtain rfl : cA = (punitUnitA.toConstantVal, 0) := (Option.some.inj hj).symm
      obtain rfl : as = [] := List.length_eq_zero_iff.mp hsp₁.length_eq
      obtain rfl : fs = [] := List.length_eq_zero_iff.mp hsp₂.length_eq
      show interp V ρ (m₂.acval punitUnitName ψ) = pt
      rw [hUleaf ψ]
      rfl
  · -- the injections are injective
    intro ψ _ j fs j' fs' hj hj' hlen hlen' _
    match j, hj with
    | 0, _ =>
      match j', hj' with
      | 0, _ =>
        obtain rfl : fs = [] := List.length_eq_zero_iff.mp hlen
        obtain rfl : fs' = [] := List.length_eq_zero_iff.mp hlen'
        exact ⟨rfl, rfl⟩

end ConLeche.Model

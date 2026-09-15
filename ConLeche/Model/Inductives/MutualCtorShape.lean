module

public import ConLeche.Model.Inductives.SumData
public section

/-!
# The constructor's data, read off a stage run's SHAPE (task #315)

`ctorDataI_ofShape` is the body of `sumCtorData_of`
(`ConLeche/Model/Inductives/SumData.lean`) taken at the pieces
`checkSumCtor_shape` returns, rather than at the run itself.  The
mutual route's constructor stage (`checkMutualCtor`, task #278)
returns the SAME tuple, so its data
(`ConLeche/Model/Inductives/MutualData.lean`) is this theorem at
those pieces — the reading argument is written once.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-- **The constructor's data, from its stage run's SHAPE** — the
pieces `checkSumCtor_shape` returns.  The mutual route's stage
(`checkMutualCtor`, task #278) returns the same tuple, so its data is
this theorem at those pieces (`ConLeche/Model/Inductives/MutualData.lean`). -/
theorem ctorDataI_ofShape (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {T : Name} {lps : List Name} {nP nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {cvC cvTa cvCa : ConstantVal} {caps : IndCaps}
    {bs : List (Expr × ConLeche.BinderMeta)} {sorts : List Level} {ty' : Expr}
    {fvsP : List Expr} {crest : Expr} {xFvs idxArgs : List Expr}
    (hccv : ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env
      { cvC with type := ty' } = .ok cvCa)
    (hresid : ∃ cbs es, cvCa.type.stripPis (nP + nF)
      = some (cbs, Expr.mkAppN (.const T (lps.map .param)) (ConLeche.structPsAt nF nP ++ es)) ∧
      es.length = nIdx)
    (hopC : openPisAtFvars nP cvCa.type 0 = some (fvsP, crest))
    (hopX : openPisAtFvars nF crest nP
      = some (xFvs, Expr.mkAppN (.const T (lps.map .param)) (fvsP ++ idxArgs)))
    (hlenI : idxArgs.length = nIdx)
    (hsorts : ConLeche.checkStructFieldSortsI (ConLeche.fueledOps μ F) env isProp large resSort
      nP xFvs idxArgs nF = .ok sorts)
    (hfT : env.find? T = some (.indInfo cvTa caps))
    (hlpsT : cvTa.levelParams = lps)
    (hstripT : cvTa.type.stripPis (nP + nIdx) = some (bs, .sort resSort)) :
    ∃ (ds : (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (Es : (Name → Nat) → List AnnotTerm) (srcs : List (Option Nat)),
      idxArgs
          = (Expr.mkAppN (.const T (lps.map .param)) (fvsP ++ idxArgs)).getAppArgs.drop nP ∧
      CtorDataI mp.base2 T lps cvCa nP nF nIdx resSort isProp large idxArgs ds Es srcs := by
  obtain ⟨-, -, -, -, hlbt, hitf, type', stype, u, hann', htp', -, hst,
    hens, rfl⟩ := ConLeche.checkConstantVal_inv hccv
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann' hitf hlbt
  simp only at htf' hbt' htp' hst hens hopC hresid
  have hw : Expr.WScoped 0 type' := Expr.WScoped.of_not_hasFvar htf'
  have hL : Expr.LeavesBounded type' := Expr.LeavesBounded.of_not_hasFvar htf'
  have hnil : type'.fvarLeaves = [] :=
    Expr.fvarLeaves_eq_nil_of_not_hasFvar htf'
  have hlenP : fvsP.length = nP := openPisAtFvars_length _ hopC
  have hopAll := openPisAtFvars_add nP hopC (by rw [Nat.zero_add]; exact hopX)
  have hidx := openPisAtFvars_index nP type' 0 hopC
  obtain ⟨hlenX, hidxX, -⟩ := opening_vars_at hopX
  obtain ⟨F', tb, vb, hib, hensb, -, hbits⟩ :=
    piBits_of_infer hμ (nP + nF) hopAll hst hens
  rw [Nat.zero_add] at hib hensb
  obtain ⟨tf, htf⟩ := inferTypeCore_mkAppN_fn_inv (fvsP ++ idxArgs) hib
  obtain ⟨ci, hfci, -, rfl⟩ := ConLeche.inferTypeCore_const_inv htf
  obtain rfl : ci = .indInfo cvTa caps := Option.some.inj (hfci.symm.trans hfT)
  have htfT : ConLeche.inferTypeCore μ env F' (nP + nF)
      (.const T (lps.map .param)) = .ok cvTa.type := by
    have := htf
    rw [show (ConstantInfo.indInfo cvTa caps).toConstantVal = cvTa from rfl,
      hlpsT, Expr.instantiateLevelParams_self] at this
    exact this
  obtain rfl := inferTypeCore_mkAppN_sort (fvsP ++ idxArgs) htfT
    (by rw [List.length_append, hlenP, hlenI]; exact hstripT) hib
  have hvb := ensureSortCore_sort_eq hensb
  rw [hvb] at hbits
  -- the per-assignment reading
  have hper : ∀ ψ : Name → Nat, ∃ (ds : List (Nat × Nat × AnnotTerm)) (Es : List AnnotTerm),
      denoteMeta mp.base2.acval env ψ 0 type'
        = some (mkPisAV ds (ctorBodyAVI mp.base2 T nP nF ψ Es)) ∧
      ds.length = nP + nF ∧ Es.length = nIdx ∧
      DenoteMetaSpine mp.base2.acval env ψ (nP + nF) idxArgs Es ∧
      (∀ d ∈ ds, (resSort.eval ψ = 0 ↔ d.2.1 = 0)) ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ (mkPisAV ds (ctorBodyAVI mp.base2 T nP nF ψ Es))) ∧
      DomsBelow 0 ds ∧ (∀ E ∈ Es, Term.bvarsBelow (nP + nF) E.erase) := by
    intro ψ
    have hc := claimsAt_of hμ mp ψ F
    obtain ⟨Ta, hTa⟩ := acceptedReads_of mp.base2 ψ hst hw hbt' hL
    obtain ⟨-, -, hokT, -, -⟩ := hc.inferRow hst hw hbt' hL (CtxOk.nil hnil) hTa
    have hokT' : ∀ ρ : Nat → V, WellDenotedV V ρ Ta := fun ρ =>
      hokT ρ (Sat_nil V ρ)
    obtain ⟨Γ, R, htele, hop'⟩ := opened_of hopAll htf' hbt' hTa hokT'
    -- the residual's spine, inverted
    obtain ⟨fa, vs, hfa, hsp, hR⟩ := denoteMeta_mkAppN_inv hop'.body
    have hfa' : fa = mp.base2.acval T ψ := by
      have hconst := denoteMeta_const (acval := mp.base2.acval) (env := env) (φ := ψ)
        (d := nP + nF) hfT
        (show (lps.map Level.param).length
          = (ConstantInfo.indInfo cvTa caps).toConstantVal.levelParams.length by
          show (lps.map Level.param).length = cvTa.levelParams.length
          rw [hlpsT, List.length_map])
      have hsubst : Level.substFn ψ (ConstantInfo.indInfo cvTa caps).toConstantVal.levelParams
          (lps.map Level.param) = ψ := by
        show Level.substFn ψ cvTa.levelParams (lps.map Level.param) = ψ
        rw [hlpsT]
        exact Level.substFn_param_self ψ _
      rw [hconst, hsubst] at hfa
      exact (Option.some.inj hfa).symm
    subst hfa'
    obtain ⟨vs₁, vs₂, rfl, hsp₁, hsp₂⟩ := DenoteMetaSpine.append_inv hsp
    have hvs₁ : vs₁ = paramBvars nP nF := by
      have := DenoteMetaSpine.unique hsp₁
        (denoteMetaSpine_indexed (acval := mp.base2.acval) (env := env) (φ := ψ) (d := nP + nF)
          fvsP 0 hidx)
      rw [this, hlenP]
      unfold paramBvars
      apply List.map_congr_left
      intro k _
      rw [Nat.zero_add]
    subst hvs₁
    have hR' : R = ctorBodyAVI mp.base2 T nP nF ψ vs₂ := hR
    subst hR'
    obtain ⟨ds, hst', -⟩ := stripPisAV_of_piTeleAV htele
    obtain ⟨hTeq, hlen⟩ := stripPisAV_eq_mkPis hst'
    subst hTeq
    have hbelowAll := stripPisAV_below hst' (bvarsBelow_of_reading hw hbt' hTa)
    refine ⟨ds, vs₂, hTa, hlen, by rw [← hsp₂.length, hlenI], hsp₂, ?_, hokT', hbelowAll.1, ?_⟩
    · intro d hd
      exact (stripPisAV_bits (nP + nF) (hbits ψ) hTa hst' d hd).symm
    · intro E hE
      have hb := hbelowAll.2
      rw [Nat.zero_add] at hb
      unfold ctorBodyAVI at hb
      rw [AnnotTerm.erase_mkAppN] at hb
      exact (bvarsBelow_mkAppN_inv hb).2 _
        (List.mem_map.mpr ⟨E, List.mem_append_right _ hE, rfl⟩)
  -- the sources
  obtain ⟨hlenS, hfields⟩ := ConLeche.checkStructFieldSortsI_inv hsorts
  have hspec : ∀ ψ, _ := fun ψ => Classical.choose_spec (Classical.choose_spec (hper ψ))
  refine ⟨fun ψ => Classical.choose (hper ψ),
    fun ψ => Classical.choose (Classical.choose_spec (hper ψ)),
    srcsOf xFvs idxArgs sorts nF, ?_, ?_⟩
  · rw [Expr.getAppArgs_mkAppN, show (Expr.const T (lps.map .param)).getAppArgs = [] from rfl,
      List.nil_append, List.drop_left' hlenP]
  refine ⟨hresid, fun ψ => (hspec ψ).1, fun ψ => (hspec ψ).2.1, fun ψ => (hspec ψ).2.2.1,
    hlenI, fun ψ => (hspec ψ).2.2.2.1,
    fun ψ => (hspec ψ).2.2.2.2.1, fun ψ => (hspec ψ).2.2.2.2.2.1,
    fun ψ => (hspec ψ).2.2.2.2.2.2.1, fun ψ => (hspec ψ).2.2.2.2.2.2.2, ?_,
    srcsOf_length _ _ _ _, ?_, ?_, ?_⟩
  · -- level dependence
    intro ψ₁ ψ₂ hφ
    have h2 := (hspec ψ₂).1
    have h1 : denoteMeta mp.base2.acval env ψ₂ 0 type'
        = some (mkPisAV (Classical.choose (hper ψ₁))
          (ctorBodyAVI mp.base2 T nP nF ψ₁ (Classical.choose (Classical.choose_spec (hper ψ₁))))) := by
      rw [← denoteMeta_params_ext mp.base2 hφ 0 type' htp']
      exact (hspec ψ₁).1
    obtain ⟨hds, hbody⟩ := mkPisAV_inj
      (by rw [(hspec ψ₁).2.1, (hspec ψ₂).2.1]) (Option.some.inj (h1.symm.trans h2))
    refine ⟨hds, ?_⟩
    obtain ⟨-, hargs⟩ := mkAppN_inj_args (f := mp.base2.acval T ψ₁) (g := mp.base2.acval T ψ₂) hbody
      (by rw [List.length_append, List.length_append, (hspec ψ₁).2.2.1, (hspec ψ₂).2.2.1])
    exact List.append_cancel_left hargs
  · -- the sources are index positions
    intro s hs l hsl
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hs
    have hjn : j < nF := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      rwa [srcsOf_length] at this
    rw [srcsOf_getElem? _ _ _ _ _ hjn] at hj
    have hj' := Option.some.inj hj
    rw [hsl] at hj'
    split at hj'
    · exact nomatch hj'
    · have := firstIdx_some hj'
      rw [← hlenI]
      exact (List.getElem?_eq_some_iff.mp this).1
  · -- an index source reads to the field variable
    intro j l hjl ψ
    have hjn : j < nF := by
      have := (List.getElem?_eq_some_iff.mp hjl).1
      rwa [srcsOf_length] at this
    rw [srcsOf_getElem? _ _ _ _ _ hjn] at hjl
    have hjl' := Option.some.inj hjl
    split at hjl'
    · exact nomatch hjl'
    · have hidxl := firstIdx_some hjl'
      obtain ⟨fv, hfv⟩ : ∃ fv, xFvs[j]? = some fv := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨ty, rfl⟩ := hidxX j fv hfv
      rw [List.getD_eq_getElem?_getD, hfv, Option.getD_some] at hidxl
      obtain ⟨v, hv, hread⟩ := DenoteMetaSpine.getElem? ((hspec ψ).2.2.2.1) hidxl
      rw [denoteMeta_fvar, show nP + nF - 1 - (nP + j) = nF - 1 - j from by omega] at hread
      rw [hv, Option.some.inj hread]
  · -- the unsourced fields are propositional at a large-eliminating
    -- family instantiated at `Prop`
    intro hl ψ hw0 ρ hρ
    have hc := claimsAt_of hμ mp ψ F
    have hC : Opened mp.base2 ψ (nP + nF) type' (fvsP ++ xFvs)
        (Expr.mkAppN (.const T (lps.map .param)) (fvsP ++ idxArgs))
        (((Classical.choose (hper ψ)).map (·.2.2)).reverse)
        (ctorBodyAVI mp.base2 T nP nF ψ (Classical.choose (Classical.choose_spec (hper ψ)))) :=
      opened_of_peel hopAll htf' hbt' (hspec ψ).1 (hspec ψ).2.1 (hspec ψ).2.2.2.2.2.1
    have hlenDs : (Classical.choose (hper ψ)).length = nP + nF := (hspec ψ).2.1
    have hΓlen : ((((Classical.choose (hper ψ)).map (·.2.2)).reverse)).length = nP + nF := by
      rw [List.length_reverse, List.length_map, hlenDs]
    have hρ' : Sat V (((((Classical.choose (hper ψ)).map (·.2.2)).reverse)).drop
        (nP + nF - (nP + 0))) ρ := by
      rw [show nP + nF - (nP + 0) = nP + nF - nP from by omega,
        drop_fields_eq hlenDs nP (Nat.le_refl _), Nat.sub_self, List.drop_zero]
      exact hρ
    have hFsEq := fieldsFrom_eq_drop (ds := Classical.choose (hper ψ)) (nP := nP) (nF := nF) hlenDs
    rw [← hFsEq]
    have h := fieldsBoundSrc_of_frame (Γ := ((Classical.choose (hper ψ)).map (·.2.2)).reverse)
      (srcs := srcsOf xFvs idxArgs sorts nF) rfl hΓlen ?_ 0 (Nat.zero_le _) ρ hρ'
    · rw [List.drop_zero] at h; exact h
    intro j hj hsj ρ hρ
    obtain ⟨fv, ty, u, hfv, hu, hi, hens, hleq, hz⟩ := hfields j hj
    have hfvA : (fvsP ++ xFvs)[nP + j]? = some fv := by
      rw [List.getElem?_append_right (by omega), hlenP, Nat.add_sub_cancel_left]
      exact hfv
    obtain ⟨-, hws, hb, hL, hleaf⟩ := hC.var (nP + j) fv hfvA
    have hCtx := hC.ctx (i := nP + j) (by omega) hws hleaf
    have hread := hC.doms (nP + j) fv hfvA
    have hmem := (hc.sortRow hi hens hws hb hL hCtx hread ρ hρ).2
    -- the source is `none`: the sort evaluates to `0`
    have hu0 : u.eval ψ = 0 := by
      cases hp : isProp with
      | false =>
        have hle := Level.leq_sound (hleq hp) ψ
        omega
      | true =>
        rw [srcsOf_getElem? _ _ _ _ _ hj] at hsj
        have hsj' := Option.some.inj hsj
        have hsu : sorts.getD j .zero = u := by
          rw [List.getD_eq_getElem?_getD, hu, Option.getD_some]
        rw [hsu] at hsj'
        split at hsj'
        · next hequ => exact Level.isEquiv_sound (beq_iff_eq.mp hequ) ψ
        · rcases hz hp hl with h | h
          · exact Level.isEquiv_sound (beq_iff_eq.mp h) ψ
          · exfalso
            have hfvx : xFvs.getD j default = fv := by
              rw [List.getD_eq_getElem?_getD, hfv, Option.getD_some]
            rw [hfvx] at hsj'
            obtain ⟨i, hi'⟩ := firstIdx_of_mem (List.contains_iff_mem.mp h)
            rw [hi'] at hsj'
            exact nomatch hsj'
    rw [hu0] at hmem
    exact hmem

end ConLeche.Model

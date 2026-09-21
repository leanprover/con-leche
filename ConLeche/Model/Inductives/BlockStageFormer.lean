module

public import ConLeche.Model.Inductives.BlockLeafOk
public import ConLeche.Model.Inductives.FixStageFormer
public import ConLeche.Verify.Inductives.BlockWF
public section

/-!
# The k type formers' conses (task #315 M3)

`checkBlockInds` stores **all `k` formers before any constructor is
looked at** (official's `declare_inductive_types`), so the Model tier's
first block stage is a LOOP over `consBlockInds`, not a single cons.
Two things follow, and they are the whole content of this module.

* **`blockLeafWalks`** — `FixStageFormer.lean`'s `fixLeafWalks` at `k`:
  member `mm`'s leaf `blockTyAV … mm` has the same two hereditary
  premises (`ParamsOkXBI`, the tower's bit-validity), walked from the
  former's telescope down to the frame below the parameters and the
  member's index variables, where the block-wide base facts — the `k`
  index telescopes graded (`BlockIdxOk`), the `k` X-chain families
  graded (`BlockChainsOkI`) and valid — are the base.  The base facts
  are block-wide but the walk is member-local: the target enters
  nowhere.

* **`stageBlockFormers`** — the loop.  It is **abstract in the leaves**
  (`AOf : Nat → (Name → Nat) → AnnotTerm`), exactly as `ctorsLoopGen`
  is abstract in `leafT`: what a member's cons needs of its leaf is the
  five currency facts, and `blockLeafWalks` + the `blockTyAV` capstones
  supply them for the fixpoint leaf.  The one structural novelty at `k`
  is the η invariant: between the formers' conses and the last member's
  constructors up to `k` families are η-pending, so the loop threads
  `EtaFamiliesClosedExceptL env names` (`ConLeche/Verify/EnvGuards.lean`)
  rather than the one-family `EtaFamiliesClosedExcept`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps BlockShape)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The block leaf's two hereditary premises -/

section Walks

variable {k nP nIdx : Nat} {resSort : Level}
  {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
  {rsss : Nat → List (List Bool)} {tgtsss : Nat → List (List Nat)}
  {tlsss : Nat → List (List (List (Nat × Nat × AnnotTerm)))}
  {Eisss : Nat → List (List (List AnnotTerm))} {Fsss Esss : Nat → List (List AnnotTerm)}

/-- **The block leaf's two hereditary premises**, from the former's
data and the block-wide base facts at the parameter frame
(`fixLeafWalks` at `k` members). -/
theorem blockLeafWalks {pps : List (Nat × Nat × AnnotTerm)} {w : Nat}
    (hlen : pps.length = nP + nIdx) (hbits : ∀ d ∈ pps, d.2.1 ≠ 0)
    (hokTy : ∀ ρ : Nat → V, WellDenotedV V ρ (mkPisAV pps (.sort w)))
    {mm : Nat} (hmm : mm < k)
    (hIdsm : Idss mm = ((pps.drop nP).map (·.2.2)))
    (hIdx : ∀ ρp : Nat → V, Sat V ((pps.take nP).map (·.2.2)).reverse ρp →
      BlockIdxOk (V := V) k uf ρp Idss ∧ ∀ c, c < k → FieldsValid ρp (Idss c))
    (hX : ∀ ρp : Nat → V, Sat V ((pps.take nP).map (·.2.2)).reverse ρp →
      BlockChainsOkI k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss)
    (hXV : ∀ ρp : Nat → V, Sat V ((pps.take nP).map (·.2.2)).reverse ρp →
      ∀ Y, Y ∈ˢ famsSpaceB k w ρp uf Idss → ∀ c, c < k →
      ∀ t, t ∈ˢ idxSet (uf c) ρp (Idss c) →
      SumFieldsValid (cons t (cons Y ρp))
        (chainsXBI uf Idss (Idss c).length (rsss c) (tgtsss c) (tlsss c) (Eisss c)
          (Fsss c) (Esss c)))
    (ρ : Nat → V) :
    ParamsOkXBI k w ρ uf Idss rsss tgtsss tlsss Eisss Fsss Esss mm pps ∧
      UnderTowerValid ρ
        (.app (projAV mm ((blockBodyAV k w uf Idss rsss tgtsss tlsss Eisss Fsss Esss).liftN
            (Idss mm).length 0))
          (mkTowerGo (uf mm) (Idss mm))) pps := by
  have hst := stripPisAV_mkPisAV pps (.sort w)
  rw [hlen] at hst
  have htele := piTeleAV_of_stripPisAV hst
  obtain ⟨okΓ, -⟩ := piTeleAV_graded (V := V) htele (Δ₀ := []) (fun ρ _ => hokTy ρ)
  simp only [List.append_nil] at okΓ
  have hlenΓ : ((pps.map (·.2.2)).reverse).length = nP + nIdx := by simp [hlen]
  have hent : ∀ i, i < nP + nIdx → ∃ p, pps[i]? = some p ∧
      p.2.2 = ((pps.map (·.2.2)).reverse).getD (nP + nIdx - 1 - i) default := by
    intro i hi
    have hil : i < pps.length := by rw [hlen]; exact hi
    refine ⟨pps[i], List.getElem?_eq_getElem hil, ?_⟩
    rw [getD_reverse_of_peel hlen hi (List.getElem?_eq_getElem hil)]
  have hΓnil : ((pps.map (·.2.2)).reverse).drop (nP + nIdx - 0) = [] := by
    rw [Nat.sub_zero, List.drop_eq_nil_of_le (by rw [hlenΓ]; exact Nat.le_refl _)]
  have hIdsLen : (Idss mm).length = nIdx := by rw [hIdsm]; simp [hlen]
  -- the base facts at a frame satisfying the whole telescope
  have hbase : ∀ ρ : Nat → V, Sat V ((pps.map (·.2.2)).reverse) ρ →
      BlockBaseI k w ρ uf Idss rsss tgtsss tlsss Eisss Fsss Esss mm ∧
      AnnotValid V ρ
        (.app (projAV mm ((blockBodyAV k w uf Idss rsss tgtsss tlsss Eisss Fsss Esss).liftN
            (Idss mm).length 0))
          (mkTowerGo (uf mm) (Idss mm))) := by
    intro ρ hρ
    rw [reverse_map_take_drop pps nP] at hρ
    -- the parameter frame (at the MEMBER's index count: `hIdsm` is what
    -- makes the block-wide facts land at member `mm`'s own frame)
    have hle : (Idss mm).length ≤ (((pps.drop nP).map (·.2.2)).reverse).length := by
      rw [List.length_reverse, ← hIdsm]; exact Nat.le_refl _
    have hle2 : (((pps.drop nP).map (·.2.2)).reverse).length ≤ (Idss mm).length := by
      rw [List.length_reverse, ← hIdsm]; exact Nat.le_refl _
    have hρp : Sat V ((pps.take nP).map (·.2.2)).reverse
        (fun j => ρ (j + (Idss mm).length)) := by
      have := Sat_drop hρ (Idss mm).length
      rwa [List.drop_append_of_le_length hle, List.drop_eq_nil_of_le hle2,
        List.nil_append] at this
    have hsh : shiftE (Idss mm).length 0 ρ = fun j => ρ (j + (Idss mm).length) := by
      rw [shiftE_zero]
    -- the index spine
    have hspI := spineFit_of_sat (Δ₀ := ((pps.take nP).map (·.2.2)).reverse)
      (Ds := (pps.drop nP).map (·.2.2)) hρ
    rw [← hIdsm, ← frameIdx_eq_reverse_map] at hspI
    obtain ⟨hI, hIV⟩ := hIdx _ hρp
    refine ⟨⟨by rw [hsh]; exact hI, by rw [hsh]; exact hX _ hρp, by rw [hsh]; exact hspI⟩, ?_⟩
    have hfr : consList (frameIdx (Idss mm).length ρ) (fun j => ρ (j + (Idss mm).length)) = ρ := by
      have := consList_frameIdx (Idss mm).length ρ
      rwa [hsh] at this
    have hv := blockLeafBody_validV hI hIV (hXV _ hρp) hmm
      (is := frameIdx (Idss mm).length ρ) hspI
    rwa [hfr] at hv
  constructor
  · have hw := hereditaryWalk (V := V)
      (Q := fun ρ ds => ParamsOkXBI k w ρ uf Idss rsss tgtsss tlsss Eisss Fsss Esss mm ds)
      hlenΓ hlen hent okΓ
      (fun ρ hρ => (hbase ρ hρ).1)
      (fun ρ d ds hd hok hrec => ⟨hbits d hd, hok.1, hrec⟩)
      0 (Nat.zero_le _) ρ (by rw [hΓnil]; exact Sat_nil V ρ)
    simpa using hw
  · have hw := hereditaryWalk (V := V)
      (Q := fun ρ ds => UnderTowerValid ρ
        (.app (projAV mm ((blockBodyAV k w uf Idss rsss tgtsss tlsss Eisss Fsss Esss).liftN
            (Idss mm).length 0))
          (mkTowerGo (uf mm) (Idss mm))) ds)
      hlenΓ hlen hent okΓ
      (fun ρ hρ => (hbase ρ hρ).2)
      (fun ρ d ds hd hok hrec => ⟨hok.2, hrec⟩)
      0 (Nat.zero_le _) ρ (by rw [hΓnil]; exact Sat_nil V ρ)
    simpa using hw

end Walks

/-! ## The k formers' conses -/

/-- **The P step at one block member's former cons**: the leaf's five
currency facts and the capability laws, at the environment holding the
EARLIER members' formers.  `stageFixFormer`'s body, with the former's
`checkConstantVal` run replaced by the facts it yields (the run happened
at the PRE-block environment, not at this one) and the η closure taken
over the block's whole member list. -/
theorem stageBlockFormer (mp : EnvModelM V μ env) {names : List Name}
    (hE : ConLeche.EtaFamiliesClosedExceptL env names)
    {cvTa : ConstantVal} {caps : IndCaps} {A : (Name → Nat) → AnnotTerm}
    {nP : Nat} {resSort : Level} {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hfresh : env.find? cvTa.name = none)
    (hnres : ConLeche.reservedBasisNames.contains cvTa.name = false)
    (hpshape : cvTa.name.isProjFnShape = false)
    (hcb : ConstsBound env cvTa.type)
    (hwfI : ConLeche.EnvWF ⟨.indInfo cvTa caps :: env.consts⟩)
    (hFD : FormerData mp.base2 cvTa nP resSort pps)
    (hAbelow : ∀ ψ, Term.bvarsBelow 0 (A ψ).erase)
    (hAparams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvTa.levelParams, ψ₁ q = ψ₂ q) → A ψ₁ = A ψ₂)
    (hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenoted V ρ (A ψ))
    (hAvalid : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotValid V ρ (A ψ))
    (hAmem : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (A ψ) ∈ˢ interp V ρ (mkPisAV (pps ψ) (.sort (resSort.eval ψ))))
    (hTlaws : ∀ m₂ : EnvModel V ⟨.indInfo cvTa caps :: env.consts⟩,
      m₂.acval = acvalWith mp.base2.acval cvTa.name A →
      CapsLawsAt m₂ cvTa.name cvTa caps) :
    ∃ mp' : EnvModelM V μ ⟨.indInfo cvTa caps :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval cvTa.name A := by
  have hreadI : ∀ ψ : Name → Nat,
      denoteMeta (acvalWith mp.base2.acval cvTa.name A)
        ⟨.indInfo cvTa caps :: env.consts⟩ ψ 0 cvTa.type
        = some (mkPisAV (pps ψ) (.sort (resSort.eval ψ))) := fun ψ =>
    denoteMeta_cons_mono (c₀ := .indInfo cvTa caps) hfresh
      (ConsCrossAt.ofNtc fun _ h => nomatch h) ψ 0 hcb (hFD.read ψ)
  have hnresI : ConLeche.reservedBasisNames.contains
      (ConstantInfo.indInfo cvTa caps).name = false := hnres
  refine declStep_preserves_of_ind_member_cons mp (c₀ := .indInfo cvTa caps)
    (A := A) hfresh hnresI (Or.inl ⟨_, _, rfl⟩)
    (ConsHead.ofFresh hwfI hAbelow hnresI
      (fun _ h => nomatch h)
      (fun _ _ _ _ h => nomatch h))
    (fun ψ kk => AnnotTerm.liftN_eq_self _
      (Term.bvarsBelow.mono (Nat.zero_le kk) (hAbelow ψ)) 1)
    hAparams hAok hAvalid (fun ψ => ⟨_, hreadI ψ⟩) ?_ ?_ ?_
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadI ψ).symm.trans hta)
    exact hFD.okTy ψ ρ
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadI ψ).symm.trans hta)
    exact hAmem ψ ρ
  · intro m₂ hac
    refine capsOk_cons_native mp (c₀ := .indInfo cvTa caps)
      (A := A) (T := cvTa.name) hfresh
      (ConsCrossEnv.ofNtc fun _ h => nomatch h) hpshape
      (Or.inl ⟨cvTa, caps, rfl, rfl⟩) ?_ m₂ hac ?_
    · -- the OTHER stored families: outside the block they are closed;
      -- a still-pending MEMBER's η constructor is a `ctorInfo`, which
      -- this cons — a former — is not
      intro T' cvT' caps' hf hne hres hcape hfam
      by_cases hmemT : T' ∈ names
      · obtain ⟨-, ⟨cvC', cnP, cnF, hfC'⟩, -⟩ := hfam
        intro hh
        rw [hh, ConLeche.Env.find?_cons_self] at hfC'
        exact nomatch (Option.some.inj hfC')
      · exact etaCtor_ne_of_closed hfresh (hE T' cvT' caps' hf hmemT hcape hres)
    · intro cvT caps' hf _
      have hself := ConLeche.Env.find?_cons_self (ConstantInfo.indInfo cvTa caps) env
      obtain ⟨rfl, rfl⟩ :=
        ConstantInfo.indInfo.inj (Option.some.inj (hself.symm.trans hf))
      exact hTlaws m₂ hac

/-- **The `k` type formers' conses, in order** (`checkBlockInds`'s
`consBlockInds`).  Abstract in the leaves, as `ctorsLoopGen` is abstract
in `leafT`: the leaf's five currency facts (`hAbelowOf` … `hAmemOf`) and
the member's capability laws (`hTlawsOf`) are the per-member inputs, and
`blockLeafWalks` with the `blockTyAV` capstones supplies them for the
fixpoint leaf.  The η invariant is threaded over the block's whole
member list, because all `k` formers are stored before any constructor. -/
theorem stageBlockFormers {p₁ : BlockShape} {isRec : Bool} {names : List Name}
    {cvTasAll : List ConstantVal} {A : Nat → (Name → Nat) → AnnotTerm}
    {nPOf : Nat → Nat} {resSort : Level}
    {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hnames : ∀ (j : Nat) (cvTa : ConstantVal), cvTasAll[j]? = some cvTa →
      cvTa.name ∈ names)
    (hndN : ∀ (j j' : Nat) (c c' : ConstantVal), cvTasAll[j]? = some c →
      cvTasAll[j']? = some c' → j ≠ j' → c.name ≠ c'.name)
    (hnresOf : ∀ (j : Nat) (cvTa : ConstantVal), cvTasAll[j]? = some cvTa →
      ConLeche.reservedBasisNames.contains cvTa.name = false)
    (hpshapeOf : ∀ (j : Nat) (cvTa : ConstantVal), cvTasAll[j]? = some cvTa →
      cvTa.name.isProjFnShape = false)
    (htyWF : ∀ (j : Nat) (cvTa : ConstantVal), cvTasAll[j]? = some cvTa →
      cvTa.type.hasFvar = false ∧
      cvTa.type.allLevelParamsDefined cvTa.levelParams = true ∧
      cvTa.type.looseBVarsBounded 0 = true ∧
      (cvTa.type.stripPis p₁.nP).isSome = true)
    (hAbelowOf : ∀ (j : Nat) (ψ : Name → Nat), Term.bvarsBelow 0 (A j ψ).erase)
    (hAparamsOf : ∀ (j : Nat) (cvTa : ConstantVal), cvTasAll[j]? = some cvTa →
      ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvTa.levelParams, ψ₁ q = ψ₂ q) → A j ψ₁ = A j ψ₂)
    (hAokOf : ∀ (j : Nat) (ψ : Name → Nat) (ρ : Nat → V), WellDenoted V ρ (A j ψ))
    (hAvalidOf : ∀ (j : Nat) (ψ : Name → Nat) (ρ : Nat → V), AnnotValid V ρ (A j ψ))
    (hAmemOf : ∀ (j : Nat) (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (A j ψ) ∈ˢ interp V ρ (mkPisAV (ppsOf j ψ) (.sort (resSort.eval ψ))))
    (hTlawsOf : ∀ (j : Nat) (cvTa : ConstantVal), cvTasAll[j]? = some cvTa →
      ∀ {env' : Env} (m' : EnvModel V env')
        (m₂ : EnvModel V ⟨.indInfo cvTa (ConLeche.blockCapsAt p₁ j isRec) :: env'.consts⟩),
      m₂.acval = acvalWith m'.acval cvTa.name (A j) →
      CapsLawsAt m₂ cvTa.name cvTa (ConLeche.blockCapsAt p₁ j isRec)) :
    ∀ (rest : List ConstantVal) (i : Nat) (env : Env) (mp : EnvModelM V μ env),
      (∀ j, rest[j]? = cvTasAll[i + j]?) → i + rest.length = cvTasAll.length →
      ConLeche.EtaFamiliesClosedExceptL env names →
      (∀ (j : Nat) (cvTa : ConstantVal), cvTasAll[j]? = some cvTa →
        cvTa.type.constsResolve env = true) →
      (∀ (j : Nat) (cvTa : ConstantVal), i ≤ j → cvTasAll[j]? = some cvTa →
        env.find? cvTa.name = none) →
      (∀ (j : Nat) (cvTa : ConstantVal), cvTasAll[j]? = some cvTa →
        FormerData mp.base2 cvTa (nPOf j) resSort (ppsOf j)) →
      (∀ (j : Nat) (cvTa : ConstantVal), j < i → cvTasAll[j]? = some cvTa →
        env.find? cvTa.name = some (.indInfo cvTa (ConLeche.blockCapsAt p₁ j isRec)) ∧
        ∀ ψ, mp.base2.acval cvTa.name ψ = A j ψ) →
      ∃ mp' : EnvModelM V μ (ConLeche.consBlockInds p₁ isRec rest i env),
        ConLeche.EtaFamiliesClosedExceptL (ConLeche.consBlockInds p₁ isRec rest i env) names ∧
        (∀ (j : Nat) (cvTa : ConstantVal), cvTasAll[j]? = some cvTa →
          FormerData mp'.base2 cvTa (nPOf j) resSort (ppsOf j)) ∧
        (∀ (j : Nat) (cvTa : ConstantVal), cvTasAll[j]? = some cvTa →
          (ConLeche.consBlockInds p₁ isRec rest i env).find? cvTa.name
            = some (.indInfo cvTa (ConLeche.blockCapsAt p₁ j isRec)) ∧
          ∀ ψ, mp'.base2.acval cvTa.name ψ = A j ψ)
  | [], i, env, mp, _, hk, hE, _, _, hFD, hcons => by
    simp only [List.length_nil, Nat.add_zero] at hk
    refine ⟨mp, hE, hFD, ?_⟩
    intro j cvTa hj
    exact hcons j cvTa (by rw [hk]; exact (List.getElem?_eq_some_iff.mp hj).1) hj
  | cvTa :: rest, i, env, mp, hrest, hk, hE, hres, hfreshOf, hFD, hcons => by
    have hi : cvTasAll[i]? = some cvTa := by
      have := hrest 0; simpa using this.symm
    have hfresh : env.find? cvTa.name = none := hfreshOf i cvTa (Nat.le_refl _) hi
    have hcb : ConstsBound env cvTa.type :=
      constsBound_of_constsResolve _ (hres i cvTa hi)
    obtain ⟨hhf, hlp, hlb, hspi⟩ := htyWF i cvTa hi
    have hwfI : ConLeche.EnvWF
        ⟨.indInfo cvTa (ConLeche.blockCapsAt p₁ i isRec) :: env.consts⟩ :=
      ConLeche.envWF_cons_blockInd mp.base2.wf hhf hlp (hres i cvTa hi) hlb hspi
    obtain ⟨mpI, hacI⟩ := stageBlockFormer mp (names := names) hE hfresh
      (hnresOf i cvTa hi) (hpshapeOf i cvTa hi) hcb hwfI (hFD i cvTa hi)
      (hAbelowOf i) (hAparamsOf i cvTa hi) (hAokOf i) (hAvalidOf i) (hAmemOf i)
      (fun m₂ hac => hTlawsOf i cvTa hi mp.base2 m₂ hac)
    -- the invariants at the extension
    have hne : ∀ (j : Nat) (cvTb : ConstantVal), cvTasAll[j]? = some cvTb → j ≠ i →
        cvTb.name ≠ cvTa.name := fun j cvTb hj hji => hndN j i cvTb cvTa hj hi hji
    have hE' : ConLeche.EtaFamiliesClosedExceptL
        (⟨.indInfo cvTa (ConLeche.blockCapsAt p₁ i isRec) :: env.consts⟩ : Env) names :=
      hE.cons hfresh (fun _ _ heq _ => by
        obtain ⟨rfl, -⟩ := ConstantInfo.indInfo.inj heq
        exact Or.inr (hnames i cvTa hi))
    have hres' : ∀ (j : Nat) (cvTb : ConstantVal), cvTasAll[j]? = some cvTb →
        cvTb.type.constsResolve
          (⟨.indInfo cvTa (ConLeche.blockCapsAt p₁ i isRec) :: env.consts⟩ : Env) = true :=
      fun j cvTb hj => Expr.constsResolve_mono (hres j cvTb hj)
    have hfreshOf' : ∀ (j : Nat) (cvTb : ConstantVal), i + 1 ≤ j → cvTasAll[j]? = some cvTb →
        (⟨.indInfo cvTa (ConLeche.blockCapsAt p₁ i isRec) :: env.consts⟩ : Env).find?
          cvTb.name = none := by
      intro j cvTb hij hj
      rw [ConLeche.Env.find?_cons,
        if_neg (fun hh => hne j cvTb hj (by omega) hh.symm)]
      exact hfreshOf j cvTb (by omega) hj
    have hFD' : ∀ (j : Nat) (cvTb : ConstantVal), cvTasAll[j]? = some cvTb →
        FormerData mpI.base2 cvTb (nPOf j) resSort (ppsOf j) := by
      intro j cvTb hj
      exact (hFD j cvTb hj).cross (c₀ := .indInfo cvTa (ConLeche.blockCapsAt p₁ i isRec))
        hfresh (ConsCrossAt.ofNtc fun _ h => nomatch h)
        (constsBound_of_constsResolve _ (hres j cvTb hj)) mpI.base2 hacI
    have hcons' : ∀ (j : Nat) (cvTb : ConstantVal), j < i + 1 → cvTasAll[j]? = some cvTb →
        (⟨.indInfo cvTa (ConLeche.blockCapsAt p₁ i isRec) :: env.consts⟩ : Env).find? cvTb.name
          = some (.indInfo cvTb (ConLeche.blockCapsAt p₁ j isRec)) ∧
        ∀ ψ, mpI.base2.acval cvTb.name ψ = A j ψ := by
      intro j cvTb hji hj
      rcases Nat.lt_or_ge j i with hlt | hge
      · obtain ⟨hfj, hleafj⟩ := hcons j cvTb hlt hj
        refine ⟨ConLeche.Env.find?_cons_of_fresh hfresh hfj, fun ψ => ?_⟩
        rw [hacI]
        show acvalWith mp.base2.acval cvTa.name (A i) cvTb.name ψ = _
        rw [acvalWith_ne (hne j cvTb hj (by omega))]
        exact hleafj ψ
      · have hij : j = i := by omega
        subst hij
        obtain rfl := Option.some.inj (hi.symm.trans hj)
        refine ⟨ConLeche.Env.find?_cons_self _ env, fun ψ => ?_⟩
        rw [hacI]
        exact congrFun acvalWith_self ψ
    have hrest' : ∀ j, rest[j]? = cvTasAll[i + 1 + j]? := by
      intro j
      have := hrest (j + 1)
      rwa [show i + (j + 1) = i + 1 + j from by omega] at this
    exact stageBlockFormers hnames hndN hnresOf hpshapeOf htyWF hAbelowOf hAparamsOf hAokOf
      hAvalidOf hAmemOf hTlawsOf rest (i + 1) _ mpI hrest' (by simp at hk; omega) hE'
      hres' hfreshOf' hFD' hcons'

end ConLeche.Model

import Setlec.SetP.DirectEntryLawP

/-!
# The projection entry's cons (task #175 W4c, P3 module 7, part 6)

`stageEntry`: the P step at a tower entry's cons.  The entry's leaf is
a constant-bit λ-tower over the entry type's binder data with a
**choice body**: `Classical.choice` at the residual — the residual is
inhabited at every satisfying frame (the graph regime by the tower's
projection membership, the squash regime by the proof field at the
point prefix, or, at the first field, by the fitting chain's head),
so the leaf inhabits the entry type whatever the instantiation.  (The
projection *value* is never the leaf's business: a `.proj` node reads
as `projAV`, and the stored constant is a table entry no term
names.)  The leaf's walks are the entry frame's; the entry's law is
`entryLawP`, assembled from the three semantic cores over the frames.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory Setlec.SetTheory.Tower
open Setlec.SetR (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta ProjEntry projFnName)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The choice body -/

/-- The point witnesses a non-empty set's double negation. -/
theorem pt_mem_dnegSpace2 {A x : V} (hx : x ∈ˢ A) : (pt : V) ∈ˢ dnegSpace2 V A := by
  unfold dnegSpace2
  rw [piR_zero]
  refine pt_mem_truthVal fun f hf => ?_
  exfalso
  rw [piR_zero] at hf
  obtain ⟨hp, -⟩ := mem_truthVal.mp hf
  obtain ⟨y, hy⟩ := hp x hx
  exact not_mem_empty y hy

/-- `Classical.choice` at level `u` inhabits its type's reading. -/
theorem choiceV2_mem (u : Nat) :
    choiceV2 V u ∈ˢ piR u (univ u : V)
      (fun A => piR u (dnegSpace2 V A) fun _ => A) := by
  unfold choiceV2
  refine lamR_mem (V := V) fun A _ => ?_
  refine lamR_mem (V := V) fun h hh => ?_
  obtain ⟨x, hx⟩ := exists_mem_of_dneg2 V hh
  exact schoice_mem hx

/-- A residual's level: some universe every satisfying frame's reading
lands in (`0` if none). -/
noncomputable def resLevel (V : Type w) [SetTheory V] (Γ : List AVExpr) (R : AVExpr) : Nat :=
  Classical.epsilon fun u : Nat => ∀ ρ : Nat → V, Sat2 V Γ ρ → interp2 V ρ R ∈ˢ (univ u : V)

theorem resLevel_spec {Γ : List AVExpr} {R : AVExpr}
    (h : ∃ u : Nat, ∀ ρ : Nat → V, Sat2 V Γ ρ → interp2 V ρ R ∈ˢ (univ u : V)) :
    ∀ ρ : Nat → V, Sat2 V Γ ρ → interp2 V ρ R ∈ˢ (univ (resLevel V Γ R) : V) :=
  Classical.epsilon_spec h

/-- The entry leaf's body: choice at the residual. -/
def entryBody (u : Nat) (R : AVExpr) : AVExpr :=
  .app (.app (.const .choice [u]) R) .prf

/-- The body is graded, bit-valid and a member of the residual wherever
the residual is a non-empty set of level `u`. -/
theorem entryBody_ok {u : Nat} {R : AVExpr} {ρ : Nat → V}
    (hokR : AnnotOkP V ρ R) (hu : interp2 V ρ R ∈ˢ (univ u : V))
    (hne : ∃ y, y ∈ˢ interp2 V ρ R) :
    AnnotOk2 V ρ (entryBody u R) ∧ AnnotValidV V ρ (entryBody u R) ∧
      interp2 V ρ (entryBody u R) ∈ˢ interp2 V ρ R := by
  obtain ⟨y, hy⟩ := hne
  have hval : interp2 V ρ (entryBody u R) = schoice (interp2 V ρ R) := by
    show SetTheory.app (SetTheory.app (bval2 V .choice [u]) (interp2 V ρ R)) pt = _
    exact choiceV2_app V hu (pt_mem_dnegSpace2 hy)
  refine ⟨?_, ?_, by rw [hval]; exact schoice_mem hy⟩
  · unfold entryBody
    rw [AnnotOk2_app]
    refine ⟨?_, trivial, ?_⟩
    · rw [AnnotOk2_app]
      refine ⟨trivial, hokR.1, u, univ u,
        fun A => piR u (dnegSpace2 V A) fun _ => A, ?_, hu, fun h0 _ _ => ?_⟩
      · show bval2 V .choice [u] ∈ˢ _
        exact choiceV2_mem u
      · subst h0
        exact piR_zero_mem_univZero
    · refine ⟨u, dnegSpace2 V (interp2 V ρ R), fun _ => interp2 V ρ R, ?_,
        by rw [interp2_prf]; exact pt_mem_dnegSpace2 hy, fun h0 _ _ => ?_⟩
      · show SetTheory.app (bval2 V .choice [u]) (interp2 V ρ R) ∈ˢ _
        by_cases hu0 : u = 0
        · subst hu0
          show SetTheory.app (choiceV2 V 0) _ ∈ˢ _
          rw [choiceV2, lamR_zero, app_pt, piR_zero]
          exact pt_mem_truthVal fun _ _ => ⟨y, hy⟩
        · show SetTheory.app (choiceV2 V u) _ ∈ˢ _
          rw [choiceV2, app_lamR_pos hu0 hu]
          exact lamR_mem fun h hh => schoice_mem hy
      · subst h0
        rw [← univ_zero]
        exact hu
  · unfold entryBody
    rw [AnnotValidV_app, AnnotValidV_app]
    exact ⟨⟨trivial, hokR.2⟩, trivial⟩

omit [SetTheory V] in
theorem entryBody_below {u : Nat} {R : AVExpr} {k : Nat} (h : VExpr.bvarsBelow k R.erase) :
    VExpr.bvarsBelow k (entryBody u R).erase :=
  ⟨⟨trivial, h⟩, trivial⟩

/-! ## The residual is inhabited -/

/-- At a squash instance under the guard, the point inhabits the field
at the point prefix. -/
theorem squash_pt_mem {nP nF i : Nat} {ds : List (Nat × Nat × AVExpr)} {sorts : List Level}
    {ψ : Name → Nat} {ρ' : Nat → V}
    (hlenDs : ds.length = nP + nF) (hi : i < nF)
    (hsorts : ∀ j, j < nF → ∀ as : List V,
      SpineFit ρ' (((ds.drop nP).map (·.2.2)).take j) as →
      interp2 V (consList as ρ') (((ds.drop nP).map (·.2.2)).getD j default)
        ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V))
    (hguard : ∀ j, j ≤ i → (sorts.getD j .zero).eval ψ = 0)
    {as' : List V} (hspAs : SpineFit ρ' ((ds.drop nP).map (·.2.2)) as') :
    (pt : V) ∈ˢ interp2 V (consList (List.replicate i pt) ρ')
      (((ds.drop nP).map (·.2.2)).getD i default) := by
  have hlenFs : (((ds.drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
  obtain ⟨hpre, hnext⟩ := spineFit_prefix_next hspAs (by rw [hlenFs]; exact hi)
  have hrep : as'.take i = List.replicate i pt := by
    have := spineFit_eq_replicate_pt hpre ?_
    · rwa [List.length_take, hlenFs, show min i nF = i from by omega] at this
    intro j hj bs hbs
    rw [List.length_take, hlenFs] at hj
    rw [List.take_take, show min j i = j from by omega] at hbs
    have := hsorts j (by omega) bs hbs
    rw [hguard j (by omega)] at this
    rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega),
      ← List.getD_eq_getElem?_getD]
    exact this
  have hz := hsorts i hi _ hpre
  rw [hguard i (Nat.le_refl _)] at hz
  have hval := mem_univ_zero hz hnext
  rw [hval, hrep] at hnext
  exact hnext

/-! ## The cons -/

/-- **The P step at a tower entry's cons.** -/
theorem stageEntry (hμ : μ.verified = true) (mp : EnvS2PM V μ env)
    {F i : Nat} {p : DirectParts} {cvTa cvCa : ConstantVal} {sorts : List Level}
    {guard : Level} {pty : Expr} {envOut : Env}
    (hEntry : Setlec.checkDirectProjEntry (Setlec.fueledOps μ F) p.cvT.name p.cvC.name
      p.cvT.levelParams p.nP p.nF p.resSort guard cvCa pty env i = .ok envOut)
    (hwf : Setlec.EnvWF envOut)
    (hfT : env.find? p.cvT.name = some (.indInfo cvTa (Setlec.directCaps p)))
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    (hfC : env.find? p.cvC.name = some (.ctorInfo cvCa p.nP p.nF))
    (hlpsC : cvCa.levelParams = p.cvT.levelParams)
    (hstripC : (cvCa.type.stripPis (p.nP + p.nF)).isSome = true)
    (hProp : p.isProp = (Level.isEquiv p.resSort .zero == some true))
    (hTshape : p.cvT.name.isProjFnShape = false)
    (hCshape : p.cvC.name.isProjFnShape = false)
    (hresT : Setlec.reservedBasisNames.contains p.cvT.name = false)
    (hresR : Setlec.reservedBasisNames.contains (p.cvT.name.str "rec") = false)
    (hresC : Setlec.reservedBasisNames.contains p.cvC.name = false)
    (hi : i < p.nF)
    (hguardSem : ∀ ψ : Name → Nat, guard.eval ψ = 0 →
      ∀ j, j ≤ i → (sorts.getD j .zero).eval ψ = 0)
    (hO5 : (Level.isEquiv p.resSort .zero == some true) = false →
      ∀ ψ : Name → Nat, p.resSort.eval ψ = 0 → guard.eval ψ = 0)
    (hguardOrFirst : ∀ ψ : Name → Nat, p.resSort.eval ψ = 0 → guard.eval ψ = 0 ∨ i = 0)
    (hnp : NoProjEnv env p.cvT.name i)
    (hprev : ∀ j, j < i → ∃ entry, env.findProj? p.cvT.name j = some entry ∧ entry.tower = true)
    {pps ds : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hFD : FormerData mp.base2 cvTa p.nP p.resSort pps)
    (hCD : CtorData mp.base2 p.cvT.name cvCa p.nP p.nF p.resSort ds)
    (hleafT : ∀ ψ, mp.base2.acval p.cvT.name ψ
      = directTyAV (p.resSort.eval ψ) (pps ψ) (((ds ψ).drop p.nP).map (·.2.2)))
    (hleafC : ∀ ψ, mp.base2.acval p.cvC.name ψ
      = directMkAV (p.resSort.eval ψ) (ds ψ) (((ds ψ).drop p.nP).map (·.2.2)))
    (hiff : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V ((pps ψ).map (·.2.2)).reverse ρ ↔
        Sat2 V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ)
    (hfields : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ →
        FieldsOkB (p.resSort.eval ψ) ρ (((ds ψ).drop p.nP).map (·.2.2)) ∧
        FieldsValid ρ (((ds ψ).drop p.nP).map (·.2.2)) ∧
        (p.isProp = false →
          FieldsBound (p.resSort.eval ψ) ρ (((ds ψ).drop p.nP).map (·.2.2))) ∧
        (p.isProp = true → p.large = true →
          FieldsBound 0 ρ (((ds ψ).drop p.nP).map (·.2.2))) ∧
        (∀ j, j < p.nF → ∀ as : List V,
          SpineFit ρ ((((ds ψ).drop p.nP).map (·.2.2)).take j) as →
          interp2 V (consList as ρ) ((((ds ψ).drop p.nP).map (·.2.2)).getD j default)
            ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V))) :
    ∃ (A : (Name → Nat) → AVExpr) (mp' : EnvS2PM V μ envOut),
      mp'.base2.acval = acvalWith mp.base2.acval (projFnName p.cvT.name i) A := by
  -- the stage's shape
  obtain ⟨hnf, -, ptyA, hann, hlpd, hcr, hb, hnfA, -, ⟨sty, u, hinf, hens⟩, hfresh,
    ⟨fvsP, prest, sbs, sbody, sdom, tFvs, resid, tfv, cdomsP, crestP, cds, nmC, fdom, bodyC, mbC,
      hopP, hsb, hsd, hsdeq, hopT, htfv, hci, hdoms, hcf, hrdeq⟩, rfl⟩ :=
    Setlec.checkDirectProjEntry_shape hEntry
  let entry : ProjEntry := ⟨p.cvT.name, i, p.cvT.levelParams, p.nP, p.cvC.name, p.nF, ptyA,
    guard, p.resSort, true, false, true⟩
  obtain ⟨vb, eds, R, hED⟩ := entryData_of hμ mp hlpd hb hnfA hinf hens hopP hopT
  -- the field-chain facts, in the frames' spelling
  have hbound : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ → p.resSort.eval ψ ≠ 0 →
      FieldsBound (p.resSort.eval ψ) ρ (((ds ψ).drop p.nP).map (·.2.2)) := by
    intro ψ ρ hρ hw
    cases hp : p.isProp
    · exact (hfields ψ ρ hρ).2.2.1 hp
    · exfalso
      apply hw
      rw [hp] at hProp
      exact Level.isEquiv_sound (beq_iff_eq.mp hProp.symm) ψ
  have hokB : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ →
      FieldsOkB (p.resSort.eval ψ) ρ (((ds ψ).drop p.nP).map (·.2.2)) ∧
      FieldsValid ρ (((ds ψ).drop p.nP).map (·.2.2)) :=
    fun ψ ρ h => ⟨(hfields ψ ρ h).1, (hfields ψ ρ h).2.1⟩
  have hsorts : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ →
      ∀ j, j < p.nF → ∀ as : List V,
        SpineFit ρ ((((ds ψ).drop p.nP).map (·.2.2)).take j) as →
        interp2 V (consList as ρ) ((((ds ψ).drop p.nP).map (·.2.2)).getD j default)
          ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V) :=
    fun ψ ρ h => (hfields ψ ρ h).2.2.2.2
  have hframes := entryFrames hμ mp hopP hsb hsd hsdeq hopT htfv hci hdoms hcf hrdeq hfT hlpsT
    hfC hprev hi hED hFD hCD hleafT hiff hokB hbound hsorts
  have hpok : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ParamsOkT (p.resSort.eval ψ) ρ (((ds ψ).drop p.nP).map (·.2.2)) (pps ψ) :=
    fun ψ ρ => (formerWalks hFD (fun ψ' ρ' h => hokB ψ' ρ' ((hiff ψ' ρ').mp h)) ψ ρ).1
  -- names
  have hneT : p.cvT.name ≠ projFnName p.cvT.name i := by
    intro h
    have := projFnName_isProjFnShape p.cvT.name i
    rw [← h, hTshape] at this
    exact nomatch this
  have hneC : p.cvC.name ≠ projFnName p.cvT.name i := by
    intro h
    have := projFnName_isProjFnShape p.cvT.name i
    rw [← h, hCshape] at this
    exact nomatch this
  have hnres : Setlec.reservedBasisNames.contains (projFnName p.cvT.name i) = false := by
    cases h : Setlec.reservedBasisNames.contains (projFnName p.cvT.name i)
    · rfl
    · exact absurd rfl (Setlec.projFnName_ne_reserved h)
  -- the crossings
  have hcrossT : ConsCrossAt (.projInfo entry) cvTa.type := by
    intro e' he' _
    cases he'
    exact hnp.type _ (Setlec.SetR.Env.find?_mem hfT)
  have hcrossC : ConsCrossAt (.projInfo entry) cvCa.type := by
    intro e' he' _
    cases he'
    exact hnp.type _ (Setlec.SetR.Env.find?_mem hfC)
  have hcrossE : ConsCrossAt (.projInfo entry) ptyA := by
    intro e' he' _
    cases he'
    exact Setlec.annotateCore_noProjAt μ hann hnf hfresh
  have hcbT : ConstsBound env cvTa.type :=
    constsBound_of_constsResolve _ (mp.base2.wf _ (Setlec.SetR.Env.find?_mem hfT)).2.2.1
  have hcbC : ConstsBound env cvCa.type :=
    constsBound_of_constsResolve _ (mp.base2.wf _ (Setlec.SetR.Env.find?_mem hfC)).2.2.1
  have hcbE : ConstsBound env ptyA := constsBound_of_constsResolve _ hcr
  -- the leaf
  let Γe : (Name → Nat) → List AVExpr := fun ψ => ((eds ψ).map (·.2.2)).reverse
  let m : (Name → Nat) → Nat := fun ψ => ((eds ψ).getD 0 default).2.1
  let body : (Name → Nat) → AVExpr := fun ψ => entryBody (resLevel V (Γe ψ) (R ψ)) (R ψ)
  let A : (Name → Nat) → AVExpr := fun ψ => mkLamsC (m ψ) (eds ψ) (body ψ)
  have hlenFs : ∀ ψ, ((((ds ψ).drop p.nP).map (·.2.2))).length = p.nF := by
    intro ψ; simp [hCD.len ψ]
  have hlenΓ : ∀ ψ, (Γe ψ).length = p.nP + 1 := by intro ψ; simp [Γe, hED.len ψ]
  have hz : ∀ ψ, ∀ d ∈ eds ψ, (m ψ = 0 ↔ d.2.1 = 0) := by
    intro ψ d hd
    have h0 : (eds ψ).getD 0 default ∈ eds ψ :=
      Setlec.getD_mem (by rw [hED.len ψ]; omega)
    show ((eds ψ).getD 0 default).2.1 = 0 ↔ d.2.1 = 0
    rw [hED.bits ψ _ h0, hED.bits ψ d hd]
  -- the residual is inhabited at every satisfying frame
  have hne : ∀ (ψ : Name → Nat) (ρ : Nat → V), Sat2 V (Γe ψ) ρ →
      ∃ y, y ∈ˢ interp2 V ρ (R ψ) := by
    intro ψ ρ hρ
    obtain ⟨hiffP, hsubj, hres⟩ := hframes ψ
    have hsplit : Γe ψ = (Γe ψ).getD 0 default :: (Γe ψ).drop 1 := by
      have := drop_succ_eq_getD_cons (Γ := Γe ψ) (n := p.nP + 1) (i := p.nP) (hlenΓ ψ)
        (by omega)
      rwa [Nat.sub_self, List.drop_zero, show p.nP + 1 - 1 - p.nP = 0 from by omega,
        show p.nP + 1 - p.nP = 1 from by omega] at this
    have hρ' := hρ
    rw [hsplit] at hρ'
    obtain ⟨hx, ht⟩ := Sat2_cons_inv hρ'
    have hsat := (hiffP p.nP (Nat.le_refl _) _).mp (by
      rw [show p.nP + 1 - p.nP = 1 from by omega]; exact ht)
    rw [Nat.sub_self, List.drop_zero] at hsat
    rw [hsubj _ ht] at hx
    have hguard' : p.resSort.eval ψ = 0 → ∀ j, j < i → (sorts.getD j .zero).eval ψ = 0 := by
      intro h0 j hj
      rcases hguardOrFirst ψ h0 with hg | hi0
      · exact hguardSem ψ hg j (Nat.le_of_lt hj)
      · omega
    rw [hres hguard' ρ hρ]
    by_cases hw : p.resSort.eval ψ = 0
    · rw [hw] at hx
      obtain ⟨hpt, as', hfits⟩ := towerSet_zero_elim _ hx
      have hspAs := fitsS_teleOfFields.mp hfits
      rcases hguardOrFirst ψ hw with hg | hi0
      · refine ⟨pt, ?_⟩
        rw [hpt, projList_pt]
        exact squash_pt_mem (hCD.len ψ) hi (hsorts ψ _ hsat) (hguardSem ψ hg) hspAs
      · subst hi0
        refine ⟨as'.getD 0 pt, ?_⟩
        rw [hpt, projList_pt]
        have := (spineFit_prefix_next hspAs (by rw [hlenFs]; exact hi)).2
        simpa using this
    · refine ⟨projS i (ρ 0), ?_⟩
      have h := projS_mem_teleOfFields (fun h0 => absurd h0 hw) hx (i := i) (by rw [hlenFs]; exact hi)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenFs]; exact hi)]
      exact h
  have hlev : ∀ (ψ : Name → Nat) (ρ : Nat → V), Sat2 V (Γe ψ) ρ →
      interp2 V ρ (R ψ) ∈ˢ (univ (resLevel V (Γe ψ) (R ψ)) : V) :=
    fun ψ => resLevel_spec ⟨vb.eval ψ, hED.resSort ψ⟩
  have hbase : ∀ (ψ : Name → Nat) (ρ : Nat → V), Sat2 V (Γe ψ) ρ →
      UnderTowerOk (m ψ) ρ (body ψ) (R ψ) [] ∧ UnderTowerValid ρ (body ψ) [] := by
    intro ψ ρ hρ
    obtain ⟨h1, h2, h3⟩ := entryBody_ok ((hED.opened ψ).okR ρ hρ) (hlev ψ ρ hρ) (hne ψ ρ hρ)
    refine ⟨⟨h1, h3, fun h0 => ?_⟩, h2⟩
    have hm : ((eds ψ).getD 0 default).2.1 = 0 := h0
    rw [hED.bits ψ _ (Setlec.getD_mem (by rw [hED.len ψ]; omega))] at hm
    have := hED.resSort ψ ρ hρ
    rw [hm] at this
    rwa [← univ_zero]
  -- the walks
  have hwalks : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      UnderTowerOk (m ψ) ρ (body ψ) (R ψ) (eds ψ) ∧ UnderTowerValid ρ (body ψ) (eds ψ) := by
    intro ψ ρ
    have hR := hED.opened ψ
    have hent : ∀ i', i' < p.nP + 1 → ∃ q, (eds ψ)[i']? = some q ∧
        q.2.2 = (Γe ψ).getD (p.nP + 1 - 1 - i') default := by
      intro i' hi'
      have hil : i' < (eds ψ).length := by rw [hED.len ψ]; exact hi'
      exact ⟨_, List.getElem?_eq_getElem hil,
        by rw [getD_reverse_of_peel (hED.len ψ) hi' (List.getElem?_eq_getElem hil)]⟩
    have hnil : Sat2 V ((Γe ψ).drop (p.nP + 1 - 0)) ρ := by
      rw [Nat.sub_zero, List.drop_eq_nil_of_le (by rw [hlenΓ ψ]; exact Nat.le_refl _)]
      exact Sat2_nil V ρ
    constructor
    · have hw := hereditaryWalk (V := V)
        (Q := fun ρ ds' => UnderTowerOk (m ψ) ρ (body ψ) (R ψ) ds')
        (hlenΓ ψ) (hED.len ψ) hent hR.okΓ (fun ρ hρ => (hbase ψ ρ hρ).1)
        (fun ρ d ds' _ hok hrec => ⟨hok.1, hrec⟩) 0 (Nat.zero_le _) ρ hnil
      rw [List.drop_zero] at hw
      exact hw
    · have hw := hereditaryWalk (V := V)
        (Q := fun ρ ds' => UnderTowerValid ρ (body ψ) ds')
        (hlenΓ ψ) (hED.len ψ) hent hR.okΓ (fun ρ hρ => (hbase ψ ρ hρ).2)
        (fun ρ d ds' _ hok hrec => ⟨hok.2, hrec⟩) 0 (Nat.zero_le _) ρ hnil
      rw [List.drop_zero] at hw
      exact hw
  have hleaf : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotOkP V ρ (A ψ) ∧ interp2 V ρ (A ψ) ∈ˢ interp2 V ρ (mkPisAV (eds ψ) (R ψ)) :=
    fun ψ ρ => ⟨⟨mkLamsC_ok2 (hz ψ) (hwalks ψ ρ).1, mkLamsC_validV (hwalks ψ ρ).2⟩,
      mkLamsC_mem (hz ψ) (hwalks ψ ρ).1⟩
  have hAbelow : ∀ ψ, VExpr.bvarsBelow 0 (A ψ).erase := fun ψ =>
    mkLamsC_below (hED.below ψ) (by
      rw [Nat.zero_add, hED.len ψ]
      exact entryBody_below (bvarsBelow_of_reading (hED.opened ψ).bodyScoped.1
        (hED.opened ψ).bodyScoped.2.1 (hED.opened ψ).body))
  -- the reading at the extension
  have hreadE : ∀ ψ : Name → Nat,
      denoteP (acvalWith mp.base2.acval (ConstantInfo.projInfo entry).name A)
        ⟨.projInfo entry :: env.consts⟩ ψ 0 ptyA = some (mkPisAV (eds ψ) (R ψ)) :=
    fun ψ => denoteP_cons_mono hfresh hcrossE ψ 0 hcbE (hED.read ψ)
  have hfT₂ : (⟨.projInfo entry :: env.consts⟩ : Env).find? p.cvT.name
      = some (.indInfo cvTa (Setlec.directCaps p)) := by
    rw [Setlec.Env.find?_cons, if_neg (fun h => hneT h.symm)]
    exact hfT
  have hfC₂ : (⟨.projInfo entry :: env.consts⟩ : Env).find? p.cvC.name
      = some (.ctorInfo cvCa p.nP p.nF) := by
    rw [Setlec.Env.find?_cons, if_neg (fun h => hneC h.symm)]
    exact hfC
  refine ⟨A, ?_⟩
  refine declStepPM_of_tower_cons mp (entry := entry) (A := A) hfresh hnres rfl hwf hAbelow hnp
    ⟨rfl, hresT, hresR, hresC, hi, ⟨cvTa, Setlec.directCaps p, hfT₂, hlpsT⟩,
      cvCa, hfC₂, hlpsC, hstripC⟩
    (fun ψ k => AVExpr.liftN_eq_self _
      (VExpr.bvarsBelow.mono (Nat.zero_le k) (hAbelow ψ)) 1)
    ?_ (fun ψ ρ => (hleaf ψ ρ).1.1) (fun ψ ρ => (hleaf ψ ρ).1.2)
    (fun ψ => ⟨_, hreadE ψ⟩) ?_ ?_ ?_
  · -- level dependence
    intro ψ₁ ψ₂ hφ
    obtain ⟨h1, h2⟩ := hED.params ψ₁ ψ₂ hφ
    show mkLamsC (((eds ψ₁).getD 0 default).2.1) (eds ψ₁)
        (entryBody (resLevel V (((eds ψ₁).map (·.2.2)).reverse) (R ψ₁)) (R ψ₁))
      = mkLamsC (((eds ψ₂).getD 0 default).2.1) (eds ψ₂)
        (entryBody (resLevel V (((eds ψ₂).map (·.2.2)).reverse) (R ψ₂)) (R ψ₂))
    rw [h1, h2]
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadE ψ).symm.trans hta)
    exact hED.okTy ψ ρ
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadE ψ).symm.trans hta)
    exact (hleaf ψ ρ).2
  · -- the entry's law
    intro m₂ hac φ
    have hacT : ∀ ψ, m₂.acval p.cvT.name ψ = mp.base2.acval p.cvT.name ψ := by
      intro ψ
      rw [hac]
      show acvalWith mp.base2.acval (projFnName p.cvT.name i) A p.cvT.name ψ = _
      rw [acvalWith_ne hneT]
    have hacC : ∀ ψ, m₂.acval p.cvC.name ψ = mp.base2.acval p.cvC.name ψ := by
      intro ψ
      rw [hac]
      show acvalWith mp.base2.acval (projFnName p.cvT.name i) A p.cvC.name ψ = _
      rw [acvalWith_ne hneC]
    have hFD₂ : FormerData m₂ cvTa p.nP p.resSort pps :=
      hFD.cross (c₀ := .projInfo entry) (A := A) hfresh hcrossT hcbT m₂ hac
    have hreadE₂ : ∀ ψ, denoteP m₂.acval ⟨.projInfo entry :: env.consts⟩ ψ 0 ptyA
        = some (mkPisAV (eds ψ) (R ψ)) :=
      hED.cross (c₀ := .projInfo entry) (A := A) hfresh hcrossE hcbE m₂ hac
    refine ⟨rfl, rfl, rfl, hi, ⟨cvTa, Setlec.directCaps p, hfT₂, hlpsT, ?_, rfl, rfl, rfl⟩,
      ?_, cvCa, hfC₂, hlpsC, ?_, ?_⟩
    · show (!p.isProp) = !(Level.isEquiv p.resSort .zero == some true)
      rw [hProp]
    · show (Level.isEquiv p.resSort .zero == some true) = false →
        ∀ ψ : Name → Nat, p.resSort.eval ψ = 0 → guard.eval ψ = 0
      exact hO5
    · -- the per-instantiation laws
      intro us _
      refine ⟨⟨mkPisAV (eds (Level.substFn φ p.cvT.levelParams us))
        (R (Level.substFn φ p.cvT.levelParams us)), ?_, ?_⟩, ?_⟩
      · show denoteP m₂.acval _ φ 0 (ptyA.instantiateLevelParams p.cvT.levelParams us) = _
        rw [denotePInstLevels m₂ φ p.cvT.levelParams us 0 ptyA]
        exact hreadE₂ _
      · -- (A)
        intro hguardAt ρ vs x rest hlenVs hokApp hokx hmem hpeel
        have hguard' : p.resSort.eval (Level.substFn φ p.cvT.levelParams us) = 0 →
            ∀ j, j ≤ i → (sorts.getD j .zero).eval (Level.substFn φ p.cvT.levelParams us) = 0 :=
          fun h0 => hguardSem _ (hguardAt h0)
        obtain ⟨hiffP, hsubj, hres⟩ := hframes (Level.substFn φ p.cvT.levelParams us)
        have hacT' : m₂.acval p.cvT.name (Level.substFn φ p.cvT.levelParams us)
            = directTyAV (p.resSort.eval (Level.substFn φ p.cvT.levelParams us))
              (pps (Level.substFn φ p.cvT.levelParams us))
              (((ds (Level.substFn φ p.cvT.levelParams us)).drop p.nP).map (·.2.2)) := by
          rw [hacT, hleafT]
        rw [hacT'] at hokApp hmem
        exact entryTypingCore (hCD.len _) (hFD.len _) (hED.len _) (hpok _) (hiff _) (hbound _)
          (hsorts _) hguard' hi hiffP hsubj
          (hres fun h0 j hj => hguard' h0 j (Nat.le_of_lt hj)) (hED.opened _).okR
          ρ vs x rest hlenVs hokApp hokx hmem hpeel
      · -- (B)
        intro hpos ρ ys hlen hok
        have hw : p.resSort.eval (Level.substFn φ p.cvT.levelParams us) ≠ 0 := hpos
        have hacC' : m₂.acval p.cvC.name (Level.substFn φ p.cvT.levelParams us)
            = directMkAV (p.resSort.eval (Level.substFn φ p.cvT.levelParams us))
              (ds (Level.substFn φ p.cvT.levelParams us))
              (((ds (Level.substFn φ p.cvT.levelParams us)).drop p.nP).map (·.2.2)) := by
          rw [hacC, hleafC]
        rw [hacC'] at hok ⊢
        exact entryIotaCore hw (hCD.len _) hi (hbound _) ys hlen hok
    · -- (C)
      intro cvT capsT hf us _
      obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj (hfT₂.symm.trans hf))
      refine ⟨mkPisAV (pps (Level.substFn φ p.cvT.levelParams us))
        (.sort (p.resSort.eval (Level.substFn φ p.cvT.levelParams us))), ?_, hFD.okTy _, ?_⟩
      · rw [denotePInstLevels m₂ φ cvTa.levelParams us 0 cvTa.type, hlpsT]
        exact hFD₂.read _
      · intro ρ ts rest x hlents hfit hmem
        have hsp := spineFit_of_teleFitP (by rw [hFD.len]; exact hlents) hfit
        have hacT' : m₂.acval p.cvT.name (Level.substFn φ p.cvT.levelParams us)
            = directTyAV (p.resSort.eval (Level.substFn φ p.cvT.levelParams us))
              (pps (Level.substFn φ p.cvT.levelParams us))
              (((ds (Level.substFn φ p.cvT.levelParams us)).drop p.nP).map (·.2.2)) := by
          rw [hacT, hleafT]
        have hacC' : m₂.acval p.cvC.name (Level.substFn φ p.cvT.levelParams us)
            = directMkAV (p.resSort.eval (Level.substFn φ p.cvT.levelParams us))
              (ds (Level.substFn φ p.cvT.levelParams us))
              (((ds (Level.substFn φ p.cvT.levelParams us)).drop p.nP).map (·.2.2)) := by
          rw [hacC, hleafC]
        have hmem' : x ∈ˢ ts.foldl SetTheory.app (interp2 V ρ
            (directTyAV (p.resSort.eval (Level.substFn φ p.cvT.levelParams us))
              (pps (Level.substFn φ p.cvT.levelParams us))
              (((ds (Level.substFn φ p.cvT.levelParams us)).drop p.nP).map (·.2.2)))) := by
          rw [← hacT']; exact hmem
        show x = (ts ++ (List.range p.nF).map fun j => projS j x).foldl SetTheory.app
          (interp2 V ρ (m₂.acval p.cvC.name (Level.substFn φ p.cvT.levelParams us)))
        rw [hacC']
        exact entryEtaCore (hCD.len _) (hFD.len _) (hpok _) (hiff _) (hbound _) ts x hlents hsp hmem'

end Setlec.SetR.Interp2

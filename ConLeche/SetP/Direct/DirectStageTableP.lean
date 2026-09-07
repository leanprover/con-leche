import ConLeche.SetP.Direct.DirectEntryLawP
import ConLeche.Verify.Direct.DirectPartsInv

/-!
# The projection table's cons (task #175 S1)

`stageTable`: the P step at the direct install's last stage — the
structure's projection **table**, one constant holding every field's
body (`checkDirectProjTable`).  The table's leaf is `Sort 0` (a
member of its dummy type's reading; a table is not a term), and what
the cons owes is the tower law at every field
(`declStepPM_of_tower_cons`):

* **(A)** the typing law reads body `i` through the dummy telescope
  (`denoteP_projTele_zero`); the opened body is the constructor's
  field domain at the variables (`directProjBody_open`), whose frame
  facts are `bodyFrames`, and `entryTypingCore` closes;
* **(B)** the iota law and **(C)** the η law are the block's own
  (`entryIotaCore`/`entryIotaCoreZero`, `entryEtaCore`), as before.

The squash regime's guard content (`directProjGuards_getD` over the
field-sort run) and the unused earlier fields' invariance
(`openPisAtFvars_leaf_free`) are derived here per field, as the
retired per-slot fold derived them per slot.
-/

namespace ConLeche.SetP
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.VExpr ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AVExpr)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta ProjEntry ProjTable projTableName)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-- The table name has the reserved shape. -/
theorem projTableName_isProjFnShape (T : Name) :
    (projTableName T).isProjFnShape = true := rfl

/-- **The P step at the projection table's cons.** -/
theorem stageTable (mp : EnvS2PM V μ env)
    {F : Nat} {p : DirectParts} {cvTa cvCa : ConstantVal} {sorts : List Level}
    {envS : Env} {xFvs : List Expr} {envOut : Env}
    (hsorts : ConLeche.checkDirectFieldSorts (ConLeche.fueledOps μ F) envS p.isProp p.large
      p.resSort p.nP xFvs p.nF = .ok sorts)
    (hTbl : ConLeche.checkDirectProjTable (m := ConLeche.CheckM) p.cvT.name p.cvC.name
      p.cvT.levelParams p.nP p.nF p.resSort
      (ConLeche.directProjGuards cvCa.type p.nP p.nF sorts) 0 cvCa env = .ok envOut)
    (hfT : env.find? p.cvT.name = some (.indInfo cvTa (ConLeche.directCaps p)))
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    (hfC : env.find? p.cvC.name = some (.ctorInfo cvCa p.nP p.nF))
    (hlpsC : cvCa.levelParams = p.cvT.levelParams)
    (hstripC : (cvCa.type.stripPis (p.nP + p.nF)).isSome = true)
    (hProp : p.isProp = (Level.isEquiv p.resSort .zero == some true))
    (hTshape : p.cvT.name.isProjFnShape = false)
    (hCshape : p.cvC.name.isProjFnShape = false)
    (hresT : ConLeche.reservedBasisNames.contains p.cvT.name = false)
    (hresR : ConLeche.reservedBasisNames.contains (p.cvT.name.str "rec") = false)
    (hresC : ConLeche.reservedBasisNames.contains p.cvC.name = false)
    (hnp : ∀ j, NoProjEnv env p.cvT.name j)
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
    Nonempty (EnvS2PM V μ envOut) := by
  have hwf' : ConLeche.EnvWF envOut := ConLeche.direct_table_wf mp.base2.wf hTbl
  obtain ⟨bodies, hbodies, -, -, hfresh, rfl⟩ := ConLeche.checkDirectProjTable_inv hTbl
  let tbl : ProjTable := ⟨p.cvT.name, p.cvT.levelParams, p.nP, p.cvC.name, p.nF, p.resSort,
    bodies, ConLeche.directProjGuards cvCa.type p.nP p.nF sorts, 0⟩
  obtain ⟨hlenS, hsortsAll⟩ := ConLeche.checkDirectFieldSorts_inv hsorts
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
  have hsortsF : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ →
      ∀ j, j < p.nF → ∀ as : List V,
        SpineFit ρ ((((ds ψ).drop p.nP).map (·.2.2)).take j) as →
        interp2 V (consList as ρ) ((((ds ψ).drop p.nP).map (·.2.2)).getD j default)
          ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V) :=
    fun ψ ρ h => (hfields ψ ρ h).2.2.2.2
  have hpok : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ParamsOkT (p.resSort.eval ψ) ρ (((ds ψ).drop p.nP).map (·.2.2)) (pps ψ) :=
    fun ψ ρ => (formerWalks hFD (fun ψ' ρ' h => hokB ψ' ρ' ((hiff ψ' ρ').mp h)) ψ ρ).1
  -- the guards' content: the official join over the used earlier slots
  have hguardSem : ∀ k, k < p.nF → ∀ ψ : Name → Nat,
      ((ConLeche.directProjGuards cvCa.type p.nP p.nF sorts).getD k .zero).eval ψ = 0 →
      (sorts.getD k .zero).eval ψ = 0 ∧
      ∀ j, j < k → ConLeche.directUsedLater cvCa.type p.nP j = true →
        (sorts.getD j .zero).eval ψ = 0 := by
    intro k hk ψ h0
    rw [ConLeche.directProjGuards_getD _ _ _ _ hk,
      eval_foldl_max_if_zero_iff ψ (ConLeche.directUsedLater cvCa.type p.nP)
        (fun j => sorts.getD j .zero)] at h0
    exact ⟨h0.1, fun j hj hu => h0.2 j (List.mem_range.mpr hj) hu⟩
  have hguardOf : ∀ k, k < p.nF → ∀ ψ : Name → Nat,
      (∀ j, j ≤ k → (sorts.getD j .zero).eval ψ = 0) →
      ((ConLeche.directProjGuards cvCa.type p.nP p.nF sorts).getD k .zero).eval ψ = 0 := by
    intro k hk ψ hall
    rw [ConLeche.directProjGuards_getD _ _ _ _ hk,
      eval_foldl_max_if_zero_iff ψ (ConLeche.directUsedLater cvCa.type p.nP)
        (fun j => sorts.getD j .zero)]
    exact ⟨hall k (Nat.le_refl _), fun j hj _ => hall j (Nat.le_of_lt (List.mem_range.mp hj))⟩
  have hsortD : ∀ j, j < p.nF → ∃ u, sorts.getD j .zero = u ∧
      (p.isProp = false → Level.leq u p.resSort = some true) := by
    intro j hj
    obtain ⟨-, -, u, -, hu, -, -, hleq, -⟩ := hsortsAll j hj
    exact ⟨u, by rw [List.getD_eq_getElem?_getD, hu]; rfl, hleq⟩
  have hO5 : ∀ k, k < p.nF → (Level.isEquiv p.resSort .zero == some true) = false →
      ∀ ψ : Name → Nat, p.resSort.eval ψ = 0 →
      ((ConLeche.directProjGuards cvCa.type p.nP p.nF sorts).getD k .zero).eval ψ = 0 := by
    intro k hk hne ψ h0
    refine hguardOf k hk ψ fun j hj => ?_
    obtain ⟨u, hu, hleq⟩ := hsortD j (by omega)
    rw [hu]
    have := Level.leq_sound (hleq (by rw [hProp]; exact hne)) ψ
    omega
  -- the constructor type's scoping
  obtain ⟨hCf, -, -, hCb, -⟩ := mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfC)
  simp only [ConstantInfo.toConstantVal] at hCf hCb
  -- the unused earlier fields are free in the projected field's type
  obtain ⟨fvsA, oA, hopAll⟩ := openPisAtFvars_of_stripPis_isSome (p.nP + p.nF) 0 hstripC
  have hlenA : fvsA.length = p.nP + p.nF := openPisAtFvars_length _ hopAll
  have hfree : ∀ (ψ : Name → Nat) (k : Nat), k < p.nF → ∀ (j : Nat), j < k →
      ConLeche.directUsedLater cvCa.type p.nP j = false →
      ∃ X : AVExpr, (((ds ψ).drop p.nP).map (·.2.2)).getD k default = X.liftN 1 (k - 1 - j) := by
    intro ψ k hk j hj hun
    have hsome : (cvCa.type.stripPis (p.nP + j + 1)).isSome = true :=
      ConLeche.stripPis_isSome_of_le (by omega) hstripC
    obtain ⟨⟨bs, rest⟩, hst⟩ := Option.isSome_iff_exists.mp hsome
    have hrest : rest.hasLooseBVar 0 = false := by
      unfold ConLeche.directUsedLater at hun
      rw [hst] at hun
      have hun' : rest.hasLooseBVarB 0 = false := hun
      rw [ConLeche.Expr.hasLooseBVarB_eq] at hun'
      exact hun'
    obtain ⟨hleavesK, -⟩ := openPisAtFvars_leaf_free (p.nP + p.nF) (p.nP + j) hopAll (by omega)
      hst hrest (by
        intro l hl
        rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hCf] at hl
        exact absurd hl List.not_mem_nil)
    obtain ⟨pps', b, hstA, -, -, hbind⟩ := denoteP_openPis (p.nP + p.nF) hopAll (hCD.read ψ)
    have hppsEq : pps' = ds ψ := by
      have h2 := stripPisAV_mkPisAV (ds ψ) (ctorBodyAV mp.base2 p.cvT.name p.nP p.nF ψ)
      rw [hCD.len ψ] at h2
      exact (Prod.mk.inj (Option.some.inj (hstA.symm.trans h2))).1
    obtain ⟨x, hx⟩ : ∃ x, fvsA[p.nP + k]? = some x :=
      ⟨fvsA[p.nP + k]'(by rw [hlenA]; omega), List.getElem?_eq_getElem (by rw [hlenA]; omega)⟩
    obtain ⟨q, hq, -, hqread⟩ := hbind (p.nP + k) x hx
    rw [hppsEq] at hq
    have hW : Expr.WScoped (0 + (p.nP + k)) (Expr.fvarTypeD x) :=
      openPisAtFvars_typeWScoped (p.nP + p.nF) hopAll (Expr.WScoped.of_not_hasFvar hCf) _ x hx
    have hleaf : ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves, l.1 ≠ p.nP + j := by
      intro l hl
      have hsub : l ∈ x.fvarLeaves := by
        cases x with
        | fvar idx ty =>
          simp only [Expr.fvarLeaves, Expr.fvarTypeD] at hl ⊢
          exact List.mem_cons_of_mem _ hl
        | _ => exact hl
      have := hleavesK (p.nP + k) (by omega) x hx l hsub
      simpa using this
    obtain ⟨X, hX⟩ := denoteP_liftN_of_leaf_free mp.base2 (0 + (p.nP + k)) (Expr.fvarTypeD x) hW
      (q := p.nP + j) (by omega) (by intro l hl; exact hleaf l hl) hqread
    refine ⟨X, ?_⟩
    have hFk : (((ds ψ).drop p.nP).map (·.2.2)).getD k default = q.2.2 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_drop, hq]
      rfl
    rw [hFk, hX, show 0 + (p.nP + k) - 1 - (p.nP + j) = k - 1 - j from by omega]
  -- names
  have hneT : p.cvT.name ≠ projTableName p.cvT.name := by
    intro h
    have := projTableName_isProjFnShape p.cvT.name
    rw [← h, hTshape] at this
    exact nomatch this
  have hneC : p.cvC.name ≠ projTableName p.cvT.name := by
    intro h
    have := projTableName_isProjFnShape p.cvT.name
    rw [← h, hCshape] at this
    exact nomatch this
  have hnres : ConLeche.reservedBasisNames.contains (projTableName p.cvT.name) = false :=
    ConLeche.reservedBasisNames_not_num _ _
  -- the crossings
  have hcrossT : ConsCrossAt (.projInfo tbl) cvTa.type := by
    intro t2 he' j
    cases he'
    exact (hnp j).type _ (ConLeche.Semantics.Env.find?_mem hfT)
  have hcrossC : ConsCrossAt (.projInfo tbl) cvCa.type := by
    intro t2 he' j
    cases he'
    exact (hnp j).type _ (ConLeche.Semantics.Env.find?_mem hfC)
  have hcbT : ConstsBound env cvTa.type :=
    constsBound_of_constsResolve _ (mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfT)).2.2.1
  have hcbC : ConstsBound env cvCa.type :=
    constsBound_of_constsResolve _ (mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfC)).2.2.1
  -- the lookups at the extension
  have hfT₂ : (⟨.projInfo tbl :: env.consts⟩ : Env).find? p.cvT.name
      = some (.indInfo cvTa (ConLeche.directCaps p)) := by
    rw [ConLeche.Env.find?_cons, if_neg (fun h => hneT h.symm)]
    exact hfT
  have hfC₂ : (⟨.projInfo tbl :: env.consts⟩ : Env).find? p.cvC.name
      = some (.ctorInfo cvCa p.nP p.nF) := by
    rw [ConLeche.Env.find?_cons, if_neg (fun h => hneC h.symm)]
    exact hfC
  have hfTbl₂ : (⟨.projInfo tbl :: env.consts⟩ : Env).find? (projTableName p.cvT.name)
      = some (.projInfo tbl) := ConLeche.Env.find?_cons_self _ _
  have hprev₂ : ∀ j, j < p.nF →
      ∃ entry, (⟨.projInfo tbl :: env.consts⟩ : Env).findProj? p.cvT.name j
        = some entry :=
    fun j hj => ⟨tbl.entry j, ConLeche.Env.findProj?_of_table hfTbl₂ hj⟩
  -- the head data at every field
  have hhead : ∀ i, i < p.nF → ConLeche.TowerHead ⟨.projInfo tbl :: env.consts⟩ (tbl.entry i) :=
    fun i hi => ⟨hresT, hresR, hresC, hi, ⟨cvTa, ConLeche.directCaps p, hfT₂, hlpsT⟩,
      ⟨cvCa, hfC₂, hlpsC, hstripC⟩⟩
  suffices hlaw : ∀ m₂ : EnvS2Core V ⟨.projInfo tbl :: env.consts⟩,
      m₂.acval = acvalWith mp.base2.acval (ConstantInfo.projInfo tbl).name (fun _ => .sort 0) →
      ∀ (φ : Name → Nat) (i : Nat), i < tbl.numFields →
        TowerEntryLawP m₂ φ tbl.structName i (tbl.entry i) by
    obtain ⟨mp', -⟩ := declStepPM_of_tower_cons mp (tbl := tbl) hfresh hnres hwf' hnp hhead hlaw
    exact ⟨mp'⟩
  -- the fields' laws
  intro m₂ hac φ i hi
  replace hi : i < p.nF := hi
  have hacT : ∀ ψ, m₂.acval p.cvT.name ψ = mp.base2.acval p.cvT.name ψ := by
    intro ψ
    rw [hac]
    show acvalWith mp.base2.acval (projTableName p.cvT.name) _ p.cvT.name ψ = _
    rw [acvalWith_ne hneT]
  have hacC : ∀ ψ, m₂.acval p.cvC.name ψ = mp.base2.acval p.cvC.name ψ := by
    intro ψ
    rw [hac]
    show acvalWith mp.base2.acval (projTableName p.cvT.name) _ p.cvC.name ψ = _
    rw [acvalWith_ne hneC]
  have hFD₂ : FormerData m₂ cvTa p.nP p.resSort pps :=
    hFD.cross (c₀ := .projInfo tbl) hfresh hcrossT hcbT m₂ hac
  have hCD₂ : CtorData m₂ p.cvT.name cvCa p.nP p.nF p.resSort ds :=
    hCD.cross (c₀ := .projInfo tbl) hfresh hneT hcrossC hcbC m₂ hac
  -- the body, opened at the variables
  obtain ⟨cds, bodyB, mbB, hcf⟩ :=
    ConLeche.directProjBody_open hbodies hstripC hCb hi
  refine ⟨rfl, rfl, hi, ⟨cvTa, ConLeche.directCaps p, hfT₂, hlpsT, fun he => ⟨?_, rfl, rfl, rfl⟩⟩,
    hO5 i hi, cvCa, hfC₂, hlpsC, ?_, ?_⟩
  · have he' : (!p.isProp) = true := he
    show (Level.isEquiv p.resSort .zero == some true) = false
    rw [← hProp]
    cases hp : p.isProp
    · rfl
    · rw [hp] at he'; exact nomatch he'
  · -- the per-instantiation laws
    intro us _
    -- the body's frame at the instantiation
    -- the subject's frame: a member of the bare tuple tower (offset 0)
    obtain ⟨fdomA, hfdA, hokFd, hresFd⟩ := bodyFrames m₂ (off := 0) hcf hCf hCb
      (fun j hj => by
        obtain ⟨entry, hfe⟩ := hprev₂ j (by omega)
        refine ⟨entry, hfe, ?_⟩
        obtain ⟨tbl', hf', -, rfl⟩ := ConLeche.Env.findProj?_some hfe
        obtain rfl : tbl = tbl' := ConstantInfo.projInfo.inj (Option.some.inj (hfTbl₂.symm.trans hf'))
        rfl) hi
      (hCD₂.len (Level.substFn φ p.cvT.levelParams us))
      (hCD₂.below (Level.substFn φ p.cvT.levelParams us))
      (hCD₂.read (Level.substFn φ p.cvT.levelParams us))
      (hokB _) (hsortsF _)
      (used := ConLeche.directUsedLater cvCa.type p.nP) (hfree _ i hi)
      (fun ρ => ρ 0 ∈ˢ towerSet (p.resSort.eval (Level.substFn φ p.cvT.levelParams us))
        (teleOfFields (fun j => ρ (j + 1))
          (((ds (Level.substFn φ p.cvT.levelParams us)).drop p.nP).map (·.2.2))))
      (fun ρ hx _ hw => by
        rw [hw] at hx
        obtain ⟨hpt, as', hfits⟩ := towerSet_zero_elim _ hx
        exact ⟨hpt, as', fitsS_teleOfFields.mp hfits⟩)
      (fun ρ hx _ hw => by
        obtain ⟨hspAll, -⟩ := towerSet_elim_teleOfFields hw hx
        rw [List.length_map, List.length_drop, hCD₂.len, Nat.add_sub_cancel_left] at hspAll
        exact hspAll)
      (fun ρ hx hsat j hj => by
        by_cases hw0 : p.resSort.eval (Level.substFn φ p.cvT.levelParams us) = 0
        · rw [hw0] at hx
          obtain ⟨hpt, -⟩ := towerSet_zero_elim _ hx
          exact annotOk2_projAV_pt trivial (by rw [interp2_bvar, hpt])
        · exact annotOk2_projAV_tower (hbound _ _ hsat hw0) hx trivial (by rw [interp2_bvar])
            (by rw [List.length_map, List.length_drop, hCD₂.len, Nat.add_sub_cancel_left]; exact hj))
    have hread : denoteP m₂.acval ⟨.projInfo tbl :: env.consts⟩ φ 0
        (ConLeche.projTele ((tbl.entry i).numParams + 1)
          ((tbl.entry i).body.instantiateLevelParams (tbl.entry i).levelParams us))
        = some (mkPisAV (List.replicate (p.nP + 1) (0, 1, .sort 0)) fdomA) := by
      show denoteP m₂.acval _ φ 0 (ConLeche.projTele (p.nP + 1)
        ((bodies.getD i default).instantiateLevelParams p.cvT.levelParams us)) = _
      rw [← ConLeche.projTele_instantiateLevelParams,
        denotePInstLevels m₂ φ p.cvT.levelParams us 0]
      exact denoteP_projTele_zero hfdA
    refine ⟨⟨_, hread, ?_⟩, ?_⟩
    · -- (A)
      intro hguardAt ρ vs x rest hlenVs hokApp hokx hmem hpeel
      have hguard' : p.resSort.eval (Level.substFn φ p.cvT.levelParams us) = 0 →
          (sorts.getD i .zero).eval (Level.substFn φ p.cvT.levelParams us) = 0 ∧
          ∀ j, j < i → ConLeche.directUsedLater cvCa.type p.nP j = true →
            (sorts.getD j .zero).eval (Level.substFn φ p.cvT.levelParams us) = 0 :=
        fun h0 => hguardSem i hi _ (hguardAt h0)
      have hacT' : m₂.acval tbl.structName (Level.substFn φ (tbl.entry i).levelParams us)
          = directTyAV (p.resSort.eval (Level.substFn φ p.cvT.levelParams us))
            (pps (Level.substFn φ p.cvT.levelParams us))
            (((ds (Level.substFn φ p.cvT.levelParams us)).drop p.nP).map (·.2.2)) := by
        show m₂.acval p.cvT.name (Level.substFn φ p.cvT.levelParams us) = _
        rw [hacT, hleafT]
      rw [hacT'] at hokApp hmem
      exact entryTypingCore (hCD.len _) (hFD.len _) (by simp) (hpok _) (hiff _) (hbound _)
        (hsortsF _) (used := ConLeche.directUsedLater cvCa.type p.nP) hguard' (hfree _ i hi) hi
        hresFd (hokFd (fun h0 => (hguard' h0).2)) ρ vs x rest hlenVs hokApp hokx hmem hpeel
    · -- (B): the constructor type's reading at the instantiation,
      -- then the two regimes (task #175 W6)
      refine ⟨mkPisAV (ds (Level.substFn φ p.cvT.levelParams us))
        (ctorBodyAV m₂ p.cvT.name p.nP p.nF (Level.substFn φ p.cvT.levelParams us)),
        ?_, ?_⟩
      · rw [denotePInstLevels m₂ φ cvCa.levelParams us 0 cvCa.type, hlpsC]
        exact hCD₂.read _
      · intro hguardAt ρ ys rest hlen hok hfit
        have hacC' : m₂.acval (tbl.entry i).ctor (Level.substFn φ (tbl.entry i).levelParams us)
            = directMkAV (p.resSort.eval (Level.substFn φ p.cvT.levelParams us))
              (ds (Level.substFn φ p.cvT.levelParams us))
              (((ds (Level.substFn φ p.cvT.levelParams us)).drop p.nP).map (·.2.2)) := by
          show m₂.acval p.cvC.name (Level.substFn φ p.cvT.levelParams us) = _
          rw [hacC, hleafC]
        rw [hacC'] at hok ⊢
        by_cases hw : p.resSort.eval (Level.substFn φ p.cvT.levelParams us) = 0
        · -- squash: the certified fit pins the selected field to a
          -- proposition's domain
          have hsp : SpineFit ρ ((ds (Level.substFn φ p.cvT.levelParams us)).map (·.2.2))
              (ys.map (interp2 V ρ)) :=
            spineFit_of_teleFitP (by simp only [List.length_map, hlen, hCD.len]; rfl) hfit
          rw [hw]
          exact entryIotaCoreZero (hCD.len _) hi (hsortsF _)
            (hguardSem i hi _ (hguardAt hw)).1 ys hlen hsp
        · -- graph: the grading's slot chain
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
      have hacT' : m₂.acval tbl.structName (Level.substFn φ (tbl.entry i).levelParams us)
          = directTyAV (p.resSort.eval (Level.substFn φ p.cvT.levelParams us))
            (pps (Level.substFn φ p.cvT.levelParams us))
            (((ds (Level.substFn φ p.cvT.levelParams us)).drop p.nP).map (·.2.2)) := by
        show m₂.acval p.cvT.name (Level.substFn φ p.cvT.levelParams us) = _
        rw [hacT, hleafT]
      have hacC' : m₂.acval (tbl.entry i).ctor (Level.substFn φ (tbl.entry i).levelParams us)
          = directMkAV (p.resSort.eval (Level.substFn φ p.cvT.levelParams us))
            (ds (Level.substFn φ p.cvT.levelParams us))
            (((ds (Level.substFn φ p.cvT.levelParams us)).drop p.nP).map (·.2.2)) := by
        show m₂.acval p.cvC.name (Level.substFn φ p.cvT.levelParams us) = _
        rw [hacC, hleafC]
      have hmem' : x ∈ˢ ts.foldl SetTheory.app (interp2 V ρ
          (directTyAV (p.resSort.eval (Level.substFn φ p.cvT.levelParams us))
            (pps (Level.substFn φ p.cvT.levelParams us))
            (((ds (Level.substFn φ p.cvT.levelParams us)).drop p.nP).map (·.2.2)))) := by
        rw [← hacT']; exact hmem
      rw [hacC']
      exact entryEtaCore (hCD.len _) (hFD.len _) (hpok _) (hiff _) (hbound _) ts x hlents hsp hmem'

end ConLeche.SetP

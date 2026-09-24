module

public import ConLeche.Model.Inductives.FixEntryLaw
public import ConLeche.Model.Inductives.FixAssemblyKit
import ConLeche.Model.Inductives.StructStageTable
import ConLeche.Verify.Inductives.StructPartsInv
import ConLeche.Model.Annot.BitLevels
import ConLeche.Model.Annot.BitInst
public section

/-!
# The projection table's cons on the fixpoint route (task #210 Part A)

`stageFixTable`: the P step at the recursive route's last stage — the
projection **table** of a STRUCTURE-LIKE block (one constructor, no
index; `checkNativeTable`).  It is the structure route's table
stage (`stageTable`, `ConLeche/Model/Inductives/StructStageTable.lean`)
read against the fixpoint carrier: the family at the parameters is
the one-constructor fibre of the tagged union (`sumSet w (sumFibre w
ρ' [Fs ++ [idxEqAV []]])`, the block's `hfold`), so the subject of a
projection is a TAGGED point-terminated tuple and the fields sit at
projection offset `1` (`ProjTable.off`).  The three laws are the fix
entry cores (`FixEntryLawP.lean`); the bodies' frames are
`bodyFrames` at the fibre's frame.  **The former's leaf is ABSTRACT**
there and here (`L`, with `hlam`/`hfold`): a block MEMBER's leaf
(`blockTyAV`) is the same stage at a different reading (task #315 M3).

`declNativeTable` is the assembly-facing wrapper: the case split
on `checkNativeTable` (nothing consed at a block that is not
structure-like), the block's data specialised to one constructor and
no index, and the `NoProjEnv` bookkeeping across the block's conses
(the former, the constructor, the generated recursor).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps InductiveShape
  BinderMeta ProjEntry ProjTable RecRule RecFieldKind projTableName)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## Small facts -/

omit [SetTheory V] in
/-- Lifting by nothing is the identity on a field chain. -/
theorem liftFields_zero : ∀ (k : Nat) (Fs : List AnnotTerm), liftFields 0 k Fs = Fs
  | _, [] => rfl
  | k, F :: Fs => by rw [liftFields_cons, AnnotTerm.liftN_zero, liftFields_zero (k + 1) Fs]

omit [SetTheory V] in
/-- The one constructor's restricted chain at no index is its
unrestricted chain closed by the trivial index equation. -/
theorem rChains_single_nil (Fs : List AnnotTerm) :
    rChains 0 0 [Fs] [[]] = [Fs ++ [idxEqAV []]] := by
  simp [rChains, rChain, idxEqsAt, liftFields_zero]

/-- `NoProjEnv` across the constructors' conses. -/
theorem noProjEnv_consSumCtors {T : Name} {i nP : Nat} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {env₀ : Env},
      NoProjEnv env₀ T i → (∀ cA ∈ ctorsA, Expr.NoProjAt T i cA.1.type) →
      NoProjEnv (ConLeche.consSumCtors nP ctorsA env₀) T i
  | [], _, h, _ => h
  | cA :: rest, env₀, h, hall => by
    simp only [ConLeche.consSumCtors]
    refine noProjEnv_consSumCtors (h.cons (c₀ := .ctorInfo cA.1 nP cA.2) (NoProjHead.ofType
      (hall cA List.mem_cons_self) (fun _ _ _ h => nomatch h)
      (fun _ _ _ _ h => nomatch h) (fun _ h => nomatch h))) ?_
    exact fun c hc => hall c (List.mem_cons_of_mem _ hc)

/-! ## The P step -/

set_option maxHeartbeats 3200000 in
/-- **The P step at the fixpoint route's projection table** (task #210
Part A): `stageTable` against the one-constructor fibre. -/
theorem stageFixTable (mp : EnvModelM V μ env)
    {T : Name} {lps : List Name} {nP : Nat} {resSort : Level} {isProp : Bool}
    {cvTa cvCa : ConstantVal} {nF : Nat} {sorts : List Level}
    {envOut : Env} {caps : IndCaps}
    (hTbl : ConLeche.checkStructProjTable (m := ConLeche.CheckM) T cvCa.name
      lps nP nF resSort
      (ConLeche.structProjGuards cvCa.type nP nF sorts) 1 cvCa env = .ok envOut)
    (hfT : env.find? T = some (.indInfo cvTa caps))
    (hcaps : caps.eta = true → (Level.isEquiv resSort .zero == some true) = false ∧
      caps.etaCtor = cvCa.name ∧ caps.etaParams = nP ∧ caps.etaFields = nF)
    (hlpsT : cvTa.levelParams = lps)
    (hfC : env.find? cvCa.name = some (.ctorInfo cvCa nP nF))
    (hlpsC : cvCa.levelParams = lps)
    (hstripC : (cvCa.type.stripPis (nP + nF)).isSome = true)
    (hProp : isProp = (Level.isEquiv resSort .zero == some true))
    (hTshape : T.isProjFnShape = false)
    (hCshape : cvCa.name.isProjFnShape = false)
    (hresT : ConLeche.reservedBasisNames.contains T = false)
    (hresR : ConLeche.reservedBasisNames.contains (T.str "rec") = false)
    (hresC : ConLeche.reservedBasisNames.contains cvCa.name = false)
    (hnp : ∀ j, NoProjEnv env T j)
    {pps ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    (hFD : FormerData mp.base2 cvTa nP resSort pps)
    (hCDread : ∀ ψ, denoteMeta mp.base2.acval env ψ 0 cvCa.type
      = some (mkPisAV (ds ψ) (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ))))
    (hCDlen : ∀ ψ, (ds ψ).length = nP + nF)
    (hCDbelow : ∀ ψ, DomsBelow 0 (ds ψ))
    (hleq : ∀ k, k < nF → isProp = false → Level.leq (sorts.getD k .zero) resSort = some true)
    {L : (Name → Nat) → AnnotTerm}
    (hleafT : ∀ ψ, mp.base2.acval T ψ = L ψ)
    (hleafC : ∀ ψ, mp.base2.acval cvCa.name ψ
      = sumMkAV (resSort.eval ψ) 0 (ds ψ) (((ds ψ).drop nP).map (·.2.2))
          (uChains [((ds ψ).drop nP).map (·.2.2)]))
    (hlam : ∀ ψ, ∃ B, L ψ = mkLamsAV ((pps ψ).map fun d => (resSort.eval ψ + 1, d.2.2)) B)
    (hfold : ∀ (ψ : Name → Nat) (ρ : Nat → V) (ts : List V),
      SpineFit ρ ((pps ψ).map (·.2.2)) ts →
      ts.foldl SetTheory.app (interp V ρ (L ψ))
        = sumSet (resSort.eval ψ) (sumFibre (resSort.eval ψ) (consList ts ρ)
            [((ds ψ).drop nP).map (·.2.2) ++ [idxEqAV []]]))
    (hiff : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V ((pps ψ).map (·.2.2)).reverse ρ ↔
        Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ)
    (hfields : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
        FieldsOkB (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2)) ∧
        FieldsValid ρ (((ds ψ).drop nP).map (·.2.2)))
    (hboundP : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
        isProp = false → FieldsBound (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2)))
    (hsortsF : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
        ∀ j, j < nF → ∀ as : List V,
          SpineFit ρ ((((ds ψ).drop nP).map (·.2.2)).take j) as →
          interp V (consList as ρ) ((((ds ψ).drop nP).map (·.2.2)).getD j default)
            ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V)) :
    ∃ (tbl : ProjTable) (mp' : EnvModelM V μ envOut),
      envOut = ⟨.projInfo tbl :: env.consts⟩ ∧ tbl.structName = T ∧
      env.find? (ConstantInfo.projInfo tbl).name = none ∧
      mp'.base2.acval = acvalWith mp.base2.acval (ConstantInfo.projInfo tbl).name
        (fun _ => .sort 0) := by
  have hwf' : ConLeche.EnvWF envOut := ConLeche.direct_table_wf mp.base2.wf hTbl
  obtain ⟨bodies, hbodies, -, -, hfresh, rfl⟩ := ConLeche.checkStructProjTable_inv hTbl
  let tbl : ProjTable := ⟨T, lps, nP, cvCa.name, nF, resSort,
    bodies, ConLeche.structProjGuards cvCa.type nP nF sorts, 1⟩
  -- the field-chain facts, in the frames' spelling
  have hbound : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ → resSort.eval ψ ≠ 0 →
      FieldsBound (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2)) := by
    intro ψ ρ hρ hw
    cases hp : isProp
    · exact hboundP ψ ρ hρ hp
    · exfalso
      apply hw
      rw [hp] at hProp
      exact Level.isEquiv_sound (beq_iff_eq.mp hProp.symm) ψ
  have hokB : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
      FieldsOkB (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2)) :=
    fun ψ ρ h => (hfields ψ ρ h).1
  -- the guards' content: the official join over the used earlier slots
  have hguardSem : ∀ k, k < nF → ∀ ψ : Name → Nat,
      ((ConLeche.structProjGuards cvCa.type nP nF sorts).getD k .zero).eval ψ = 0 →
      (sorts.getD k .zero).eval ψ = 0 ∧
      ∀ j, j < k → ConLeche.structUsedLater cvCa.type nP j = true →
        (sorts.getD j .zero).eval ψ = 0 := by
    intro k hk ψ h0
    rw [ConLeche.structProjGuards_getD _ _ _ _ hk,
      eval_foldl_max_if_zero_iff ψ (ConLeche.structUsedLater cvCa.type nP)
        (fun j => sorts.getD j .zero)] at h0
    exact ⟨h0.1, fun j hj hu => h0.2 j (List.mem_range.mpr hj) hu⟩
  have hguardOf : ∀ k, k < nF → ∀ ψ : Name → Nat,
      (∀ j, j ≤ k → (sorts.getD j .zero).eval ψ = 0) →
      ((ConLeche.structProjGuards cvCa.type nP nF sorts).getD k .zero).eval ψ = 0 := by
    intro k hk ψ hall
    rw [ConLeche.structProjGuards_getD _ _ _ _ hk,
      eval_foldl_max_if_zero_iff ψ (ConLeche.structUsedLater cvCa.type nP)
        (fun j => sorts.getD j .zero)]
    exact ⟨hall k (Nat.le_refl _), fun j hj _ => hall j (Nat.le_of_lt (List.mem_range.mp hj))⟩
  have hO5 : ∀ k, k < nF → (Level.isEquiv resSort .zero == some true) = false →
      ∀ ψ : Name → Nat, resSort.eval ψ = 0 →
      ((ConLeche.structProjGuards cvCa.type nP nF sorts).getD k .zero).eval ψ = 0 := by
    intro k hk hne ψ h0
    refine hguardOf k hk ψ fun j hj => ?_
    have := Level.leq_sound (hleq j (by omega) (by rw [hProp]; exact hne)) ψ
    omega
  -- the constructor type's scoping
  obtain ⟨hCf, -, -, hCb, -⟩ := mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfC)
  simp only [ConstantInfo.toConstantVal] at hCf hCb
  -- the unused earlier fields are free in the projected field's type
  obtain ⟨fvsA, oA, hopAll⟩ := openPisAtFvars_of_stripPis_isSome (nP + nF) 0 hstripC
  have hlenA : fvsA.length = nP + nF := openPisAtFvars_length _ hopAll
  have hfree : ∀ (ψ : Name → Nat) (k : Nat), k < nF → ∀ (j : Nat), j < k →
      ConLeche.structUsedLater cvCa.type nP j = false →
      ∃ X : AnnotTerm, (((ds ψ).drop nP).map (·.2.2)).getD k default = X.liftN 1 (k - 1 - j) := by
    intro ψ k hk j hj hun
    have hsome : (cvCa.type.stripPis (nP + j + 1)).isSome = true :=
      ConLeche.stripPis_isSome_of_le (by omega) hstripC
    obtain ⟨⟨bs, rest⟩, hst⟩ := Option.isSome_iff_exists.mp hsome
    have hrest : rest.hasLooseBVar 0 = false := by
      unfold ConLeche.structUsedLater at hun
      rw [hst] at hun
      have hun' : rest.hasLooseBVarB 0 = false := hun
      rw [ConLeche.Expr.hasLooseBVarB_eq] at hun'
      exact hun'
    obtain ⟨hleavesK, -⟩ := openPisAtFvars_leaf_free (nP + nF) (nP + j) hopAll (by omega)
      hst hrest (by
        intro l hl
        rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hCf] at hl
        exact absurd hl List.not_mem_nil)
    obtain ⟨pps', b, hstA, -, -, hbind⟩ := denoteMeta_openPis (nP + nF) hopAll (hCDread ψ)
    have hppsEq : pps' = ds ψ := by
      have h2 := stripPisAV_mkPisAV (ds ψ) (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ))
      rw [hCDlen ψ] at h2
      exact (Prod.mk.inj (Option.some.inj (hstA.symm.trans h2))).1
    obtain ⟨x, hx⟩ : ∃ x, fvsA[nP + k]? = some x :=
      ⟨fvsA[nP + k]'(by rw [hlenA]; omega), List.getElem?_eq_getElem (by rw [hlenA]; omega)⟩
    obtain ⟨q, hq, -, hqread⟩ := hbind (nP + k) x hx
    rw [hppsEq] at hq
    have hW : Expr.WScoped (0 + (nP + k)) (Expr.fvarTypeD x) :=
      openPisAtFvars_typeWScoped (nP + nF) hopAll (Expr.WScoped.of_not_hasFvar hCf) _ x hx
    have hleaf : ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves, l.1 ≠ nP + j := by
      intro l hl
      have hsub : l ∈ x.fvarLeaves := by
        cases x with
        | fvar idx ty =>
          simp only [Expr.fvarLeaves, Expr.fvarTypeD] at hl ⊢
          exact List.mem_cons_of_mem _ hl
        | _ => exact hl
      have := hleavesK (nP + k) (by omega) x hx l hsub
      simpa using this
    obtain ⟨X, hX⟩ := denoteMeta_liftN_of_leaf_free mp.base2 (0 + (nP + k)) (Expr.fvarTypeD x) hW
      (q := nP + j) (by omega) (by intro l hl; exact hleaf l hl) hqread
    refine ⟨X, ?_⟩
    have hFk : (((ds ψ).drop nP).map (·.2.2)).getD k default = q.2.2 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_drop, hq]
      rfl
    rw [hFk, hX, show 0 + (nP + k) - 1 - (nP + j) = k - 1 - j from by omega]
  -- names
  have hneT : T ≠ projTableName T := by
    intro h
    have := projTableName_isProjFnShape T
    rw [← h, hTshape] at this
    exact nomatch this
  have hneC : cvCa.name ≠ projTableName T := by
    intro h
    have := projTableName_isProjFnShape T
    rw [← h, hCshape] at this
    exact nomatch this
  have hnres : ConLeche.reservedBasisNames.contains (projTableName T) = false :=
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
  have hfT₂ : (⟨.projInfo tbl :: env.consts⟩ : Env).find? T
      = some (.indInfo cvTa caps) := by
    rw [ConLeche.Env.find?_cons, if_neg (fun h => hneT h.symm)]
    exact hfT
  have hfC₂ : (⟨.projInfo tbl :: env.consts⟩ : Env).find? cvCa.name
      = some (.ctorInfo cvCa nP nF) := by
    rw [ConLeche.Env.find?_cons, if_neg (fun h => hneC h.symm)]
    exact hfC
  have hfTbl₂ : (⟨.projInfo tbl :: env.consts⟩ : Env).find? (projTableName T)
      = some (.projInfo tbl) := ConLeche.Env.find?_cons_self _ _
  have hprev₂ : ∀ j, j < nF →
      ∃ entry, (⟨.projInfo tbl :: env.consts⟩ : Env).findProj? T j
        = some entry :=
    fun j hj => ⟨tbl.entry j, ConLeche.Env.findProj?_of_table hfTbl₂ hj⟩
  -- the head data at every field
  have hhead : ∀ i, i < nF → ConLeche.TowerHead ⟨.projInfo tbl :: env.consts⟩ (tbl.entry i) :=
    fun i hi => ⟨hresT, hresR, hresC, hi, ⟨cvTa, caps, hfT₂, hlpsT⟩,
      ⟨cvCa, hfC₂, hlpsC, hstripC⟩⟩
  suffices hlaw : ∀ m₂ : EnvModel V ⟨.projInfo tbl :: env.consts⟩,
      m₂.acval = acvalWith mp.base2.acval (ConstantInfo.projInfo tbl).name (fun _ => .sort 0) →
      ∀ (φ : Name → Nat) (i : Nat), i < tbl.numFields →
        TowerEntryLaw m₂ φ tbl.structName i (tbl.entry i) by
    obtain ⟨mp', hac'⟩ :=
      declStep_preserves_of_tower_cons mp (tbl := tbl) hfresh hnres hwf' hnp hhead hlaw
    exact ⟨tbl, mp', rfl, rfl, hfresh, hac'⟩
  -- the fields' laws
  intro m₂ hac φ i hi
  replace hi : i < nF := hi
  have hacT : ∀ ψ, m₂.acval T ψ = mp.base2.acval T ψ := by
    intro ψ
    rw [hac]
    show acvalWith mp.base2.acval (projTableName T) _ T ψ = _
    rw [acvalWith_ne hneT]
  have hacC : ∀ ψ, m₂.acval cvCa.name ψ = mp.base2.acval cvCa.name ψ := by
    intro ψ
    rw [hac]
    show acvalWith mp.base2.acval (projTableName T) _ cvCa.name ψ = _
    rw [acvalWith_ne hneC]
  have hFD₂ : FormerData m₂ cvTa nP resSort pps :=
    hFD.cross (c₀ := .projInfo tbl) hfresh hcrossT hcbT m₂ hac
  -- the constructor type's reading at the extension
  have hCDread₂ : ∀ ψ, denoteMeta m₂.acval ⟨.projInfo tbl :: env.consts⟩ ψ 0 cvCa.type
      = some (mkPisAV (ds ψ) (ctorBodyAVI m₂ T nP nF ψ (Es ψ))) := by
    intro ψ
    have hbody : ctorBodyAVI m₂ T nP nF ψ (Es ψ)
        = ctorBodyAVI mp.base2 T nP nF ψ (Es ψ) := by
      unfold ctorBodyAVI; rw [hacT]
    rw [hbody, hac]
    exact denoteMeta_cons_mono hfresh hcrossC ψ 0 hcbC (hCDread ψ)
  -- the body, opened at the variables
  obtain ⟨cds, bodyB, mbB, hcf⟩ :=
    ConLeche.structProjBody_open hbodies hstripC hCb hi
  refine ⟨rfl, rfl, hi, ⟨cvTa, caps, hfT₂, hlpsT, hcaps⟩,
    hO5 i hi, cvCa, hfC₂, hlpsC, ?_, ?_⟩
  · -- the per-instantiation laws
    intro us _
    -- the subject's frame: a member of the one-constructor fibre of
    -- the tagged union (offset 1)
    obtain ⟨fdomA, hfdA, hokFd, hresFd⟩ := bodyFrames m₂ (off := 1) hcf hCf hCb
      (fun j hj => by
        obtain ⟨entry, hfe⟩ := hprev₂ j (by omega)
        refine ⟨entry, hfe, ?_⟩
        obtain ⟨tbl', hf', -, rfl⟩ := ConLeche.Env.findProj?_some hfe
        obtain rfl : tbl = tbl' := ConstantInfo.projInfo.inj (Option.some.inj (hfTbl₂.symm.trans hf'))
        rfl) hi
      (hCDlen (Level.substFn φ lps us))
      (hCDbelow (Level.substFn φ lps us))
      (hCDread₂ (Level.substFn φ lps us))
      (fun ρ h => hfields _ ρ h) (hsortsF _)
      (used := ConLeche.structUsedLater cvCa.type nP) (hfree _ i hi)
      (fun ρ => ρ 0 ∈ˢ sumSet (resSort.eval (Level.substFn φ lps us))
        (sumFibre (resSort.eval (Level.substFn φ lps us)) (fun j => ρ (j + 1))
          [((ds (Level.substFn φ lps us)).drop nP).map (·.2.2) ++ [idxEqAV []]]))
      (fun ρ hx _ hw => by
        rw [hw] at hx
        exact fixFibre_zero_elim hx)
      (fun ρ hx _ hw => by
        obtain ⟨fs, heq, hsp, -⟩ := fixFibre_elim hw hx
        have hlenF : fs.length = nF := by
          rw [hsp.length_eq, List.length_map, List.length_drop, hCDlen, Nat.add_sub_cancel_left]
        rw [heq, dropS_one_inj, ← hlenF, projList_mkTower_take (Nat.le_refl _), List.take_length]
        exact hsp)
      (fun ρ hx hsat j hj => by
        refine wellDenoted_projAV_succ_fibre (fun _ => hokB _ _ hsat) trivial ?_ ?_
        · rw [interp_bvar]; exact hx
        · rw [List.length_map, List.length_drop, hCDlen, Nat.add_sub_cancel_left]; exact hj)
    have hread : denoteMeta m₂.acval ⟨.projInfo tbl :: env.consts⟩ φ 0
        (ConLeche.projTele ((tbl.entry i).numParams + 1)
          ((tbl.entry i).body.instantiateLevelParams (tbl.entry i).levelParams us))
        = some (mkPisAV (List.replicate (nP + 1) (0, 1, .sort 0)) fdomA) := by
      show denoteMeta m₂.acval _ φ 0 (ConLeche.projTele (nP + 1)
        ((bodies.getD i default).instantiateLevelParams lps us)) = _
      rw [← ConLeche.projTele_instantiateLevelParams,
        denotePInstLevels m₂ φ lps us 0]
      exact denoteMeta_projTele_zero hfdA
    refine ⟨⟨_, hread, ?_⟩, ?_⟩
    · -- (A)
      intro hguardAt ρ vs x rest hlenVs hokApp hokx hmem hpeel
      have hguard' : resSort.eval (Level.substFn φ lps us) = 0 →
          (sorts.getD i .zero).eval (Level.substFn φ lps us) = 0 ∧
          ∀ j, j < i → ConLeche.structUsedLater cvCa.type nP j = true →
            (sorts.getD j .zero).eval (Level.substFn φ lps us) = 0 :=
        fun h0 => hguardSem i hi _ (hguardAt h0)
      have hacT' : m₂.acval tbl.structName (Level.substFn φ (tbl.entry i).levelParams us)
          = L (Level.substFn φ lps us) := by
        show m₂.acval T (Level.substFn φ lps us) = _
        rw [hacT, hleafT]
      rw [hacT'] at hokApp hmem
      exact fixEntryTypingCore (hCDlen _) (hFD.len _) (by simp) (hiff _) (hokB _)
        (hsortsF _) (used := ConLeche.structUsedLater cvCa.type nP) hguard' (hfree _ i hi) hi
        (hlam _) (hfold _) hresFd (hokFd (fun h0 => (hguard' h0).2)) ρ vs x rest hlenVs hokApp
        hokx hmem hpeel
    · -- (B): the constructor type's reading at the instantiation,
      -- then the two regimes
      refine ⟨mkPisAV (ds (Level.substFn φ lps us))
        (ctorBodyAVI m₂ T nP nF (Level.substFn φ lps us)
          (Es (Level.substFn φ lps us))), ?_, ?_⟩
      · rw [denotePInstLevels m₂ φ cvCa.levelParams us 0 cvCa.type, hlpsC]
        exact hCDread₂ _
      · intro hguardAt ρ ys rest hlen hok hfit
        have hacC' : m₂.acval (tbl.entry i).ctor (Level.substFn φ (tbl.entry i).levelParams us)
            = sumMkAV (resSort.eval (Level.substFn φ lps us)) 0
              (ds (Level.substFn φ lps us))
              (((ds (Level.substFn φ lps us)).drop nP).map (·.2.2))
              (uChains [((ds (Level.substFn φ lps us)).drop nP).map (·.2.2)]) := by
          show m₂.acval cvCa.name (Level.substFn φ lps us) = _
          rw [hacC, hleafC]
        rw [hacC'] at hok ⊢
        show interp V ρ (projAV (i + 1) _) = _
        by_cases hw : resSort.eval (Level.substFn φ lps us) = 0
        · -- squash: the certified fit pins the selected field to a
          -- proposition's domain
          have hsp : SpineFit ρ ((ds (Level.substFn φ lps us)).map (·.2.2))
              (ys.map (interp V ρ)) :=
            spineFit_of_teleFit (by simp only [List.length_map, hlen, hCDlen]; rfl) hfit
          rw [hw]
          exact fixEntryIotaCoreZero (hCDlen _) hi (hsortsF _)
            (hguardSem i hi _ (hguardAt hw)).1 ys hlen hsp
        · -- graph: the grading's slot chain
          exact fixEntryIotaCore hw (hCDlen _) hi (hokB _) ys hlen hok
  · -- (C)
    intro cvT capsT hf us _
    obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj (hfT₂.symm.trans hf))
    refine ⟨mkPisAV (pps (Level.substFn φ lps us))
      (.sort (resSort.eval (Level.substFn φ lps us))), ?_, hFD.okTy _, ?_⟩
    · rw [denotePInstLevels m₂ φ cvTa.levelParams us 0 cvTa.type, hlpsT]
      exact hFD₂.read _
    · intro ρ ts rest x hlents hfit hmem
      have hsp := spineFit_of_teleFit (by rw [hFD.len]; exact hlents) hfit
      have hacT' : m₂.acval tbl.structName (Level.substFn φ (tbl.entry i).levelParams us)
          = L (Level.substFn φ lps us) := by
        show m₂.acval T (Level.substFn φ lps us) = _
        rw [hacT, hleafT]
      have hacC' : m₂.acval (tbl.entry i).ctor (Level.substFn φ (tbl.entry i).levelParams us)
          = sumMkAV (resSort.eval (Level.substFn φ lps us)) 0
            (ds (Level.substFn φ lps us))
            (((ds (Level.substFn φ lps us)).drop nP).map (·.2.2))
            (uChains [((ds (Level.substFn φ lps us)).drop nP).map (·.2.2)]) := by
        show m₂.acval cvCa.name (Level.substFn φ lps us) = _
        rw [hacC, hleafC]
      rw [hacT'] at hmem
      rw [hacC']
      show x = (ts ++ (List.range nF).map fun j => projS (j + 1) x).foldl SetTheory.app _
      exact fixEntryEtaCore (hCDlen _) (hFD.len _) (hiff _) (hokB _) (hfold _) ts x hlents hsp hmem

end ConLeche.Model

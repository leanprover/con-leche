module

public import ConLeche.Model.Inductives.BlockTableOf
import ConLeche.Model.Inductives.BlockStageTable
import ConLeche.Model.Inductives.BlockStageTables
import ConLeche.Model.Inductives.MutualNoProj
import ConLeche.Model.Inductives.MutualRecsStore
import ConLeche.Model.Inductives.MutualFormersKit
import ConLeche.Model.Inductives.MutualRecsStage
import ConLeche.Verify.Inductives.MutualGrouped
import ConLeche.Verify.Inductives.MutualInv
public section

/-!
# The tables' stage, discharged; `declBlock` closed (task #315, M4 s5)

`MutualTablesModeled` (`DeclBlock.lean`) is PROVED: at the recursors'
environment the datum instantiates the flat table bundle at every
structure-like member (`tableMember_of`, `memberTableOk_of` —
`BlockTableOf.lean`'s set-level clauses, the datum's readings, the
table facts, the names read off the run, the `NoProjEnv` bookkeeping
`MutualNoProj.lean`), and the members' fold (`stageBlockTables`,
`BlockStageTables.lean`) at the P step (`blockTableStep`,
`BlockStageTable.lean`) conses the tables one by one.

With it `declBlock` has no premise beyond the run: `declMutual`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecRule MutualBlock
  MutualFormerA MutualCtor fueledOps)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## The bundle at a structure-like member, from the datum -/

/-- **The flat table bundle at a structure-like member**, from the
datum at the recursors' environment: the readings are the datum's,
the set-level clauses `BlockTableOf.lean`'s, the sorts the table
facts', the names the run's. -/
theorem tableMember_of {env : Env} {m : EnvModel V env} {b : MutualBlock}
    {fms : List MutualFormerA} {sortss : List (List Level)} {d : BlockRepData V}
    (hreps : BlockReps m d) (htyped : ∀ ψ : Name → Nat, FormersTyped m d ψ ∧ CtorsTyped m d ψ)
    (htf : MutualTableFacts b fms sortss d)
    {mIdx : Nat} (hmm : mIdx < d.k) {f : MutualFormerA} (hft : fms[mIdx]? = some f)
    (hname : d.memberName mIdx = f.cvTa.name)
    (hstored : MemberStored m b.lps b.nP f d.resSort (d.ppsM mIdx))
    (hnP : d.nP = b.nP) (hnIdx : f.nIdx = 0)
    {cA : ConstantVal × Nat} (hone : d.ctorsM mIdx = [cA]) {J : Nat}
    (hJ : b.ownOffset mIdx = J) (hlpsC : cA.1.levelParams = b.lps)
    (hnp : ∀ j, NoProjEnv env f.cvTa.name j)
    (hTshape : f.cvTa.name.isProjFnShape = false)
    (hresT : ConLeche.reservedBasisNames.contains f.cvTa.name = false)
    (hresR : ConLeche.reservedBasisNames.contains (f.cvTa.name.str "rec") = false)
    (hCshape : cA.1.name.isProjFnShape = false)
    (hresC : ConLeche.reservedBasisNames.contains cA.1.name = false)
    {sorts : List Level} (hsj : sortss[J]? = some sorts) :
    TableMember m b.lps d.nP f.cvTa.name f.cvTa cA.1 cA.2 J f.s d.isProp sorts (d.ppsM mIdx)
      (d.dsF mIdx 0) (d.esF mIdx 0) (d.tableCarrier mIdx) := by
  obtain ⟨cvT, cvR, mI, rP, rules, h⟩ := hreps mIdx hmm
  have hj : (d.ctorsM mIdx)[0]? = some cA := by rw [hone]; rfl
  have hnI : d.nIdxAt mIdx = 0 := by
    have h1 := hstored.data.len (fun _ => 0)
    have h2 := h.ppsM_length (fun _ => 0)
    rw [hnIdx, ← hnP] at h1
    omega
  have hsEq : ∀ ψ : Name → Nat, f.s.eval ψ = d.resSort.eval ψ := hstored.sEq
  have hBC := h.ctors mIdx 0 cA hmm hj
  have hcd := hBC.2.2
  have hinj : ∀ (ψ : Name → Nat) (fs : List V),
      d.inj ψ mIdx 0 fs = injW (d.w ψ) J (mkTower (fs ++ [pt])) := by
    intro ψ fs
    rw [htf.inj, Nat.add_zero, hJ]
  have hJ0 : b.ownOffset mIdx + 0 = J := by rw [Nat.add_zero, hJ]
  obtain ⟨sorts', hsj', hlenS, hleqS, hfieldsS⟩ := htf.sorts mIdx 0 cA hmm hj
  rw [hJ0] at hsj'
  obtain rfl : sorts = sorts' := Option.some.inj (hsj.symm.trans hsj')
  have hfD : fms.getD mIdx default = f := by
    rw [List.getD_eq_getElem?_getD, hft]; rfl
  rw [hfD] at hleqS
  exact
    { nproj := hnp
      fT := hstored.find
      lpsT := hstored.lps
      fC := hBC.1
      lpsC := hlpsC
      stripC := by
        obtain ⟨cbs, es, hst, -⟩ := hcd.resid
        rw [hst]; rfl
      prop := by rw [isPropBit_congr hsEq]; exact h.isProp
      Tshape := hTshape
      Cshape := hCshape
      resT := hresT
      resR := hresR
      resC := hresC
      FD := by
        have hFD := hstored.data
        rw [hnIdx, Nat.add_zero, ← hnP] at hFD
        exact FormerData.congr_sort hFD (fun ψ => (hsEq ψ).symm)
      CDread := fun ψ => by rw [← hname]; exact hcd.read ψ
      CDlen := hcd.len
      CDbelow := hcd.below
      CDbits := fun ψ dd hdd => by rw [hsEq]; exact hcd.bits ψ dd hdd
      leq := hleqS
      Tmem := fun ψ ρ => by
        rw [← hname, hsEq]
        exact (htyped ψ).1 mIdx hmm ρ
      Cmem := fun ψ ρ => by
        rw [← hname]
        exact (htyped ψ).2 mIdx hmm 0 cA hj ρ
      fold := fun ψ ρ ts hsp => by
        rw [← hname]
        exact h.table_fold hreps (htf.frame mIdx hmm) hnI ψ ρ ts hsp
      fib := fun ψ ρ' hρ' => by
        rw [hsEq]
        exact hreps.table_fibreAt (htyped ψ).1 hmm hone hnI (hinj ψ) hρ'
      ctor := fun ψ ρ as fs hspP hspF => by
        rw [hsEq]
        exact h.table_ctor hreps hone (hinj ψ) ρ as fs hspP hspF
      iff := fun ψ ρ => by
        have hfr := htf.frame mIdx hmm ψ ρ
        rw [List.take_of_length_le (by rw [h.ppsM_length, hnI, Nat.add_zero]; exact Nat.le_refl _)]
          at hfr
        exact hfr.trans (h.paramsIff mIdx 0 cA hmm hj ψ ρ)
      fields := fun ψ ρ hρ => by
        have hs := hfieldsS ψ ρ hρ
        rw [hsEq]
        exact ⟨hs.1, hs.2.1⟩
      boundP := fun ψ ρ hρ hp => by
        rw [hsEq]
        exact (hfieldsS ψ ρ hρ).2.2.1 hp
      sortsF := fun ψ ρ hρ j hjF as hsp => (hfieldsS ψ ρ hρ).2.2.2 j hjF as hsp }

/-- **A member's table data, when the kernel conses its table**: at a
structure-like member the bundle from the datum, with the kernel's
constructor position identified with the datum's (`ownCtors`, the
grouping). -/
theorem memberTableOk_of {env env₀ : Env} {m : EnvModel V env} {b : MutualBlock}
    {fms : List MutualFormerA} {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)}
    {d : BlockRepData V} (h3 : ConLeche.mutualCtorsGrouped b.ctors = true)
    (hlenA : ctorsA.length = b.ctors.length)
    (hnamesA : ∀ (J : Nat) (cA : ConstantVal × Nat) (ct : MutualCtor),
      ctorsA[J]? = some cA → b.ctors[J]? = some ct →
      cA.1.name = ct.cv.name ∧ cA.2 = ct.nF ∧ cA.1.levelParams = b.lps)
    (hd : MutualDatumOf env₀ b fms ctorsA d) (hreps : BlockReps m d)
    (htyped : ∀ ψ : Name → Nat, FormersTyped m d ψ ∧ CtorsTyped m d ψ)
    (htf : MutualTableFacts b fms sortss d)
    {mIdx : Nat} {f : MutualFormerA} (hft : fms[mIdx]? = some f) (hmm : mIdx < b.k)
    (hstored : MemberStored m b.lps b.nP f d.resSort (d.ppsM mIdx))
    (hnp : ∀ j, NoProjEnv env f.cvTa.name j)
    (hTshape : f.cvTa.name.isProjFnShape = false)
    (hresT : ConLeche.reservedBasisNames.contains f.cvTa.name = false)
    (hresR : ConLeche.reservedBasisNames.contains (f.cvTa.name.str "rec") = false)
    (hcnames : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
      cA.1.name.isProjFnShape = false ∧ ConLeche.reservedBasisNames.contains cA.1.name = false)
    (hsortsLen : sortss.length = ctorsA.length) :
    MemberTableOk m b ctorsA sortss d.isProp (fun t => d.tableCarrier t) f mIdx := by
  intro J c hown hnIdx
  have hown0 : (b.ownCtors mIdx)[0]? = some (J, c) := by rw [hown]; rfl
  have hJ : b.ownOffset mIdx = J := by
    have := ownCtors_getElem?_idx h3 hown0
    omega
  obtain ⟨hcJ, -⟩ := ownCtors_getElem?_ctors hown0
  have hJl : J < ctorsA.length := by rw [hlenA]; exact (List.getElem?_eq_some_iff.mp hcJ).1
  have hcA : ctorsA[J]? = some (ctorsA.getD J default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hJl]; rfl
  obtain ⟨hnm, hnF, hlpsC⟩ := hnamesA J _ c hcA hcJ
  have hmmd : mIdx < d.k := by rw [hd.k]; exact hmm
  have hone : d.ctorsM mIdx = [ctorsA.getD J default] := by rw [hd.ctors mIdx hmm, hown]; rfl
  have hname : d.memberName mIdx = f.cvTa.name := by
    show d.memberNames.getD mIdx .anonymous = _
    rw [hd.memberNames, List.getD_eq_getElem?_getD, List.getElem?_map, hft]; rfl
  obtain ⟨sorts, hsj⟩ : ∃ sorts, sortss[J]? = some sorts :=
    ⟨_, List.getElem?_eq_getElem (by rw [hsortsLen]; exact hJl)⟩
  have hsD : sortss.getD J [] = sorts := by rw [List.getD_eq_getElem?_getD, hsj]; rfl
  obtain ⟨hCshape, hresC⟩ := hcnames J _ hcA
  refine ⟨d.ppsM mIdx, d.dsF mIdx 0, d.esF mIdx 0, hnm, hnF, ?_⟩
  have htm := tableMember_of hreps htyped htf hmmd hft hname hstored hd.nP hnIdx hone hJ hlpsC hnp
    hTshape hresT hresR hCshape hresC hsj
  rw [hsD, ← hnF, ← hd.nP]
  exact htm

/-! ## The named fact, discharged -/

/-- **Stage 5 keeps the model** — `MutualTablesModeled`, proved: the
bundle at every structure-like member from the datum, the fold over
the members at the P step. -/
theorem mutualTablesModeled {F : Nat} : MutualTablesModeled V μ F := by
  intro hμ env hwf hproj b streamRecs fms f₀ tq₀ ctorsA sortss kinds formers4 ctors4 cvRas rulesOf
    envOut h0 h1 h2 h3 hformers hf₀ htq₀ hcross hL hctors hkinds hfo hgd hrectys hrules hrecNames
    mp₃ d hd hreps htyped hstored htf htbl
  have hnp := mutualNoProj hwf hproj hformers hctors hgd hrectys hrules
  have hnames := mutualMemberNames hformers
  have hnamesEq := mutualMemberNames_eq hformers
  have hcnames := mutualCtorNames hctors
  obtain ⟨hlenA, hnamesA⟩ := ctorsA_names_of hctors h1
  obtain ⟨-, hsortsLen, -⟩ := ConLeche.checkMutualCtors_inv hctors
  obtain ⟨hchecks, -⟩ := ConLeche.mutualFormers_inv hformers
  have hlenF : fms.length = b.k := (mutualFormerChecks_pos hchecks).1
  have hnd : (fms.map (·.cvTa.name)).Nodup := by
    rw [hnamesEq]
    have h0' := h0
    unfold ConLeche.MutualBlock.blockNames at h0'
    exact (List.nodup_append.mp (List.nodup_append.mp h0').1).1
  refine stageBlockTables (isProp := d.isProp) (S := fun t => d.tableCarrier t) blockTableStep mp₃ htbl hnd ?_
  intro q hq
  have hft : fms[q.2]? = some q.1 := List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hq)
  have hmm : q.2 < b.k := by rw [← hlenF]; exact (List.getElem?_eq_some_iff.mp hft).1
  obtain ⟨-, hTshape, hresT, hrec⟩ := hnames q.2 q.1 hft
  have hresR : ConLeche.reservedBasisNames.contains (q.1.cvTa.name.str "rec") = false := by
    rw [← hrec]; exact (hrecNames q.2 hmm).2.1
  exact memberTableOk_of h3 hlenA hnamesA hd hreps htyped htf hft hmm (hstored q.2 q.1 hft)
    (hnp q.2 q.1 hft) hTshape hresT hresR hcnames (by rw [hsortsLen, hlenA])

/-! ## `declBlock`, closed -/

/-- **The model survives a mutual block** — `declBlock` at its two
named facts, both proved (`mutualCoreModeled`, `mutualTablesModeled`):
no premise beyond the mode, the pre-block model, the η closure, the
recursor records' pin and the run. -/
theorem declMutual (hμ : μ.verifiedChecks = true) {F : Nat} {env envOut : Env}
    {p : ConLeche.MutualParts} (mp : EnvModelM V μ env) (hE : ConLeche.EtaFamiliesClosed env)
    (hpinOk : ConLeche.mutualRecPinOk p = true)
    (h : ConLeche.Semantics.DeclMutualRun μ F env p envOut) :
    Nonempty (EnvModelM V μ envOut) :=
  declBlock hμ mp hE hpinOk mutualCoreModeled mutualTablesModeled h

end ConLeche.Model

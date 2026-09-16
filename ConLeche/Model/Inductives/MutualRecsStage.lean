module

public import ConLeche.Model.Inductives.MutualRecData
public import ConLeche.Model.Inductives.MutualCore
import ConLeche.Model.Inductives.MutualRecsProvision
import ConLeche.Model.Inductives.FixStageRec
import ConLeche.Model.Inductives.BlockRecKit
import ConLeche.Model.Inductives.BlockRecLeaf
import ConLeche.Model.Inductives.BlockRecValid
import ConLeche.Semantics.Tower.SigChainWire
import ConLeche.Model.Inductives.MutualFormersKit
public section

/-!
# The recursors' stage: the readings from the run (task #315 U-8, M4 s4a)

The recursor types' readings (`MutualRecData`, `mutualRecData_of`) are
read off the generated types against the members' and constructors'
reading premises (`FormerReadsM`, `MutualCtorReadsM`).  At the uniform
datum those premises come from the datum's own clauses: a constructor's
`BlockCtorData` (`BlockRep.ctors`, through `blockCtorRead_of`) and the
members' stored records — the ONE run fact the datum does not carry,
`MemberStored`: member `t`'s checked constant is what the store finds
under its name, at the block's level parameters, its telescope ending
in its own sort, its `FormerData` at the datum's parameter data.  The
kinds the run classified are the datum's (`hkinds`: `ksF`/`tgts` are
`kindsOf`/`tgtAt` of the classification at the block's own position,
`ownOffset mm + j`), so the generated constructors' `recFields` are
the datum's recursive positions paired with their targets
(`mutualRecFieldsOf_eq`).

The recursor list, the position tables and the member table are the
datum's (`MutualRecs.lean`); the block's `k` recursor types then read
to `blockRds`, member `mm`'s reading's Π-tower over the datum's lists,
graded at the kernel's inferred sort (`blockRecData_of`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule
  BinderMeta MutualBlock MutualFormerA MutualFormer MutualCtor4)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The members stored at the datum's readings -/

/-- The reading layer's record, at the generators' former. -/
theorem MemberStored.toFormerFacts {m : EnvModel V env} {lps : List Name} {nP : Nat}
    {f : MutualFormerA} {resSort : Level} {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (h : MemberStored m lps nP f resSort pps) :
    MutualFormerFacts m lps nP ⟨f.cvTa.name, f.nIdx, f.cvTa.type⟩ f.cvTa f.s pps where
  find := ⟨{}, h.find⟩
  tty := rfl
  lps := h.lps
  strip := h.strip
  data := h.data.congr_sort (fun ψ => (h.sEq ψ).symm)

/-! ## The datum's constructors at the block's positions -/

section Positions

variable {b : MutualBlock} {fms : List MutualFormerA} {ctorsA : List (ConstantVal × Nat)}
  {d : BlockRepData V}

omit [SetTheory V] in
/-- The datum's minor index is the block's own offset. -/
theorem MutualDatumOf.minorIdx_eq (hd : MutualDatumOf env b fms ctorsA d) {c : Nat} (hc : c < b.k)
    (j : Nat) : d.minorIdx c j = b.ownOffset c + j := by
  unfold BlockRepData.minorIdx ConLeche.MutualBlock.ownOffset
  congr 2
  refine List.map_congr_left fun t ht => ?_
  rw [hd.ctors t (Nat.lt_trans (List.mem_range.mp ht) hc), List.length_map]

omit [SetTheory V] in
/-- The datum's constructor count is the block's. -/
theorem MutualDatumOf.nCtors_eq (hd : MutualDatumOf env b fms ctorsA d)
    (h2 : b.ctors.all (fun c => c.member < b.k) = true) (hlenA : ctorsA.length = b.ctors.length) :
    d.nCtors = ctorsA.length := by
  have : d.nCtors = b.ownOffset b.k := by
    unfold BlockRepData.nCtors ConLeche.MutualBlock.ownOffset
    rw [hd.k]
    congr 1
    exact List.map_congr_left fun t ht => by
      rw [hd.ctors t (List.mem_range.mp ht), List.length_map]
  rw [this, ownOffset_k h2, hlenA]

omit [SetTheory V] in
/-- A member's constructor is the checked constructor at the block's
position, listed under that member. -/
theorem MutualDatumOf.ctorsM_get (hd : MutualDatumOf env b fms ctorsA d)
    (hg : ConLeche.mutualCtorsGrouped b.ctors = true) (hlenA : ctorsA.length = b.ctors.length)
    {c j : Nat} (hc : c < b.k) {cA : ConstantVal × Nat} (hj : (d.ctorsM c)[j]? = some cA) :
    b.ownOffset c + j < ctorsA.length ∧ ctorsA[b.ownOffset c + j]? = some cA ∧
      ∃ ct, b.ctors[b.ownOffset c + j]? = some ct ∧ ct.member = c := by
  rw [hd.ctors c hc, List.getElem?_map] at hj
  obtain ⟨⟨J, ct⟩, hq, rfl⟩ := Option.map_eq_some_iff.mp hj
  have hJ := ownCtors_getElem?_idx hg hq
  obtain ⟨hct, hmem⟩ := ownCtors_getElem?_ctors hq
  subst hJ
  have hlt : b.ownOffset c + j < ctorsA.length := by
    rw [hlenA]; exact (List.getElem?_eq_some_iff.mp hct).1
  refine ⟨hlt, ?_, ct, hct, hmem⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  rfl

end Positions

/-! ## The readings from the run -/

section Readings

variable {F : Nat} {b : MutualBlock} {fms : List MutualFormerA}
  {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)}
  {kinds : List (List (RecFieldKind × Nat))} {formers4 : List MutualFormer}
  {ctors4 : List MutualCtor4} {d : BlockRepData V} {m : EnvModel V env} {env₀ : Env}

omit [SetTheory V] in
/-- The generators' formers, positionally. -/
theorem formers4_getD (hgd : ConLeche.mutualGenData b fms ctorsA kinds = (formers4, ctors4))
    {t : Nat} (ht : t < fms.length) :
    formers4.getD t default
      = ⟨(fms.getD t default).cvTa.name, (fms.getD t default).nIdx,
          (fms.getD t default).cvTa.type⟩ := by
  obtain ⟨hf4, -⟩ := Prod.mk.inj hgd
  rw [← hf4, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem ht,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
  rfl

omit [SetTheory V] in
theorem formers4_length (hgd : ConLeche.mutualGenData b fms ctorsA kinds = (formers4, ctors4)) :
    formers4.length = fms.length := by
  obtain ⟨hf4, -⟩ := Prod.mk.inj hgd
  rw [← hf4]
  simp

omit [SetTheory V] in
theorem ctors4_length (hgd : ConLeche.mutualGenData b fms ctorsA kinds = (formers4, ctors4))
    (hlenK : kinds.length = ctorsA.length) (hlenA : ctorsA.length = b.ctors.length) :
    ctors4.length = ctorsA.length := by
  obtain ⟨-, hc4⟩ := Prod.mk.inj hgd
  rw [← hc4, List.length_zipWith, List.length_zip, hlenK, hlenA]
  omega

omit [SetTheory V] in
/-- The generators' constructors, positionally. -/
theorem ctors4_getElem? (hgd : ConLeche.mutualGenData b fms ctorsA kinds = (formers4, ctors4))
    {J : Nat} {cA : ConstantVal × Nat} (hJ : ctorsA[J]? = some cA) {ct : ConLeche.MutualCtor}
    (hct : b.ctors[J]? = some ct) {ks : List (RecFieldKind × Nat)} (hks : kinds[J]? = some ks) :
    ctors4[J]? = some ⟨ct.cv.name, ct.nF, cA.1.type, ct.member, ConLeche.mutualRecFieldsOf ks⟩ := by
  obtain ⟨-, hc4⟩ := Prod.mk.inj hgd
  have hzip : (b.ctors.zip ctorsA)[J]? = some (ct, cA) := by
    rw [List.zip, List.getElem?_zipWith, hct, hJ]
  rw [← hc4, List.getElem?_zipWith, hzip, hks]

/-- **The checked constructors' names, field counts and level
parameters are the block record's** (`checkMutualCtors`' constant
check keeps the name and the level parameters). -/
theorem ctorsA_names_of {isProp : Bool} (hctors : ConLeche.checkMutualCtors (m := ConLeche.CheckM)
      (ConLeche.fueledOps μ F) env b fms isProp b.ctors = .ok (ctorsA, sortss))
    (h1 : (b.formers.all (fun f => f.1.levelParams == b.lps) &&
      b.ctors.all (fun c => c.cv.levelParams == b.lps)) = true) :
    ctorsA.length = b.ctors.length ∧
    ∀ (J : Nat) (cA : ConstantVal × Nat) (ct : ConLeche.MutualCtor),
      ctorsA[J]? = some cA → b.ctors[J]? = some ct →
      cA.1.name = ct.cv.name ∧ cA.2 = ct.nF ∧ cA.1.levelParams = b.lps := by
  obtain ⟨hlenA, -, hall⟩ := ConLeche.checkMutualCtors_inv hctors
  refine ⟨hlenA, fun J cA ct hJ hct => ?_⟩
  obtain ⟨hnF, sorts, -, hrun⟩ := hall J ct cA hct hJ
  obtain ⟨⟨ty', hccv⟩, -, -⟩ := ConLeche.checkMutualCtor_shape hrun
  obtain ⟨-, -, -, -, -, -, _, _, _, -, -, -, -, -, hty⟩ := ConLeche.checkConstantVal_inv hccv
  have hlpsC : ct.cv.levelParams = b.lps := by
    have h1' := h1
    simp only [Bool.and_eq_true] at h1'
    have := List.all_eq_true.mp h1'.2 ct (List.mem_of_getElem? hct)
    simpa using this
  rw [hty]
  exact ⟨rfl, hnF, hlpsC⟩

/-- **The members' reading premises** at the datum's readers. -/
theorem blockFormerReadsM_of (hd : MutualDatumOf env₀ b fms ctorsA d)
    (hgd : ConLeche.mutualGenData b fms ctorsA kinds = (formers4, ctors4))
    (hstored : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      MemberStored m b.lps b.nP f d.resSort (d.ppsM t))
    (ψ : Name → Nat) :
    FormerReadsM m ψ b.lps b.nP (fun t => m.acval (d.memberName t) ψ) d.nIdxAt
      (fun t => (d.ppsM t ψ).take b.nP) (fun t => (d.ppsM t ψ).drop b.nP) formers4 := by
  have hlen := formers4_length hgd
  refine formerReadsM_of (cvTaOf := fun t => (fms.getD t default).cvTa)
    (sOf := fun t => (fms.getD t default).s) (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_) ψ
  · rw [hlen] at ht
    rw [formers4_getD hgd ht]
    show (d.memberNames.getD t .anonymous) = _
    rw [hd.memberNames, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem ht, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
    rfl
  · rw [hlen] at ht
    rw [formers4_getD hgd ht]
    show (d.nIdxs.getD t 0) = _
    rw [hd.nIdxs, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem ht, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
    rfl
  · rw [hlen] at ht
    rw [formers4_getD hgd ht]
    exact (hstored t _ (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]; rfl)).toFormerFacts

/-- **The constructors' reading premises** at the datum's lists and
tables. -/
theorem blockCtorReadsM_of (hd : MutualDatumOf env₀ b fms ctorsA d) (hreps : BlockReps m d)
    (h2 : b.ctors.all (fun c => c.member < b.k) = true)
    (hg : ConLeche.mutualCtorsGrouped b.ctors = true)
    (hlenA : ctorsA.length = b.ctors.length) (hlenK : kinds.length = ctorsA.length)
    (hnames : ∀ (J : Nat) (cA : ConstantVal × Nat) (ct : ConLeche.MutualCtor),
      ctorsA[J]? = some cA → b.ctors[J]? = some ct →
      cA.1.name = ct.cv.name ∧ cA.2 = ct.nF ∧ cA.1.levelParams = b.lps)
    (hgd : ConLeche.mutualGenData b fms ctorsA kinds = (formers4, ctors4))
    (hkinds : ∀ mm j, mm < b.k → j < (d.ctorsM mm).length →
      d.ksF mm j = kindsOf (mutKsOf kinds (b.ownOffset mm + j)) ∧
      ∀ i, d.tgts mm j i = tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i)
    (ψ : Name → Nat) :
    MutualCtorReadsM m ψ b.lps b.nP d.recTname d.nIdxAt d.recMots d.recTgts ctors4 (d.recCds ψ) := by
  have hlen4 := ctors4_length hgd hlenK hlenA
  have hnC := hd.nCtors_eq h2 hlenA
  refine ⟨by rw [d.recCds_length, hnC, ← hlen4], ?_⟩
  intro J hJ
  rw [hlen4] at hJ
  have hJn : J < d.nCtors := by rw [hnC]; exact hJ
  obtain ⟨c, j, cA, hc, hj, rfl⟩ := d.minor_index hJn
  have hck : c < b.k := by rw [← hd.k]; exact hc
  have hj' : j < (d.ctorsM c).length := (List.getElem?_eq_some_iff.mp hj).1
  obtain ⟨hlt, hJA, ct, hct, hmem⟩ := hd.ctorsM_get hg hlenA hck hj
  have hoff := hd.minorIdx_eq hck j
  obtain ⟨hnm, hnF, hlpsA⟩ := hnames _ cA ct hJA hct
  have hks : kinds[b.ownOffset c + j]? = some (mutKsOf kinds (b.ownOffset c + j)) := by
    unfold mutKsOf
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenK]; exact hlt)]
    rfl
  have h4 := ctors4_getElem? hgd hJA hct hks
  obtain ⟨hksF, htgts⟩ := hkinds c j hck hj'
  obtain ⟨cvT, cvR, mI, rP, rules, hrep⟩ := hreps c hc
  obtain ⟨hfind, hlpsC, hD⟩ := hrep.ctors c j cA hc hj
  rw [hlpsC.symm.trans hlpsA] at hD
  have hfields : ConLeche.mutualRecFieldsOf (mutKsOf kinds (b.ownOffset c + j))
      = (ConLeche.recIdxOf (d.ksF c j)).map fun i => (i, d.tgts c j i) := by
    rw [mutualRecFieldsOf_eq, hksF]
    exact List.map_congr_left fun i _ => by rw [htgts i]
  show MutualCtorRead m ψ b.lps b.nP d.recTname d.nIdxAt (d.recMots (d.minorIdx c j))
    (d.recTgts (d.minorIdx c j)) (ctors4.getD (d.minorIdx c j) default)
    ((d.recCds ψ).getD (d.minorIdx c j) default)
  rw [d.recMots_at hc hj', d.recTgts_at hc hj', List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, d.recCds_getElem? ψ hc hj', d.cds_getElem? ψ hj, hoff, h4,
    ← hnm, ← hnF, hmem, hfields, Option.getD_some, Option.getD_some, ← hd.nP]
  refine blockCtorRead_of ψ hfind hlpsA hD (d.recTname_lt hc) rfl fun i hi => ?_
  have hilt : i < (d.ksF c j).length := (mem_recIdxOf.mp hi).1
  exact ⟨d.recTname_lt (hrep.tgtsLt c j i hc hj' hilt), rfl⟩

/-- **The block's recursor types read to the datum's Π-towers, graded
at the kernel's inferred sort** — `mutualRecData_of` at every member,
the readings the datum's. -/
theorem blockRecData_of (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    (hd : MutualDatumOf env₀ b fms ctorsA d) (hreps : BlockReps mp.base2 d)
    (hlenF : fms.length = b.k) (h0k : 0 < b.k)
    (h2 : b.ctors.all (fun c => c.member < b.k) = true)
    (hg : ConLeche.mutualCtorsGrouped b.ctors = true)
    (hlenA : ctorsA.length = b.ctors.length) (hlenK : kinds.length = ctorsA.length)
    (hnames : ∀ (J : Nat) (cA : ConstantVal × Nat) (ct : ConLeche.MutualCtor),
      ctorsA[J]? = some cA → b.ctors[J]? = some ct →
      cA.1.name = ct.cv.name ∧ cA.2 = ct.nF ∧ cA.1.levelParams = b.lps)
    (hgd : ConLeche.mutualGenData b fms ctorsA kinds = (formers4, ctors4))
    (hkinds : ∀ mm j, mm < b.k → j < (d.ctorsM mm).length →
      d.ksF mm j = kindsOf (mutKsOf kinds (b.ownOffset mm + j)) ∧
      ∀ i, d.tgts mm j i = tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i)
    (hstored : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      MemberStored mp.base2 b.lps b.nP f d.resSort (d.ppsM t))
    {streamRecs : Option (List (ConstantVal × List RecRule))} {cvRas : List ConstantVal}
    (hrectys : ConLeche.checkMutualRecTys (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env b
      formers4 ctors4 streamRecs b.k = .ok cvRas) :
    cvRas.length = d.k ∧
    ∀ t, t < d.k →
      MutualRecData mp.base2 (cvRas.getD t default) d.nP d.k d.nCtors (d.nIdxAt t) t b.elimLevel
        (d.blockRds mp.base2 b.elimLevel t) ∧
      ∃ u : Level, ∀ (ψ : Name → Nat) (ρ : Nat → V),
        interp V ρ (mkPisAV (d.blockRds mp.base2 b.elimLevel t ψ) (d.blockConc t))
          ∈ˢ (univ (u.eval ψ) : V) := by
  obtain ⟨hlenR, hallR⟩ := ConLeche.checkMutualRecTys_inv hrectys
  have hk4 : formers4.length = d.k := by rw [formers4_length hgd, hlenF, hd.k]
  have hn4 : ctors4.length = d.nCtors := by rw [ctors4_length hgd hlenK hlenA, hd.nCtors_eq h2 hlenA]
  have hFReads := blockFormerReadsM_of hd hgd hstored
  have hCReads := blockCtorReadsM_of hd hreps h2 hg hlenA hlenK hnames hgd hkinds
  have hmots : ∀ J, J < ctors4.length → d.recMots J < formers4.length := by
    intro J hJ
    rw [hn4] at hJ
    obtain ⟨c, j, cA, hc, hj, rfl⟩ := d.minor_index hJ
    rw [d.recMots_at hc (List.getElem?_eq_some_iff.mp hj).1, hk4]
    exact hc
  have hmemF : ∀ t, t < d.k → ∃ f, fms[t]? = some f ∧ d.memberName t = f.cvTa.name := by
    intro t ht
    have ht' : t < fms.length := by rw [hlenF, ← hd.k]; exact ht
    refine ⟨fms.getD t default, by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht']; rfl, ?_⟩
    show d.memberNames.getD t .anonymous = _
    rw [hd.memberNames, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem ht', List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht']
    rfl
  have hfT : ∀ q : Nat, ∃ ci : ConstantInfo,
      env.find? (d.recTname q) = some ci ∧ ci.toConstantVal.levelParams = b.lps := by
    intro q
    have hq : (if q < d.k then q else 0) < d.k := by
      split
      · assumption
      · rw [hd.k]; exact h0k
    obtain ⟨f, hf, hname⟩ := hmemF _ hq
    have hfind := (hstored _ f hf).find
    refine ⟨.indInfo f.cvTa {}, ?_, (hstored _ f hf).lps⟩
    show env.find? (d.memberName (if q < d.k then q else 0)) = _
    rw [hname]
    exact hfind
  refine ⟨by rw [hlenR, hd.k], fun t ht => ?_⟩
  obtain ⟨cvRa, hget, hrun⟩ := hallR t (by rw [← hd.k]; exact ht)
  have hcv : cvRas.getD t default = cvRa := by rw [List.getD_eq_getElem?_getD, hget]; rfl
  rw [hcv]
  have h := mutualRecData_of (V := V) hμ mp hrun (Lof := fun t ψ => mp.base2.acval (d.memberName t) ψ)
    (nIdxOf := d.nIdxAt) (ppsOf := fun t ψ => (d.ppsM t ψ).take b.nP)
    (ipsOf := fun t ψ => (d.ppsM t ψ).drop b.nP) (cds := fun ψ => d.recCds ψ)
    (mots := d.recMots) (tgts := d.recTgts) hFReads hCReads hmots hfT (by rw [hk4]; exact ht)
  rw [hk4, hn4, ← hd.nP] at h
  exact h

end Readings

/-! ## The leaf and the provisioned model -/

namespace BlockRepData

variable (d : BlockRepData V)

/-- **The block's rule equations** at the datum's lists (the leaf's
specification, `specEqs` at the readings built here). -/
@[expose] def recEqs (m : EnvModel V env) (elimL : Level) (ψ : Name → Nat) : List AnnotTerm :=
  d.specEqs m ψ elimL (d.recLs m ψ) d.recNIdxs (d.recPps ψ) (d.recIpss ψ) (d.recCds ψ)
    d.recMots d.recTgts

/-- **Member `t`'s recursor leaf**: the chosen tuple's `t`-th
projection (`blockLeafAV`) at the datum's readings, taken at the
level assignment RESTRICTED to the recursors' level parameters
(`restrictΨ rlps ψ`) — the leaf then depends on those parameters
alone by construction, and the readings agree at the two assignments
(`MutualRecData.params`). -/
@[expose] def recLeaf (m : EnvModel V env) (elimL : Level) (s : (Name → Nat) → Nat)
    (rlps : List Name) (t : Nat) (ψ : Name → Nat) : AnnotTerm :=
  blockLeafAV (s (restrictΨ rlps ψ)) d.k (fun t' => d.blockRds m elimL t' (restrictΨ rlps ψ))
    d.blockConc (d.recEqs m elimL (restrictΨ rlps ψ)) t

end BlockRepData

/-- **The state after the recursors' rule-less conses** — what the
store's stage (M4 s4b) consumes: the `k` recursors are consed at the
generated names with the leaves `recLeaf`, every other leaf is the
constructors' model's, the stored types' readings are at the
provisioned model, and the leaves are typed at their readings and
satisfy the block's rule equations (the ι rules, `blockRecs_iota`). -/
structure ProvisionedRecs {env₂ : Env} (mp₂ : EnvModelM V μ env₂) (b : MutualBlock)
    (fms : List MutualFormerA) (cvRas : List ConstantVal) (d : BlockRepData V)
    (s : (Name → Nat) → Nat)
    (mpP : EnvModelM V μ (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂)) : Prop where
  eta : ConLeche.EtaFamiliesClosed (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂)
  lenR : cvRas.length = d.k
  names : ∀ t, t < d.k → (cvRas.getD t default).name = b.recName t ∧
    (cvRas.getD t default).levelParams = b.rlps
  leaves : ∀ t, t < d.k → ∀ ψ : Name → Nat,
    mpP.base2.acval (cvRas.getD t default).name ψ = d.recLeaf mp₂.base2 b.elimLevel s b.rlps t ψ
  agree : ∀ nm : Name, (∀ t, t < d.k → nm ≠ (cvRas.getD t default).name) →
    mpP.base2.acval nm = mp₂.base2.acval nm
  recData : ∀ t, t < d.k → MutualRecData mpP.base2 (cvRas.getD t default) d.nP d.k d.nCtors
    (d.nIdxAt t) t b.elimLevel (d.blockRds mp₂.base2 b.elimLevel t)
  leafTyped : ∀ (ψ : Name → Nat) (ρ : Nat → V) (t : Nat), t < d.k →
    WellDenotedV V ρ (d.recLeaf mp₂.base2 b.elimLevel s b.rlps t ψ) ∧
    interp V ρ (d.recLeaf mp₂.base2 b.elimLevel s b.rlps t ψ)
      ∈ˢ interp V ρ (mkPisAV (d.blockRds mp₂.base2 b.elimLevel t ψ) (d.blockConc t))
  iota : ∀ (ψ : Name → Nat) (ρ : Nat → V),
    ∀ e ∈ d.recEqs mp₂.base2 b.elimLevel (restrictΨ b.rlps ψ),
      (pt : V) ∈ˢ interp V
        (consList ((List.range d.k).map fun t =>
          interp V ρ (d.recLeaf mp₂.base2 b.elimLevel s b.rlps t ψ)) ρ) e

omit [SetTheory V] in
theorem le_foldr_max : ∀ (l : List Nat) (x : Nat), x ∈ l → x ≤ l.foldr max 0
  | [], _, h => nomatch h
  | y :: l, x, h => by
    rw [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (le_foldr_max l x h) (Nat.le_max_right _ _)

section Provision

variable {F : Nat} {b : MutualBlock} {fms : List MutualFormerA} {f₀ : MutualFormerA}
  {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)}
  {kinds : List (List (RecFieldKind × Nat))} {formers4 : List MutualFormer}
  {ctors4 : List MutualCtor4} {d : BlockRepData V}

/-- **The recursors' provisioning stage at the datum** (M4 s4a): the
recursor types read to the datum's Π-towers (`blockRecData_of`), the
block's recursor tuple exists at every assignment (`blockRecsAt`),
its projections are closed (`blockRecAVI_below`), bit-valid
(`blockRecAVI_validV`, `blockEq_valid`) and stable under the
recursors' level parameters (`restrictΨ`), and the `k` rule-less
conses keep the model (`recsProvision`). -/
theorem mutualRecsProvision (hμ : μ.verifiedChecks = true) {env₂ : Env}
    (mp₂ : EnvModelM V μ env₂) (hE₂ : ConLeche.EtaFamiliesClosed env₂)
    (h0 : b.blockNames.Nodup)
    (h1 : (b.formers.all (fun f => f.1.levelParams == b.lps) &&
      b.ctors.all (fun c => c.cv.levelParams == b.lps)) = true)
    (h2 : b.ctors.all (fun c => c.member < b.k) = true)
    (h3 : ConLeche.mutualCtorsGrouped b.ctors = true)
    (hf₀ : fms[0]? = some f₀) (hlenF : fms.length = b.k) (hL : b.large = f₀.s.isNeverZero)
    {env₁ : Env} {isProp : Bool}
    (hctors : ConLeche.checkMutualCtors (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env₁ b fms
      isProp b.ctors = .ok (ctorsA, sortss))
    (hlenK : kinds.length = ctorsA.length)
    (hgd : ConLeche.mutualGenData b fms ctorsA kinds = (formers4, ctors4))
    {streamRecs : Option (List (ConstantVal × List RecRule))} {cvRas : List ConstantVal}
    (hrectys : ConLeche.checkMutualRecTys (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env₂ b
      formers4 ctors4 streamRecs b.k = .ok cvRas)
    (hd : MutualDatumOf env b fms ctorsA d) (hreps : BlockReps mp₂.base2 d)
    (htyped : ∀ ψ : Name → Nat, FormersTyped mp₂.base2 d ψ ∧ CtorsTyped mp₂.base2 d ψ)
    (hrecNames : ∀ t, t < b.k → env₂.find? (b.recName t) = none ∧
      ConLeche.reservedBasisNames.contains (b.recName t) = false ∧
      (b.recName t).isProjFnShape = false)
    (hstored : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      MemberStored mp₂.base2 b.lps b.nP f d.resSort (d.ppsM t))
    (hkinds : ∀ mm j, mm < b.k → j < (d.ctorsM mm).length →
      d.ksF mm j = kindsOf (mutKsOf kinds (b.ownOffset mm + j)) ∧
      ∀ i, d.tgts mm j i = tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i) :
    ∃ (s : (Name → Nat) → Nat)
      (mpP : EnvModelM V μ (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂)),
      ProvisionedRecs mp₂ b fms cvRas d s mpP := by
  obtain ⟨hlenA, hnames⟩ := ctorsA_names_of hctors h1
  have h0k : 0 < b.k := by rw [← hlenF]; exact (List.getElem?_eq_some_iff.mp hf₀).1
  obtain ⟨hlenR, hRD⟩ := blockRecData_of hμ mp₂ hd hreps hlenF h0k h2 h3 hlenA hlenK hnames hgd
    hkinds hstored hrectys
  -- **the sort**: the members' inferred sorts, joined
  have hu : ∀ t, ∃ u : Level, t < d.k → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (mkPisAV (d.blockRds mp₂.base2 b.elimLevel t ψ) (d.blockConc t))
        ∈ˢ (univ (u.eval ψ) : V) := by
    intro t
    by_cases ht : t < d.k
    · obtain ⟨u, hu⟩ := (hRD t ht).2
      exact ⟨u, fun _ => hu⟩
    · exact ⟨.zero, fun h => absurd h ht⟩
  let uOf : Nat → Level := fun t => Classical.choose (hu t)
  have huOf : ∀ t, t < d.k → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (mkPisAV (d.blockRds mp₂.base2 b.elimLevel t ψ) (d.blockConc t))
        ∈ˢ (univ ((uOf t).eval ψ) : V) := fun t => Classical.choose_spec (hu t)
  let sOf : (Name → Nat) → Nat := fun ψ => ((List.range d.k).map fun t => (uOf t).eval ψ).foldr max 0
  have hsOf : ∀ t, t < d.k → ∀ ψ : Name → Nat, (uOf t).eval ψ ≤ sOf ψ := fun t ht ψ =>
    le_foldr_max _ _ (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩)
  refine ⟨sOf, ?_⟩
  -- **the readings** at every assignment
  have hR : ∀ ψ : Name → Nat, BlockReadings mp₂.base2 d ψ b.elimLevel (d.recLs mp₂.base2 ψ)
      d.recNIdxs (d.recPps ψ) (d.recIpss ψ) (d.recCds ψ) d.recMots d.recTgts :=
    fun ψ => d.blockReadings_of mp₂.base2 ψ b.elimLevel (fun mm hmm => (hRD mm hmm).1.below ψ)
  have hwℓ : ∀ ψ : Name → Nat, d.w ψ = 0 → b.elimLevel.eval ψ = 0 := by
    intro ψ hw
    have hw' : f₀.s.eval ψ = 0 := by
      have : d.w ψ = (fms.getD 0 default).s.eval ψ := by
        show d.resSort.eval ψ = _
        rw [hd.resSort]
      rw [this, List.getD_eq_getElem?_getD, hf₀] at hw
      exact hw
    exact elimLevel_zero_of_w_zero hL ψ hw'
  have hT : ∀ (ψ : Name → Nat) (ρ : Nat → V) (mm : Nat), mm < d.k →
      interp V ρ (mkPisAV (d.blockRds mp₂.base2 b.elimLevel mm ψ) (d.blockConc mm))
        ∈ˢ (univ (sOf ψ) : V) ∧
      WellDenoted V ρ (mkPisAV (d.blockRds mp₂.base2 b.elimLevel mm ψ) (d.blockConc mm)) :=
    fun ψ ρ mm hmm => ⟨univ_mono (hsOf mm hmm ψ) _ (huOf mm hmm ψ ρ),
      ((hRD mm hmm).1.okTy ψ ρ).1⟩
  -- **the tuple** at the restricted assignment
  have hleafAt : ∀ (ψ : Name → Nat) (ρ : Nat → V), ∃ a : Nat → V,
      (∀ mm, mm < d.k →
        a mm ∈ˢ interp V ρ (mkPisAV (d.blockRds mp₂.base2 b.elimLevel mm (restrictΨ b.rlps ψ))
          (d.blockConc mm)) ∧
        interp V ρ (d.recLeaf mp₂.base2 b.elimLevel sOf b.rlps mm ψ) = a mm ∧
        WellDenoted V ρ (d.recLeaf mp₂.base2 b.elimLevel sOf b.rlps mm ψ)) ∧
      ∀ e ∈ d.recEqs mp₂.base2 b.elimLevel (restrictΨ b.rlps ψ),
        (pt : V) ∈ˢ interp V (consList ((List.range d.k).map a) ρ) e :=
    fun ψ ρ => hreps.blockRecsAt (fun ψ => (htyped ψ).1) (fun ψ => (htyped ψ).2) hwℓ hR
      (s := sOf) (fun ψ ρ mm hmm => hT ψ ρ mm hmm) (restrictΨ b.rlps ψ) ρ
  -- **the run facts** about the generated recursors
  obtain ⟨hlenR', hallR⟩ := ConLeche.checkMutualRecTys_inv hrectys
  have hshape : ∀ t, t < d.k →
      (cvRas.getD t default).name = b.recName t ∧
      (cvRas.getD t default).levelParams = b.rlps ∧
      (cvRas.getD t default).type.hasFvar = false ∧
      (cvRas.getD t default).type.allLevelParamsDefined b.rlps = true ∧
      (cvRas.getD t default).type.looseBVarsBounded 0 = true ∧
      (cvRas.getD t default).type.constsResolve env₂ = true := by
    intro t ht
    obtain ⟨cvRa, hget, hrun⟩ := hallR t (by rw [← hd.k]; exact ht)
    obtain ⟨recTy, sty, u, -, hlp, hres, hbv, hfv, -, -, -, rfl⟩ :=
      ConLeche.checkMutualRecTy_shape hrun
    rw [List.getD_eq_getElem?_getD, hget]
    exact ⟨rfl, rfl, hfv, hlp, hbv, hres⟩
  have hnd : (cvRas.map (·.name)).Nodup := by
    have hmapEq : cvRas.map (·.name) = (List.range b.k).map b.recName := by
      refine List.ext_getElem? fun t => ?_
      rw [List.getElem?_map, List.getElem?_map]
      by_cases ht : t < b.k
      · have htl : t < cvRas.length := by rw [hlenR, hd.k]; exact ht
        rw [List.getElem?_range ht, List.getElem?_eq_getElem htl]
        have := (hshape t (by rw [hd.k]; exact ht)).1
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htl] at this
        simp only [Option.map_some, Option.some.injEq]
        exact this
      · rw [List.getElem?_eq_none (by rw [hlenR, hd.k]; omega),
          List.getElem?_eq_none (by rw [List.length_range]; omega)]
        rfl
    rw [hmapEq]
    have h0' := h0
    unfold ConLeche.MutualBlock.blockNames at h0'
    exact (List.nodup_append.mp h0').2.1
  -- **the leaf's laws**
  have hAparams : ∀ t, t < d.k → ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ q ∈ (cvRas.getD t default).levelParams, ψ₁ q = ψ₂ q) →
      d.recLeaf mp₂.base2 b.elimLevel sOf b.rlps t ψ₁
        = d.recLeaf mp₂.base2 b.elimLevel sOf b.rlps t ψ₂ := by
    intro t ht ψ₁ ψ₂ hφ
    rw [(hshape t ht).2.1] at hφ
    unfold BlockRepData.recLeaf
    rw [restrictΨ_congr hφ]
  have hAcl : ∀ t, t < d.k → ∀ ψ : Name → Nat,
      Term.bvarsBelow 0 (d.recLeaf mp₂.base2 b.elimLevel sOf b.rlps t ψ).erase := by
    intro t ht ψ
    unfold BlockRepData.recLeaf blockLeafAV
    refine blockRecAVI_below (K := 0) (fun mm hmm => ?_) (fun e he => ?_) t
    · exact blockRecTy_below ((hRD mm hmm).1.below _) ((hRD mm hmm).1.len _)
    · rw [Nat.zero_add]
      exact hreps.specEqs_below (hR _) e he
  have hleaf : ∀ t, t < d.k → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      WellDenotedV V ρ (d.recLeaf mp₂.base2 b.elimLevel sOf b.rlps t ψ) ∧
      interp V ρ (d.recLeaf mp₂.base2 b.elimLevel sOf b.rlps t ψ)
        ∈ˢ interp V ρ (mkPisAV (d.blockRds mp₂.base2 b.elimLevel t ψ) (d.blockConc t)) := by
    intro t ht ψ ρ
    obtain ⟨a, ha, -⟩ := hleafAt ψ ρ
    obtain ⟨hmem, hval, hwd⟩ := ha t ht
    have hrds : d.blockRds mp₂.base2 b.elimLevel t ψ
        = d.blockRds mp₂.base2 b.elimLevel t (restrictΨ b.rlps ψ) :=
      (hRD t ht).1.params ψ _ fun q hq =>
        (restrictΨ_agree b.rlps ψ q (by rw [← (hshape t ht).2.1]; exact hq)).symm
    refine ⟨⟨hwd, ?_⟩, by rw [hrds, hval]; exact hmem⟩
    unfold BlockRepData.recLeaf blockLeafAV
    refine blockRecAVI_validV
      (fun mm hmm => ⟨(hT _ ρ mm hmm).1, (hT _ ρ mm hmm).2, ((hRD mm hmm).1.okTy _ ρ).2⟩)
      (fun rs hlen hrs e he => ?_) t
    obtain ⟨c, j, cA, hc, hj, rfl⟩ := d.mem_specEqs he
    exact ⟨specEqAV_univZero _ _ _ _,
      hreps.blockEq_wd (htyped _).1 (htyped _).2 (hR _)
        (fun mm hmm ρ => ((hRD mm hmm).1.okTy _ ρ).1) ρ hlen hrs hc hj,
      hreps.blockEq_valid (htyped _).1 (htyped _).2 (fun n ρ => mp₂.acval_validV n _ ρ) (hR _)
        (fun mm hmm ρ => (hRD mm hmm).1.okTy _ ρ) ρ hlen hrs hc hj⟩
  -- **the conses**
  obtain ⟨mpP, hEP, -, hRDP, hleafP, hagP⟩ :=
    recsProvision (k := d.k) (nP := d.nP) (n := d.nCtors) (nIdxOf := d.nIdxAt)
      (elimL := b.elimLevel) (rds := d.blockRds mp₂.base2 b.elimLevel)
      (A := d.recLeaf mp₂.base2 b.elimLevel sOf b.rlps) (b := b) (fms := fms) mp₂ hlenR hleaf hAcl
      hAparams
      (fun t ht => by rw [(hshape t ht).1]; exact (hrecNames t (by rw [← hd.k]; exact ht)).2.1)
      (fun t ht => by rw [(hshape t ht).1]; exact (hrecNames t (by rw [← hd.k]; exact ht)).2.2)
      (fun t ht => ⟨(hshape t ht).2.2.1,
        by rw [(hshape t ht).2.1]; exact (hshape t ht).2.2.2.1, (hshape t ht).2.2.2.2.1⟩)
      hnd (fun t ht => by rw [(hshape t ht).1]; exact (hrecNames t (by rw [← hd.k]; exact ht)).1)
      (fun t ht => (hshape t ht).2.2.2.2.2) hE₂ (fun t ht => (hRD t ht).1)
  refine ⟨mpP, hEP, hlenR, fun t ht => ⟨(hshape t ht).1, (hshape t ht).2.1⟩, hleafP, hagP, hRDP,
    fun ψ ρ t ht => hleaf t ht ψ ρ, fun ψ ρ e he => ?_⟩
  obtain ⟨a, ha, hi⟩ := hleafAt ψ ρ
  have hmap : (List.range d.k).map a
      = (List.range d.k).map fun t => interp V ρ (d.recLeaf mp₂.base2 b.elimLevel sOf b.rlps t ψ) :=
    List.map_congr_left fun t ht => ((ha t (List.mem_range.mp ht)).2.1).symm
  rw [← hmap]
  exact hi e he

end Provision

/-! ## The store's stage, named -/

/-- **The store keeps the model and the datum** — the named fact of
`mutualRecsModeled_of` (M4 s4b): at the provisioned model
(`ProvisionedRecs`: the `k` recursors consed rule-less with the
chosen tuple's projections as leaves, typed and satisfying the rule
equations), the group store — the same `k` names with their rules, a
swap — cons a model of the recursors' environment at which the datum
still holds, every other leaf the constructors' model's.  The run
facts are `MutualRecsModeled`'s, verbatim.  Consumer:
`mutualRecsModeled_of`. -/
@[expose] def MutualRecsStored (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat) : Prop :=
  μ.verifiedChecks = true →
  ∀ {env : Env} (mp : EnvModelM V μ env), ConLeche.EtaFamiliesClosed env →
  ∀ (b : MutualBlock) (streamRecs : Option (List (ConstantVal × List RecRule)))
    (fms : List MutualFormerA) (f₀ : MutualFormerA) (tq₀ : List Expr × Expr)
    (ctorsA : List (ConstantVal × Nat)) (sortss : List (List Level))
    (kinds : List (List (RecFieldKind × Nat))) (formers4 : List ConLeche.MutualFormer)
    (ctors4 : List ConLeche.MutualCtor4) (cvRas : List ConstantVal)
    (rulesOf : List (List (ConLeche.MutualCtor × Expr))),
    b.blockNames.Nodup →
    (b.formers.all (fun f => f.1.levelParams == b.lps) &&
      b.ctors.all (fun c => c.cv.levelParams == b.lps)) = true →
    b.ctors.all (fun c => c.member < b.k) = true →
    ConLeche.mutualCtorsGrouped b.ctors = true →
    ConLeche.mutualFormers (m := ConLeche.CheckM) (fueledOps μ F) b.nP b.formers env
      = .ok (ConLeche.consMutualFormers fms env, fms) →
    fms[0]? = some f₀ →
    ConLeche.openPisAtFvars b.nP f₀.cvTa.type 0 = some tq₀ →
    ConLeche.mutualCrossChecks (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consMutualFormers fms env) b.nP f₀ (tq₀.1.map Expr.fvarTypeD) fms = .ok () →
    b.large = f₀.s.isNeverZero →
    ConLeche.checkMutualCtors (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consMutualFormers fms env) b fms (Level.isEquiv f₀.s .zero == some true) b.ctors
      = .ok (ctorsA, sortss) →
    ConLeche.classifyMutualKinds (m := ConLeche.CheckM) b.members3 b.lps b.nP ctorsA
      = .ok kinds →
    ConLeche.mutualFieldsOk env b.members3 b.lps b.nP ctorsA kinds = true →
    ConLeche.mutualGenData b fms ctorsA kinds = (formers4, ctors4) →
    ConLeche.checkMutualRecTys (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env)) b formers4 ctors4
      streamRecs b.k = .ok cvRas →
    ConLeche.checkMutualAllRules (m := ConLeche.CheckM)
      (ConLeche.provisionMutualRecs b fms cvRas.zipIdx
        (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env)))
      b formers4 ctors4 streamRecs b.k = .ok rulesOf →
    ∀ (mp₂ : EnvModelM V μ (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env))),
      ConLeche.EtaFamiliesClosed
        (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env)) →
      (∀ n, n ∉ b.blockNames → ∀ ψ : Name → Nat, mp₂.base2.acval n ψ = mp.base2.acval n ψ) →
      ∀ d : BlockRepData V, MutualDatumOf env b fms ctorsA d → BlockReps mp₂.base2 d →
        (∀ ψ : Name → Nat, FormersTyped mp₂.base2 d ψ ∧ CtorsTyped mp₂.base2 d ψ) →
        (∀ t, t < b.k →
          (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env)).find?
            (b.recName t) = none ∧
          ConLeche.reservedBasisNames.contains (b.recName t) = false ∧
          (b.recName t).isProjFnShape = false) →
        (∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
          MemberStored mp₂.base2 b.lps b.nP f d.resSort (d.ppsM t)) →
        (∀ mm j, mm < b.k → j < (d.ctorsM mm).length →
          d.ksF mm j = kindsOf (mutKsOf kinds (b.ownOffset mm + j)) ∧
          ∀ i, d.tgts mm j i = tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i) →
        ∀ (s : (Name → Nat) → Nat)
          (mpP : EnvModelM V μ (ConLeche.provisionMutualRecs b fms cvRas.zipIdx
            (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env)))),
          ProvisionedRecs mp₂ b fms cvRas d s mpP →
          ∃ mp₃ : EnvModelM V μ
              (ConLeche.storeMutualRecs
                (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env)) b fms
                rulesOf cvRas.zipIdx
                (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env))),
            (∀ n, n ∉ b.blockNames → ∀ ψ : Name → Nat, mp₃.base2.acval n ψ = mp₂.base2.acval n ψ) ∧
            BlockReps mp₃.base2 d ∧
            (∀ ψ : Name → Nat, FormersTyped mp₃.base2 d ψ ∧ CtorsTyped mp₃.base2 d ψ) ∧
            ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
              MemberStored mp₃.base2 b.lps b.nP f d.resSort (d.ppsM t)

/-- **The recursors' stage, modulo its store**: the provisioning half
(`mutualRecsProvision`) and the named store half. -/
theorem mutualRecsModeled_of {F : Nat} (hst : MutualRecsStored V μ F) :
    MutualRecsModeled V μ F := by
  intro hμ env mp hE b streamRecs fms f₀ tq₀ ctorsA sortss kinds formers4 ctors4 cvRas rulesOf
    h0 h1 h2 h3 hformers hf₀ htq₀ hcross hL hctors hkindsC hfo hgd hrectys hrules mp₂ hE₂ hagree
    d hd hreps htyped hrecNames hstored hkinds
  obtain ⟨hchecks, -⟩ := ConLeche.mutualFormers_inv hformers
  have hlenF : fms.length = b.k := (mutualFormerChecks_pos hchecks).1
  obtain ⟨-, -, -, hlenK⟩ := ConLeche.classifyMutualKinds_inv hkindsC
  obtain ⟨s, mpP, hP⟩ := mutualRecsProvision hμ mp₂ hE₂ h0 h1 h2 h3 hf₀ hlenF hL hctors hlenK hgd
    hrectys hd hreps htyped hrecNames hstored hkinds
  exact hst hμ mp hE b streamRecs fms f₀ tq₀ ctorsA sortss kinds formers4 ctors4 cvRas rulesOf
    h0 h1 h2 h3 hformers hf₀ htq₀ hcross hL hctors hkindsC hfo hgd hrectys hrules mp₂ hE₂ hagree
    d hd hreps htyped hrecNames hstored hkinds s mpP hP

/-- **`declBlock` at the store's fact**: the model survives a mutual
block, given the store's stage (`MutualRecsStored`) and the tables'
(`MutualTablesModeled`). -/
theorem declBlock_of_stored (hμ : μ.verifiedChecks = true) {F : Nat} {envOut : Env}
    {p : ConLeche.MutualParts} (mp : EnvModelM V μ env) (hE : ConLeche.EtaFamiliesClosed env)
    (hpinOk : ConLeche.mutualRecPinOk p = true)
    (hst : MutualRecsStored V μ F) (htables : MutualTablesModeled V μ F)
    (h : ConLeche.Semantics.DeclMutualRun μ F env p envOut) :
    Nonempty (EnvModelM V μ envOut) :=
  declBlock_of_recs hμ mp hE hpinOk (mutualRecsModeled_of hst) htables h

end ConLeche.Model

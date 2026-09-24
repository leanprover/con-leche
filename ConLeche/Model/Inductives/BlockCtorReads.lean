module

public import ConLeche.Model.Inductives.BlockStageCtors
import ConLeche.Model.Inductives.BlockPosRun
import ConLeche.Model.Annot.CanonCrest
import ConLeche.Model.Inductives.BlockHoleRead
import ConLeche.Model.Inductives.FixAssemblyKit
import ConLeche.Verify.Inductives.NestScope

public section

/-!
# M2 at the uniform install: the constructors' canonical readings (lane CONTSEM)

`LfpCtorReads` (`Model/Annot/EnvModelM.lean`) for a uniform block's
datum `d.toLfp`, at the constructors' environment: the reading theorem
`blockCtor_walkRead` at the CANONICAL abstraction (parameters the
variables `0 ..< nP`, member `m` the variable `nP + m`, all annotated
`Sort 0`), which the theorem admits because it reads the walk's term up
to erasure; the canonical instantiation exists because the concrete one
does (the stored type opens at its parameters, `BlockCtorDataI.opens`);
M2′ is the positivity stage's check (`nestNoMemberConst`), which is
blind to the holes' annotations (`nestOcc_nestAbstract_blind`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape BlockParts instPisWith
  nestAbstract)

universe w

variable {V : Type w} [SetTheory V]

omit [SetTheory V] in
/-- **M2′ at the canonical holes, from the positivity stage's run**: the
stage checked every constructor's member-abstracted type for a member
constant (`nestNoMemberConst`) at its own holes; the check does not see
the holes' annotations. -/
theorem canonOcc_of_positivity {ops : ConLeche.CheckerOps ConLeche.CheckM} {env₁ : Env}
    {find? : Name → Option ConstantInfo} {consts : List ConstantInfo} {p : BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    (hrun : ConLeche.checkBlockPositivity ops env₁ find? consts p cvTas ctorsAs = .ok ())
    {d : BlockData V} {lps : List Name}
    (hnames : p.memberNames = d.memberNames) (hlps : p.lps = lps)
    (hk : d.k = d.memberNames.length)
    (hctorsAs : ∀ c, c < d.k → ctorsAs[c]? = some (d.ctorsM c)) :
    ∀ c, c < d.k → ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      (canonAbs d.memberNames lps d.nP d.k cA.1.type).nestOcc d.memberNames 0 0 = false := by
  obtain ⟨cvTa0, fvsP, rest, holes, -, -, hholes, hall⟩ := ConLeche.checkBlockPositivity_inv hrun
  intro c hc j cA hcj
  obtain ⟨-, -, -, -, hocc⟩ := hall c (d.ctorsM c) (hctorsAs c hc) j cA hcj
  have hn : (p.nestCtx fvsP find? consts).names = d.memberNames := hnames
  rw [hn] at hocc
  rw [← hocc]
  refine nestOcc_nestAbstract_blind (by rw [hn]; rfl) (by rw [← hlps]; rfl) ?_
    (fun h hm => ?_) (fun h hm => ?_) _ _
  · rw [canonHoles_length, ConLeche.nestHoles_length hholes, hn, hk]
  · obtain ⟨mm, -, rfl⟩ := mem_canonHoles hm
    exact ⟨_, _, rfl⟩
  · obtain ⟨i, cv, caps, -, rfl⟩ := ConLeche.nestHoles_mem hholes h hm
    exact ⟨_, _, rfl⟩

/-- **M2 at a uniform block** (see the module docstring). -/
theorem blockCtorReads_of {env : Env} {m : EnvModel V env} {d : BlockData V} {lps : List Name}
    {cvTas : List ConstantVal} {p₁ : BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm}
    (hN : BlockNamesOk (V := V) d cvTas) (hcore : BlockCtorsCore m d lps cvTas p₁ isRec A d.k)
    (hk : d.k = d.memberNames.length) (hnd : d.memberNames.Nodup)
    (hfresh : ∀ n ∈ d.memberNames, d.env₀.find? n = none)
    (hlpsT : ∀ (c : Nat) (cvTb : ConstantVal), c < d.k → cvTas[c]? = some cvTb →
      cvTb.levelParams = lps)
    (hclosed : ∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      cA.1.type.hasFvar = false)
    (hocc : ∀ c, c < d.k → ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      (canonAbs d.memberNames lps d.nP d.k cA.1.type).nestOcc d.memberNames 0 0 = false) :
    LfpCtorReads m.acval env d.toLfp := by
  refine ⟨hk.symm, fun c hc j hj => ?_⟩
  have hc' : c < d.k := hc
  have hcj : (d.ctorsM c)[j]? = some (d.ctorsM c)[j] := List.getElem?_eq_getElem hj
  generalize hcA : (d.ctorsM c)[j] = cA at hcj
  have hname : d.toLfp.ctorName c j = cA.1.name := by
    show ((d.ctorsM c).getD j default).1.name = _
    rw [List.getD_eq_getElem?_getD, hcj]; rfl
  obtain ⟨hfind, hlpsC, -⟩ := hcore.2.2.2 c hc' j cA hcj
  have hD₀ := (hcore.2.2.1 c j cA hcj).2.2
  have hCf := hclosed c j cA hcj
  -- the canonical abstraction
  let ctx := canonCtx d.memberNames lps d.nP
  have hh : ∀ h ∈ canonHoles d.nP d.k, ∃ i ty, h = .fvar i ty := by
    intro h hm
    obtain ⟨mm, -, rfl⟩ := mem_canonHoles hm
    exact ⟨_, _, rfl⟩
  have hholes : ∀ t, t < d.k → ∃ ty, (canonHoles d.nP d.k)[t]? = some (.fvar (d.nP + t) ty) :=
    fun t ht => ⟨_, canonHoles_getElem? ht⟩
  -- the canonical instantiation exists: the concrete one does
  obtain ⟨crest, hopP, -⟩ := hD₀.opens
  have hA₂ := nestAbstract_instPisWith (ctx := ctx) hh (instPisWith_of_openPis d.nP hopP)
  have hpar' : Expr.ErasedEqL ((d.fvsPF c j).map (nestAbstract ctx (canonHoles d.nP d.k)))
      (canonParams d.nP) := by
    refine erasedEqL_of_fvarIdx _ _ 0 (fun i x hx => ?_) (fun i x hx => ?_)
      (by rw [List.length_map, hD₀.pLen, canonParams_length])
    · rw [List.getElem?_map] at hx
      rcases hq : (d.fvsPF c j)[i]? with _ | y
      · rw [hq] at hx; exact nomatch hx
      · rw [hq] at hx
        obtain ⟨ty, rfl⟩ := hD₀.pIdx i y hq
        simp only [Option.map_some, Option.some.injEq] at hx
        exact ⟨_, by rw [← hx, Nat.zero_add]; rfl⟩
    · exact ⟨_, by rw [canonParams_getElem? hx, Nat.zero_add]⟩
  obtain ⟨Acr, hAcr, -⟩ := instPisWith_erasedEq hpar' (Expr.ErasedEq.rfl _) hA₂
  have hpar : Expr.ErasedEqL ctx.params (d.fvsPF c j) := by
    refine erasedEqL_of_fvarIdx _ _ 0 (fun i x hx => ?_) (fun i x hx => ?_)
      (by rw [show ctx.params = canonParams d.nP from rfl, canonParams_length, hD₀.pLen])
    · exact ⟨_, by rw [canonParams_getElem? hx, Nat.zero_add]⟩
    · obtain ⟨ty, h⟩ := hD₀.pIdx i x hx
      exact ⟨ty, by rw [h, Nat.zero_add]⟩
  have htgt : ∀ l, l < cA.2 → d.tgts c j l < d.k := fun l _ => by
    rw [← hN.2.2.2]; exact hN.2.1 c j l
  -- the parameter telescope's length (member 0's former)
  have hk0 : 0 < d.k := Nat.lt_of_le_of_lt (Nat.zero_le c) hc'
  obtain ⟨cvTa0, hcv0⟩ : ∃ cvTa0, cvTas[0]? = some cvTa0 :=
    ⟨_, List.getElem?_eq_getElem (by rw [hN.2.2.2]; exact hk0)⟩
  obtain ⟨-, -, -, hFD0⟩ := hcore.1 0 cvTa0 hcv0
  refine ⟨cA.1, d.nP, cA.2, by rw [hname]; exact hfind, hCf, fun mm hmm => ?_,
    by rw [hlpsC]; exact hocc c hc' j cA hcj, Acr, by rw [hlpsC]; exact hAcr, fun ψ => ?_⟩
  · -- the members' formers, at the constructor's levels
    obtain ⟨cvTb, hcvb⟩ : ∃ cvTb, cvTas[mm]? = some cvTb :=
      ⟨_, List.getElem?_eq_getElem (by rw [hN.2.2.2]; exact hmm)⟩
    obtain ⟨hfb, -, -, -⟩ := hcore.1 mm cvTb hcvb
    refine ⟨cvTb, ConLeche.blockCapsAt p₁ mm isRec, ?_, by rw [hlpsC, hlpsT mm cvTb hmm hcvb]⟩
    show env.find? (d.memberNames.getD mm .anonymous) = _
    rw [show d.memberNames.getD mm .anonymous = cvTb.name from hN.1 mm cvTb hcvb]
    exact hfb
  · obtain ⟨ab, hca, hab⟩ := blockCtor_walkRead (m := m) hcj hD₀ (ctx := ctx) rfl rfl rfl hk hpar
      hh hholes hnd hfresh htgt hc' (Expr.WScoped.of_not_hasFvar hCf) ψ hAcr
    have hlenP0 : (d.ppsM 0 ψ).length = d.nP + d.nIdxAt 0 := hFD0.len ψ
    have hlenParams : (d.params ψ).length = d.nP := by
      simp only [BlockData.params, List.length_map, List.length_take, hlenP0]; omega
    have habLen : (d.absF ψ c j).length = cA.2 := by
      rw [BlockData.absF, List.length_map, List.length_range]
      have hFssD : (d.Fss c ψ).getD j [] = ((d.dsF c j ψ).drop d.nP).map (·.2.2) :=
        fssOfR_fixCtorDataList_getD hcj
      rw [hFssD, List.length_map, List.length_drop, hD₀.len ψ]
      omega
    exact ⟨hlenParams, habLen, ab, hca, hab⟩

end ConLeche.Model

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
datum `d.toLfp`, at the constructors' environment: the reading fact the
constructors' stage carries (`BlockAbsRead`: the CANONICAL abstraction —
parameters the variables `0 ..< nP`, member `m` the variable `nP + m`,
all annotated `Sort 0` — reads as the fields with holes); M2′ is the
positivity stage's check (`nestNoMemberConst`), which is blind to the
holes' annotations (`canonOcc_of_positivity`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape BlockParts instPisWith
  nestAbstract)

universe w

variable {V : Type w} [SetTheory V]

/-- **M2 at a uniform block** (see the module docstring). -/
theorem blockCtorReads_of {env : Env} {m : EnvModel V env} {d : BlockData V} {lps : List Name}
    {cvTas : List ConstantVal} {p₁ : BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm}
    (hN : BlockNamesOk (V := V) d cvTas) (hcore : BlockCtorsCore m d lps cvTas p₁ isRec A d.k)
    (hk : d.k = d.memberNames.length)
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
  obtain ⟨Acr, hAcr, hr⟩ := (hcore.2.2.1 c j cA hcj).2.2.2
  have hCf := hclosed c j cA hcj
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
  · obtain ⟨ab, hca, hlab, hab⟩ := hr ψ
    have hlenP0 : (d.ppsM 0 ψ).length = d.nP + d.nIdxAt 0 := hFD0.len ψ
    have hlenParams : (d.params ψ).length = d.nP := by
      simp only [BlockData.params, List.length_map, List.length_take, hlenP0]; omega
    have habLen : (d.absF ψ c j).length = cA.2 := by
      rw [← hab, List.length_map, hlab]
    exact ⟨hlenParams, habLen, ab, hca, hab⟩

end ConLeche.Model

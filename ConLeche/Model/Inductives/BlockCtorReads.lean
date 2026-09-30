module

public import ConLeche.Model.Inductives.BlockStageCtors
import ConLeche.Model.Inductives.BlockHoleRead
import ConLeche.Model.Annot.BitInst
import ConLeche.Verify.EnvWF
import ConLeche.Model.Annot.CanonCrest
import ConLeche.Model.Annot.BitRename

public section

/-!
# M2 at the uniform install: the constructors' canonical readings

`LfpCtorReads` (`Model/Annot/EnvModelM.lean`) for a uniform block's
datum `d.toLfp`, at the constructors' environment: the reading fact the
constructors' stage carries (`BlockAbsRead`: the CANONICAL abstraction —
parameters the variables `0 ..< nP`, each member's whole application the
variable `nP + m`, all annotated `Sort 0` — reads as the fields with
holes); that it names no member follows from official's
uniform-occurrence check (`nestUniform`, `canonOcc_of_positivity`); each
hole's type is its member's former at the canonical parameters, read as
the member's index tower (`formerHoleTy_read`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape BlockParts instPisWith)

universe w

variable {V : Type w} [SetTheory V]

/-- **A former's hole type, read**: a closed type reading as a Π-tower
whose first `n` binders it binds syntactically, instantiated at the
canonical parameters, reads at depth `n` as the rest of the tower. -/
theorem formerHoleTy_read {env : Env} {acval : Name → (Name → Nat) → AnnotTerm}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    {ψ : Name → Nat} {T : Expr} {n : Nat} (hcl : T.hasFvar = false)
    (hstrip : (T.stripPis n).isSome = true) {ab : List (Nat × Nat × AnnotTerm)} {B : AnnotTerm}
    (hn : n ≤ ab.length) (hr : denoteMeta acval env ψ 0 T = some (mkPisAV ab B)) :
    ∃ ty, instPisWith (canonParams n) T = some ty ∧ Expr.WScoped n ty ∧
      ∀ d, n ≤ d → denoteMeta acval env ψ d ty = some ((mkPisAV (ab.drop n) B).liftN (d - n) 0) := by
  obtain ⟨fvs, o, hop⟩ := openPisAtFvars_of_stripPis_isSome n 0 hstrip
  have hio := instPisWith_of_openPis n hop
  have hEq : Expr.ErasedEqL fvs (canonParams n) :=
    erasedEqL_of_fvarIdx _ _ 0 (fun i x hx => ConLeche.openPisAtFvars_index _ _ _ hop i x hx)
      (fun i x hx => ⟨.sort .zero, by rw [canonParams_getElem? hx, Nat.zero_add]⟩)
      (by rw [openPisAtFvars_length _ hop, canonParams_length])
  obtain ⟨A, hA, hoA⟩ := instPisWith_erasedEq hEq (Expr.ErasedEq.rfl _) hio
  obtain ⟨pps, b, hst, hb, -, -⟩ := denoteMeta_openPis n hop hr
  rw [stripPisAV_mkPisAV_take _ _ _ hn] at hst
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hst)
  have hAw : Expr.WScoped n A := by
    refine ConLeche.wscoped_instPisWith (fun x hx => ?_) (Expr.WScoped.of_not_hasFvar hcl) hA
    obtain ⟨i, hi'⟩ := List.getElem?_of_mem hx
    have hlt : i < n := by
      have := (List.getElem?_eq_some_iff.mp hi').1; rwa [canonParams_length] at this
    rw [canonParams_getElem? hi']
    simp [Expr.WScoped, hlt]
  have hAr : denoteMeta acval env ψ n A = some (mkPisAV (ab.drop n) B) := by
    rw [← denoteMeta_erasedEq hoA]; simpa using hb
  refine ⟨A, hA, hAw, fun d hd => ?_⟩
  rw [denoteMeta_lift hacl hAw d hd, hAr]
  rfl

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
      ∃ A, ConLeche.nestCanonCrest d.memberNames (lps.map .param) d.nP cA.1.type = some A ∧
        A.nestOcc d.memberNames 0 0 = false)
    -- the constructors' parameter binders are satisfied where the block's are (the
    -- constructors' frames)
    (hpars : ∀ c, c < d.k → ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      ∀ (ψ : Name → Nat) (ρ : Nat → V), Sat V (d.params ψ).reverse ρ →
        Sat V (((d.dsF c j ψ).take d.nP).map (·.2.2)).reverse ρ) :
    LfpCtorReads m.acval env d.toLfp := by
  refine ⟨hk.symm, fun c hc j hj => ?_⟩
  have hc' : c < d.k := hc
  have hcj : (d.ctorsM c)[j]? = some (d.ctorsM c)[j] := List.getElem?_eq_getElem hj
  generalize hcA : (d.ctorsM c)[j] = cA at hcj
  have hname : d.toLfp.ctorName c j = cA.1.name := by
    show ((d.ctorsM c).getD j default).1.name = _
    rw [List.getD_eq_getElem?_getD, hcj]; rfl
  obtain ⟨hfind, hlpsC, -⟩ := hcore.2.2.2 c hc' j cA hcj
  obtain ⟨-, Acr, hAcr, hr⟩ := (hcore.2.2.1 c j cA hcj).2.2.2
  have hCf := hclosed c j cA hcj
  -- the parameter telescope's length (member 0's former)
  have hk0 : 0 < d.k := Nat.lt_of_le_of_lt (Nat.zero_le c) hc'
  obtain ⟨cvTa0, hcv0⟩ : ∃ cvTa0, cvTas[0]? = some cvTa0 :=
    ⟨_, List.getElem?_eq_getElem (by rw [hN.2.2]; exact hk0)⟩
  obtain ⟨-, -, -, hFD0⟩ := hcore.1 0 cvTa0 hcv0
  have hcd := (hcore.2.2.1 c j cA hcj).2.2.1
  obtain ⟨A', hA', hocc'⟩ := hocc c hc' j cA hcj
  rw [hAcr] at hA'
  obtain rfl := Option.some.inj hA'
  refine ⟨cA.1, d.nP, cA.2, by rw [hname]; exact hfind, hCf, fun mm hmm => ?_,
    fun ψ dsC bodyC hrd' hle ρ hsat => ?_,
    Acr, by rw [hlpsC]; exact hAcr, hocc', fun ψ => ?_⟩
  · -- the members' formers, at the constructor's levels
    obtain ⟨cvTb, hcvb⟩ : ∃ cvTb, cvTas[mm]? = some cvTb :=
      ⟨_, List.getElem?_eq_getElem (by rw [hN.2.2]; exact hmm)⟩
    obtain ⟨hfb, -, -, -⟩ := hcore.1 mm cvTb hcvb
    refine ⟨cvTb, ConLeche.blockCapsAt p₁ mm isRec, ?_, by rw [hlpsC, hlpsT mm cvTb hmm hcvb]⟩
    show env.find? (d.memberNames.getD mm .anonymous) = _
    rw [show d.memberNames.getD mm .anonymous = cvTb.name from hN.1 mm cvTb hcvb]
    exact hfb
  · -- the reading is the constructor record's, so its parameter binders are the frames'
    have hle' : d.nP ≤ (d.dsF c j ψ).length := by rw [hcd.len ψ]; omega
    have h1 := stripPisAV_mkPisAV_take d.nP dsC bodyC hle
    have h2 := stripPisAV_mkPisAV_take d.nP (d.dsF c j ψ)
      (ctorBodyAVI m (d.memberName c) d.nP cA.2 ψ (d.esF c j ψ)) hle'
    rw [← Option.some.inj (hrd'.symm.trans (hcd.read ψ)), h1] at h2
    have htk : dsC.take d.nP = (d.dsF c j ψ).take d.nP := (Prod.mk.inj (Option.some.inj h2)).1
    rw [htk]
    exact hpars c hc' j cA hcj ψ ρ hsat
  · obtain ⟨ab, abN, hca, -, hlab, hlabN, -, habN, hEq⟩ := hr ψ
    have hlenP0 : (d.ppsM 0 ψ).length = d.nP + d.nIdxAt 0 := hFD0.len ψ
    have hlenParams : (d.params ψ).length = d.nP := by
      simp only [BlockData.params, List.length_map, List.length_take, hlenP0]; omega
    have habLen : (d.absF ψ c j).length = cA.2 := by
      rw [← habN, List.length_map, hlabN]
    refine ⟨hlenParams, habLen, ab, (List.range d.k).map fun t =>
      (mkPisAV ((d.ppsM t ψ).drop d.nP) (.sort (d.w ψ))).liftN t 0, hca, hlab,
      by simp [BlockData.toLfp], fun mm hmm => ?_, hEq⟩
    obtain ⟨cvTb, hcvb⟩ : ∃ cvTb, cvTas[mm]? = some cvTb :=
      ⟨_, List.getElem?_eq_getElem (by rw [hN.2.2]; exact hmm)⟩
    obtain ⟨hfb, -, -, hFDt⟩ := hcore.1 mm cvTb hcvb
    have hmm' : mm < d.k := hmm
    have hcvbCl : cvTb.type.hasFvar = false :=
      (m.wf _ (List.mem_of_find?_eq_some hfb)).1
    obtain ⟨bs, s, hsyn⟩ := hFDt.syn
    obtain ⟨ty, hty, -, hread⟩ := formerHoleTy_read m.acval_closed (ψ := ψ) hcvbCl
      (stripPis_isSome_of_le (Nat.le_add_right d.nP _) (by rw [hsyn]; rfl))
      (by rw [hFDt.len ψ]; omega) (hFDt.read ψ)
    refine ⟨cvTb, ConLeche.blockCapsAt p₁ mm isRec, ty, ?_, hty, ?_⟩
    · show env.find? (d.memberNames.getD mm .anonymous) = _
      rw [show d.memberNames.getD mm .anonymous = cvTb.name from hN.1 mm cvTb hcvb]
      exact hfb
    · rw [hread (d.nP + mm) (Nat.le_add_right _ _), List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range hmm', show d.nP + mm - d.nP = mm by omega]
      rfl

end ConLeche.Model

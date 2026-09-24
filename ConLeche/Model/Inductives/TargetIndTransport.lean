module

import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.TargetIndRen
import ConLeche.Model.Inductives.TargetResidue
import ConLeche.Verify.BridgeWfImp
import ConLeche.Model.Inductives.StructBits
public import ConLeche.Model.Inductives.TargetRuleData
public import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Inductives.BlockHoleRead
public import ConLeche.Model.Inductives.BlockDatum

public section

/-!
# The target check's abstract field types, read at the hole frame (lane RECLIB, B4)

The target check types a call on the MEMBER-ABSTRACTED field type
(`tgtAbsM`, holes at `B + t` after the prefix and the fields).  The lfp
clause's hole reading of the same field is its entry of `absF` (lane
HOLE2): the stored constructor type at the canonical parameters, the
fields opened above the holes at `nP + t` (`blockField_holeRead`).  The two are one
term up to a renaming of the free variables (`TargetIndRen.lean`): the
parameters stay, the holes move from `nP + t` to `B + t`, the fields
from `nP + k + i` to `rP + i`.  So a field lying in its hole reading at
a frame of hole values lies in the kernel's abstract type read at the
rule frame extended by the same hole values (`tgtField_transport`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo FEnv BlockParts TargetMajor
  NestCtx nestAbstract instPisWith openPisAtFvars)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- Two lists of variables at the same consecutive indices are related
along the diagonal below their length. -/
theorem frenL_of_fvarIdx :
    ∀ (as bs : List Expr) (o n : Nat),
      (∀ (i : Nat) (x : Expr), as[i]? = some x → ∃ ty, x = .fvar (o + i) ty) →
      (∀ (i : Nat) (x : Expr), bs[i]? = some x → ∃ ty, x = .fvar (o + i) ty) →
      as.length = bs.length → o + as.length ≤ n →
      FRenL (fun a b => a < n ∧ b = a) as bs
  | [], [], _, _, _, _, _, _ => trivial
  | [], _ :: _, _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, _, h, _ => by simp at h
  | a :: as, b :: bs, o, n, ha, hb, h, hn => by
    obtain ⟨ta, rfl⟩ := ha 0 a rfl
    obtain ⟨tb, rfl⟩ := hb 0 b rfl
    refine ⟨⟨by simp at hn; omega, rfl⟩, frenL_of_fvarIdx as bs (o + 1) n (fun i x hx => ?_)
      (fun i x hx => ?_) (by simpa using h) (by simp at hn; omega)⟩
    · obtain ⟨ty, hty⟩ := ha (i + 1) x hx
      exact ⟨ty, by rw [hty]; congr 1; omega⟩
    · obtain ⟨ty, hty⟩ := hb (i + 1) x hx
      exact ⟨ty, by rw [hty]; congr 1; omega⟩

theorem getD_app3 {α : Type _} (A B C : List α) (x : α) (i : Nat) :
    (A ++ (B ++ C)).getD i x = if i < A.length then A.getD i x else
      if i - A.length < B.length then B.getD (i - A.length) x else
        C.getD (i - A.length - B.length) x := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  by_cases h1 : i < A.length <;> by_cases h2 : i - A.length < B.length <;> simp [h1, h2]

/-- A consed valuation read at the variable `i` of its list, from below
the list's length. -/
theorem consList_at {L : List V} {ρ : Nat → V} {i : Nat} (hi : i < L.length) :
    consList L ρ (L.length - 1 - i) = L.getD i pt := by
  rw [consList_getD_of_lt _ _ _ (by omega), show L.length - 1 - (L.length - 1 - i) = i by omega]

section Transport

variable {F : Nat} {fe : FEnv} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {nested : Bool} {blk : List ConstantInfo}
  {out : List (ConstantVal × TargetMajor × List Expr)} {mpC : EnvModelM V μ fe.env}
  {d : BlockData V} {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}

/-- **THE TRANSPORT**: a field lying in its hole reading at a frame of
hole values `hv` lies in the target check's member-abstracted type of
that field, read past the rule frame and the holes, at the rule frame
extended by the same hole values. -/
theorem tgtField_transport (hμ : μ.verifiedChecks = true)
    (h : ConLeche.RecStageOk μ F fe.env pp cvTas ctorsAs (tgtRs out))
    (R : ConLeche.TargetRecRun μ F fe pp.toBlockShape nested blk cvTas ctorsAs out)
    (hdR : ∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    {c j : Nat} {r0 : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[c]? = some r0) {cA : ConstantVal × Nat} (hcA : r0.2.2.2[j]? = some cA)
    {rhs : Expr} (hrhs : r0.2.1[j]? = some rhs)
    (ψ : Name → Nat) (ρ : Nat → V) {xs fs hv : List V}
    (hxs : xs.length = pp.toBlockShape.rulePrefixAt c) (hfs : fs.length = cA.2)
    (hhv : hv.length = d.k)
    (hfit : SpineFit (consList hv (consList (xs.take d.nP) ρ))
      (d.absF ψ (pp.toBlockShape.recTgtAt c) j) fs)
    (hsatH : Sat V (d.holeCtx ψ).reverse (consList hv (consList (xs.take d.nP) ρ)))
    {fi : Nat} (hfi : fi < cA.2) (Aty : AnnotTerm)
    (hA : denoteMeta mpC.base2.acval fe.env ψ
      (tgtB pp.toBlockShape (tgtRs out) c j + cvTas.length)
      (tgtAbsM pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) c j
        ((tgtFieldFvs pp.toBlockShape (tgtRs out) c j).getD fi default).fvarTypeD) = some Aty) :
    fs.getD fi pt ∈ˢ interp V (consList (xs ++ fs ++ hv) ρ) Aty := by
  obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR
  have hk : (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k
      = (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).memberNames.length := by
    simp [blockDataOf, blockDataPre, BlockData.withPhi, ConLeche.BlockShape.k,
      ConLeche.BlockShape.memberNames]
  generalize hdd : blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf = d at *
  have hnamesP : d.memberNames = pp.toBlockShape.memberNames := by
    rw [← hdd]; rfl
  -- the constructor at the member
  have hmaj := blockRecMajor_run (V := V) hμ mpC h hmr hr ψ
  have hctM : d.ctorsM (pp.toBlockShape.recTgtAt c) = r0.2.2.2 := by
    obtain ⟨-, -, hctA, -⟩ := recStage_ctorsAt h hr
    rw [← hdd]
    show ctorsAs.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hctA]; rfl
  have hcj : (d.ctorsM (pp.toBlockShape.recTgtAt c))[j]? = some cA := by rw [hctM]; exact hcA
  obtain ⟨hfindC, -, -⟩ := hcore.2.2.2 _ hmaj.2.1 j cA hcj
  have hD₀ := (hcore.2.2.1 _ j cA hcj).2.2.1
  have hD := hD₀
  obtain ⟨crestM, hopP, hopX⟩ := hD.opens
  have hCf : cA.1.type.hasFvar = false :=
    (mpC.base2.wf _ (List.mem_of_find?_eq_some hfindC)).1
  have hwty : Expr.WScoped 0 cA.1.type := Expr.WScoped.of_not_hasFvar hCf
  have hwc : Expr.WScoped d.nP crestM := by
    have := (ConLeche.openPisAtFvars_WScoped d.nP _ 0 hopP hwty).2
    rwa [Nat.zero_add] at this
  -- the kernel's rule run
  obtain ⟨rc, rhs0, M, Q, hrc, hmem, hds, -, hFld, -, -, -, -, -⟩ := targetRuleAt R hr hcA hrhs
  have hrP : rc.rP = pp.toBlockShape.rulePrefixAt c := by
    simp only [ConLeche.BlockShape.rulePrefixAt, List.getD_eq_getElem?_getD]
    rw [show pp.toBlockShape.recs = pp.recs from rfl, hrc]; rfl
  have hct : ConLeche.targetCtorAt M cA.1 = cA.1.type := by
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hmem
    simp [ConLeche.targetCtorAt, ht]
  have hB : tgtB pp.toBlockShape (tgtRs out) c j = rc.rP + cA.2 := by rw [tgtB_at hr hcA, hrP]
  have hcrestK := Q.hcrest
  rw [hct] at hcrestK
  have hnPle : d.nP ≤ rc.rP := by rw [hrP]; exact hmaj.1
  have hprefLen : Q.fvsPref.length = rc.rP := ConLeche.Model.openPisAtFvars_length _ Q.hpref
  have hdsLen : M.ds.length = d.nP := by
    rw [hds, List.length_take, hprefLen, hmr.1]; exact Nat.min_eq_left (hmr.1 ▸ hnPle)
  have hdsIdx : ∀ (i : Nat) (x : Expr), M.ds[i]? = some x → ∃ ty, x = .fvar (0 + i) ty := by
    intro i x hx
    rw [hds, List.getElem?_take] at hx
    split at hx
    · exact ConLeche.openPisAtFvars_index _ _ _ Q.hpref i x hx
    · exact nomatch hx
  have hparIdx : ∀ (i : Nat) (x : Expr), (d.fvsPF (pp.toBlockShape.recTgtAt c) j)[i]? = some x →
      ∃ ty, x = .fvar (0 + i) ty := fun i x hx => by
    obtain ⟨ty, hty⟩ := hD.pIdx i x hx
    exact ⟨ty, by rw [hty, Nat.zero_add]⟩
  have hL : FRenL (fun a b => a < d.nP ∧ b = a) (d.fvsPF (pp.toBlockShape.recTgtAt c) j) M.ds :=
    frenL_of_fvarIdx _ _ 0 d.nP hparIdx hdsIdx (by rw [hD.pLen, hdsLen])
      (by rw [hD.pLen, Nat.zero_add]; exact Nat.le_refl _)
  have hT : FRen (fun a b => a < d.nP ∧ b = a) cA.1.type cA.1.type :=
    FRen.refl_of_fvarsBelow (d := 0) (fun i h => absurd h (Nat.not_lt_zero _)) hwty.fvarsBelow
  obtain ⟨crK, hcrK, hcrel⟩ := instPisWith_fren hL hT (instPisWith_of_openPis d.nP hopP)
  rw [hcrestK] at hcrK
  obtain rfl := Option.some.inj hcrK
  -- the fields, opened on both sides
  obtain ⟨xsK, rK, hopK, hxsK, -⟩ := openPisAtFvars_fren cA.2 (d' := rc.rP) hcrel hopX
  rw [Q.hfld] at hopK
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hopK)
  obtain ⟨x, hx⟩ : ∃ x, (d.xFvsF (pp.toBlockShape.recTgtAt c) j)[fi]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hD.xLen]; exact hfi)⟩
  obtain ⟨xK, hxK, hrel0⟩ := hxsK fi x hx
  have hxKeq : (tgtFieldFvs pp.toBlockShape (tgtRs out) c j).getD fi default = xK := by
    rw [← hFld, List.getD_eq_getElem?_getD, hxK]; rfl
  rw [hxKeq, hB] at hA
  -- the clause's hole reading of the field
  let ctx : NestCtx := ⟨d.memberNames, pp.lps, d.nP, [], [], .zero, fun _ => none, []⟩
  let holes : List Expr := (List.range d.k).map fun t => .fvar (d.nP + t) (.sort .zero)
  have hholes : ∀ (t : Nat) (y : Expr), holes[t]? = some y → ∃ ty, y = .fvar (d.nP + t) ty := by
    intro t y hy
    have ht : t < d.k := by simpa [holes] using (List.getElem?_eq_some_iff.mp hy).1
    simp only [holes, List.getElem?_map, List.getElem?_range ht, Option.map_some,
      Option.some.injEq] at hy
    exact ⟨_, hy.symm⟩
  obtain ⟨abD, hlD, hEqF, hreadD⟩ := blockField_holeRead (m := mpC.base2) (env := fe.env) (d := d)
    (lps := pp.lps) (hcore.2.2.1 _ j cA hcj).2.2.2 (ctx := ctx) rfl rfl rfl hk (holes := holes)
    hholes (by simp [holes]) hopP (fun i y hy => hD.pIdx i y hy) hwc hopX ψ
  have hread := hreadD hx
  -- the fit, through the link, on the declared crest's fields
  have hfitD : SpineFit (consList hv (consList (xs.take d.nP) ρ)) abD fs :=
    (hEqF.spineFit_iff hsatH fs).mpr hfit
  -- the renaming
  have hkL : cvTas.length = d.k := hN.2.2
  have h2 := FRen.trans (fren_shiftFromN d.nP ctx.names.length x.fvarTypeD).symm hrel0
  have h3 := fren_abs (R' := fun a b =>
      (∃ b', (a = if b' < d.nP then b' else b' + ctx.names.length) ∧
        ((b' < d.nP ∧ b = b') ∨ ∃ l, l < fi ∧ b' = d.nP + l ∧ b = rc.rP + l)) ∨
      (∃ t, t < d.k ∧ a = d.nP + t ∧ b = rc.rP + cA.2 + t))
    ctx holes pp.toBlockShape.memberNames (pp.lps.map Level.param)
    (ConLeche.targetHoles (cvTas.map (·.type)) (rc.rP + cA.2)) hnamesP rfl
    (fun t ht => by
      have htk : t < d.k := by rw [hk, hnamesP]; exact ht
      refine ⟨d.nP + t, rc.rP + cA.2 + t, .sort .zero, (cvTas.map (·.type)).getD t default,
        by simp [holes, List.getElem?_range htk], ?_, Or.inr ⟨t, htk, rfl, rfl⟩⟩
      simp [ConLeche.targetHoles, List.getElem?_range (show t < cvTas.length by omega)])
    (fun a b hab => Or.inl hab) h2
  -- the two readings have one value
  have hcl : ∀ (n : Name) (ψ' : Name → Nat) (ρ₁ ρ₂ : Nat → V),
      interp V ρ₁ (mpC.base2.acval n ψ') = interp V ρ₂ (mpC.base2.acval n ψ') :=
    fun n ψ' ρ₁ ρ₂ => acval_interp_closed mpC.base2 n ψ' ρ₁ ρ₂
  have hxsT : (xs.take d.nP).length = d.nP := by rw [List.length_take, hxs, ← hrP]; omega
  have hfsT : (fs.take fi).length = fi := by rw [List.length_take]; omega
  have hA' : denoteMeta mpC.base2.acval fe.env ψ (rc.rP + cA.2 + cvTas.length)
      (ConLeche.targetAbs pp.toBlockShape.memberNames (pp.lps.map Level.param)
        (ConLeche.targetHoles (cvTas.map (·.type)) (rc.rP + cA.2)) xK.fvarTypeD) = some Aty := by
    have := hA
    unfold tgtAbsM at this
    rw [hB] at this
    exact this
  have hLlen : (xs.take d.nP ++ (hv ++ fs.take fi)).length = d.nP + d.k + fi := by
    simp only [List.length_append, hxsT, hhv, hfsT]; omega
  have hL'len : (xs ++ fs ++ hv).length = rc.rP + cA.2 + cvTas.length := by
    simp only [List.length_append, hxs, hfs, hhv, hkL, hrP]
  have hval := denoteMeta_fren_interp hcl h3 (d.nP + d.k + fi) (rc.rP + cA.2 + cvTas.length)
    (consList (xs.take d.nP ++ (hv ++ fs.take fi)) ρ) (consList (xs ++ fs ++ hv) ρ)
    (by
      intro a b hab
      have key : a < d.nP + d.k + fi ∧ b < rc.rP + cA.2 + cvTas.length ∧
          (xs.take d.nP ++ (hv ++ fs.take fi)).getD a pt = (xs ++ fs ++ hv).getD b pt := by
        have hcn : ctx.names.length = d.k := hk.symm
        rw [hcn] at hab
        have hxsL : xs.length = rc.rP := by rw [hxs, hrP]
        rw [List.append_assoc, getD_app3, getD_app3, hxsT, hhv, hxsL, hfs]
        rcases hab with ⟨b', hT, (⟨hb', rfl⟩ | ⟨l, hl, rfl, rfl⟩)⟩ | ⟨t, ht, rfl, rfl⟩
        · rw [if_pos hb'] at hT
          subst hT
          refine ⟨by omega, by omega, ?_⟩
          rw [if_pos hb', if_pos (by omega)]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hb']
        · rw [if_neg (by omega)] at hT
          subst hT
          refine ⟨by omega, by omega, ?_⟩
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
          rw [show d.nP + l + d.k - d.nP - d.k = l by omega, show rc.rP + l - rc.rP = l by omega]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hl]
        · refine ⟨by omega, by omega, ?_⟩
          rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega)]
          congr 1; omega
      obtain ⟨ha, hb, hv'⟩ := key
      refine ⟨ha, hb, ?_⟩
      rw [← hLlen, ← hL'len, consList_at (by omega), consList_at (by omega)]
      exact hv')
    hread hA'
  -- the field lies in its hole reading
  have hmemA := ConLeche.Semantics.FixKI.spineFit_getD_mem' hfitD (l := fi)
    (by rw [← hfitD.length_eq, hfs]; exact hfi)
  rw [← consList_append, ← consList_append, hval] at hmemA
  exact hmemA

end Transport

end ConLeche.Model

module

public import ConLeche.Model.Inductives.NestedCtorRead
import ConLeche.Verify.Inductives.NestedRestoreKit
import ConLeche.Verify.Inductives.NestedRestoreOpen
import ConLeche.Model.Inductives.NestedTransfer
import ConLeche.Model.IndTowerRead
import ConLeche.Model.Inductives.StructData
import ConLeche.Model.Inductives.StructTele
import ConLeche.Model.Inductives.StructStageFormer
import ConLeche.Model.Inductives.SumRecRead
public section

/-!
# THE REFLEXIVE NESTED FIELD'S ENTRY (task #315, M6 s9′)

The reading law's remaining field shape (`NestedCtorRead`'s
`ReadCtx.fieldEqA`/`fieldEqB` cover the auxiliary-free and the
finitary nested ones): a REFLEXIVE nested field, whose auxiliary
domain is a `∀`-telescope ending in the copy's head `aux p⃗ ıs` and
whose restored domain is the same telescope ending in the pin
re-opened at the parameter openers.

The restore rebuilds the telescope binder for binder, so the two
domains open at the SAME openers `afvs` (`rf_restoredOpen`), the
openers' annotations read alike (the transfer), the index arguments
read alike, and the restored entry is therefore the Π-tower over the
auxiliary telescope data `tss` of the container's leaf at the pin's
components lifted past the earlier fields and the telescope — which
is exactly what `ReadCtx.agree_of`'s `hnestRefl` premise asks for.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  NestedParts MutualBlock ElimState NestedPin IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The restored telescope, opened -/

/-- **The restored telescope opens at the auxiliary openers**: the
restore keeps every binder of a reflexive field's domain and touches
only its body, so `openPisAtFvars` at the auxiliary length yields the
SAME openers `afvs` and the restored body at those openers — which,
the pin being closed, is the pin applied to the instantiated index
arguments.  The binder count is read off the body's constant head. -/
theorem rf_restoredOpen {d L : Nat} {tbs : List (Expr × BinderMeta)}
    {xty ty' P' : Expr} {n hn : Name} {us hus : List Level}
    {afvs fvsP is₀ is : List Expr}
    (hstripA : xty.stripPis L = some (tbs, Expr.mkAppN (.const n us) (fvsP ++ is₀)))
    (hopA : openPisAtFvars L xty d = some (afvs, Expr.mkAppN (.const n us) (fvsP ++ is)))
    (hstripR : ty'.stripPis L = some (tbs, Expr.mkAppN P' is₀))
    (his : is = is₀.map (Expr.instSeq afvs (L - 1)))
    (hPb : P'.looseBVarsBounded 0 = true)
    (hPfn : P'.getAppFn = .const hn hus) :
    openPisAtFvars L ty' d = some (afvs, Expr.mkAppN P' is) ∧
      (ty'.piBinders).1.length = L := by
  have hlenT : tbs.length = L := Expr.stripPis_length _ hstripA
  have htyA : xty = ConLeche.mkPisB tbs (Expr.mkAppN (.const n us) (fvsP ++ is₀)) :=
    ConLeche.stripPis_mkPisB _ hstripA
  have htyR : ty' = ConLeche.mkPisB tbs (Expr.mkAppN P' is₀) :=
    ConLeche.stripPis_mkPisB _ hstripR
  obtain ⟨fvs, -, -, hlaw⟩ := ConLeche.openPisAtFvars_mkPisB L tbs hlenT d
  have hA := hlaw (Expr.mkAppN (.const n us) (fvsP ++ is₀))
  rw [← htyA, hopA] at hA
  simp only [Option.some.injEq, Prod.mk.injEq] at hA
  obtain ⟨rfl, -⟩ := hA
  refine ⟨?_, ?_⟩
  · rw [htyR, hlaw (Expr.mkAppN P' is₀), rk_instSeq_mkAppN,
      rk_instSeq_eq_self_of_bounded _ _ hPb, ← his]
  · rw [htyR, rk_piBinders_mkPisB_length tbs _ (by rw [Expr.getAppFn_mkAppN]; exact hPfn), hlenT]

/-! ## The reading law's context -/

section Assembly

variable {F : Nat} {mp : EnvModelM V μ env} {p : NestedParts} {b : MutualBlock}
  {fms : List MutualFormerA} {f₀ : MutualFormerA} {ctorsA : List (ConstantVal × Nat)}
  {sortss : List (List Level)} {kinds : List (List (RecFieldKind × Nat))}
  {mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env)}
  {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {W : (Name → Nat) → Nat}
  {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
  {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
  {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
  {ctorsR : List (List (ConstantVal × Nat × Nat))}
  {dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {xFvsR : Nat → Nat → List Expr}
  {pinsS : List PinSyn}

local notation "ENV₁" => (ConLeche.consMutualFormers (fms.take p.k) env)
local notation "SCR" => (ConLeche.consMutualFormers fms env)
local notation "D" => (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS)

variable {st : ElimState} {envAux : Env} {stored : List AuxStored} {fmsA ctorsA₀ : List ConstantVal}
  {mp₁' : EnvModelM V μ (ConLeche.consMutualFormers (fms.take p.k) env)}
  (C : ReadCtx (V := V) (μ := μ) (env := env) (F := F) (mp := mp) (p := p) (b := b) (fms := fms)
    (f₀ := f₀) (ctorsA := ctorsA) (sortss := sortss) (kinds := kinds) (mp₁ := mp₁) (ppsF := ppsF)
    (W := W) (idxF := idxF) (dsF := dsF) (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF)
    (xFvsF := xFvsF) (xrestF := xrestF) (eissF := eissF) (tssF := tssF) (ctorsR := ctorsR)
    (pinsS := pinsS) st envAux stored fmsA ctorsA₀ mp₁')
include C

/-- **The restored pin keeps its container head**: re-opening the
abstracted pin at a constructor's parameter openers changes only
annotations (`rk_restoredPin_getAppFn`), the pin being closed because
its components read (`nt_pin_bounded`). -/
theorem ReadCtx.rfPinHead {q : Nat} {qn : NestedPin} (hq : st.pins[q]? = some qn)
    {J : Nat} {cA' : ConstantVal × Nat} (hJ : ctorsA[J]? = some cA') (ψ : Name → Nat) :
    (Expr.instSeq (fvsPF J) (b.nP - 1) (Expr.abstractRange qn.pin 0 p.nP 0)).getAppFn
      = .const qn.container (pinsS.getD q default).lvls := by
  have hCD := C.h.CD J cA' hJ
  have hql : q < pinsS.length := by
    rw [C.PF.pinsLen]; exact (List.getElem?_eq_some_iff.mp hq).1
  obtain ⟨-, hpin⟩ := C.PF.pinRec q qn hq
  rw [hpin, ← C.hnP]
  exact ConLeche.rk_restoredPin_getAppFn hCD.pLen (C.fvsPIdx hJ)
    (nt_pin_bounded (J := qn.container) (lvls := (pinsS.getD q default).lvls)
      (C.PF.pinDs q hql ψ))

section Entries

variable {mm j : Nat} {c : ConstantVal × Nat × Nat} {cA : ConstantVal × Nat}
  {crestR : Expr} {xFvsRc : List Expr}
  (RC : RestoredCtor (μ := μ) (env := env) (F := F) (p := p) (b := b) (fms := fms)
    (ctorsA := ctorsA) (kinds := kinds) (fvsPF := fvsPF) (xFvsF := xFvsF) (xrestF := xrestF)
    (st := st) mm j c cA crestR xFvsRc)
  {dsRc : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  (RS : ReadSpec mp₁' (fms.getD mm default).cvTa.name b.nP cA.2 c.1 (esF (b.ownOffset mm + j)) dsRc)
include RC RS

/-- **A reflexive nested field's entry**: the restored domain opens at
the auxiliary openers, its binder count is the auxiliary telescope's,
the openers' annotations and the index arguments read at the prefix
model to the auxiliary telescope data and index readings, and the
restored entry is the Π-tower of the container's leaf at the pin's
lifted components over that telescope. -/
theorem ReadCtx.fieldEqC (ψ : Name → Nat) {i q : Nat} {qn : NestedPin} {x ty' : Expr}
    {tbs : List (Expr × BinderMeta)} {is₀ afvs is : List Expr}
    (hx : (xFvsF (b.ownOffset mm + j))[i]? = some x)
    (hx' : xFvsRc[i]? = some (.fvar (b.nP + i) ty'))
    (hq : st.pins[q]? = some qn)
    (hk : kindAt (mutKsOf kinds (b.ownOffset mm + j)) i = .reflexive)
    (hopA : openPisAtFvars (x.fvarTypeD.piBinders).1.length x.fvarTypeD (b.nP + i)
      = some (afvs, Expr.mkAppN (.const qn.aux (b.lps.map .param))
        (fvsPF (b.ownOffset mm + j) ++ is)))
    (hstripA : x.fvarTypeD.stripPis (x.fvarTypeD.piBinders).1.length
      = some (tbs, Expr.mkAppN (.const qn.aux (b.lps.map .param))
        (fvsPF (b.ownOffset mm + j) ++ is₀)))
    (his : is = is₀.map (Expr.instSeq afvs ((x.fvarTypeD.piBinders).1.length - 1)))
    (hstripR : ty'.stripPis (x.fvarTypeD.piBinders).1.length
      = some (tbs, Expr.mkAppN (Expr.instSeq (fvsPF (b.ownOffset mm + j)) (b.nP - 1)
          (Expr.abstractRange qn.pin 0 p.nP 0)) is₀)) :
    openPisAtFvars ((tssF (b.ownOffset mm + j) ψ).getD i []).length ty' (b.nP + i)
      = some (afvs, Expr.mkAppN (Expr.instSeq (fvsPF (b.ownOffset mm + j)) (b.nP - 1)
          (Expr.abstractRange qn.pin 0 p.nP 0)) is) ∧
    ((tssF (b.ownOffset mm + j) ψ).getD i []).length = (ty'.piBinders).1.length ∧
    (∀ (k : Nat) (a : Expr), afvs[k]? = some a →
      denoteMeta mp₁'.base2.acval ENV₁ ψ (b.nP + i + k) a.fvarTypeD
        = some (((tssF (b.ownOffset mm + j) ψ).getD i []).getD k default).2.2) ∧
    DenoteMetaSpine mp₁'.base2.acval ENV₁ ψ (b.nP + i + ((tssF (b.ownOffset mm + j) ψ).getD i []).length)
      is ((eissF (b.ownOffset mm + j) ψ).getD i []) ∧
    ((dsRc ψ).getD (b.nP + i) default).2.2
      = mkPisAV ((tssF (b.ownOffset mm + j) ψ).getD i [])
          (AnnotTerm.mkAppN (mp₁'.base2.acval ((D).pinAt q).J (((D).pinAt q).ψJ ψ))
            ((((D).pinAt q).Ds ψ).map
                (·.liftN (i + ((tssF (b.ownOffset mm + j) ψ).getD i []).length) 0)
              ++ (eissF (b.ownOffset mm + j) ψ).getD i [])) := by
  have hCD := C.h.CD _ _ RC.hJ
  have hil : i < cA.2 := by
    rw [← hCD.xLen]; exact (List.getElem?_eq_some_iff.mp hx).1
  have hlenT : tbs.length = (x.fvarTypeD.piBinders).1.length := Expr.stripPis_length _ hstripA
  have htyA : x.fvarTypeD = ConLeche.mkPisB tbs (Expr.mkAppN (.const qn.aux (b.lps.map .param))
      (fvsPF (b.ownOffset mm + j) ++ is₀)) := ConLeche.stripPis_mkPisB _ hstripA
  have htyR : ty' = ConLeche.mkPisB tbs (Expr.mkAppN (Expr.instSeq (fvsPF (b.ownOffset mm + j))
      (b.nP - 1) (Expr.abstractRange qn.pin 0 p.nP 0)) is₀) :=
    ConLeche.stripPis_mkPisB _ hstripR
  have hargs : (Expr.mkAppN (.const qn.aux (b.lps.map Level.param))
      (fvsPF (b.ownOffset mm + j) ++ is)).getAppArgs.drop b.nP = is := by
    rw [Expr.getAppArgs_mkAppN,
      show (Expr.const qn.aux (b.lps.map Level.param)).getAppArgs = [] from rfl,
      List.nil_append, List.drop_left' hCD.pLen]
  -- the auxiliary reflexive facts
  obtain ⟨afvs₀, body₀, hop₀, hLt, hafvsRead, hsp₀⟩ := hCD.reflOpen ψ i x hx hk
  rw [hLt, hopA] at hop₀
  simp only [Option.some.injEq, Prod.mk.injEq] at hop₀
  obtain ⟨rfl, rfl⟩ := hop₀
  rw [hargs] at hsp₀
  obtain ⟨afvs', body', hopA', -, haRes, -, -, -, hisRes, -, -⟩ := hCD.opened.reflF i x hx hk
  rw [hopA] at hopA'
  simp only [Option.some.injEq, Prod.mk.injEq] at hopA'
  obtain ⟨rfl, rfl⟩ := hopA'
  rw [hargs] at hisRes
  have hTssLen : ((tssF (b.ownOffset mm + j) ψ).getD i []).length = tbs.length :=
    hLt.trans hlenT.symm
  -- the openers' annotations and the index arguments, transferred
  have hcRead : ∀ (k : Nat) (a : Expr), afvs[k]? = some a →
      denoteMeta mp₁'.base2.acval ENV₁ ψ (b.nP + i + k) a.fvarTypeD
        = some (((tssF (b.ownOffset mm + j) ψ).getD i []).getD k default).2.2 := by
    intro k a ha
    rw [← C.transfer ψ (b.nP + i + k) a.fvarTypeD
      (constsResolve_consMutualFormers (haRes a (List.mem_of_getElem? ha)))]
    exact hafvsRead k a ha
  have hdSpine : DenoteMetaSpine mp₁'.base2.acval ENV₁ ψ
      (b.nP + i + ((tssF (b.ownOffset mm + j) ψ).getD i []).length) is
      ((eissF (b.ownOffset mm + j) ψ).getD i []) :=
    (C.transferSpine ψ _ (fun a ha => constsResolve_consMutualFormers (hisRes a ha))).mp hsp₀
  -- the restored opening
  have hPfn := C.rfPinHead hq RC.hJ ψ
  have hPb := nt_looseBVarsBounded_of_denoteMeta _ _
    (C.pinRead (dsR := dsR) (xFvsR := xFvsR) hq hCD.pLen (C.fvsPIdx RC.hJ) ψ 0)
  obtain ⟨hopR, hpb⟩ := rf_restoredOpen hstripA hopA hstripR his hPb hPfn
  refine ⟨by rw [hLt]; exact hopR, hLt.trans hpb.symm, hcRead, hdSpine, ?_⟩
  -- the restored entry, read through the opened telescope
  have hE := C.entryR RC RS ψ (k := b.nP + i) (x := .fvar (b.nP + i) ty') (by
    rw [List.getElem?_append_right (by rw [hCD.pLen]; exact Nat.le_add_right _ _), hCD.pLen,
      Nat.add_sub_cancel_left]
    exact hx')
  have hopR' : openPisAtFvars tbs.length ty' (b.nP + i)
      = some (afvs, Expr.mkAppN (Expr.instSeq (fvsPF (b.ownOffset mm + j)) (b.nP - 1)
          (Expr.abstractRange qn.pin 0 p.nP 0)) is) := by
    rw [hlenT]; exact hopR
  obtain ⟨Γ, R, htele, hbodyR, hopenRead⟩ :=
    openPisAtFvars_denotePTele (acval := mp₁'.base2.acval) (env := ENV₁) (φ := ψ)
      tbs.length hopR' hE
  rw [← hTssLen] at hbodyR
  have hRval : R = AnnotTerm.mkAppN (mp₁'.base2.acval ((D).pinAt q).J (((D).pinAt q).ψJ ψ))
      ((((D).pinAt q).Ds ψ).map
          (·.liftN (i + ((tssF (b.ownOffset mm + j) ψ).getD i []).length) 0)
        ++ (eissF (b.ownOffset mm + j) ψ).getD i []) := by
    have hpin := C.pinRead (dsR := dsR) (xFvsR := xFvsR) hq hCD.pLen (C.fvsPIdx RC.hJ) ψ
      (i + ((tssF (b.ownOffset mm + j) ψ).getD i []).length)
    rw [← Nat.add_assoc] at hpin
    have hbody := denoteMeta_mkAppN hdSpine hpin
    rw [annotMkAppN_append] at hbody
    exact Option.some.inj (hbodyR.symm.trans hbody)
  obtain ⟨pps, hst, hΓ⟩ := stripPisAV_of_piTeleAV htele
  obtain ⟨hEeq, hppsLen⟩ := stripPisAV_eq_mkPis hst
  -- the two telescopes' data agree entry by entry
  have hafvsLen : afvs.length = tbs.length := by
    rw [openPisAtFvars_length _ hopA, hlenT]
  have hAread : denoteMeta mp₁.base2.acval SCR ψ (b.nP + i)
      (ConLeche.mkPisB tbs (Expr.mkAppN (.const qn.aux (b.lps.map .param))
        (fvsPF (b.ownOffset mm + j) ++ is₀)))
      = some ((dsF (b.ownOffset mm + j) ψ).getD (b.nP + i) default).2.2 := by
    rw [← htyA]; exact hCD.domRead ψ i x hx
  have hRread : denoteMeta mp₁'.base2.acval ENV₁ ψ (b.nP + i)
      (ConLeche.mkPisB tbs (Expr.mkAppN (Expr.instSeq (fvsPF (b.ownOffset mm + j)) (b.nP - 1)
        (Expr.abstractRange qn.pin 0 p.nP 0)) is₀))
      = some ((dsRc ψ).getD (b.nP + i) default).2.2 := by
    rw [← htyR]; exact hE
  have hstA := stripPisAV_mkPisAV ((tssF (b.ownOffset mm + j) ψ).getD i [])
    (AnnotTerm.mkAppN (mp₁.base2.acval
        (mutualNameOf b.members3 (tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i)) ψ)
      (paramBvarsAt b.nP (b.nP + i + ((tssF (b.ownOffset mm + j) ψ).getD i []).length)
        ++ (eissF (b.ownOffset mm + j) ψ).getD i []))
  rw [← hCD.reflEntry ψ i hk hil, hTssLen] at hstA
  have hppsEq : pps = (tssF (b.ownOffset mm + j) ψ).getD i [] := by
    apply List.ext_getElem?
    intro k
    rcases Nat.lt_or_ge k tbs.length with hklt | hkge
    · obtain ⟨pk, hpk⟩ : ∃ pk, pps[k]? = some pk :=
        ⟨_, List.getElem?_eq_getElem (by rw [hppsLen]; exact hklt)⟩
      obtain ⟨tk, htk⟩ : ∃ tk, ((tssF (b.ownOffset mm + j) ψ).getD i [])[k]? = some tk :=
        ⟨_, List.getElem?_eq_getElem (by rw [hTssLen]; exact hklt)⟩
      obtain ⟨ak, hak⟩ : ∃ ak, afvs[k]? = some ak :=
        ⟨_, List.getElem?_eq_getElem (by rw [hafvsLen]; exact hklt)⟩
      obtain ⟨bk, hbk⟩ : ∃ bk, tbs[k]? = some bk := ⟨_, List.getElem?_eq_getElem hklt⟩
      obtain ⟨hR1, hR2⟩ := stripPisAV_denoteMeta_mkPisB tbs hRread hst k pk bk hpk hbk
      obtain ⟨hA1, hA2⟩ := stripPisAV_denoteMeta_mkPisB tbs hAread hstA k tk bk htk hbk
      have h22 : pk.2.2 = tk.2.2 := by
        have h1 := hopenRead k ak hak
        rw [hcRead k ak hak] at h1
        rw [← hΓ, getD_reverse_of_peel hppsLen hklt hpk] at h1
        rw [Option.some.inj h1.symm, List.getD_eq_getElem?_getD, htk, Option.getD_some]
      rw [hpk, htk, Prod.ext (hR1.trans hA1.symm) (Prod.ext (hR2.trans hA2.symm) h22)]
    · rw [List.getElem?_eq_none (by rw [hppsLen]; exact hkge),
        List.getElem?_eq_none (by rw [hTssLen]; exact hkge)]
  rw [hEeq, hppsEq, hRval]

end Entries

end Assembly

end ConLeche.Model

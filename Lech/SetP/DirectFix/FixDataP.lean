import Lech.SetP.DirectSum.SumDataP
import Lech.SetP.Direct.DirectBodyFramesP
import Lech.Verify.Direct.FixWF

/-!
# The recursive constructor's data (task #188)

A recursive constructor's data at a carrier storing the former: the
sum's data (`CtorDataI`, the readings of the constructor's telescope)
together with what the recursive route's field-kinds guard pins on the
OPENED annotated type (`directFixOpenedOk`, read positionally:
`FixOpened`), and the readings it yields — every field's opened domain
reads to its entry (`domRead`); a recursive field's domain is the
family at the parameter variables and index expressions whose
readings `Eis` are read at the field's own depth (`eisRead`), the entry
being the former's leaf at the parameter variables and those readings
(`recEntry`); an ordinary field's domain resolves before the block, so
its reading is the same at every carrier storing the former; a
recursive field's variable is a leaf of no later domain nor of the
residual, so the later entries and the residual's index readings are
lifts over its slot.
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The opened-form guard, positionally -/

/-- `directFixOpenedOk`, read positionally. -/
structure FixOpened (env₀ : Env) (T : Name) (lps : List Name) (nP nIdx nF : Nat)
    (ks : List RecFieldKind) (fvsP xFvs : List Expr) (xrest : Expr) : Prop where
  residRes : ∀ e ∈ xrest.getAppArgs.drop nP, e.constsResolve env₀ = true
  ord : ∀ i x, xFvs[i]? = some x → ks.getD i .ordinary = .ordinary →
    x.fvarTypeD.constsResolve env₀ = true
  recF : ∀ i x, xFvs[i]? = some x → ks.getD i .ordinary = .recursive →
    x.fvarTypeD.getAppFn = Expr.const T (lps.map .param) ∧
    x.fvarTypeD.getAppArgs.take nP = fvsP ∧
    x.fvarTypeD.getAppArgs.length = nP + nIdx ∧
    (∀ e ∈ x.fvarTypeD.getAppArgs.drop nP, e.constsResolve env₀ = true) ∧
    (∀ y ∈ xFvs.drop (i + 1), y.fvarTypeD.mentionsFvar (nP + i) = false) ∧
    xrest.mentionsFvar (nP + i) = false
  kinds : ∀ i, i < nF → ks.getD i .ordinary = .ordinary ∨ ks.getD i .ordinary = .recursive

theorem fixOpened_of {env₀ : Env} {T : Name} {lps : List Name} {nP nIdx : Nat} {cty : Expr}
    {nF : Nat} {ks : List RecFieldKind}
    (h : Lech.directFixOpenedOk env₀ T lps nP nIdx cty nF ks = true) :
    ∃ (fvsP : List Expr) (crest : Expr) (xFvs : List Expr) (xrest : Expr),
      openPisAtFvars nP cty 0 = some (fvsP, crest) ∧
      openPisAtFvars nF crest nP = some (xFvs, xrest) ∧
      FixOpened env₀ T lps nP nIdx nF ks fvsP xFvs xrest := by
  unfold Lech.directFixOpenedOk at h
  split at h
  · next fvsP crest hop =>
    split at h
    · next xFvs xrest hox =>
      simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
      obtain ⟨hres, hall⟩ := h
      have hlenX : xFvs.length = nF := openPisAtFvars_length _ hox
      refine ⟨fvsP, crest, xFvs, xrest, hop, hox, ⟨hres, ?_, ?_, ?_⟩⟩
      · intro i x hx hk
        have hi : i < nF := by
          rw [← hlenX]; exact (List.getElem?_eq_some_iff.mp hx).1
        have := hall i hi
        rw [hx, hk] at this
        exact this
      · intro i x hx hk
        have hi : i < nF := by
          rw [← hlenX]; exact (List.getElem?_eq_some_iff.mp hx).1
        have := hall i hi
        rw [hx, hk] at this
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.not_eq_eq_eq_not,
          Bool.not_true, List.any_eq_false] at this
        obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := this
        exact ⟨h1, h2, h3, h4, fun y hy => by simpa using h5 y hy, h6⟩
      · intro i hi
        have := hall i hi
        cases hx : xFvs[i]? with
        | none => rw [hx] at this; exact nomatch this
        | some x =>
          rw [hx] at this
          cases hk : ks.getD i .ordinary with
          | ordinary => exact Or.inl rfl
          | recursive => exact Or.inr rfl
          | negative => rw [hk] at this; exact nomatch this
          | unsupported => rw [hk] at this; exact nomatch this
    · exact nomatch h
  · exact nomatch h

/-! ## The constructor's data -/

/-- **A recursive constructor's data** at a carrier storing the former
(see the module docstring). -/
structure FixCtorDataI {env : Env} (m : EnvS2Core V env) (env₀ : Env) (T : Name)
    (lps : List Name) (cvC : ConstantVal) (nP nF nIdx : Nat) (resSort : Level)
    (isProp large : Bool) (idxArgs : List Expr)
    (ds : (Name → Nat) → List (Nat × Nat × AVExpr)) (Es : (Name → Nat) → List AVExpr)
    (srcs : List (Option Nat)) (ks : List RecFieldKind) (fvsP xFvs : List Expr) (xrest : Expr)
    (Eiss : (Name → Nat) → List (List AVExpr)) : Prop
    extends CtorDataI m T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs where
  opened : FixOpened env₀ T lps nP nIdx nF ks fvsP xFvs xrest
  ksLen : ks.length = nF
  xLen : xFvs.length = nF
  pLen : fvsP.length = nP
  xIdx : ∀ k x, xFvs[k]? = some x → ∃ nm ty, x = Expr.fvar (nP + k) nm ty
  pIdx : ∀ k x, fvsP[k]? = some x → ∃ nm ty, x = Expr.fvar k nm ty
  idxEq : idxArgs = xrest.getAppArgs.drop nP
  domRead : ∀ ψ i x, xFvs[i]? = some x →
    denoteP m.acval env ψ (nP + i) x.fvarTypeD = some ((ds ψ).getD (nP + i) default).2.2
  eissLen : ∀ ψ, (Eiss ψ).length = nF
  eisRead : ∀ ψ i x, xFvs[i]? = some x → ks.getD i .ordinary = .recursive →
    DenoteSpineP m.acval env ψ (nP + i) (x.fvarTypeD.getAppArgs.drop nP) ((Eiss ψ).getD i [])
  eisLen : ∀ ψ i, ks.getD i .ordinary = .recursive → i < nF → ((Eiss ψ).getD i []).length = nIdx
  recEntry : ∀ ψ i, ks.getD i .ordinary = .recursive → i < nF →
    ((ds ψ).getD (nP + i) default).2.2
      = AVExpr.mkAppN (m.acval T ψ) (paramBvarsAt nP (nP + i) ++ (Eiss ψ).getD i [])
  eissParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvC.levelParams, ψ₁ q = ψ₂ q) → Eiss ψ₁ = Eiss ψ₂
  eissBelow : ∀ ψ i, ∀ E ∈ (Eiss ψ).getD i [], VExpr.bvarsBelow (nP + i) E.erase
  ordNone : ∀ ψ i, ks.getD i .ordinary ≠ .recursive → (Eiss ψ).getD i [] = []

end Lech.SetP

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel
open Lech.TT Lech.TTVerify SetTheory
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w'

variable {V : Type w'} [SetTheory V] {μ : CheckMode} {env : Env}

/-- The parameter variables read to the parameter spine at depth `D`. -/
theorem denoteSpineP_params {acval : Name → (Name → Nat) → AVExpr} {φ : Name → Nat}
    (D : Nat) {fvsP : List Expr} {nP : Nat} (hlen : fvsP.length = nP)
    (hidx : ∀ k x, fvsP[k]? = some x → ∃ nm ty, x = Expr.fvar k nm ty) :
    DenoteSpineP acval env φ D fvsP (paramBvarsAt nP D) := by
  have := denoteSpineP_fvars (acval := acval) (env := env) (φ := φ) D fvsP 0
    (fun k x hx => by
      obtain ⟨nm, ty, h⟩ := hidx k x hx
      exact ⟨nm, ty, by rw [h, Nat.zero_add]⟩)
  rw [hlen] at this
  have he : ((List.range nP).map fun k => AVExpr.bvar (D - 1 - (0 + k))) = paramBvarsAt nP D := by
    unfold paramBvarsAt
    apply List.map_congr_left
    intro k _
    rw [Nat.zero_add]
  rwa [he] at this

/-- **The recursive constructor's data**, from its stage run at the
environment holding the former and the opened-form guard. -/
theorem fixCtorData_of (hμ : μ.verifiedChecks = true) (mp : EnvS2PM V μ env)
    {F : Nat} {T : Name} {lps : List Name} {nP nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {cvC cvTa cvCa : ConstantVal} {env₀ env₁ : Env} {caps : IndCaps}
    {bs : List (Name × Expr × BinderMeta)} {ks : List RecFieldKind}
    (hCtor : Lech.checkDirectSumCtor (Lech.fueledOps μ F) env₁ env T lps nP nIdx resSort
      isProp large cvC nF cvTa = .ok cvCa)
    (hfT : env.find? T = some (.indInfo cvTa caps))
    (hlpsT : cvTa.levelParams = lps)
    (hstripT : cvTa.type.stripPis (nP + nIdx) = some (bs, .sort resSort))
    (hks : ks.length = nF)
    (hopened : Lech.directFixOpenedOk env₀ T lps nP nIdx cvCa.type nF ks = true) :
    ∃ (idxArgs : List Expr) (ds : (Name → Nat) → List (Nat × Nat × AVExpr))
      (Es : (Name → Nat) → List AVExpr) (srcs : List (Option Nat))
      (fvsP xFvs : List Expr) (xrest : Expr) (Eiss : (Name → Nat) → List (List AVExpr)),
      FixCtorDataI mp.base2 env₀ T lps cvCa nP nF nIdx resSort isProp large idxArgs ds Es srcs
        ks fvsP xFvs xrest Eiss := by
  obtain ⟨idxArgs, ds, Es, srcs, -, ⟨fvsP, crest, xFvs, xrest, hopP, hopX, hidxEq⟩, hCD⟩ :=
    sumCtorData_of hμ mp hCtor hfT hlpsT hstripT
  obtain ⟨fvsP', crest', xFvs', xrest', hopP', hopX', hO⟩ := fixOpened_of hopened
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hopP.symm.trans hopP'))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hopX.symm.trans hopX'))
  obtain ⟨hcf, -, -, hcb⟩ := Lech.direct_sum_ctor_typeWF hCtor
  obtain ⟨hlenP, hidxP, -⟩ := opening_vars_at hopP
  obtain ⟨hlenX, hidxX, -⟩ := opening_vars_at hopX
  have hidxX' : ∀ k x, xFvs[k]? = some x → ∃ nm ty, x = Expr.fvar (nP + k) nm ty := hidxX
  have hidxP' : ∀ k x, fvsP[k]? = some x → ∃ nm ty, x = Expr.fvar k nm ty := fun k x hx => by
    obtain ⟨nm, ty, h⟩ := hidxP k x hx
    exact ⟨nm, ty, by rw [h, Nat.zero_add]⟩
  have hopAll : openPisAtFvars (nP + nF) cvCa.type 0 = some (fvsP ++ xFvs, xrest) :=
    openPisAtFvars_add nP hopP (by rw [Nat.zero_add]; exact hopX)
  -- every field's opened domain reads to its entry
  have hdomRead : ∀ ψ i x, xFvs[i]? = some x →
      denoteP mp.base2.acval env ψ (nP + i) x.fvarTypeD
        = some ((ds ψ).getD (nP + i) default).2.2 := by
    intro ψ i x hx
    have hO := openedP_of_peel hopAll hcf hcb (hCD.read ψ) (hCD.len ψ) (hCD.okTy ψ)
    have hxA : (fvsP ++ xFvs)[nP + i]? = some x := by
      rw [List.getElem?_append_right (by omega), hlenP, Nat.add_sub_cancel_left]
      exact hx
    have hi : i < nF := by rw [← hlenX]; exact (List.getElem?_eq_some_iff.mp hx).1
    have hd := hO.doms (nP + i) x hxA
    have hget : (ds ψ)[nP + i]? = some ((ds ψ).getD (nP + i) default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hCD.len ψ]; omega)]
      rfl
    rw [getD_reverse_of_peel (hCD.len ψ) (by omega) hget] at hd
    exact hd
  -- a recursive field's index readings
  have hex : ∀ (ψ : Name → Nat) (i : Nat), ks.getD i .ordinary = .recursive → i < nF →
      ∃ Eis : List AVExpr, Eis.length = nIdx ∧
        (∀ x, xFvs[i]? = some x →
          DenoteSpineP mp.base2.acval env ψ (nP + i) (x.fvarTypeD.getAppArgs.drop nP) Eis) ∧
        ((ds ψ).getD (nP + i) default).2.2
          = AVExpr.mkAppN (mp.base2.acval T ψ) (paramBvarsAt nP (nP + i) ++ Eis) := by
    intro ψ i hk hi
    have hil : i < xFvs.length := by omega
    obtain ⟨x, hx⟩ : ∃ x, xFvs[i]? = some x := ⟨_, List.getElem?_eq_getElem hil⟩
    obtain ⟨hfn, htake, hlenA, -, -, -⟩ := hO.recF i x hx hk
    have hshape : x.fvarTypeD
        = Expr.mkAppN (.const T (lps.map .param)) (fvsP ++ x.fvarTypeD.getAppArgs.drop nP) := by
      conv => lhs; rw [← Expr.mkAppN_getApp x.fvarTypeD]
      rw [hfn, ← htake, List.take_append_drop]
    have hread := hdomRead ψ i x hx
    rw [hshape] at hread
    obtain ⟨fa, vs, hfa, hsp, hea⟩ := denoteP_mkAppN_inv hread
    have hlpsT' : (ConstantInfo.indInfo cvTa caps).toConstantVal.levelParams = lps := by
      simpa [ConstantInfo.toConstantVal] using hlpsT
    have hfa' : fa = mp.base2.acval T ψ := by
      rw [denoteP_const hfT (by rw [hlpsT']; simp), hlpsT', Level.substFn_param_self] at hfa
      exact (Option.some.inj hfa).symm
    obtain ⟨vs₁, vs₂, rfl, hsp₁, hsp₂⟩ := DenoteSpineP.append_inv hsp
    have hvs₁ : vs₁ = paramBvarsAt nP (nP + i) :=
      DenoteSpineP.unique hsp₁ (denoteSpineP_params (nP + i) hlenP hidxP')
    refine ⟨vs₂, ?_, fun x' hx' => ?_, ?_⟩
    · rw [← hsp₂.length, List.length_drop, hlenA]; omega
    · obtain rfl := Option.some.inj (hx.symm.trans hx')
      exact hsp₂
    · rw [hea, hfa', hvs₁]
  -- the readings, chosen
  let Eis : (Name → Nat) → Nat → List AVExpr := fun ψ i =>
    if h : ks.getD i .ordinary = .recursive ∧ i < nF then Classical.choose (hex ψ i h.1 h.2)
    else []
  have hEis : ∀ ψ i (h : ks.getD i .ordinary = .recursive ∧ i < nF),
      (Eis ψ i).length = nIdx ∧
      (∀ x, xFvs[i]? = some x →
        DenoteSpineP mp.base2.acval env ψ (nP + i) (x.fvarTypeD.getAppArgs.drop nP) (Eis ψ i)) ∧
      ((ds ψ).getD (nP + i) default).2.2
        = AVExpr.mkAppN (mp.base2.acval T ψ) (paramBvarsAt nP (nP + i) ++ Eis ψ i) := by
    intro ψ i h
    simp only [Eis, dif_pos h]
    exact Classical.choose_spec (hex ψ i h.1 h.2)
  have hEisNone : ∀ ψ i, ks.getD i .ordinary ≠ .recursive → Eis ψ i = [] := by
    intro ψ i h
    simp only [Eis]
    rw [dif_neg]
    intro h'
    exact h h'.1
  let Eiss : (Name → Nat) → List (List AVExpr) := fun ψ => (List.range nF).map (Eis ψ)
  have hEissGet : ∀ ψ i, i < nF → (Eiss ψ).getD i [] = Eis ψ i := by
    intro ψ i hi
    simp only [Eiss, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some]
  have hEissGet' : ∀ ψ i, (Eiss ψ).getD i [] = if i < nF then Eis ψ i else [] := by
    intro ψ i
    split
    · next hi => exact hEissGet ψ i hi
    · next hi =>
      simp only [Eiss, List.getD_eq_getElem?_getD, List.getElem?_map]
      rw [List.getElem?_eq_none (by simp; omega)]
      rfl
  refine ⟨idxArgs, ds, Es, srcs, fvsP, xFvs, xrest, Eiss, ⟨hCD, hO, hks, hlenX, hlenP, hidxX',
    hidxP', hidxEq, hdomRead, fun ψ => by simp [Eiss], ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro ψ i x hx hk
    have hi : i < nF := by rw [← hlenX]; exact (List.getElem?_eq_some_iff.mp hx).1
    rw [hEissGet ψ i hi]
    exact (hEis ψ i ⟨hk, hi⟩).2.1 x hx
  · intro ψ i hk hi
    rw [hEissGet ψ i hi]
    exact (hEis ψ i ⟨hk, hi⟩).1
  · intro ψ i hk hi
    rw [hEissGet ψ i hi]
    exact (hEis ψ i ⟨hk, hi⟩).2.2
  · intro ψ₁ ψ₂ hφ
    have hds := (hCD.params ψ₁ ψ₂ hφ).1
    simp only [Eiss]
    apply List.map_congr_left
    intro i hi
    have hi' : i < nF := List.mem_range.mp hi
    by_cases hk : ks.getD i .ordinary = .recursive
    · have h1 := (hEis ψ₁ i ⟨hk, hi'⟩).2.2
      have h2 := (hEis ψ₂ i ⟨hk, hi'⟩).2.2
      rw [hds] at h1
      have heq := h1.symm.trans h2
      have hl : (paramBvarsAt nP (nP + i) ++ Eis ψ₁ i).length
          = (paramBvarsAt nP (nP + i) ++ Eis ψ₂ i).length := by
        simp [(hEis ψ₁ i ⟨hk, hi'⟩).1, (hEis ψ₂ i ⟨hk, hi'⟩).1]
      exact List.append_cancel_left (mkAppN_inj_args heq hl).2
    · rw [hEisNone ψ₁ i hk, hEisNone ψ₂ i hk]
  · intro ψ i E hE
    rw [hEissGet' ψ i] at hE
    split at hE
    · next hi =>
      by_cases hk : ks.getD i .ordinary = .recursive
      · have hentry := (hEis ψ i ⟨hk, hi⟩).2.2
        have hb := DomsBelow.getD_below (nP + i) (hCD.below ψ) (by rw [hCD.len ψ]; omega)
        rw [Nat.zero_add, hentry, AVExpr.erase_mkAppN] at hb
        obtain ⟨-, hall⟩ := bvarsBelow_mkAppN_inv hb
        exact hall E.erase (List.mem_map.mpr ⟨E, List.mem_append_right _ hE, rfl⟩)
      · rw [hEisNone ψ i hk] at hE
        exact nomatch hE
    · exact nomatch hE
  · intro ψ i hk
    rw [hEissGet' ψ i]
    split
    · exact hEisNone ψ i hk
    · rfl

end Lech.SetP

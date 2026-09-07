import Lech.SetP.IndNestedParamP
import Lech.SetP.Annot.Bit

/-!
# `RecRuleLawP`'s pin conjunct, produced (task #161, IND TIER part 9)

Part 6 refuted the unconditional form of the nested pins' grading and
part 7 landed its producer (`nestedPinGradeP`); this file is the
producer's **consumer-facing row** — the conjunct exactly as
`RecRuleLawP` states it, at one pin index, from the checker's own two
recorded rows.

Three suppliers meet here, and none of them is routed:

* the pin's **instantiated** reading is `IotaThmNR`'s `TypedListW` row
  read through `denoteP_isSome_of_denote` (`Annot/BitReads.lean`) — a
  derivation carries a denotation, and a denotation carries a reading;
* the pin's **`openRev`** reading — the object the conjunct
  existentially quantifies — is `pinOpenRevReadsP`
  (`Interp2/IndOpenRevP.lean`), `pinCrossP`'s reading direction;
* the pin's **grading at the public frame** is `nestedPinFireP`
  (`Interp2/IndNestedParamP.lean`) on the `TypedListOk` row, read at
  the padded recursor-frame context — which is exactly the context
  `nestedPinGradeP`'s certificate premise is guarded by.
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory
open Lech.Semantics (AVExpr)
open Lech (CheckMode Env Expr Name isDefEqCore inferTypeCore
  TypedListOk)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

set_option maxHeartbeats 3200000 in
/-- **`RecRuleLawP`'s pin conjunct at one index**, from the two
recorded rows. -/
theorem nestedPinRowP {m : EnvS2Core V env} {F : Nat}
    (hclaims : DefEqClaims2P μ m φ F)
    (hinfC : InferClaims2P μ m φ F)
    (hreads : InferReadsP m μ φ F)
    {rP cnF cnP : Nat}
    -- the public (recursor) frame
    {fvsP : List Expr} (hfvsPlen : fvsP.length = rP)
    (hshapeP : ∀ (i : Nat) (x : Expr), fvsP[i]? = some x →
      ∃ ty, x = Expr.fvar i ty)
    (hwsFvsP : ∀ x ∈ fvsP, Expr.WScoped rP x)
    (hleafClosedP : ∀ l, (∃ x ∈ fvsP, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2 ∈ fvsP)
    (hlbFvsP : ∀ (i : Nat) (ty : Expr),
      Expr.fvar i ty ∈ fvsP → ty.looseBVarsBounded 0 = true)
    {TV : AVExpr} {ΓP : List AVExpr} {RP : AVExpr}
    (htowerP : PiTeleP rP TV ΓP RP)
    (hokTV : ∀ σ : Nat → V, AnnotOkP V σ TV)
    (hdomsP0 : ∀ (i : Nat) (x : Expr), fvsP[i]? = some x →
      denoteP m.acval env φ i (Expr.fvarTypeD x)
        = some (ΓP.getD (rP - 1 - i) default))
    -- the stored pins
    {pins : List Expr} (hpinsLen : pins.length = cnP)
    (hpinsWf : ∀ p ∈ pins, p.hasFvar = false ∧
      p.looseBVarsBounded rP = true)
    -- the constructor type at the stored instantiation, and the run
    {ctyP : Expr} (hCw : ctyP.hasFvar = false)
    (hCb : ctyP.looseBVarsBounded 0 = true)
    {TVjP : AVExpr}
    (hTVjP : denoteP m.acval env φ (rP + cnF) ctyP = some TVjP)
    (hokTVjP : ∀ σ : Nat → V, AnnotOkP V σ TVjP)
    {cdomsP : List Expr} {crestP : Expr}
    (hcinstP : Expr.instPisAt
      (pins.map (Expr.instSpine (fvsP.take rP) (rP - 1))) ctyP
      = some (cdomsP, crestP))
    (hTyped : TypedListOk μ F env (rP + cnF)
      (pins.map (Expr.instSpine (fvsP.take rP) (rP - 1))) cdomsP)
    -- the pins' instantiated readings (`TypedListW`'s own denotation,
    -- through `denoteP_isSome_of_denote`)
    (hpinRead : ∀ q, q < cnP → ∃ w, denoteP m.acval env φ (rP + cnF)
      (Expr.instSpine (fvsP.take rP) (rP - 1) (pins.getD q default))
      = some w) :
    ∀ q, q < cnP →
      ∃ vpa : AVExpr,
        denoteP m.acval env φ rP
          (openRev 0 rP (pins.getD q default)) = some vpa ∧
        ∀ (ρ : Nat → V) (zs : List AVExpr) (restR : AVExpr),
          zs.length = rP → (∀ z ∈ zs, AnnotOkP V ρ z) →
          TeleFitPA V ρ TV zs restR →
          AnnotOkP V ρ (AVExpr.instRevChain zs vpa) := by
  have hΓPlen : ΓP.length = rP := htowerP.length
  have htkPlen : (fvsP.take rP).length = rP := by
    rw [List.length_take, hfvsPlen]
    omega
  have hbFvsP : ∀ x ∈ fvsP, x.looseBVarsBounded 0 = true := by
    intro x hx
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hx
    obtain ⟨nm, ty, rfl⟩ := hshapeP q x hq
    rfl
  -- the truncated frame's own facts (the spine `nestedPinGradeP` runs
  -- its certificate at)
  have hosShape : ∀ (i : Nat) (x : Expr), (fvsP.take rP)[i]? = some x →
      ∃ ty, x = Expr.fvar i ty := by
    intro i x hx
    have hi : i < rP := by
      rcases Nat.lt_or_ge i rP with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none (by rw [htkPlen]; omega)] at hx
        exact nomatch hx
    rw [List.getElem?_take_of_lt hi] at hx
    exact hshapeP i x hx
  have hosWs : ∀ x ∈ fvsP.take rP, Expr.WScoped (rP + cnF) x :=
    fun x hx => (hwsFvsP x (List.mem_of_mem_take hx)).mono (by omega)
  have hosB : ∀ x ∈ fvsP.take rP, x.looseBVarsBounded 0 = true :=
    fun x hx => hbFvsP x (List.mem_of_mem_take hx)
  -- the pins, pointwise
  have hpgetd : ∀ q, q < cnP → pins[q]? = some (pins.getD q default) := by
    intro q hq
    rw [List.getD]
    rcases hp : pins[q]? with _ | p
    · rw [List.getElem?_eq_none_iff, hpinsLen] at hp
      omega
    · rfl
  have hpwd : ∀ q, q < cnP → (pins.getD q default).hasFvar = false ∧
      (pins.getD q default).looseBVarsBounded rP = true :=
    fun q hq => hpinsWf _ (List.mem_of_getElem? (hpgetd q hq))
  -- the padded recursor-frame context
  have hΔblen : (List.replicate cnF (AVExpr.sort 0) ++ ΓP).length
      = rP + cnF := by
    rw [List.length_append, List.length_replicate, hΓPlen]
    omega
  have hΔbent : ∀ i, i < rP →
      (List.replicate cnF (AVExpr.sort 0) ++ ΓP)[rP + cnF - 1 - i]?
        = some (ΓP.getD (rP - 1 - i) default) := by
    intro i hi
    rw [List.getElem?_append_right
        (by simp only [List.length_replicate]; omega),
      List.length_replicate,
      show rP + cnF - 1 - i - cnF = rP - 1 - i from by omega,
      List.getD]
    rcases hg : ΓP[rP - 1 - i]? with _ | A
    · rw [List.getElem?_eq_none_iff] at hg; omega
    · rfl
  have hfire := nestedPinFireP hclaims hinfC hreads
    (K := rP + cnF) (by omega) hfvsPlen hshapeP hwsFvsP hleafClosedP
    hlbFvsP htowerP hokTV hdomsP0 hpinsLen hpinsWf hCw hCb hTVjP
    hokTVjP hcinstP hTyped hpinRead hΔblen hΔbent
  intro q hq
  obtain ⟨hpw, hpb⟩ := hpwd q hq
  obtain ⟨w0, hw0⟩ := hpinRead q hq
  obtain ⟨vpa, hvpden⟩ := pinOpenRevReadsP (acval := m.acval)
    (cval := m.cvalE) (env := env) (φ := φ) m.acval_closed
    (fun n ψ y k =>
      AVExprSubst.inst_eq_self_of_closed (m.acval_closed n ψ) y k)
    m.acval_erase m.cval_closed htkPlen hosShape hosWs hosB
    hpw hpb hw0
  refine ⟨vpa, hvpden, ?_⟩
  intro ρ zs restR hzslen hzsOk hfit
  refine nestedPinGradeP (acval := m.acval) (cval := m.cvalE)
    (env := env) (φ := φ) m.acval_closed
    (fun n ψ y k =>
      AVExprSubst.inst_eq_self_of_closed (m.acval_closed n ψ) y k)
    m.acval_erase m.cval_closed htkPlen hosShape hosWs hosB
    hpw hpb hvpden htowerP ?_ hzslen hzsOk hfit
  intro w1 hw1 σ hσ
  obtain ⟨w2, hw2, hokw2, -⟩ := hfire q hq σ hσ
  obtain rfl : w1 = w2 := Option.some.inj (hw1.symm.trans hw2)
  exact hokw2

end Lech.SetP

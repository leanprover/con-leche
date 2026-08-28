import Setlec.SetR.Bridge.DeclInd

/-!
# The assembly (task #148, T6)

`checkDecl` → `DeclR` by dispatch, and the `checkDecls` fold that
carries the `EnvS` invariant along it.  This is the transpose of the
TT lane's `checkDeclTT` / `foldlM_TT` pair
(`Setlec/TTVerify/Consistency.lean`).

Three per-declaration bridge obligations stay **named hypotheses**
here rather than being discharged: the `Nat` equation certificates,
the div/mod pins and the reduce pins.  Each is stated *attached* — it
quantifies over an `EnvS V env` and speaks at that `m`'s own
valuation — which is what keeps it dischargeable (an unattached
valuation in a semantic hypothesis is the campaign's recorded vacuity
signature).
-/

namespace Setlec.SetR
open Setlec.TT Setlec.TTVerify SetTheory
universe w
variable {V : Type w} [SetTheory V]

/-- **The direct-structure path is compile-time disabled**
(`directStructsEnabled = false`), so `checkDecl`'s `indDecl` clause
*is* `checkIndDecl`.  `DeclR` records the modeled path only, and this
is the single place that dependence is discharged — worth its own
name so the audit can find it. -/
theorem directParts?_none (env : Env) (block : List ConstantInfo) :
    directParts? env block = none := by
  unfold directParts?
  cases directPartsCore? block with
  | none => rfl
  | some p => simp [directStructsEnabled]

def DivModPinBridgeR (V : Type w) [SetTheory V] (μ : CheckMode)
    (F : Nat) : Prop :=
  ∀ {env env' : Env} (m : EnvS V env) {n : Name} {v : Expr},
    natDivModNames.contains n = true →
    checkDivModPin (m := CheckM) (fueledOps μ F) env env' n = .ok () →
    DivModPinR μ F env env' m.cval n v

def ReducePinBridgeR (V : Type w) [SetTheory V] (μ : CheckMode)
    (F : Nat) : Prop :=
  ∀ {env env' : Env} (m : EnvS V env) {n : Name} {value : Expr},
    reduceOpNames.contains n = true →
    checkReducePin (m := CheckM) (fueledOps μ F) env env' n value
      = .ok () →
    ReducePinR μ F env env' m.cval n value

theorem checkDeclR_sound (hkey : MemberKeyS V) (heta : MemberEtaS V)
    {μ : CheckMode} {F : Nat}
    (hdmR : DivModPinBridgeR V μ F)
    (hrpR : ReducePinBridgeR V μ F)
    {env env₂ : Env} (m : EnvS V env) {d : Declaration}
    (h : checkDecl μ (fueledOps μ F) env d = .ok env₂) :
    DeclR μ F m.cval env d env₂ :=
  checkDeclR_of
    (fun hh => declDefnR m (fun hn hp => hdmR m hn hp) hh)
    (fun hh => declThmR m hh)
    (fun hh => declOpaqueR m (fun hn hp => hrpR m hn hp) hh)
    (fun hh => declAxiomR m hh)
    (fun hh => declBasisR hh)
    -- the direct-structure path is compile-time disabled
    -- (`directStructsEnabled = false`), so `checkDecl`'s `indDecl`
    -- clause *is* `checkIndDecl`.  The `DeclR` relation records the
    -- modeled path only, and this is where that is discharged.
    (fun hh => declIndRS hkey heta m (by
      simpa [checkDecl, directParts?_none] using hh)) h

theorem foldlM_R (hkey : MemberKeyS V) (heta : MemberEtaS V)
    {μ : CheckMode} {F : Nat}
    (hdmR : DivModPinBridgeR V μ F)
    (hrpR : ReducePinBridgeR V μ F)
    (hdm : DivModPinS V) (hrp : ReducePinS V) (hstd : StdAxiomKeyS V)
    (hofr : OfReduceKeyS V) (hbas : DeclBasisS V) (hind : DeclIndS V) :
    ∀ (ds : List Declaration) (env : Env) {env' : Env},
      Nonempty (EnvS V env) →
      ds.foldlM (checkDecl μ (fueledOps μ F)) env = .ok env' →
      Nonempty (EnvS V env')
  | [], _, _, hm, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hm
  | d :: ds, env, _, hm, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : checkDecl μ (fueledOps μ F) env d with
    | error e => rw [hd] at h; exact nomatch h
    | ok env1 =>
      rw [hd] at h
      obtain ⟨m⟩ := hm
      exact foldlM_R hkey heta hdmR hrpR hdm hrp hstd hofr hbas
        hind ds env1
        (declStepS hdm hrp hstd hofr hbas hind m
          (checkDeclR_sound hkey heta hdmR hrpR m hd)) h

end Setlec.SetR

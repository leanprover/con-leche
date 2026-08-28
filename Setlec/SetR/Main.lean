import Setlec.SetR.Bridge.Sound

/-!
# The `SetR` route's consistency theorems (task #148, T6)

The replacements for `Setlec/Model/Consistency*.lean`'s top-level
claims, on the algorithmic-relation route.  Three of the fourteen land
here — the ones over `checkDecls` at `fueledOps`.  The other eleven are
the `_S`/`_C`/`_SP` driver variants, each of which needs its *own*
fold soundness (`foldlM_soundS`, `foldlM_soundC`, `foldSP` in the
Model lane); they are a distinct shape and are tracked separately.

Every theorem here carries its obligations as **named hypotheses**,
all stated attached to an `EnvS`.  That is deliberate: the campaign's
recorded vacuity signature is a valuation with no invariant attached,
and these are the last place new hypotheses enter.
-/

namespace Setlec.SetR
open Setlec.TT Setlec.TTVerify SetTheory
universe u w
variable {V : Type w} [SetTheory V]

theorem no_constant_of_Empty_R {env : Env} (m : EnvS V env)
    (c : ConstantInfo) (hc : c ∈ env.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨t, hTi, hrest⟩ := m.mem_type c hc (fun _ => 0)
  rw [hty, denoteClosed, denote_const] at hTi
  revert hTi
  cases hf : env.find? emptyName with
  | none => intro hTi; exact nomatch hTi
  | some ci =>
    dsimp only
    split
    · next hlen =>
      intro hTi
      obtain rfl := (Option.some.inj hTi).symm
      obtain ⟨u0, hu0⟩ := m.empty_pinned
        (Level.substFn (fun _ => 0) ci.toConstantVal.levelParams [])
      obtain ⟨hmem, -⟩ := hrest (fun _ => (SetTheory.empty : V))
      rw [hu0, interp_emptyT] at hmem
      exact not_mem_empty _ hmem
    · intro hTi; exact nomatch hTi

/-- **The acceptance theorem, on the `SetR` route.** -/
theorem checkDecls_sound_R (hkey : MemberKeyS V) (heta : MemberEtaS V)
    {μ : CheckMode} {F : Nat}
    (hdmR : DivModPinBridgeR V μ F)
    (hdm : DivModPinS V) (hrp : ReducePinS V) (hstd : StdAxiomKeyS V)
    (hofr : OfReduceKeyS V) (hbas : DeclBasisS V) (hind : DeclIndS V)
    {ds : List Declaration} {env' : Env}
    (h : checkDecls μ (fueledOps μ F) ds = .ok env') :
    Nonempty (EnvS V env') :=
  foldlM_R hkey heta hdmR hdm hrp hstd hofr hbas hind
    ds Env.empty ⟨EnvS.empty V⟩ h

/-- **No proof of `Empty` is ever accepted**, on the `SetR` route. -/
theorem no_proof_of_Empty_R (hkey : MemberKeyS V) (heta : MemberEtaS V)
    {μ : CheckMode} {F : Nat}
    (hdmR : DivModPinBridgeR V μ F)
    (hdm : DivModPinS V) (hrp : ReducePinS V) (hstd : StdAxiomKeyS V)
    (hofr : OfReduceKeyS V) (hbas : DeclBasisS V) (hind : DeclIndS V)
    {ds : List Declaration} {env' : Env}
    (h : checkDecls μ (fueledOps μ F) ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨m⟩ := checkDecls_sound_R hkey heta hdmR hdm hrp
    hstd hofr hbas hind h
  exact no_constant_of_Empty_R m c hc hty

end Setlec.SetR

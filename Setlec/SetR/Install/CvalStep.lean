import Setlec.SetR.Install.IndStagesS

/-!
# Running one environment ahead of the model (task #148, T5, finding 6)

A capability key (`etaLawKeyS`, `unitLawKeyS`) has to conclude its law
**at the extension** — that is what `EnvS.cons`'s head obligation asks
for — while the only model in hand is the one *below* it.  Stating the
key over an `EnvS` at the law's own environment is circular:
`EnvSHyp` carries `caps_ok`, so the bundle at the extension already
contains the law being proved.

The escape is the one the TT lane's `modeledCapsUnitTT` already uses:
run every *semantic* step at the smaller environment, with the
installed valuation, and move only the statement across.  This file
holds the four moves that needs.

* `denote_cvalStep` — the valuation change alone (the environment is
  fixed).  Unconditional: `denote` returns `none` at an unresolved
  constant, so agreeing on the stored ones is enough.
* `EnvS.mem_type_step`, `EqLawV.cvalStep`, `EqFormerKeyV.cvalStep` —
  the three model facts the keys actually consume, moved to the
  installed valuation.
* `EtaLawV.up` / `UnitLawV.up` — the statement's own move.  Both laws
  read the environment through **one** premise, the former's denoted
  type, so the transport is `Installs.denoteDown` composed with the
  valuation change.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-- A stored constant's name is found. -/
theorem Env.isSome_find?_of_mem {env : Env} {c : ConstantInfo}
    (hc : c ∈ env.consts) : (env.find? c.name).isSome = true := by
  rcases h : env.find? c.name with _ | ci
  · unfold Setlec.Env.find? at h
    rw [List.find?_eq_none] at h
    exact absurd (h c hc) (by simp)
  · rfl

/-- The valuation change of an install, at the *unextended*
environment. -/
theorem denote_cvalStep {env : Env} {cval cval' : TConstVal}
    {c₀ : ConstantInfo} (hi : Installs env cval cval' c₀)
    (φ : Name → Nat) (d : Nat) (e : Expr) :
    denote cval env φ d e = denote cval' env φ d e := by
  have hagE : ∀ n ci, env.find? n = some ci → cval n = cval' n := by
    intro n ci hf
    refine hi.ag n ?_
    intro hh
    rw [hh, hi.fresh] at hf
    exact nomatch hf
  exact denote_cval_congr hagE hi.lit.nat hi.lit.succ hi.lit.sol
    hi.lit.nil hi.lit.cons hi.lit.char hi.lit.ofn d e

/-- Stored constants keep their front doors under an install's
valuation change. -/
theorem EnvS.mem_type_step {env : Env} (mS : EnvS V env)
    {cval' : TConstVal} {c₀ : ConstantInfo}
    (hi : Installs env mS.cval cval' c₀) :
    ∀ c ∈ env.consts, ∀ φ : Name → Nat,
      ∃ t, denoteClosed cval' env φ c.toConstantVal.type = some t ∧
        ∀ ρ : Nat → V,
          interp V ρ (cval' c.name φ) ∈ˢ interp V ρ t ∧ AnnotOkV V ρ t := by
  intro c hc φ
  obtain ⟨t, ht, hfacts⟩ := mS.mem_type c hc φ
  refine ⟨t, ?_, ?_⟩
  · rw [show denoteClosed cval' env φ c.toConstantVal.type
        = denoteClosed mS.cval env φ c.toConstantVal.type from
      (denote_cvalStep hi φ 0 _).symm]
    exact ht
  · rw [← hi.agree (n := c.name) (Env.isSome_find?_of_mem hc)]
    exact hfacts

/-- The pinned `Eq` law survives the valuation change: it reads the
valuation only at `eqName`, which the law's own premise stores. -/
theorem EqLawV.cvalStep {env : Env} {cval cval' : TConstVal}
    {c₀ : ConstantInfo} (hi : Installs env cval cval' c₀)
    (h : EqLawV V env cval) : EqLawV V env cval' := by
  intro hf
  rw [← hi.agree (n := eqName) (by rw [hf]; rfl)]
  exact h hf

/-- …and so does the firing key. -/
theorem EqFormerKeyV.cvalStep {env : Env} {cval cval' : TConstVal}
    {c₀ : ConstantInfo} {φ : Name → Nat}
    (hi : Installs env cval cval' c₀)
    (heqfE : env.find? eqName = some eqA)
    (h : EqFormerKeyV V env cval φ) : EqFormerKeyV V env cval' φ := by
  have hag : cval eqName = cval' eqName :=
    hi.agree (n := eqName) (by rw [heqfE]; rfl)
  refine ⟨fun ψ => by rw [← hag]; exact h.1 ψ, ?_⟩
  intro us hus T hT ρ
  rw [← hag]
  refine h.2 us hus T ?_ ρ
  rw [show denoteClosed cval env φ _
      = denoteClosed cval' env φ _ from denote_cvalStep hi φ 0 _]
  exact hT

/-- The eta law crosses one install: it reads the environment through
the former's denoted type alone. -/
theorem EtaLawV.up {env : Env} {cval cval' : TConstVal}
    {c₀ : ConstantInfo} (hi : Installs env cval cval' c₀)
    {T : Name} {cvT : ConstantVal} {caps : IndCaps}
    (hres : ∀ us : List Level,
      (cvT.type.instantiateLevelParams cvT.levelParams us).constsResolve
        env = true)
    (h : EtaLawV V env cval' T cvT caps) :
    EtaLawV V ⟨c₀ :: env.consts⟩ cval' T cvT caps := by
  intro φ' us ρ xs TV rest B hlen hTV
  refine h φ' us ρ xs TV rest B hlen ?_
  rw [show denoteClosed cval' env φ' _
      = denoteClosed cval env φ' _ from (denote_cvalStep hi φ' 0 _).symm]
  exact hi.denoteDown (hres us) hTV

/-- The unit-like law crosses one install, by the same reading. -/
theorem UnitLawV.up {env : Env} {cval cval' : TConstVal}
    {c₀ : ConstantInfo} (hi : Installs env cval cval' c₀)
    {T : Name} {cvT : ConstantVal} {caps : IndCaps}
    (hres : ∀ us : List Level,
      (cvT.type.instantiateLevelParams cvT.levelParams us).constsResolve
        env = true)
    (h : UnitLawV V env cval' T cvT caps) :
    UnitLawV V ⟨c₀ :: env.consts⟩ cval' T cvT caps := by
  intro φ' us ρ xs TV rest x y hlen hTV
  refine h φ' us ρ xs TV rest x y hlen ?_
  rw [show denoteClosed cval' env φ' _
      = denoteClosed cval env φ' _ from (denote_cvalStep hi φ' 0 _).symm]
  exact hi.denoteDown (hres us) hTV

end Setlec.SetR

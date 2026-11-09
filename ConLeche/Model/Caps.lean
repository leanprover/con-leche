module

public import ConLeche.Model.Install

public section

/-!
# The structure-capability laws across a fresh cons (task #161, caps
tier)

The statements (`TeleFit`, `EtaLaw`, `CapsOk`) live in `Env/Laws.lean` beside `NatOps`,
`DivMod` and `EqLaw` — the `EnvModelM` field `caps_ok` must mention
them.  This file is the *preservation* half: `capsOk_cons_fresh`, the obligation every
value-kind harvest discharges.

The law **carries the instantiated former type's reading**, so the
crossing must move that reading forward too
(`denote_cons_mono`, on `ConstsBound` of the instantiated type
— `constsBound_instType`).  Everything else is `acvalWith_ne` at the
two leaves the law mentions (the former and the capability
constructor), each `≠` the fresh name because `EtaFamilyStored`
*stores* them at kinds the value-kind harvests never cons.

The head case is therefore not a case at all: a `defnInfo`/`thmInfo`/
`axiomInfo` cons can be neither the former (an `indInfo` lookup) nor
the capability constructor (a `ctorInfo` lookup), so both
disequalities are `ConstantInfo.noConfusion`.  This is *simpler* than
`natOps_cons_fresh`, whose head case needs a disjunctive premise.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  IndCaps)

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env}

/-! ## The instantiated former type is prefix-bound

The law needs it as a `ConstsBound`:
`Expr.constsResolve_instantiateLevelParams` composed with
`constsBound_of_constsResolve`. -/

/-- **A stored constant's level-instantiated type is prefix-bound.**
Level instantiation does not move constants, so this is the stored
type's own `constsResolve` read through `ConstsBound`. -/
theorem constsBound_instType {env : Env} (hwf : ConLeche.EnvWF env)
    {c : ConstantInfo} (hc : c ∈ env.consts) (us : List Level) :
    ConstsBound env
      (c.toConstantVal.type.instantiateLevelParams
        c.toConstantVal.levelParams us) := by
  obtain ⟨-, -, hty, -⟩ := hwf.consts c hc
  refine constsBound_of_constsResolve _ ?_
  rw [ConLeche.Expr.constsResolve_instantiateLevelParams]
  exact hty

/-! ## The family descent

An extended-environment family whose two stored members are of kinds
the cons is not descends verbatim to the prefix, and its two names miss
the fresh name. -/

/-- **The stored family descends past a value-kind cons**, together
with the two disequalities the law's leaf transport needs. -/
theorem etaFamilyStored_descend {c₀ : ConstantInfo} {T : Name}
    {cvT : ConstantVal} {caps : IndCaps}
    (hnotind : ∀ cv caps, c₀ ≠ .indInfo cv caps)
    (hnotctor : ∀ cv np nf, c₀ ≠ .ctorInfo cv np nf)
    (hf : (⟨c₀ :: env.consts, env.tables⟩ : Env).find? T = some (.indInfo cvT caps))
    (hfam : ConLeche.EtaFamilyStored ⟨c₀ :: env.consts, env.tables⟩ T caps) :
    env.find? T = some (.indInfo cvT caps) ∧
      ConLeche.EtaFamilyStored env T caps ∧
      T ≠ c₀.name ∧ caps.etaCtor ≠ c₀.name := by
  obtain ⟨hCres, ⟨cvC, cnP, cnF, hfC⟩, hfP⟩ := hfam
  -- the former is not the cons: the cons is not an `indInfo`
  have hnT : T ≠ c₀.name := by
    rintro rfl
    rw [ConLeche.Env.find?_cons, ite_eq_left rfl] at hf
    exact hnotind cvT caps (Option.some.inj hf)
  -- the capability constructor is not the cons: it is a `ctorInfo`
  have hnC : caps.etaCtor ≠ c₀.name := by
    intro heq
    rw [heq, ConLeche.Env.find?_cons, ite_eq_left rfl] at hfC
    exact hnotctor cvC cnP cnF (Option.some.inj hfC)
  have hdown : ∀ n : Name, n ≠ c₀.name →
      (⟨c₀ :: env.consts, env.tables⟩ : Env).find? n = env.find? n := by
    intro n hn
    rw [ConLeche.Env.find?_cons, ite_eq_right (fun hh => hn hh.symm)]
  exact ⟨by rwa [hdown _ hnT] at hf,
    ⟨hCres, ⟨cvC, cnP, cnF, by rwa [hdown _ hnC] at hfC⟩, hfP⟩, hnT, hnC⟩

/-! ## The crossing -/

/-- **`CapsOk` at a fresh value-kind cons** — every `defnInfo`,
`thmInfo` and `axiomInfo` harvest discharges its `caps_ok` obligation
here.  (An `indInfo`/`ctorInfo` cons may *complete* a family
and so genuinely owes the law; those installs supply it bespoke.) -/
theorem capsOk_cons_fresh (mp : EnvModelM V env)
    (hprev : CapsOk mp.base2)
    {c₀ : ConstantInfo} {A : (Name → Nat) → Term}
    (hfresh : env.find? c₀.name = none)
    (hnotind : ∀ cv caps, c₀ ≠ .indInfo cv caps)
    (hnotctor : ∀ cv np nf, c₀ ≠ .ctorInfo cv np nf)
    (m₂ : EnvModel V ⟨c₀ :: env.consts, env.tables⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval c₀.name A) :
    CapsOk m₂ := by
  intro T cvT caps hf hcape hres hfam φ' us hlen
  obtain ⟨hfE, hfam₀, hnT, hnC⟩ :=
    etaFamilyStored_descend hnotind hnotctor hf hfam
  obtain ⟨hlaw, hcoh⟩ :=
    hprev T cvT caps hfE hcape hres hfam₀ φ' us hlen
  refine ⟨?_, ?_⟩
  · intro ρ ts x hlents hfit hmem
    rw [hac, acvalWith_ne hnT] at hmem hfit
    rw [hac, acvalWith_ne hnC]
    exact hlaw ρ ts x hlents hfit hmem
  · refine hcoh.transport (fun cvC nPc nFc hf₂ => ?_)
      (fun cvC nPc nFc TCa hf hTCa => ?_) (by rw [hac, acvalWith_ne hnT])
      (fun _ _ _ => rfl)
    · rwa [ConLeche.Env.find?_cons, ite_eq_right (fun hh => hnC hh.symm)] at hf₂
    · rw [hac]
      exact denote_cons_mono hfresh _ 0
        (constsBound_instType mp.base2.wf
          (ConLeche.Env.find?_mem hf) us) hTCa

end ConLeche.Model

import Setlec.SetR.Interp2.InstallP
import Setlec.SetR.Interp2.NatStepP
import Setlec.SetR.Interp2.EmptyPin2

/-!
# The P capstone's shape (task #161, P4 — frozen early, per the ruling)

Two deliverables, both statement-sensitive and frozen here before the
harvest layer builds toward them:

* **the business end, proved now**: `no_constant_of_Empty_P` — an
  environment carrying the P invariant stores no constant of type
  `Empty`.  The membership is `mem_typeP` (the `denoteP` reading, bit
  numerals), the reading of `.const emptyName []` is the leaf by the
  `denoteP` constant clause, and the leaf's `interp2` value is the
  empty set by erasure injectivity at the constant constructor +
  `EnvS.empty_pinned` — the same three-move argument as
  `no_constant_of_Empty_2`, one currency over.
* **the final statement, frozen** (checked against the goal's letter —
  consistency of the checker on sort-annotated syntax, hypothesis
  minimal, the #16 precedent):

  `no_proof_of_Empty_P : ∀ (V) [SetTheory V] {μ}, μ.verified = true →
   ∀ {F ds env'}, checkDecls μ (fueledOps μ F) ds = .ok env' →
   ∀ c ∈ env'.consts, c.toConstantVal.type = .const emptyName [] →
   False`

  Input-level hypotheses ONLY: the accepted run, the stored constant,
  its type — plus the validating mode, which is part of the goal's
  letter (the annotated checker IS the verified mode; `--no-model`
  ignores annotations by design).  No residue hypotheses: the
  intermediate, `SemTierInputsP`-conditional form below is a
  *milestone shape*, never the close (the conditional-forms ruling).

`SemTierInputsP` names the remaining bill in ∀-environment form —
`TierInputsAtP`'s non-env-tier fields *less the literal tier*, which
landed (`Interp2/NatStepP.lean`) and the caps tier all but closed
(`Step2/CapsRowsP.lean`, `Interp2/CapsP.lean`); what remains is iota,
the proj/str install rows, and the one named caps residue
`StructUnitIrrelP`.  The harvest layer proves: accepted stream + `SemTierInputsP`
⇒ `Nonempty (EnvS2PM …)` at the final environment; this file's
`no_constant_of_Empty_P` then closes the capstone.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr EnvS)
open Setlec (CheckMode Env Expr Name Level ConstantInfo)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-! ## The Empty pin, at the core carrier -/

/-- The annotated `Empty` leaf is the pinned constant
(`acval_empty_pinned` at the denote2-free carrier). -/
theorem acval_empty_pinnedC (m : EnvS2Core V env) (ψ : Name → Nat) :
    ∃ u, m.acval emptyName ψ = .const .empty [u] := by
  obtain ⟨u, hu⟩ := m.base.empty_pinned ψ
  exact ⟨u, erase_eq_const (by rw [m.acval_erase, hu]; rfl)⟩

/-- …so its `interp2` reading is the empty set, at every
assignment. -/
theorem interp2_acval_emptyC (m : EnvS2Core V env)
    (ψ : Name → Nat) (ρ : Nat → V) :
    interp2 V ρ (m.acval emptyName ψ) = SetTheory.empty := by
  obtain ⟨u, hu⟩ := acval_empty_pinnedC m ψ
  rw [hu, interp2_const]
  rfl

/-- **The capstone's business end**: an environment carrying the P
invariant stores no constant of type `Empty` — the membership read
entirely at the validated-annotation tier (`mem_typeP` over
`denoteP`/`interp2`). -/
theorem no_constant_of_Empty_P (mp : EnvS2PM V μ env)
    (c : ConstantInfo) (hc : c ∈ env.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨ta, hta0⟩ := mp.type_reads c hc (fun _ => 0)
  have hta := hta0
  rw [hty] at hta
  cases hf : env.find? emptyName with
  | none => rw [denoteP, hf] at hta; exact nomatch hta
  | some ci =>
    by_cases hlen :
        ([] : List Level).length = ci.toConstantVal.levelParams.length
    · rw [denoteP_const hf hlen] at hta
      obtain rfl : ta = mp.base2.acval emptyName
          (Level.substFn (fun _ => 0)
            ci.toConstantVal.levelParams []) :=
        (Option.some.inj hta).symm
      have hmem := mp.mem_typeP c hc (fun _ => 0) _ hta0
        (fun _ => (SetTheory.empty : V))
      rw [interp2_acval_emptyC mp.base2] at hmem
      exact not_mem_empty _ hmem
    · rw [denoteP, hf] at hta
      dsimp only at hta
      rw [if_neg hlen] at hta
      exact nomatch hta

/-! ## The remaining bill, in ∀-environment form -/

/-- **The semantic-tier inputs** — `TierInputsAtP`'s non-env-tier
fields, ∀-environment: what the four semantic tiers discharge
(literal → caps → proj/str → iota).  The harvest layer's conditional
fold consumes this; the final capstone consumes nothing (the tiers
land as theorems). -/
structure SemTierInputsP (V : Type w) [SetTheory V] (μ : CheckMode) :
    Prop where
  /-- subject-side totality: whatever inference accepts, reads —
  the harvest layer's per-declaration readings (the primed forms),
  discharged with the proj/literal tiers' completion (`denoteP`'s
  fragment guards are the front door's acceptance guards) -/
  accepted_reads : ∀ {env : Env} (m : EnvS2Core V env)
    (φ : Name → Nat) {F d : Nat} {e t : Expr},
    Setlec.inferTypeCore μ env F d e = .ok t →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∃ ea, denoteP m.acval env φ d e = some ea
  /-- iota tier: the fired rule's reading -/
  iota_reads : ∀ {env : Env} (m : EnvS2Core V env) (φ : Name → Nat)
    (fuel : Nat), IotaReadsP μ m φ fuel
  /-- iota tier: the fired rule's row -/
  iota : ∀ {env : Env} (m : EnvS2Core V env) (φ : Name → Nat)
    (fuel : Nat), IotaStepP μ m φ fuel
  /-- proj/str install tier -/
  whnf_proj_reads : ∀ {env : Env} (m : EnvS2Core V env)
    (φ : Name → Nat) (fuel : Nat), WhnfCoreProjReadsP μ m φ fuel
  infer_proj_reads : ∀ {env : Env} (m : EnvS2Core V env)
    (φ : Name → Nat) (fuel : Nat), InferProjReadsP μ m φ fuel
  whnf_proj : ∀ {env : Env} (m : EnvS2Core V env) (φ : Name → Nat)
    (fuel : Nat), ProjStepP μ m φ fuel
  infer_proj : ∀ {env : Env} (m : EnvS2Core V env) (φ : Name → Nat)
    (fuel : Nat), InferProjStepP m μ φ fuel
  /- caps tier: NO entries.  All four capability rows left this
  census with the tier: `UnitIrrelPQ` (`unitIrrelPQ_of_claims`),
  `PairEtaIrrelP` (`pairEtaIrrelP_of_claims`), `StructEtaIrrelP`
  (`structEtaIrrelP_of_claims`, off the `EnvS2PM.caps_ok` field), and
  `StructUnitIrrelP` with the ratified one-premise repair of the unit
  half (`structUnitIrrelP_of_claims`): the caps tier is CLOSED. -/

/-- The env-fixed tier bundle, from the semantic inputs + the fold's
invariant + the one bespoke literal-tier fact (`nat_heads`, an install
product of the `Nat` basis — supplied by the fold at that install and
carried by `EnvS2PM`). -/
theorem TierInputsAtP.ofSem (hsem : SemTierInputsP V μ)
    (mp : EnvS2PM V μ env) (φ : Name → Nat) :
    TierInputsAtP V μ mp.base2 φ :=
  TierInputsAtP.ofEnvS2PM mp
    (fun fuel => hsem.iota_reads mp.base2 φ fuel)
    (fun fuel => hsem.whnf_proj_reads mp.base2 φ fuel)
    (fun fuel => hsem.infer_proj_reads mp.base2 φ fuel)
    (fun fuel => reduceNatReadsP_of mp.base2 φ fuel)
    (fun fuel => hsem.infer_proj mp.base2 φ fuel)
    (fun fuel => hsem.iota mp.base2 φ fuel)
    (fun fuel => hsem.whnf_proj mp.base2 φ fuel)
    (fun _fuel ihw => reduceNatStepP_of mp ihw)
    (fun _fuel ihw => reduceNatStepPQ_of mp ihw)

end Setlec.SetR.Interp2

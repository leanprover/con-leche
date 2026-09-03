import Setlec.SetP.InstallP
import Setlec.SetP.NatStepP
import Setlec.SetP.Step2.AcceptedP

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
  intermediate, install-tier-conditional form is a *milestone shape*,
  never the close (the conditional-forms ruling).

**The semantic bill is empty** (task #161, ENDGAME A).  This file used
to carry `SemTierInputsP`, the ∀-environment form of `TierInputsAtP`'s
non-env-tier fields.  The four semantic tiers emptied it — literal,
caps, the proj/str install rows, iota — and its last field,
`accepted_reads`, is now `acceptedReadsP_of`
(`Step2/AcceptedP.lean`): a syntactic totality walk over `inferBody`'s
clauses, where every `denoteP` failure mode is one of the front door's
own acceptance guards.  So the structure is deleted, and the harvest
layer proves: accepted stream ⇒ `Nonempty (EnvS2PM …)` at the final
environment, with only the *install-tier* bundles as premises; this
file's `no_constant_of_Empty_P` then closes the capstone.
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
(`acval_empty_pinned` at the denote2-free carrier).

**The pin is now a PREMISE** (task #161 S3): the core no longer
contains an `EnvS`, so `EnvS.empty_pinned` is not available from it.
The premise is stated in exactly the shape the census's §1.5 P-native
carrier field takes (`∀ ψ, ∃ u, cvalE emptyName ψ = emptyT u`), so S7
discharges it by projection when the field lands; until then the fold
layer supplies it from its v1 residue. -/
theorem acval_empty_pinnedC (m : EnvS2Core V env)
    (hpin : ∀ ψ : Name → Nat, ∃ u, m.cvalE emptyName ψ = emptyT u)
    (ψ : Name → Nat) :
    ∃ u, m.acval emptyName ψ = .const .empty [u] := by
  obtain ⟨u, hu⟩ := hpin ψ
  exact ⟨u, erase_eq_const (by rw [m.acval_erase, hu]; rfl)⟩

/-- …so its `interp2` reading is the empty set, at every
assignment. -/
theorem interp2_acval_emptyC (m : EnvS2Core V env)
    (hpin : ∀ ψ : Name → Nat, ∃ u, m.cvalE emptyName ψ = emptyT u)
    (ψ : Name → Nat) (ρ : Nat → V) :
    interp2 V ρ (m.acval emptyName ψ) = SetTheory.empty := by
  obtain ⟨u, hu⟩ := acval_empty_pinnedC m hpin ψ
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
      rw [interp2_acval_emptyC mp.base2 (fun ψ => by
        rw [show mp.base2.cvalE emptyName ψ = mp.base.cval emptyName ψ
              from mp.base_erase emptyName ψ]
        exact mp.base.empty_pinned ψ)] at hmem
      exact not_mem_empty _ hmem
    · rw [denoteP, hf] at hta
      dsimp only at hta
      rw [if_neg hlen] at hta
      exact nomatch hta

/-! ## The remaining bill: none

**`SemTierInputsP` is gone.**  The structure named `TierInputsAtP`'s
non-env-tier fields in ∀-environment form, and the four semantic tiers
emptied it one by one — literal (`Interp2/NatStepP.lean`), caps
(`Step2/CapsRowsP.lean`, `Interp2/CapsP.lean`), the proj/str install
rows (`Step2/StrLitP.lean`, `Step2/ReadsP.lean`,
`Step2/ProjRowsP.lean`) and iota (`Step2/IotaRowsP.lean`).  Its last
field, `accepted_reads`, is `acceptedReadsP_of`
(`Step2/AcceptedP.lean`), so the bundle has nothing left to carry and
is **deleted** rather than left as an empty structure: an empty
hypothesis is still a hypothesis in every downstream signature, and
the milestone capstone's census is read off those signatures. -/

/-- The env-fixed tier bundle, from the semantic inputs + the fold's
invariant + the one bespoke literal-tier fact (`nat_heads`, an install
product of the `Nat` basis — supplied by the fold at that install and
carried by `EnvS2PM`). -/
theorem TierInputsAtP.ofSem (mp : EnvS2PM V μ env) (φ : Name → Nat) :
    TierInputsAtP V μ mp.base2 φ :=
  TierInputsAtP.ofEnvS2PM mp
    (@fun _ _ _ _ h hw hb hL => acceptedReadsP_of mp.base2 φ h hw hb hL)
    (fun fuel => reduceNatReadsP_of mp.base2 (natOpGuardLawP_of mp) φ fuel)
    (fun _fuel ihw => reduceNatStepP_of mp ihw)
    (fun _fuel ihw => reduceNatStepPQ_of mp ihw)

end Setlec.SetR.Interp2

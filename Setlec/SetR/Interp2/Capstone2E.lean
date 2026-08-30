import Setlec.SetR.Interp2.Capstone2D

/-!
# `CheckStep2E`, assembled — generation six's capstone

The four quarters of statement generation six, joined, against
**exactly the fifteen residues generation five's capstone takes**.
No residue is added and none is retired.  That is the measurement, and
it is the finding: dual success is a *restatement* of the family, not
a reduction of its obligations.

## Two routes, and why both are recorded

**Route A (`checkStep2E_of_quarters`) — through the induction.**
`checkSound2D` already proves the `…2D` claims at every fuel from the
same fifteen residues, and `Claims2D → Claims2E` is free
(`Dual2E.lean`).  So the generation-six step follows **without using
its own induction hypotheses at all**: the four `…2E` premises of
`CheckStep2E` are discarded.  A step whose hypotheses are unused is
worth saying out loud — it is the precise sense in which generation
six's claims are a weakening of generation five's.

**Route B (`checkStep2E_of_quarters_routed`) — through the quarters.**
The four `…Step2E_of` quarters, each handed the existence factor
`Exists2E`.  At the capstone that factor is *not* a new residue: it is
`exists2E_of_checkStep2D` of the same fifteen.  Inside a single
quarter it would be, which is what the per-quarter signatures record.

The two routes prove the same statement; B is kept because it is the
one whose hypotheses are used, and A because it is the one that shows
what generation six costs.

## The capstone, re-pointed to `EnvS2U`

Both routes now conclude `CheckStep2E μ V` quantified over every
`EnvS2U`, and take their fifteen residues there too.  That is what
made `checkStep2U_of_2E`'s `EnvS2UInImage` residue drop out
(`Claims2U.lean`), and with it the pointwise residue the install keys
were carrying (`Keys2Cond.lean`'s `claims2U_of_2E`).

**What it costs, said out loud.**  The obligation did not vanish; it
moved.  Each of the fifteen is now demanded at *every* `EnvS2U`,
which is a strictly larger class than the `toU`-image of the
`EnvS2`s — so the residues became harder to discharge by exactly the
amount the claims seam became easier.  Seal 32's finding again: a
factorisation, not a localization.  Unexercised today, because none
of the fifteen is discharged in this tree and none of them reads an
existential field.

## What this does **not** establish

`Denote2Total` is not used here, and could not be: pricing `.app`
(the note in `Step2/InferQ.lean` above `inferStep2E_of`) found that it
supplies the annotation of a run's *subject* where all three of the
clause's missing annotations are a run's *result* or a *reduct*.  The
existence factor is discharged here by generation five's induction —
the same place the `…2D` claims' existential halves have always been
proved — and not by a localized law.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec (CheckMode Env Name)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **The existence factor is not a residue at the capstone.**
Generation five's induction supplies it at every fuel. -/
theorem exists2E_of_checkStep2D (hstep : CheckStep2D μ V)
    (env : Env) (m : EnvS2U V env) (φ : Name → Nat) (fuel : Nat) :
    Exists2E μ m φ fuel := by
  obtain ⟨hwc, hw, -, hi⟩ := checkSound2D hstep m φ fuel
  exact exists2E_of_claims2D hwc hw hi

/-- **The generation-six step, from the generation-five residues.**
Route A: the four `…2E` induction hypotheses are unused. -/
theorem checkStep2E_of_quarters
    (hwc : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat),
      Denote2Inst1B μ m.acval env φ)
    (hio : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), IotaStep2D μ m φ fuel)
    (hpj : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), ProjStep2D μ m φ fuel)
    (hrn : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), ReduceNatStep2D μ m φ fuel)
    (hdl : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat),
      Delta2B μ m φ)
    (hdd : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat),
      Denote2Delta2A μ m φ)
    (hrn2 : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), ReduceNat2D μ m φ fuel)
    (hpi : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), ProofIrrel2D μ m φ fuel)
    (hsp : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), DefEqSpine2D μ m φ fuel)
    (hsi : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), StuckIrrel2D μ m φ fuel)
    (hsl : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat),
      Denote2StrLit2A μ m φ)
    (hap : ∀ (env : Env) (m : EnvS2U V env), AcvalParams2 m)
    (hbs : ∀ (env : Env) (φ : Name → Nat) (fuel F : Nat),
      BinderSortAgree2A μ env φ fuel F)
    (hac : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), AppCongrStuck2D μ m φ fuel)
    (het : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), EtaCert2D μ m φ fuel)
    (hi : InferInputs2D V μ) :
    CheckStep2E μ V := by
  have hD : CheckStep2D μ V :=
    checkStep2D_of_quarters hwc hio hpj hrn hdl hdd hrn2 hpi hsp hsi
      hsl hap hbs hac het hi
  intro env m φ fuel _ _ _ _
  obtain ⟨d1, d2, d3, d4⟩ := checkSound2D hD m φ (fuel + 1)
  exact ⟨whnfCoreClaims2E_of_2D d1, whnfClaims2E_of_2D d2,
    defEqClaims2E_of_2D d3, inferClaims2E_of_2D d4⟩

/-- **The same step, through the four generation-six quarters.**
Route B: every hypothesis is used, and the existence factor the
quarters demand is supplied by `exists2E_of_checkStep2D` rather than
routed. -/
theorem checkStep2E_of_quarters_routed
    (hwc : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat),
      Denote2Inst1B μ m.acval env φ)
    (hio : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), IotaStep2D μ m φ fuel)
    (hpj : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), ProjStep2D μ m φ fuel)
    (hrn : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), ReduceNatStep2D μ m φ fuel)
    (hdl : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat),
      Delta2B μ m φ)
    (hdd : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat),
      Denote2Delta2A μ m φ)
    (hrn2 : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), ReduceNat2D μ m φ fuel)
    (hpi : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), ProofIrrel2D μ m φ fuel)
    (hsp : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), DefEqSpine2D μ m φ fuel)
    (hsi : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), StuckIrrel2D μ m φ fuel)
    (hsl : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat),
      Denote2StrLit2A μ m φ)
    (hap : ∀ (env : Env) (m : EnvS2U V env), AcvalParams2 m)
    (hbs : ∀ (env : Env) (φ : Name → Nat) (fuel F : Nat),
      BinderSortAgree2A μ env φ fuel F)
    (hac : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), AppCongrStuck2D μ m φ fuel)
    (het : ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat)
      (fuel : Nat), EtaCert2D μ m φ fuel)
    (hi : InferInputs2D V μ) :
    CheckStep2E μ V := by
  have hex := exists2E_of_checkStep2D
    (checkStep2D_of_quarters hwc hio hpj hrn hdl hdd hrn2 hpi hsp hsi
      hsl hap hbs hac het hi)
  exact checkStep2E_of (whnfCoreStep2E_of hex hwc hio hpj)
    (whnfStep2E_of hex hrn hdl)
    (defEqStep2E_of hex hdd hrn2 hpi hsp hsi hsl hap hbs hac het)
    (inferStep2E_of hex hi)

/-! ## The ledger beside `checkStep2D_of_quarters`

| | gen 5 | gen 6 |
|---|---|---|
| capstone residues | 15 | **15** |
| residues retired by the generation | — | **0** |
| residues added by the generation | — | **0** |
| claims that needed no restatement | — | 1 (defeq) |
| existence factors the *quarters* need | 0 | **3** |

Generation five's own note predicted the shape of this table for a
generation that changes one thing: *a residue that does not mention
the thing a generation changes cannot be affected by the change.*
Generation six changes where the annotations sit in the claims, and no
residue mentions that — so all fifteen pass through unchanged.  What
the table also says, and generation five's did not, is that **nothing
came off the list**: seal 29's "existence is localized" was the reason
to run the generation, and localization is the one thing it did not
buy. -/

end Setlec.SetR.Interp2

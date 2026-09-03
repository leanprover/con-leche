import Setlec.SetR.Bridge.DeclInd
import Setlec.SetR.DivModPin
import Setlec.SetR.Install.ReducePin
import Setlec.SetR.Install.BasisS
import Setlec.SetR.StdAxiomKey

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

theorem checkDeclR_sound
    {μ : CheckMode} {F : Nat}
    {env env₂ : Env} (m : EnvS V env) (hE : EtaFamiliesClosed env)
    {d : Declaration}
    (h : checkDecl μ (fueledOps μ F) env d = .ok env₂) :
    DeclR μ F m.cval env d env₂ :=
  checkDeclR_of
    (fun hh => declDefnR m hh)
    (fun hh => declThmR m hh)
    (fun hh => declOpaqueR m hh)
    (fun hh => declAxiomR m hh)
    (fun hh => declBasisR hh)
    -- the direct-structure path is compile-time disabled
    -- (`directStructsEnabled = false`), so `checkDecl`'s `indDecl`
    -- clause *is* `checkIndDecl`.  The `DeclR` relation records the
    -- modeled path only, and this is where that is discharged.
    (fun hh => declIndRS memberKeyS m hE (by
      simpa [checkDecl, directParts?_none] using hh)) h

/-- **The run half, from the checker** — the design census's **C3**
(task #161 S4).

`DeclRunR` (`SetBase/DeclRun.lean`) is `DeclR` with every derivation
conjunct deleted; this is `checkDeclR_sound` composed with the
projection, so the records stay single-sourced — nothing in `Bridge/*`
re-proves anything.

**Why it still takes `m`, and what would drop it.**  The projection's
*conclusion* names no valuation, but its route to the conclusion is the
bridge, and the bridge's per-kind proofs (`declDefnR` &c.,
`Bridge/Decl.lean`) build the guard and derivation conjuncts
interleaved.  A model-free `checkDeclRun_sound` is therefore a
re-factoring of `Bridge/Decl.lean`, not a re-statement — and it has, as
of S4, **no consumer**: every P call site holds an `EnvS` at the same
point anyway, for the v1 install round trip that `EnvS2PM.base`
carries (the S3 seal §2).  D6's house rule (never freeze a statement no
consumer has exercised) therefore puts the `m`-dropped skeleton in S5,
beside the residue removal that creates its first consumer. -/
theorem checkDeclRun_sound
    {μ : CheckMode} {F : Nat}
    {env env₂ : Env} (m : EnvS V env) (hE : EtaFamiliesClosed env)
    {d : Declaration}
    (h : checkDecl μ (fueledOps μ F) env d = .ok env₂) :
    DeclRunR μ F (DeclIndR μ F env m.cval) env d env₂ :=
  DeclR.toRun (checkDeclR_sound m hE h)

theorem foldlM_R
    {μ : CheckMode} {F : Nat}
     :
    ∀ (ds : List Declaration) (env : Env) {env' : Env},
      EnvSOk V env →
      ds.foldlM (checkDecl μ (fueledOps μ F)) env = .ok env' →
      EnvSOk V env'
  | [], _, _, hm, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hm
  | d :: ds, env, _, hm, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : checkDecl μ (fueledOps μ F) env d with
    | error e => rw [hd] at h; exact nomatch h
    | ok env1 =>
      rw [hd] at h
      obtain ⟨⟨m⟩, hE⟩ := hm
      exact foldlM_R ds env1
        (declStepS divModPinS reducePinS stdAxiomKeyS declBasisS
          (declIndS memberKeyS) m hE (checkDeclR_sound m hE hd)) h

end Setlec.SetR

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

/-- **The bridge's `m`-dropped skeleton — D6's S5 item.**

Five of the six declaration kinds bridge against `EnvR` alone (the
V-free invariant of `Bridge/Env.lean`); the sixth is a **premise**,
in the shape `declStepS` takes its five install obligations and
`declEtaStepRun` takes its η one.

**The measurement behind the shape** (task #161 S5, and it is a
finding): `Bridge/Decl.lean` never needed a model.  Ten signatures
there took `m : EnvS V env` and every one of them used it only through
`EnvS.toEnvR`; re-signing them to `EnvR env` cost **zero proof
edits**, so `declDefnR`/`declThmR`/`declOpaqueR`/`declAxiomR` and the
four pin bridges are now model-free outright, and `declBasisR` always
was.  The `indDecl` kind is the one that cannot follow, and the reason
is `Bridge/DeclInd.lean`'s **finding 8**, not the records:
`IndMembersR` carries a `ConstantValR` at *each intermediate
environment of the member fold*, and nothing builds an `EnvR` there
except by projection from the `EnvS` the install fold is producing —
so bridge and install have to walk together.  Freeing it needs an
`EnvR`-level cons for the block folds, which is the ind tier's own
de-basing, not this theorem's.

`checkDeclR_sound` below is this theorem's `EnvS` instance —
statement byte-unchanged, one source of truth. -/
theorem checkDeclR_ofEnvR
    {μ : CheckMode} {F : Nat}
    {env env₂ : Env} (mR : EnvR env)
    {d : Declaration}
    (hind : ∀ {block : List ConstantInfo} {envI : Env},
      checkIndDecl (m := CheckM) μ (fueledOps μ F) env block = .ok envI →
      DeclIndR μ F env mR.cval block envI)
    (h : checkDecl μ (fueledOps μ F) env d = .ok env₂) :
    DeclR μ F mR.cval env d env₂ :=
  checkDeclR_of
    (fun hh => declDefnR mR hh)
    (fun hh => declThmR mR hh)
    (fun hh => declOpaqueR mR hh)
    (fun hh => declAxiomR mR hh)
    (fun hh => declBasisR hh)
    -- the direct-structure path is compile-time disabled
    -- (`directStructsEnabled = false`), so `checkDecl`'s `indDecl`
    -- clause *is* `checkIndDecl`.  The `DeclR` relation records the
    -- modeled path only, and this is where that is discharged.
    (fun hh => hind (by simpa [checkDecl, directParts?_none] using hh)) h

theorem checkDeclR_sound
    {μ : CheckMode} {F : Nat}
    {env env₂ : Env} (m : EnvS V env) (hE : EtaFamiliesClosed env)
    {d : Declaration}
    (h : checkDecl μ (fueledOps μ F) env d = .ok env₂) :
    DeclR μ F m.cval env d env₂ :=
  checkDeclR_ofEnvR m.toEnvR (fun hh => declIndRS memberKeyS m hE hh) h

/-- **The run half, from the checker** — the design census's **C3**
(task #161 S4).

`DeclRunR` (`SetBase/DeclRun.lean`) is `DeclR` with every derivation
conjunct deleted; this is `checkDeclR_sound` composed with the
projection, so the records stay single-sourced — nothing in `Bridge/*`
re-proves anything.

**Why it still takes `m` — S5's measurement.**  S4 read the obstacle
as "the bridge's per-kind proofs build guard and derivation conjuncts
interleaved, so an `m`-dropped form is a re-factoring of
`Bridge/Decl.lean`".  Measured, that is **false of five kinds and true
of one**: `Bridge/Decl.lean` re-signed to `EnvR` with zero proof edits
(see `checkDeclR_ofEnvR` above), and what remains is `indDecl`'s
interleave with its install (`Bridge/DeclInd.lean`'s finding 8).  So
the `m` here is the *ind kind's* `m`, exactly, and it drops when the
ind tier de-bases — the same event that deletes `EnvS2PM.base`.  Until
then the skeleton is `checkDeclR_ofEnvR`, which has its consumer
(`checkDeclR_sound`) and needs no `EnvS` of its own. -/
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

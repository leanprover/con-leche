import Setlec.SetBase.Bridge.DeclInd
import Setlec.SetBase.Bridge.DeclRun

/-!
# The assembly (task #148, T6): the model-free half

`checkDecl` → `DeclR` by dispatch, off the V-free bridge invariant
alone.  **Task #161 S8 — the zero-opener**: S7 made the whole bridge
model-free (`checkDeclR_ofEnvRE`, which runs on an `EnvR` and whose
proof tree mentions no model), and the last P→R edge survived only
because this file still *sat* under `Setlec/SetR/`.  Killing it was a
MOVE, and this is it: the three model-free theorems below are
byte-unchanged from `Setlec/SetR/Bridge/Sound.lean`, and the collapsed
lane's own fold — `checkDeclR_sound` and `foldlM_R`, which carry the
`EnvS` invariant along the dispatch — stayed behind in that file,
which now imports this one.  (`checkDeclRun_sound` stayed behind too
until S11b's opener deleted it: consumer-free, and the S10 seal
measured its composition as a derivation route, not a projection.)

The three per-declaration bridge obligations that the collapsed fold
keeps as named hypotheses (the `Nat` equation certificates, the
div/mod pins, the reduce pins) are stated *attached* there, at their
own `m`'s valuation; nothing here mentions a valuation at all.
-/

namespace Setlec.SetR
open Setlec.TT Setlec.TTVerify SetTheory
universe w

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
V-free invariant of `SetBase/EnvR.lean`); the sixth is a **premise**,
in the shape `declStepS` takes its five install obligations and
`declEtaStepRun` takes its η one.

**The measurement behind the shape** (task #161 S5, and it is a
finding): `Bridge/Decl.lean` never needed a model.  Ten signatures
there took `m : EnvS V env` and every one of them used it only through
`EnvS.toEnvR`; re-signing them to `EnvR env` cost **zero proof
edits**, so `declDefnR`/`declThmR`/`declOpaqueR`/`declAxiomR` and the
four pin bridges are now model-free outright, and `declBasisR` always
was.  The `indDecl` kind is the one that could not follow at S5, and
the reason was `Bridge/DeclInd.lean`'s **finding 8**, not the records:
`IndMembersR` carries a `ConstantValR` at *each intermediate
environment of the member fold*, and nothing built an `EnvR` there
except by projection from the `EnvS` the install fold is producing —
so bridge and install had to walk together.  S6 and S7 supplied the
`EnvR`-level cons for the block folds (the ind tier's own de-basing),
which is what `checkDeclR_ofEnvRE` below cashes.

`checkDeclR_sound` (`SetR/Bridge/Sound.lean`) is this theorem's `EnvS`
instance — statement byte-unchanged, one source of truth. -/
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

/-- **The bridge, whole, from an `EnvR`** (task #161 S7): the ind
kind's premise of `checkDeclR_ofEnvR` is discharged by `declIndRR`,
so `checkDecl` bridges against the V-free invariant alone and
`Bridge/*` carries no model at all.

This is what Walls A and B bought.  S5 could only drop the `m` from
the five non-`ind` kinds because the ind bridge had to walk with its
install (finding 8); S6 freed the member and provisioning walks, S7
the recursor group's swap (`indRecsCoreR`) and the projection walk
(`projFnRR`).  `checkDeclR_sound` (`SetR/Bridge/Sound.lean`) is this
theorem's `EnvS` instance — statement byte-unchanged, one source of
truth.

**This is the theorem the graded lane's fold imports** (`SetP/FoldP.lean`,
through `EnvS2PM.toEnvR`), and its residence here rather than under
`Setlec/SetR/` is what takes the layering whitelist to zero. -/
theorem checkDeclR_ofEnvRE
    {μ : CheckMode} {F : Nat}
    {env env₂ : Env} (mR : EnvR env) (hE : EtaFamiliesClosed env)
    {d : Declaration}
    (h : checkDecl μ (fueledOps μ F) env d = .ok env₂) :
    DeclR μ F mR.cval env d env₂ :=
  checkDeclR_ofEnvR mR (fun hh => declIndRR mR hE hh) h

/-- **The RUN bridge, whole, from an `EnvR`** (task #161 S11a): the
run/guard record, from the checker, with **no derivation on the path
except through the `ind` kind's premise**.

This is `checkDeclR_ofEnvRE`'s run twin and the theorem the graded
lane's fold now imports.  The difference is not cosmetic and is the
batch's whole point (the S10 seal's residual B): the deleted
`checkDeclRun_sound` — `DeclR.toRun` composed *after*
`checkDeclR_sound` — projected the derivation conjuncts away in its
*statement* while keeping them in its *proof term*, so the P lane
inherited `Red.beta` for a record it never reads.  Here the five
non-`ind` kinds never build one
(`checkDeclRun_of`, `SetBase/Bridge/DeclRun.lean`), and the sixth
enters through `declIndRR` alone — one named door, in the parameter
slot S4 built for it, which S11b replaces with the `ind` run bridge.

The collapsed lane's projection route (`checkDeclRun_sound`) is gone:
S11b's opener deleted it, consumer-free. -/
theorem checkDeclRun_ofEnvRE
    {μ : CheckMode} {F : Nat}
    {env env₂ : Env} (mR : EnvR env) (hE : EtaFamiliesClosed env)
    {d : Declaration}
    (h : checkDecl μ (fueledOps μ F) env d = .ok env₂) :
    DeclRunR μ F (DeclIndR μ F env mR.cval) env d env₂ :=
  checkDeclRun_of
    -- the direct-structure path is compile-time disabled
    -- (`directStructsEnabled = false`), so `checkDecl`'s `indDecl`
    -- clause *is* `checkIndDecl` — `directParts?_none` again.
    (fun hh => declIndRR mR hE
      (by simpa [checkDecl, directParts?_none] using hh)) h

end Setlec.SetR

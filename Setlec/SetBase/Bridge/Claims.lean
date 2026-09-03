import Setlec.SetBase.EnvR

/-!
# `CheckStepR`: the bridge's fuel-induction claims (task #148, T3)

The transpose of `Setlec/TTVerify/Claims.lean` (itself the transpose of
`Setlec/Model/Core/Claims.lean`) onto the mode-indexed relation family
of `Setlec/SetR/Rel.lean`.  Reduction, definitional equality and
inference are mutually recursive on a shared fuel — the beta rule
certifies redexes by inference plus defeq — so the bridge is one mutual
fuel induction, exactly as on both existing lanes.

The transposition rule is a *directed* one:

| set model | TT lane | here |
|---|---|---|
| `interpExpr e' = interpExpr e` | `Deq Δ ⟦e⟧ ⟦e'⟧` | `Red μ Δ ⟦e⟧ ⟦e'⟧` |
| `va = vb` (defeq) | `Deq Δ ⟦a⟧ ⟦b⟧` | `DefEq μ Δ ⟦a⟧ ⟦b⟧` |
| `v ∈ˢ tv` (infer) | `HasType Δ ⟦e⟧ ⟦t⟧` | `∃ T', Infer μ Δ ⟦e⟧ T' ∧ DefEq μ Δ T' ⟦t⟧` |
| `FvarsOk … ρ e` | `CtxOk … Δ e` | `CtxOkR … Δ e` |
| `AnnotOk …` | nothing | nothing |

Two rows carry the design decisions.

**The reduction claims are directed.**  The relation family's `Red` is
the checker's *reduction*, not a symmetric equation, so the claims say
"the reduct is reachable from the subject", in that order.  Nothing is
lost: `DefEq.ofRed` (D4) turns a reduction into an equation wherever a
`Deq` was wanted, and `DefEq.symm` (D2) supplies the other orientation.
The gain is that the ι/β/ζ/proj clauses can *be* their rules rather
than be equations that happen to hold.

**The inference claim is stated up to `DefEq`** — the campaign design's
§0 decision 1, "slack in the bridge, not conv in the relation".  The
family keeps a plain `Infer.bvar` rule (`Δ[i]? = some A → …`), so a
binder congruence — which opens each side's body with *its own*
annotation while only one denotation can sit in `Δ` — cannot be served
by an on-the-nose inference claim.  What serves it is the pair form
`∃ T', Infer … v T' ∧ DefEq … T' ⟦t⟧`: every checker certificate is an
infer+defeq *pair*, every premise of the relation is such a pair, and
the slack is absorbed by `DefEq.trans` at each consumption site.
`CtxOkR`'s leaf package (`Setlec/SetBase/CtxOkR.lean`) has exactly this
shape, and `CtxOkR.openWith` takes the new head's package in it.

**Definedness of the denotation replaces truthfulness** (the TT lane's
observation, inherited): `denote` is `Option`-valued because it reads
arbitrary `Expr`s, so the reduction claims are conditional on the
subject denoting, and the inference claim — the one that establishes
definedness — asserts it outright.

## What the bridge absorbs

Fuel, the `Except` monad, the reduction *strategy* (which side to
unfold, in which order), and the four checker features that contribute
zero rules — delta (`denote_delta_step`: the reduct denotes
*identically*), `Nat`-literal packing, `litToCtorIfNat`, and the
whnf/defeq loop structure (`Red.trans` chaining).  The executable
descent (`Setlec/Verify/Disc*`, `BridgeS*`, `CheckerF`) is **inherited
unchanged**: these claims are stated over the same pure knot today's
`Model/Core` and `TTVerify` claims quantify.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify

variable {mode : CheckMode} {env : Env}

/-! ## The four claims

Stated at a generic `mode`, with the relation's mode index `μ` taken to
be that same mode.  The relation family is the **set-mode** certificate
inventory (premise-exactness, design §0), and the seven `mode.ttChecks`
certificates of task #147 are extra facts a `.ttModel` run happens to
establish: the inversions hand them back as
`mode.ttChecks = true → conjunct` implications, which the bridge simply
does not consume.  So a run at *any* mode yields a derivation, and
fixing `mode := .setModel` would be a gratuitous restriction. -/

/-- Head normalization (no delta) is a reduction of the denotation.
Transpose of `WhnfCoreClaimsTT`. -/
def WhnfCoreClaimsR (mode : CheckMode) {env : Env} (m : EnvR env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δ : List VExpr},
    whnfCore mode env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOkR mode m.cval env φ d Δ e →
    ∀ {v : VExpr}, denote m.cval env φ d e = some v →
      ∃ v', denote m.cval env φ d e' = some v' ∧
        Red mode env m.cval φ Δ v v'

/-- The reduction loop, ditto.  Transpose of `WhnfClaimsTT`. -/
def WhnfClaimsR (mode : CheckMode) {env : Env} (m : EnvR env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δ : List VExpr},
    whnf mode env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOkR mode m.cval env φ d Δ e →
    ∀ {v : VExpr}, denote m.cval env φ d e = some v →
      ∃ v', denote m.cval env φ d e' = some v' ∧
        Red mode env m.cval φ Δ v v'

/-- A positive definitional-equality verdict yields a `DefEq`
derivation.  Transpose of `DefEqClaimsTT`. -/
def DefEqClaimsR (mode : CheckMode) {env : Env} (m : EnvR env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δ : List VExpr},
    isDefEqCore mode env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOkR mode m.cval env φ d Δ a → CtxOkR mode m.cval env φ d Δ b →
    ∀ {va vb : VExpr}, denote m.cval env φ d a = some va →
      denote m.cval env φ d b = some vb → DefEq mode env m.cval φ Δ va vb

/-- Successful inference yields an `Infer` derivation **up to `DefEq`**
(design §0 decision 1; see the module docstring).  Transpose of
`InferClaimsTT`. -/
def InferClaimsR (mode : CheckMode) {env : Env} (m : EnvR env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {Δ : List VExpr},
    inferTypeCore mode env fuel d e = .ok t →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOkR mode m.cval env φ d Δ e →
    ∃ v tv, denote m.cval env φ d e = some v ∧
      denote m.cval env φ d t = some tv ∧
      ∃ T', Infer mode env m.cval φ Δ v T' ∧
        DefEq mode env m.cval φ Δ T' tv

/-! ## The induction

`checkSoundR` is the transpose of `checkSoundTT`.  Its `zero` case is
proved here (every fuel-zero spelling throws, so every claim is
vacuous); its `succ` case is the clause-by-clause work of the batches,
and is taken as the hypothesis `CheckStepR`. -/

/-- The step of the mutual fuel induction: the four claims at `fuel + 1`
from the four claims at `fuel`. -/
def CheckStepR (mode : CheckMode) : Prop :=
  ∀ (env : Env) (m : EnvR env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaimsR mode m φ fuel → WhnfClaimsR mode m φ fuel →
    DefEqClaimsR mode m φ fuel → InferClaimsR mode m φ fuel →
    WhnfCoreClaimsR mode m φ (fuel + 1) ∧ WhnfClaimsR mode m φ (fuel + 1) ∧
      DefEqClaimsR mode m φ (fuel + 1) ∧ InferClaimsR mode m φ (fuel + 1)

/-- The mutual bridge induction.  Transpose of `checkSoundTT`; only the
step is outstanding. -/
theorem checkSoundR {env : Env} (hstep : CheckStepR mode) (m : EnvR env)
    (φ : Name → Nat) :
    ∀ fuel : Nat, WhnfCoreClaimsR mode m φ fuel ∧ WhnfClaimsR mode m φ fuel ∧
      DefEqClaimsR mode m φ fuel ∧ InferClaimsR mode m φ fuel := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro d e e' Δ h
      rw [whnfCore_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
    · intro d e e' Δ h
      rw [whnf_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
    · intro d a b Δ h
      rw [isDefEqCore_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
    · intro d e t Δ h
      rw [inferTypeCore_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ fuel ih =>
    obtain ⟨ihwc, ihw, ihd, ihi⟩ := ih
    exact hstep env m φ fuel ihwc ihw ihd ihi

/-! ## Fuel-generic wrappers

The forms every consumer uses; transposes of the `*_soundTT` /
`*_factsTT` wrappers, and of `Setlec/Model/TypeChecker.lean`'s
`*_facts` / `*_sound`. -/

/-- Successful inference is bridged: the subject denotes, its inferred
type denotes, and the first has an `Infer` derivation of a type `DefEq`
to the second. -/
theorem inferTypeCore_bridge {env : Env} (hstep : CheckStepR mode)
    (m : EnvR env) (φ : Name → Nat) (fuel : Nat) {d : Nat} {e t : Expr}
    {Δ : List VExpr} (h : inferTypeCore mode env fuel d e = .ok t)
    (hws : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e) (hΔ : CtxOkR mode m.cval env φ d Δ e) :
    ∃ v tv, denote m.cval env φ d e = some v ∧
      denote m.cval env φ d t = some tv ∧
      ∃ T', Infer mode env m.cval φ Δ v T' ∧
        DefEq mode env m.cval φ Δ T' tv :=
  (checkSoundR hstep m φ fuel).2.2.2 h hws hb hLb hΔ

/-- A positive definitional-equality verdict is bridged. -/
theorem isDefEqCore_bridge {env : Env} (hstep : CheckStepR mode)
    (m : EnvR env) (φ : Name → Nat) (fuel : Nat) {d : Nat} {a b : Expr}
    {Δ : List VExpr} (h : isDefEqCore mode env fuel d a b = .ok true)
    (hwa : Expr.WScoped d a) (hba : a.looseBVarsBounded 0 = true)
    (hLa : Expr.LeavesBounded a)
    (hwb : Expr.WScoped d b) (hbb : b.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded b)
    (hΔa : CtxOkR mode m.cval env φ d Δ a)
    (hΔb : CtxOkR mode m.cval env φ d Δ b)
    {va vb : VExpr} (hva : denote m.cval env φ d a = some va)
    (hvb : denote m.cval env φ d b = some vb) :
    DefEq mode env m.cval φ Δ va vb :=
  (checkSoundR hstep m φ fuel).2.2.1 h hwa hba hLa hwb hbb hLb hΔa hΔb
    hva hvb

/-- The reduction loop is bridged: the reduct denotes and the subject
`Red`uces to it. -/
theorem whnf_bridge {env : Env} (hstep : CheckStepR mode) (m : EnvR env)
    (φ : Name → Nat) (fuel : Nat) {d : Nat} {e e' : Expr}
    {Δ : List VExpr} (h : whnf mode env fuel d e = .ok e')
    (hws : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e) (hΔ : CtxOkR mode m.cval env φ d Δ e)
    {v : VExpr} (hv : denote m.cval env φ d e = some v) :
    ∃ v', denote m.cval env φ d e' = some v' ∧
      Red mode env m.cval φ Δ v v' :=
  (checkSoundR hstep m φ fuel).2.1 h hws hb hLb hΔ hv

/-! ## Frame-condition packages

Every clause recurses into subterms and into the types it inferred for
them, so both need their four frame conditions.  Bundled once, as the
TT lane bundles them (`frame_infer`, `whnfCore_package`). -/

/-- The frame conditions of an inferred type. -/
theorem frame_inferR {cval : TConstVal} {φ : Name → Nat}
    (hwf : EnvWF env) {fuel d : Nat} {Δ : List VExpr} {e t : Expr}
    (h : inferTypeCore mode env fuel d e = .ok t)
    (hws : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e) (hC : CtxOkR mode cval env φ d Δ e) :
    Expr.WScoped d t ∧ t.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded t ∧ CtxOkR mode cval env φ d Δ t :=
  ⟨inferTypeCore_WScoped hwf fuel h hws,
    inferTypeCore_looseBVars hwf fuel h hws hb hLb,
    fun l hl => hLb l (inferTypeCore_fvarLeaves hwf fuel h hws l hl),
    CtxOkR.of_subset (inferTypeCore_fvarLeaves hwf fuel h hws) hC⟩

/-- The frame conditions of a `whnfCore` reduct, with its denotation and
the reduction to it. -/
theorem whnfCore_packageR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel d : Nat} {Δ : List VExpr} {a a' : Expr} {va : VExpr}
    (ihwc : WhnfCoreClaimsR mode m φ fuel)
    (hw : whnfCore mode env fuel d a = .ok a')
    (hws : Expr.WScoped d a) (hb : a.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded a) (hC : CtxOkR mode m.cval env φ d Δ a)
    (hva : denote m.cval env φ d a = some va) :
    ∃ va', denote m.cval env φ d a' = some va' ∧
      Red mode env m.cval φ Δ va va' ∧
      Expr.WScoped d a' ∧ a'.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded a' ∧ CtxOkR mode m.cval env φ d Δ a' := by
  obtain ⟨va', hva', hD⟩ := ihwc hw hws hb hLb hC hva
  exact ⟨va', hva', hD, whnfCore_WScoped m.wf fuel hw hws,
    whnfCore_looseBVars m.wf fuel hw hb,
    fun l hl => hLb l (whnfCore_fvarLeaves m.wf fuel hw l hl),
    CtxOkR.of_subset (whnfCore_fvarLeaves m.wf fuel hw) hC⟩

/-- The same package for the reduction loop. -/
theorem whnf_packageR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel d : Nat} {Δ : List VExpr} {a a' : Expr} {va : VExpr}
    (ihw : WhnfClaimsR mode m φ fuel)
    (hw : whnf mode env fuel d a = .ok a')
    (hws : Expr.WScoped d a) (hb : a.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded a) (hC : CtxOkR mode m.cval env φ d Δ a)
    (hva : denote m.cval env φ d a = some va) :
    ∃ va', denote m.cval env φ d a' = some va' ∧
      Red mode env m.cval φ Δ va va' ∧
      Expr.WScoped d a' ∧ a'.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded a' ∧ CtxOkR mode m.cval env φ d Δ a' := by
  obtain ⟨va', hva', hD⟩ := ihw hw hws hb hLb hC hva
  exact ⟨va', hva', hD, whnf_WScoped m.wf fuel hw hws,
    whnf_looseBVars m.wf fuel hw hb,
    fun l hl => hLb l (whnf_fvarLeaves m.wf fuel hw l hl),
    CtxOkR.of_subset (whnf_fvarLeaves m.wf fuel hw) hC⟩

end Setlec.SetR

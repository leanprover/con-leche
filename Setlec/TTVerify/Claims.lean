import Setlec.TTVerify.EnvTT
import Setlec.TTVerify.Inversion
import Setlec.TTVerify.Inst
import Setlec.TTVerify.HasTypeSubst
import Setlec.Verify.Leaves
import Setlec.Verify.InferLeaves
import Setlec.TT.Deq
import Setlec.Verify.Knot

/-!
# The fuel-induction claims

The transpose of `Setlec/Model/Core/Claims.lean` and
`Setlec/Model/TypeChecker.lean`.  Reduction, definitional equality and
inference are mutually recursive on a shared fuel — the beta rule
certifies redexes by inference plus defeq — so their soundness is one
mutual fuel induction, exactly as on the set-model side.

The transposition rule is the one from `Setlec/TTVerify/EnvTT.lean`:
**an equation between interpretations becomes a `Setlec.TT.Deq` between
denotations, and a membership becomes a `HasType` derivation.**
Concretely

| set model | here |
|---|---|
| `interpExpr e' = interpExpr e` | `Deq Δ ⟦e'⟧ ⟦e⟧` |
| `va = vb` (defeq) | `Deq Δ ⟦a⟧ ⟦b⟧` |
| `v ∈ˢ tv` (infer) | `HasType Δ ⟦e⟧ ⟦t⟧` |
| `FvarsOk … ρ e` | `CtxOk … Δ e` |
| `AnnotOk …` | **nothing** |

Two differences are worth reading off that table.

**`AnnotOk` is gone from every claim.**  On the set-model side it is a
hypothesis of the whnf/defeq claims and a *conclusion* of the infer
claim (task #100 stage 6, replacing the deleted annotation pass).  Here
there is nothing to carry: a derivation supplies at each binder what
`AnnotOk` was reconstructing, so the infer claim's conclusion is just
the typing, and the whnf claims lose two hypotheses and a conjunct.

**Definedness of the denotation replaces truthfulness.**  `denote` is
`Option`-valued, like `interpExpr` and unlike the layer's own total
`interp`, because it reads arbitrary `Expr`s.  So the reduction claims
are stated *conditionally on the subject denoting* — "if the input
denotes, the output denotes and the two are `Deq`" — which is the
partial-function form of `interpExpr e' = interpExpr e`.  The infer
claim, being the one that establishes definedness, asserts it outright.

## WITHDRAWN: the threaded typing hypothesis

An earlier revision of this file threaded a typing hypothesis through
the reduction and defeq claims, on the argument that doing so was the
path to removing the checker's per-argument re-check in `inferSpineI`
(task #124 — 98.6 % of the certificate tax,
`Setlec/TTVerify/DESIGN.md` §6).  **The threading is withdrawn**: it
cannot serve that purpose, for a structural reason, and it serves no
other.  The claims below are certificate-only, mirroring
`Setlec/Model/Core/Claims.lean` exactly.

The full argument is in `Setlec/TTVerify/DESIGN.md` §6, "Why the
certificates are structural".  In one paragraph:

> `HasType.app` — the only rule with an `.app` conclusion, up to
> `conv` — demands the argument at **the domain of the function type
> used in that application**, which the induction hypothesis for `f`
> fixes to be the checker's inferred `⟦A⟧`.  An ambient typing
> hypothesis yields, by inversion, the argument at *some* domain `A₀`
> of *some* pi type of `⟦f⟧`, and bridging `A₀` to `⟦A⟧` means
> descending a `Deq` between pi types into the domain —
> Π-domain-injectivity, which `propext` refutes.  The official
> kernel's own justification for `infer_only` is *subject reduction*,
> and this layer refutes that too, by design (§2.4's premise-free
> equations).  So the fact has to be re-established at the node, which
> is what the certificate does.

Two consequences worth stating here rather than only in DESIGN.

**The certificates are not an artifact of this bridge's shape.**  They
are forced by the combination of premise-free equations (equations
carry no typing) and premises stated at annotations rather than at
ambient types.  Every reduction rule's typing premise must be supplied
where the rule fires; no invariant carried from above can substitute.

**So a typing hypothesis would only weaken the claims for nothing.**
It costs an obligation at every recursive call — `whnfCore` recursing
into an application's head would have to hand that head a typing — and
buys no clause its premise.  Certificate-only is the mirror, and here
it is also the ceiling.
## Status (task #119 stage 2)

This module states the claims, proves the **fuel-zero** case of the
mutual induction outright, and assembles the induction from four
per-level step hypotheses.  Those four steps — the `succ` case, i.e.
the clause-by-clause mirror of `Setlec/Model/Core/{Whnf,DefEq,Infer,
Iota,…}.lean` — are the remaining work of stage 2 and are named `Prop`s
here for the same reason `CheckDeclTT` is one: so that every consumer
of an unproved step is visible in the source rather than in a comment.
-/

namespace Setlec.TTVerify

open Setlec.TT

variable {V : Type u}

/-! ## The context correspondence

The transpose of `FvarsOk`.  `FvarsOk` constrains the free-variable
*valuation* `ρ`; there is no valuation here (see
`Setlec/TTVerify/Denote.lean`), so what it constrains instead is the de
Bruijn context `Δ`.

The index arithmetic is the whole content: an `fvar` opened at depth
`i` sits at de Bruijn *level* `i`, hence at index `d - 1 - i` when read
at depth `d`, and `HasType.bvar` types `.bvar j` at `Δ[j]` lifted by
`j + 1`.  With `j = d - 1 - i` and `i < d` that lift is by `d - i`.

**A membership transposes to a *typing*, not to an identity**
(`Setlec/TTVerify/DESIGN.md` §12.10, third instance).  `FvarsOk`'s
clause is `ρ l.1 ∈ˢ T` — the variable *inhabits* its annotation — and
the first transposition wrote it as the identity `Δ[j]? = some A ∧
denote l.2.2 = some (A.liftN (d - l.1))`, which is what a membership
looks like when the model's equalities are honest identities of
values.  Here they are not: a `Deq` is a derivable equation, and the
clause has to survive one.

The place it does not is the binder congruences.  `defeqStep` compares
`.lam n₁ ty₁ b₁` with `.lam n₂ ty₂ b₂` by certifying `ty₁ ≡ ty₂` and
then opening **each body with its own annotation** — the reference
kernels open both with one local, ours keeps both — so the two opened
bodies have leaves `(d, n₁, ty₁)` and `(d, n₂, ty₂)` whose denotations
are only *definitionally* equal.  Under the identity form no single
`Δ` satisfies `CtxOk` for both, and `DefEqClaimsTT` demands one; under
the typing form the second side is the first plus `HasType.conv`,
which is exactly the move the checker's own certificate licenses.

The identity form was never *needed*: its one consumer,
`infer_fvar_claim`, wanted a typing and built it on the spot. -/
def CtxOk (cval : TConstVal) (env : Env) (φ : Name → Nat) (d : Nat)
    (Δ : List VExpr) (e : Expr) : Prop :=
  Δ.length = d ∧
  ∀ l ∈ e.fvarLeaves, l.1 < d ∧ Expr.fvarsBelow l.1 l.2.2 ∧
    ∃ T, denote cval env φ d l.2.2 = some T ∧
      HasType Δ (.bvar (d - 1 - l.1)) T

/-- At depth `0` the context is empty and there are no leaves to
constrain — the shape every declaration-level statement uses. -/
theorem CtxOk.nil {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {e : Expr} (h : e.fvarLeaves = []) : CtxOk cval env φ 0 [] e := by
  refine ⟨rfl, ?_⟩
  intro l hl
  rw [h] at hl
  exact nomatch hl

/-- **Opening a binder extends the context correspondence.**  Every
binder clause of `CheckStepTT` needs exactly this, and it is where
`denote_lift` earns its keep: an old leaf's annotation, denoted one
level deeper, is its old denotation lifted by one
(`denote_weaken_top`), which is precisely the extra `liftN` that
`Δ`'s new entry shifts every old index by.  The freshly opened
variable is the new head of `Δ`, at index `0`.

Note that `denote_weaken_top` is applied to the *annotations*, which is
why `CtxOk` demands them scoped below their own variable's index —
`WScoped`'s own condition on an `fvar` leaf, and what the checker's
scope guards establish. -/
theorem CtxOk.open {cval : TConstVal} {env : Env} {φ : Name → Nat}
    (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {d : Nat} {Δ : List VExpr} {body ty : Expr} {n : Name} {A : VExpr}
    (hb : CtxOk cval env φ d Δ body) (ht : CtxOk cval env φ d Δ ty)
    (hty : denote cval env φ d ty = some A)
    (htyb : Expr.fvarsBelow d ty) :
    CtxOk cval env φ (d + 1) (A :: Δ) (body.instantiate1 (.fvar d n ty)) := by
  -- an already-present leaf: index unchanged, slot shifted by `Δ`'s new
  -- head, annotation one lift deeper
  have shift : ∀ l : Nat × Name × Expr, l.1 < d → Expr.fvarsBelow l.1 l.2.2 →
      ∀ T, denote cval env φ d l.2.2 = some T →
        HasType Δ (.bvar (d - 1 - l.1)) T →
        l.1 < d + 1 ∧ Expr.fvarsBelow l.1 l.2.2 ∧
          ∃ S, denote cval env φ (d + 1) l.2.2 = some S ∧
            HasType (A :: Δ) (.bvar (d + 1 - 1 - l.1)) S := by
    intro l hlt hfb T hden hT
    refine ⟨by omega, hfb, T.liftN 1, ?_, ?_⟩
    · rw [denote_weaken_top hcl (Expr.fvarsBelow_mono (by omega) hfb), hden]
      rfl
    · have := hT.weakenHead A
      rw [show d + 1 - 1 - l.1 = (d - 1 - l.1) + 1 from by omega]
      simpa [VExpr.lift] using this
  refine ⟨by simp [hb.1], ?_⟩
  intro l hl
  rcases Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
  · obtain ⟨hlt, hfb, T, hden, hT⟩ := hb.2 l hl'
    exact shift l hlt hfb T hden hT
  · -- a leaf of the opened variable: either the variable itself (the
    -- new head of `Δ`, at index `0`) or one of its annotation's own
    -- leaves, which is an already-present leaf
    rw [Expr.fvarLeaves] at hl'
    rcases List.mem_cons.mp hl' with rfl | hl''
    · refine ⟨by omega, htyb, A.liftN 1, ?_, ?_⟩
      · rw [denote_weaken_top hcl htyb, hty]
        rfl
      · have := HasType.bvar (Γ := A :: Δ) (i := 0) (A := A) (by simp)
        rw [show d + 1 - 1 - d = 0 from by omega]
        exact this
    · obtain ⟨hlt, hfb, T, hden, hT⟩ := ht.2 l hl''
      exact shift l hlt hfb T hden hT

/-! ## The four claims -/

variable (m : EnvTT env) (φ : Name → Nat)

/-- Head normalization (no delta) preserves the denotation up to a
derivable equation.  Transpose of `WhnfCoreClaims`. -/
def WhnfCoreClaimsTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δ : List VExpr},
    whnfCore env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOk m.cval env φ d Δ e →
    ∀ {v : VExpr}, denote m.cval env φ d e = some v →
      ∃ v', denote m.cval env φ d e' = some v' ∧ Deq Δ v v'

/-- The reduction loop, ditto.  Transpose of `WhnfClaims`. -/
def WhnfClaimsTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δ : List VExpr},
    whnf env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOk m.cval env φ d Δ e →
    ∀ {v : VExpr}, denote m.cval env φ d e = some v →
      ∃ v', denote m.cval env φ d e' = some v' ∧ Deq Δ v v'

/-- A positive definitional-equality verdict yields a derivable
equation.  Transpose of `DefEqClaims`. -/
def DefEqClaimsTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δ : List VExpr},
    isDefEqCore env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOk m.cval env φ d Δ a → CtxOk m.cval env φ d Δ b →
    ∀ {va vb : VExpr}, denote m.cval env φ d a = some va →
      denote m.cval env φ d b = some vb → Deq Δ va vb

/-- Successful inference yields a typing derivation.  Transpose of
`InferClaims` — note that the set-model version's `AnnotOk` conjuncts
have no counterpart, so this is the whole of it. -/
def InferClaimsTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {Δ : List VExpr},
    inferTypeCore env fuel d e = .ok t →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOk m.cval env φ d Δ e →
    ∃ v tv, denote m.cval env φ d e = some v ∧
      denote m.cval env φ d t = some tv ∧ HasType Δ v tv

/-! ## The induction

`checkSoundTT` below is the transpose of `check_sound`.  Its `zero`
case is proved here (every fuel-zero spelling throws, so every claim is
vacuous); its `succ` case is the clause-by-clause work of stage 2, and
is taken as the hypothesis `CheckStepTT`. -/

/-- The step of the mutual fuel induction: the four claims at `fuel + 1`
from the four claims at `fuel`.  This is the transpose of the four
`*_claims` lemmas of `Setlec/Model/Core/*`, and it is what stage 2 of
task #119 discharges. -/
def CheckStepTT : Prop :=
  ∀ (env : Env) (m : EnvTT env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaimsTT m φ fuel → WhnfClaimsTT m φ fuel →
    DefEqClaimsTT m φ fuel → InferClaimsTT m φ fuel →
    WhnfCoreClaimsTT m φ (fuel + 1) ∧ WhnfClaimsTT m φ (fuel + 1) ∧
      DefEqClaimsTT m φ (fuel + 1) ∧ InferClaimsTT m φ (fuel + 1)

/-- The mutual soundness induction.  Transpose of `check_sound`; only
the step is outstanding. -/
theorem checkSoundTT {env : Env} (hstep : CheckStepTT) (m : EnvTT env)
    (φ : Name → Nat) :
    ∀ fuel : Nat, WhnfCoreClaimsTT m φ fuel ∧ WhnfClaimsTT m φ fuel ∧
      DefEqClaimsTT m φ fuel ∧ InferClaimsTT m φ fuel := by
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

The forms every consumer uses; transposes of the `*_facts` / `*_sound`
wrappers at the end of `Setlec/Model/TypeChecker.lean`. -/

/-- Successful inference is sound: the subject denotes, its inferred
type denotes, and the first has a derivation of the second. -/
theorem inferTypeCore_soundTT {env : Env} (hstep : CheckStepTT)
    (m : EnvTT env) (φ : Name → Nat) (fuel : Nat) {d : Nat} {e t : Expr}
    {Δ : List VExpr} (h : inferTypeCore env fuel d e = .ok t)
    (hws : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e) (hΔ : CtxOk m.cval env φ d Δ e) :
    ∃ v tv, denote m.cval env φ d e = some v ∧
      denote m.cval env φ d t = some tv ∧ HasType Δ v tv :=
  (checkSoundTT hstep m φ fuel).2.2.2 h hws hb hLb hΔ

/-- A positive definitional-equality verdict identifies denotations up
to a derivable equation. -/
theorem isDefEqCore_soundTT {env : Env} (hstep : CheckStepTT)
    (m : EnvTT env) (φ : Name → Nat) (fuel : Nat) {d : Nat} {a b : Expr}
    {Δ : List VExpr} (h : isDefEqCore env fuel d a b = .ok true)
    (hwa : Expr.WScoped d a) (hba : a.looseBVarsBounded 0 = true)
    (hLa : Expr.LeavesBounded a)
    (hwb : Expr.WScoped d b) (hbb : b.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded b)
    (hΔa : CtxOk m.cval env φ d Δ a) (hΔb : CtxOk m.cval env φ d Δ b)
    {va vb : VExpr} (hva : denote m.cval env φ d a = some va)
    (hvb : denote m.cval env φ d b = some vb) : Deq Δ va vb :=
  (checkSoundTT hstep m φ fuel).2.2.1 h hwa hba hLa hwb hbb hLb hΔa hΔb
    hva hvb

/-- Reduction preserves the denotation up to a derivable equation.

No typing is carried across — see this module's withdrawal note: an
equation in this layer transports no typing (that schema is
*refutable*), and a carried hypothesis could not supply any clause its
premise anyway. -/
theorem whnf_factsTT {env : Env} (hstep : CheckStepTT) (m : EnvTT env)
    (φ : Name → Nat) (fuel : Nat) {d : Nat} {e e' : Expr}
    {Δ : List VExpr} (h : whnf env fuel d e = .ok e')
    (hws : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e) (hΔ : CtxOk m.cval env φ d Δ e)
    {v : VExpr} (hv : denote m.cval env φ d e = some v) :
    ∃ v', denote m.cval env φ d e' = some v' ∧ Deq Δ v v' :=
  (checkSoundTT hstep m φ fuel).2.1 h hws hb hLb hΔ hv

end Setlec.TTVerify

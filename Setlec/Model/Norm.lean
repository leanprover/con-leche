import Setlec.Model.Decorate
import Setlec.Model.RawEnv

/-!
# `norm`: the skeleton normalization behind the twin relation (task #100, stage 4a)

Storage flips to the **parsed trees, untouched** — install stays pure
parse + intern.  The annotation pass, however, is not
skeleton-preserving: two of its clauses rewrite the tree rather than
just decorating it.

* `letE` — the body is annotated *as its zeta reduct* (value
  transparency; DESIGN.md task #79, where the `letE`-preserving variant
  is recorded as rejected against real streams).  So the annotated
  output is let-free.
* `proj` — the projection clause either keeps the node with the
  structure name normalized to the scrutinee type's head, or rewrites
  it away entirely (`annotateProjElim`).

So the twin relation cannot be "erase the annotations and get the
stored tree back".  It generalizes instead to

  `erase(ê) = norm(e)`

with `norm` the *pure proof-side* normalization performing exactly
those two rewrites and nothing else.  The model machinery keeps working
in its let-free regime (`norm`'s output has no `letE`), the kernel keeps
its lazy zeta, and the two are related by the substitution lemmas #79
already provides — `interp_beta` and `AnnotOk_beta`, reused here as
`interp_zeta_step`/`AnnotOk_zeta_step` rather than re-proved.

## The oracle

The projection rewrite is *not* a function of the expression: it reads
the environment's projection table and the whnf of the scrutinee's
inferred type.  It enters `norm` the same way binder annotations enter
`decorate` — as an oracle, whose agreement with the annotation pass is
a hypothesis discharged at the flip.  With the everywhere-keep oracle
`norm` is pure zeta expansion, which is the fragment the model layer
needs and the one proved out below.

## Why fuel

Zeta expansion is not size-decreasing (the substituted value may occur
many times), exactly as for `annotateCore`, which `norm` mirrors clause
for clause.  Fuel is therefore the measure, as it is there; every
statement below is at an arbitrary fixed fuel.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat}

open SetTheory Expr

/-! ## Let-freeness -/

/-- No `letE` node (not descending into `fvar` type annotations, as
`Expr.eraseCodS` and `decorate` do not either). -/
def Expr.letFree : Expr → Bool
  | .bvar _ | .fvar .. | .sort _ | .const .. | .lit _ => true
  | .app f a => f.letFree && a.letFree
  | .lam _ ty b _ | .forallE _ ty b _ => ty.letFree && b.letFree
  | .letE .. => false
  | .proj _ _ e => e.letFree

/-! ## The normalization -/

/-- The projection-rewrite oracle: at a `proj` node whose scrutinee is
already normalized, the term the annotation pass's projection clause
rewrites it to, or `none` when the node is kept.  The proof-side twin
of `annotateProjElim`'s dispatch. -/
abbrev NormOracle := Nat → Expr → Option Expr

/-- Normalize a parsed tree to the *skeleton* the annotation pass
produces: zeta-expand `letE` nodes, and apply the oracle's projection
rewrites.  Nothing else changes — in particular no annotation is
touched, which is what makes `norm` compose with the erasures. -/
def Expr.norm (O : NormOracle) : Nat → Nat → Expr → Expr
  | 0, _, e => e
  | _ + 1, _, .bvar i => .bvar i
  | _ + 1, _, .fvar idx n t => .fvar idx n t
  | _ + 1, _, .sort u => .sort u
  | _ + 1, _, .const n us => .const n us
  | _ + 1, _, .lit l => .lit l
  | f + 1, d, .app g a => .app (Expr.norm O f d g) (Expr.norm O f d a)
  | f + 1, d, .lam n ty b m =>
    .lam n (Expr.norm O f d ty) (Expr.norm O f (d + 1) b) m
  | f + 1, d, .forallE n ty b m =>
    .forallE n (Expr.norm O f d ty) (Expr.norm O f (d + 1) b) m
  -- zeta, exactly `annotateBody`'s `letE` clause: the body with the
  -- value transparent
  | f + 1, d, .letE _ _ v b => Expr.norm O f d (b.instantiate1 v)
  | f + 1, d, .proj s i e =>
    let e' := Expr.norm O f d e
    match O d (.proj s i e') with
    | some r => Expr.norm O f d r
    | none => .proj s i e'

/-- The zeta equation, for use as a rewrite (it is the definition, but
naming it keeps the value-transparency arguments readable). -/
theorem Expr.norm_letE (O : NormOracle) (f d : Nat) (n : Name)
    (ty v b : Expr) :
    Expr.norm O (f + 1) d (.letE n ty v b) =
      Expr.norm O f d (b.instantiate1 v) := rfl

/-- The everywhere-keep oracle: `norm` is then pure zeta expansion. -/
def keepOracle : NormOracle := fun _ _ => none

/-! ## `norm` is the identity where nothing is to do

The precise form of "init-prelude-style streams are unaffected": on a
tree with no `letE`, whose projection nodes the oracle keeps, `norm`
changes nothing — at *every* fuel, so no fuel bookkeeping leaks into
the flip. -/

theorem Expr.norm_id (O : NormOracle) (hO : ∀ d e, O d e = none) :
    ∀ (f d : Nat) (e : Expr), e.letFree = true → Expr.norm O f d e = e := by
  intro f
  induction f with
  | zero => intro d e _; rfl
  | succ f ih =>
    intro d e hlf
    cases e with
    | bvar i => rfl
    | fvar idx n t => rfl
    | sort u => rfl
    | const n us => rfl
    | lit l => rfl
    | app g a =>
      simp only [Expr.letFree, Bool.and_eq_true] at hlf
      simp only [Expr.norm, ih d g hlf.1, ih d a hlf.2]
    | lam n ty b m =>
      simp only [Expr.letFree, Bool.and_eq_true] at hlf
      simp only [Expr.norm, ih d ty hlf.1, ih (d + 1) b hlf.2]
    | forallE n ty b m =>
      simp only [Expr.letFree, Bool.and_eq_true] at hlf
      simp only [Expr.norm, ih d ty hlf.1, ih (d + 1) b hlf.2]
    | letE n ty v b => exact absurd hlf (by simp [Expr.letFree])
    | proj s i e =>
      simp only [Expr.letFree] at hlf
      simp only [Expr.norm, ih d e hlf, hO]

/-- `norm` at the keep oracle is the identity on let-free trees. -/
theorem Expr.norm_keep_id {f d : Nat} {e : Expr} (h : e.letFree = true) :
    Expr.norm keepOracle f d e = e :=
  Expr.norm_id keepOracle (fun _ _ => rfl) f d e h

/-! ## `norm` commutes with the shallow erasure

The composite the raw model is instantiated at is `eraseCodS ∘ norm`
(equivalently `norm ∘ eraseCodS`, by this lemma): the stored tree is
the parsed one, and the twin's shallow erasure normalizes to it.  Both
maps leave `fvar` annotations alone, which is what makes them commute
on the nose.  The oracle hypothesis is the projection clause's own
erasure congruence, discharged at the flip from the annotation pass's
agreement. -/
theorem Expr.eraseCodS_norm (O : NormOracle)
    (hO : ∀ d e, O d e.eraseCodS = (O d e).map Expr.eraseCodS) :
    ∀ (f d : Nat) (e : Expr),
      (Expr.norm O f d e).eraseCodS = Expr.norm O f d e.eraseCodS := by
  intro f
  induction f with
  | zero => intro d e; rfl
  | succ f ih =>
    intro d e
    cases e with
    | bvar i => rfl
    | fvar idx n t => rfl
    | sort u => rfl
    | const n us => rfl
    | lit l => rfl
    | app g a => simp only [Expr.norm, Expr.eraseCodS, ih d g, ih d a]
    | lam n ty b m =>
      simp only [Expr.norm, Expr.eraseCodS, ih d ty, ih (d + 1) b]
    | forallE n ty b m =>
      simp only [Expr.norm, Expr.eraseCodS, ih d ty, ih (d + 1) b]
    | letE n ty v b =>
      simp only [Expr.norm, Expr.eraseCodS, ih d (b.instantiate1 v),
        Expr.eraseCodS_instantiate1 v b 0]
    | proj s i e =>
      have hkey : O d (.proj s i (Expr.norm O f d e.eraseCodS)) =
          (O d (.proj s i (Expr.norm O f d e))).map Expr.eraseCodS := by
        rw [← ih d e]
        simpa [Expr.eraseCodS] using hO d (.proj s i (Expr.norm O f d e))
      cases hOr : O d (.proj s i (Expr.norm O f d e)) with
      | none =>
        simp only [Expr.norm, Expr.eraseCodS, hkey, hOr, Option.map_none,
          ih d e]
      | some r =>
        simp only [Expr.norm, Expr.eraseCodS, hkey, hOr, Option.map_some]
        exact ih d r

/-! ## The value-transparency bridge

One zeta step preserves the interpretation and transports annotation
truthfulness.  These are *not* new facts: they are `interp_beta` and
`AnnotOk_beta` — the substitution lemmas task #79 built for exactly
this — packaged at the `letE` clause, which is where the kernel's lazy
zeta and `norm`'s eager expansion meet. -/

/-- Interpretation side: a `letE` node and its zeta reduct interpret
alike. -/
theorem interp_zeta_step {cval : ConstVal V} {d : Nat} {n : Name}
    {ty v b : Expr} {ρ : Nat → V} {xv : V}
    (hwv : WScoped d v) (hwb : WScoped d b)
    (hbv : v.looseBVarsBounded 0 = true)
    (hxv : interpExpr V cval env φ d ρ v = some xv) :
    interpExpr V cval env φ d ρ (b.instantiate1 v) =
      interpExpr V cval env φ d ρ (.letE n ty v b) := by
  rw [interp_beta (n := n) (ty := ty) hwb.fvarsBelow hwv hbv hxv 0]
  simp only [interpExpr, hxv]

/-- Truthfulness side: the `letE` clause's own data is what the zeta
reduct needs. -/
theorem AnnotOk_zeta_step {cval : ConstVal V} {d : Nat} {n : Name}
    {ty v b : Expr} {ρ : Nat → V}
    (hwv : WScoped d v) (hwb : WScoped d b)
    (hbv : v.looseBVarsBounded 0 = true)
    (ha : AnnotOk V cval env φ d ρ (.letE n ty v b)) :
    AnnotOk V cval env φ d ρ (b.instantiate1 v) := by
  simp only [AnnotOk] at ha
  obtain ⟨-, hav, xv, hxv, haopen⟩ := ha
  exact AnnotOk_beta hwb.fvarsBelow hwv hbv hxv hav 0 haopen

/-! ## Lifting to declarations and environments

The stored environment holds parsed records; the witness holds
annotated ones.  Both maps lift through `ConstantInfo` exactly as
`Env.eraseCod` does. -/

def ConstantVal.eraseCodS (cv : ConstantVal) : ConstantVal :=
  { cv with type := cv.type.eraseCodS }

def RecRuleFire.eraseCodS : RecRuleFire → RecRuleFire
  | .nested lvls pins => .nested lvls (pins.map Expr.eraseCodS)
  | f => f

def RecRule.eraseCodS (r : RecRule) : RecRule :=
  { r with fire := r.fire.eraseCodS, rhs := r.rhs.eraseCodS }

def ProjEntry.eraseCodS (p : ProjEntry) : ProjEntry :=
  { p with ty := p.ty.eraseCodS }

def ConstantInfo.eraseCodS : ConstantInfo → ConstantInfo
  | .axiomInfo cv => .axiomInfo cv.eraseCodS
  | .defnInfo cv v h => .defnInfo cv.eraseCodS v.eraseCodS h
  | .thmInfo cv v => .thmInfo cv.eraseCodS v.eraseCodS
  | .indInfo cv caps => .indInfo cv.eraseCodS caps
  | .ctorInfo cv nP nF => .ctorInfo cv.eraseCodS nP nF
  | .recInfo cv mI rP rules => .recInfo cv.eraseCodS mI rP (rules.map RecRule.eraseCodS)
  | .projInfo e => .projInfo e.eraseCodS

def Env.eraseCodS (env : Env) : Env := ⟨env.consts.map ConstantInfo.eraseCodS⟩

def ConstantVal.norm (O : NormOracle) (f : Nat) (cv : ConstantVal) : ConstantVal :=
  { cv with type := Expr.norm O f 0 cv.type }

def RecRuleFire.norm (O : NormOracle) (f : Nat) : RecRuleFire → RecRuleFire
  | .nested lvls pins => .nested lvls (pins.map (Expr.norm O f 0))
  | fr => fr

def RecRule.norm (O : NormOracle) (f : Nat) (r : RecRule) : RecRule :=
  { r with fire := r.fire.norm O f, rhs := Expr.norm O f 0 r.rhs }

def ProjEntry.norm (O : NormOracle) (f : Nat) (p : ProjEntry) : ProjEntry :=
  { p with ty := Expr.norm O f 0 p.ty }

def ConstantInfo.norm (O : NormOracle) (f : Nat) : ConstantInfo → ConstantInfo
  | .axiomInfo cv => .axiomInfo (cv.norm O f)
  | .defnInfo cv v h => .defnInfo (cv.norm O f) (Expr.norm O f 0 v) h
  | .thmInfo cv v => .thmInfo (cv.norm O f) (Expr.norm O f 0 v)
  | .indInfo cv caps => .indInfo (cv.norm O f) caps
  | .ctorInfo cv nP nF => .ctorInfo (cv.norm O f) nP nF
  | .recInfo cv mI rP rules =>
    .recInfo (cv.norm O f) mI rP (rules.map (RecRule.norm O f))
  | .projInfo e => .projInfo (e.norm O f)

def Env.norm (O : NormOracle) (f : Nat) (env : Env) : Env :=
  ⟨env.consts.map (ConstantInfo.norm O f)⟩

/-! ## The twin relation

The stage-4 instantiation of the raw model's relation parameter: the
witness's *shallow* erasure is the stored (parsed) environment's
normalization.  With a keep oracle and let-free storage this collapses
to plain erasure (`norm_keep_id`), which is why streams without `let`
records — init-prelude style — are unaffected by the flip. -/

/-- The environment-level twin relation `erase(ê) = norm(e)` — the
instantiation of `RawEnvModelE`'s parameter at the end state. -/
def Env.TwinAt (O : NormOracle) (f : Nat) (aenv env : Env) : Prop :=
  aenv.eraseCodS = Env.norm O f env

/-- The expression-level twin relation. -/
def Expr.TwinAt (O : NormOracle) (f d : Nat) (ea e : Expr) : Prop :=
  ea.eraseCodS = Expr.norm O f d e

/-- The **end-state raw model**: the witness's shallow erasure is the
stored (parsed) environment's normalization. -/
abbrev RawEnvModelN (V : Type u) [SetTheory V] (O : NormOracle) (f : Nat)
    (env : Env) :=
  RawEnvModelE V (Env.TwinAt O f) env

/-- On let-free storage with a keep oracle the twin relation is plain
shallow erasure — the flip is invisible to such streams. -/
theorem Expr.TwinAt_keep {f d : Nat} {ea e : Expr} (h : e.letFree = true) :
    Expr.TwinAt keepOracle f d ea e ↔ ea.eraseCodS = e := by
  simp [Expr.TwinAt, Expr.norm_keep_id h]

end Setlec

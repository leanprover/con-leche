import Setlec.SetR.Rel
import Setlec.SetR.AnnotOkV

/-!
# The soundness motives and the environment-hypothesis bundle (task #148, T4)

The five motives of the mutual soundness induction, per the T4
architecture record in `Setlec/SetR/DESIGN.md` (the graded design that
made repair A free):

* the equality/membership lane is unconditional under `Sat` — no
  subject-`AnnotOkV` hypotheses anywhere, which is what closes
  `DefEq.symm`/`DefEq.trans` and the binder congruences;
* `Infer`-sound concludes the *subject's* `AnnotOkV` (the design's
  type-side conjunct is dropped — consumer check in the record);
* `Red`-sound carries the one conditional conjunct: forward `AnnotOkV`
  transport onto the reduct.

`EnvSHyp` is the hypothesis bundle the case lemmas consume — the [set]
shadow of the `EnvTT` fields the design's §2 lists, restricted to what
the 44 cases actually read, at the relations' fixed `(env, cval, φ)`.
T5's `EnvS` discharges it by projection; fields are added batch by
batch (statement-first with their consumer, per the house rule) and the
bundle freezes at the iota batch.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify
open SetTheory

universe w

variable (V : Type w) [SetTheory V]

/-! ## The motives -/

/-- What soundness concludes for a reduction: the interpretation is
preserved (unconditionally), and truthfulness transports forward.
Mirror of `WhnfCoreClaims`/`WhnfClaims` with the equality freed of the
`AnnotOk` hypothesis (T4 architecture record). -/
def RedS (Δ : List VExpr) (v w : VExpr) : Prop :=
  ∀ ρ : Nat → V, Sat V Δ ρ →
    interp V ρ v = interp V ρ w ∧ (AnnotOkV V ρ v → AnnotOkV V ρ w)

/-- What soundness concludes for an inference: the subject is truthful
and inhabits its type's interpretation.  Mirror of `InferClaims` minus
the type-side `AnnotOk` conjunct (dropped; see the record). -/
def InfS (Δ : List VExpr) (v T : VExpr) : Prop :=
  ∀ ρ : Nat → V, Sat V Δ ρ →
    AnnotOkV V ρ v ∧ interp V ρ v ∈ˢ interp V ρ T

/-- What soundness concludes for a definitional equality: the two
interpretations are equal, unconditionally.  Strictly stronger than
`DefEqClaims`' hypothesis-laden form — forced by the relation's free
`symm`/`trans` (`AnnotOkV` cannot cross a `DefEq`). -/
def DeqS (Δ : List VExpr) (a b : VExpr) : Prop :=
  ∀ ρ : Nat → V, Sat V Δ ρ → interp V ρ a = interp V ρ b

/-- What soundness concludes for a telescope certification: the spine
fits (`TeleFitV`), every argument is truthful, and the residual is
truthful whenever the telescope is.  The `certs_fit` re-hang. -/
def TeleS (Δ : List VExpr) (T : VExpr) (as : List VExpr)
    (rest : VExpr) : Prop :=
  ∀ ρ : Nat → V, Sat V Δ ρ →
    TeleFitV V ρ T as rest ∧ (∀ a ∈ as, AnnotOkV V ρ a) ∧
    (AnnotOkV V ρ T → AnnotOkV V ρ rest)

/-- What soundness concludes for a spine equality: pointwise equal
interpretations (as map equality — the form `interp_mkAppN`
congruences consume).  The `defEqList_values` re-hang. -/
def DeqLS (Δ : List VExpr) (as bs : List VExpr) : Prop :=
  ∀ ρ : Nat → V, Sat V Δ ρ →
    as.map (interp V ρ) = bs.map (interp V ρ)

/-! ## The environment-hypothesis bundle -/

/-- The semantic environment facts the soundness cases consume, at the
relations' fixed `(env, cval, φ)`.  Each field names its §2
counterpart and its T5 supplier; see the module docstring. -/
structure EnvSHyp (env : Env) (cval : TConstVal) (φ : Name → Nat) :
    Prop where
  /-- Every valuation leaf is closed (`EnvTT.cval_closed`'s shape; the
  ambient hypothesis of M1 and of every closedness rewrite). -/
  cval_closed : ∀ (n : Name) (ψ : Name → Nat), VExpr.Closed (cval n ψ)
  /-- Every valuation leaf is truthful at every environment
  (§2 `annot_okV`; supplier: the value front door's subject
  conjunct). -/
  annot_okV : ∀ (n : Name) (ψ : Name → Nat) (ρ : Nat → V),
    AnnotOkV V ρ (cval n ψ)
  /-- Every stored constant inhabits its denoted instantiated type,
  which is truthful (§2 `mem_type`; suppliers: the value front door's
  membership through the unconditional defeq, and the *type* front
  door's subject conjunct).  Keyed exactly on I3's side conditions. -/
  mem_type : ∀ (n : Name) (ci : ConstantInfo),
    env.find? n = some ci →
    ∀ us : List Level, us.length = ci.toConstantVal.levelParams.length →
    ∀ T : VExpr,
      denoteClosed cval env φ
        (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us) = some T →
      ∀ ρ : Nat → V,
        interp V ρ
            (cval n (Level.substFn φ ci.toConstantVal.levelParams us))
          ∈ˢ interp V ρ T ∧
        AnnotOkV V ρ T

end Setlec.SetR

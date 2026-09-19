module

public import ConLeche.Model.Rules.Inputs

public section

/-!
# The soundness of the inference rules (task #305, lane S-infer)

One lemma per constructor of `Infer`, at the constructor's grade
(`InferSem m φ g …` dispatches to the establishment motive at `.full`
and the consumption motive at `.io`).  The io lemmas mine
`Model/Steps/InferIO.lean` (the application clause's `appSkip` is
`infer_app_claimIO`'s gated arm: `io_domain_transfer` against the
subject's own hereditary app slot); the full ones `Model/Steps/Infer.lean`.

The λ rule's chain case needs the SHAPE of the body's inferred type
(a ∀ at the inner λ's own annotation, `infer_lam_meta_copy`'s twin
`Infer.lam_shape`), which the master induction reads off the premise
derivation and hands in as `hshape`.
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env}
  {φ : Name → Nat}

/-- `infer_sort_claim` / `infer_sort_claimIO`. -/
theorem Infer.sort_sound {g : Grade} {d : Nat} {u : Level} :
    InferSem m φ g d (.sort u) (.sort (.succ u)) := by
  sorry

/-- `infer_fvar_claim(IO)`: `CtxOk`'s leaf package. -/
theorem Infer.fvar_sound {g : Grade} {d idx : Nat} {ty : Expr} (h : idx < d) :
    InferSem m φ g d (.fvar idx ty) ty := by
  sorry

/-- `infer_const_claim(IO)`: `ConstTy` + `LeafValid`. -/
theorem Infer.const_sound (hin : RulesInputs V m φ) {g : Grade} {d : Nat}
    {n : Name} {us : List Level} {ci : ConLeche.ConstantInfo}
    (hf : env.find? n = some ci) (htower : ci.isTowerEntry = false)
    (hus : us.length = ci.toConstantVal.levelParams.length) :
    InferSem m φ g d (.const n us)
      (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us) := by
  sorry

/-- `infer_natLit_claim(IO)`: `NatLeafHeads` + `LeafValid`. -/
theorem Infer.natLit_sound (hin : RulesInputs V m φ) {g : Grade} {d n : Nat}
    (h : ConLeche.natLitSupported env = true) :
    InferSem m φ g d (.lit (.natVal n)) (.const natName []) := by
  sorry

/-- `inferStrLitStep_of_claims` (`Steps/StrLit.lean:451`). -/
theorem Infer.strLit_sound (hin : RulesInputs V m φ) {g : Grade} {d : Nat}
    {s : String} (h : ConLeche.strLitSupported env = true) :
    InferSem m φ g d (.lit (.strVal s)) (.const stringName []) := by
  sorry

/-- `infer_forallE_claim(IO)` (`Steps/Infer.lean:254`, `InferIO.lean:339`):
the two sort facts (`sortSemAt_of_claims`'s content) and the bit law. -/
theorem Infer.forallE_sound (hin : RulesInputs V m φ) {g : Grade} {d : Nat}
    {ty body s bs : Expr} {u v : Level} {mb : BinderMeta}
    (hs : InferSem m φ g d ty s) (hu : RedSem m φ d s (.sort u))
    (hbs : InferSem m φ g (d + 1) (body.instantiate1 (.fvar d ty)) bs)
    (hv : RedSem m φ (d + 1) bs (.sort v))
    (hz : Level.zeronessOf v = mb.pw) :
    InferSem m φ g d (.forallE ty body mb) (.sort (.imax u v)) := by
  sorry

/-- `infer_lam_claim(IO)` (`Steps/Infer.lean:358`, `InferIO.lean:456`):
the fibre regime fact from the leaf sort run or, at a chain node, from
the copied annotation (`piR_zero_mem_univZero`). -/
theorem Infer.lam_sound (hin : RulesInputs V m φ) {g : Grade} {d : Nat}
    {ty body s bt btt : Expr} {u v : Level} {mb : BinderMeta}
    (hs : g = .full → InferSemFull m φ d ty s)
    (hu : g = .full → RedSem m φ d s (.sort u))
    (hbt : InferSem m φ g (d + 1) (body.instantiate1 (.fvar d ty)) bt)
    (hshape : ∀ tyI bI mbI, body = .lam tyI bI mbI →
      ∃ btI, bt = .forallE (tyI.instantiate1 (.fvar d ty)) btI mbI)
    (hchain : ∀ pwI, body.lamPw = some pwI → mb.pw = pwI)
    (hbtt : body.lamPw = none → InferSemIO m φ (d + 1) bt btt)
    (hv : body.lamPw = none → RedSem m φ (d + 1) btt (.sort v))
    (hz : body.lamPw = none → Level.zeronessOf v = mb.pw) :
    InferSem m φ g d (.lam ty body mb) (.forallE ty (bt.abstract1 d) mb) := by
  sorry

/-- `infer_app_claim` / `infer_app_claimIO`'s kept arm
(`Steps/Infer.lean:842`, `InferIO.lean:609`). -/
theorem Infer.app_sound (hin : RulesInputs V m φ) {g : Grade} {d : Nat}
    {f a tf ty body ta : Expr} {mt : BinderMeta}
    (htf : InferSem m φ g d f tf) (hw : RedSem m φ d tf (.forallE ty body mt))
    (hta : InferSem m φ g d a ta) (hd : DefEqSem m φ d ta ty) :
    InferSem m φ g d (.app f a) (body.instantiate1 a) := by
  sorry

/-- **The io licence** (`infer_app_claimIO`'s gated arm): the skipped
membership from the subject's own hereditary app slot,
`io_domain_transfer` + `piR_dom_unique` at a bit pinned positive by
`pwBit_ne_zero_of_isNever`. -/
theorem Infer.appSkip_sound (hin : RulesInputs V m φ) {d : Nat}
    {f a tf ty body : Expr} {mt : BinderMeta}
    (htf : InferSemIO m φ d f tf) (hw : RedSem m φ d tf (.forallE ty body mt))
    (hnev : mt.pw.isNever = true) :
    InferSemIO m φ d (.app f a) (body.instantiate1 a) := by
  sorry

/-- `inferProjStep_of_claims` / `inferProjStepIO_of_claims`
(`Steps/ProjRows.lean:71`, `:160`): the tower law's typing clause. -/
theorem Infer.proj_sound (hin : RulesInputs V m φ) {g : Grade} {d : Nat}
    {sn : Name} {i : Nat} {pe tpe te : Expr} {us : List Level}
    {entry : ProjEntry}
    (htpe : InferSem m φ g d pe tpe) (hte : RedSem m φ d tpe te)
    (hhead : te.getAppFn = .const sn us)
    (hent : env.findProj? sn i = some entry)
    (hlen : te.getAppArgs.length = entry.numParams)
    (hus : us.length = entry.levelParams.length)
    (hprop : Level.isEquiv entry.structSort .zero = some true →
      Level.isEquiv (Level.subst entry.levelParams us entry.fieldSort) .zero
        = some true) :
    InferSem m φ g d (.proj sn i pe) (entry.typeAt us te.getAppArgs pe) := by
  sorry

end ConLeche.Model.Rules

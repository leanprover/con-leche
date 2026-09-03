import Setlec.Kernel.TypeChecker

/-!
# The io lane: infer at the licensed infer-only grade (task #161, stage 2)

**Status: the statement subject, not yet an executable lane.**  The
definitions below are the *frozen kernel frame* of the io-knot campaign
— `inferBodyIO`, the io knot, and the fueled entry point the
`InferClaimsIO2P` family is stated at.  They are **not wired into any
driver**: the shipped stacks (`Setlec/Kernel/Checker*.lean`,
`Setlec/Cached/*`) run the full knot exactly as before, so the
executable is byte-identical to master.  The wiring is HELD at the
stop-and-name recorded in `DESIGN.md` ("Task #161 STAGE 2 BATCH 1") —
see "The knot boundary, and why it cannot be drawn where the freeze
says" there.

## What the lane is

The reference kernels type-check a declaration *once*, at the front
door, and let the inferences that reduction and definitional equality
perform on their own intermediate terms re-derive types **without
re-checking application arguments** (`infer_type_core(e, infer_only)`,
lean4lean's `inferType (inferOnly := true)`).  Setlec cannot copy that
wholesale: `Typable e → InferOnly e t → HasType e t` is refuted
(spike `inferonly-metatheory`), and its semantic residue survives at
the *squash* regime — closed `V`-values satisfy every premise of the
premise-form io claim with `app ⟦f⟧ ⟦a⟧ ∉ ⟦B'⟧⟦a⟧`
(`io_membership_fails_at_squash`, the round-D study's probe 2; the
wall is model-class-wide, since any proof-irrelevant set model erases
Prop-side type identity).

What *is* licensed — mechanized, side-condition-free, at the graph
regime — is the skip at a binder whose **validated** annotation is
`never`: `io_domain_transfer`/`io_app_mem` recover the skipped
membership from the redex's own hereditary app slot through
`piR_dom_unique`, with no nonemptiness and no freshness premise.  So
the io lane's application clause skips the per-argument certificate
**iff**

* the ∀'s stored `pw` is `.never` (`PropWhen.isNever`, the ∀-`φ`
  uniform form of the claims' positive branch — exact, by
  `isNever_iff_forall_pwBit_ne_zero`), **and**
* `μ.verified = true` — the mode gate, which is part of the amended
  law 1's text (clause (i)): the gate may fire only in the modes where
  the licensing theorems' hypotheses hold.  At `.noModel` the
  annotations are not validated at all, so the datum means nothing
  there and the certificate runs.

Everything else is `inferBody` verbatim, clause for clause: the λ/∀
domain-sort checks, the λ codomain-sort validation, the `letE`
conformance and the projection typing all **stay** — they are the
suppliers the P2 validation sites consume, and a deviation in the
strict direction needs no argument.

## The knot boundary

`coreKnotIO` is a **leaf** lane: its `whnfCore`/`whnf`/`defeq`/
`annotate` are the *full* knot's, unchanged, so every certificate the
reduction and definitional-equality bodies run is the certified one and
every claim tier that models those bodies (`Red`/`Infer`/`DefEq` in
`SetR/Rel.lean`, the `denote2` D lane, the graded P lane) keeps its
present subject.  Only `infer` is the io body, and only the io body
calls it.  Consequently

* the new statement surface is **exactly one family**
  (`InferClaimsIO2P`), and the step assembly goes five-way:
  `{whnfCore, whnf, defeq, infer, inferIO}` at `fuel` give the same
  five at `fuel + 1`;
* nothing in the full lane can reach an io conclusion, which is the
  mode-provenance discipline enforced by construction rather than by
  review;
* and — the price, named here so it is not rediscovered — **the lane
  is unreachable from the executable**.  Making it reachable means
  letting a body the R tier models premise-exactly call `r.infer` at io
  grade, and that is the wall the seal records.
-/

namespace Setlec

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
variable (mode : CheckMode)

/-- **The io inference body**: `inferBody` with one clause changed —
the application rule's per-argument certificate is skipped when the
∀'s validated annotation licenses it (see the module docstring).  The
gate wraps the *test* only; the computed type (`body.instantiate1 a`)
and the "function expected" rejection are `inferBody`'s, verbatim, so
the lane is annotation-blind in its results (law 1 (iii)). -/
def inferBodyIO (r : CoreFns m) (env : Env) : Nat → Expr → m Expr :=
  fun depth e => do
    match ← viewM (m := m) e with
    | .sort u => pure (.sort (.succ u))
    | .fvar idx _ ty =>
      if idx < depth then pure ty
      else throw (.invalid "free variable out of scope")
    | .const n us => do
      match env.find? n with
      | none => throw (.invalid s!"unknown constant {n}")
      | some ci =>
        let cv := ci.toConstantVal
        unless us.length = cv.levelParams.length do
          throw (.invalid s!"incorrect number of universe levels for {n}")
        pure (cv.type.instantiateLevelParams cv.levelParams us)
    | .lit (.natVal _) => do
      if natLitSupported env then pure (.const natName [])
      else throw (.invalid "Nat literal without the Nat basis declarations")
    | .lit (.strVal _) => do
      if strLitSupported env then pure (.const stringName [])
      else throw (.notImplemented
        "string literals before the String support declarations")
    | .forallE n ty body mb => do
      match ← r.whnf depth (← r.infer depth ty) with
      | .sort u => do
        let v ← ensureSort r env (depth + 1)
          (← r.infer (depth + 1) (body.instantiate1 (.fvar depth n ty)))
        if mode.verified then
          unless (Level.zeronessOf v).equiv mb.pw do
            throw (.notImplemented "sort-annotation mismatch (forall-cod)")
        pure (.sort (.imax u v))
      | _ => throw (.invalid "expected a sort")
    | .lam n ty body mb => do
      match ← r.whnf depth (← r.infer depth ty) with
      | .sort _ => do
        let bt ← r.infer (depth + 1)
          (body.instantiate1 (.fvar depth n ty))
        if mode.verified then
          match body.lamPw with
          | some pwI =>
            unless mb.pw.equiv pwI do
              throw (.notImplemented
                "sort-annotation mismatch (lam-cod-chain)")
          | none =>
            let btt ← r.infer (depth + 1) bt
            let vb ← ensureSort r env (depth + 1) btt
            unless (Level.zeronessOf vb).equiv mb.pw do
              throw (.notImplemented
                "sort-annotation mismatch (lam-cod-leaf)")
        pure (.forallE n ty (bt.abstract1 depth) mb)
      | _ => throw (.invalid "expected a sort")
    | .app f a => do
      let tf ← r.infer depth f
      match ← r.whnf depth tf with
      | .forallE _ ty body mt => do
        -- **THE io SITE.**  At a ∀ whose validated datum is `never`
        -- the certificate is dead weight: the premise-form io claim
        -- derives `⟦a⟧ ∈ ⟦ty⟧` from the subject's own `AnnotOk2` app
        -- slot (`io_domain_transfer` + `piR_dom_unique`,
        -- side-condition free).  At a possibly-zero datum the
        -- certificate runs unconditionally — the squash regime's
        -- membership is model-class-wide unrecoverable
        -- (`io_membership_fails_at_squash`), and that fence is
        -- absolute.  `mode.verified` is the law's mode gate: the
        -- annotation is only *validated* at the verified modes.
        unless mode.verified && mt.pw.isNever do
          let ta ← r.infer depth a
          unless ← r.defeq depth ta ty do
            throw (.invalid "application type mismatch")
        pure (body.instantiate1 a)
      | _ => throw (.invalid "function expected")
    | .proj _sn i pe => do
      let te ← r.whnf depth (← r.infer depth pe)
      match te.getAppFn with
      | .const T us =>
        match env.findProj? T i with
        | some entry =>
          if entry.native ∧ te.getAppArgs.length = entry.numParams ∧
              us.length = entry.levelParams.length then do
            match te.getAppArgs, i with
            | [A, _], 0 => pure A
            | [_, B], 1 => pure (.app B (.proj T 0 pe))
            | _, _ => throw (.internal "malformed projection entry")
          else throw (.notImplemented "projection without a native entry")
        | none => throw (.notImplemented "projection without a native entry")
      | _ => throw (.notImplemented "projection without a native entry")
    | .letE _ ty v b => do
      let _ ← ensureSort r env depth (← r.infer depth ty)
      let tv ← r.infer depth v
      unless ← r.defeq depth tv ty do
        throw (.invalid "let value type mismatch")
      r.infer depth (b.instantiate1 v)
    | .bvar _ =>
      throw (.notImplemented "inferType beyond the supported fragment")

/-- **The io knot** (the leaf lane).  `whnfCore`/`whnf`/`defeq`/
`annotate` are the *full* knot's at the same fuel — the io lane
consumes the certified reduction and definitional equality and never
supplies them — and `infer` is `inferBodyIO` tied to the io knot one
level down.  The full knot never mentions this one: that asymmetry is
the mode-provenance discipline, engineered rather than reviewed. -/
def coreKnotIO (env : Env) : Nat → CoreFns m
  | 0 =>
    { whnfCore := fun _ _ => throw (.internal "fuel exhausted: whnfCore")
      whnf := fun _ _ => throw (.internal "fuel exhausted: whnf")
      infer := fun _ _ => throw (.internal "fuel exhausted: infer")
      defeq := fun _ _ _ => throw (.internal "fuel exhausted: defeq")
      annotate := fun _ _ => throw (.internal "fuel exhausted: annotate") }
  | fuel + 1 =>
    { whnfCore := (coreKnot mode env id (fuel + 1)).whnfCore
      whnf := (coreKnot mode env id (fuel + 1)).whnf
      defeq := (coreKnot mode env id (fuel + 1)).defeq
      annotate := (coreKnot mode env id (fuel + 1)).annotate
      infer := fun d e => inferBodyIO mode (coreKnotIO env fuel) env d e }

/-- The io core, tied at `CheckM`: the specification the
`InferClaimsIO2P` family is stated at. -/
def pureFnsIO (env : Env) : Nat → CoreFns CheckM :=
  coreKnotIO mode env

/-- Infer-only (io-grade) type inference, fueled — the io lane's single
entry point. -/
def inferTypeCoreIO (env : Env) (fuel depth : Nat) (e : Expr) :
    CheckM Expr :=
  (pureFnsIO mode env fuel).infer depth e

end Setlec

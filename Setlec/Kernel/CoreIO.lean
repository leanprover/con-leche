import Setlec.Kernel.CoreI

/-!
# The infer-only core (task #134, `SETLEC_INFER_ONLY` / `--infer-only`)

**A supported operating mode, not a measurement knob.**  It reproduces
the reference kernels' `infer_only` discipline: a declaration is
checked *once*, at the top, by the driver's front door; the inferences
that reduction and definitional equality perform on their own
intermediate terms re-derive types **without re-checking application
arguments**, because those arguments were already checked where the
term they came from was checked.

The two knots below are the two halves of that discipline.

* `coreKnotIO` — the **infer-only** knot.  Its `infer` is
  `inferBodyIO`, which differs from `inferBodyI` in exactly one clause:
  the application clause walks the Π-telescope with `inferSpineIO`
  (no per-argument `infer` + `defeq`) instead of `inferSpineI`.  Every
  other body — `whnfCore`, `whnf`, `defeq`, `annotate`, and every
  certificate they reach (`iotaCertsI`, the beta certificates in
  `whnfAppI`/`betaPeelI`, `projCertI`, the structure-eta and unit-like
  certificates, `projParamCertI`) — is the *certified* body, unchanged
  and still running.  This is the knot every **internal** call sees.

* `coreKnotF` — the **checking-mode** knot, and the only one the
  driver ever holds.  Its `infer` is the certified `inferBodyI` tied
  to *itself*, so the per-argument re-check runs and the mode
  propagates down the term (exactly the official kernel's
  `infer_type_core(·, infer_only)` threading its flag through the
  descent); its `whnfCore`/`whnf`/`defeq` are `coreKnotIO`'s, so the
  inferences *reduction* performs are infer-only.  Its `annotate` is
  tied to itself as well, so the checks inside the annotation pass
  (the `letE` conformance, the projection machinery) are checking-mode
  too.

Reference: `type_checker.cpp`'s `infer_type_core(e, infer_only)` —
`check(e)` enters at `infer_only = false` and threads it through
`infer_app`/`infer_lambda`/`infer_let`, while `whnf`/`is_def_eq` call
`infer_type(e)`, which enters at `infer_only = true`; lean4lean's
`TypeChecker.inferType (inferOnly := true)` inside `whnf`/`isDefEq`
against `check`'s `inferOnly := false`.  The official kernel keeps a
separate inference cache per flag value (`m_st->m_infer_type[2]`);
`coreKnotF` does the same with `IState.inferFC`, so a type derived
infer-only can never be served to a checking-mode query.

**Assurance.**  The consistency statements
(`Setlec/Model/ConsistencyP.lean` and friends) are about the default
path — `coreKnotI` → `checkDeclsSP` — and say nothing about this one.
With the flag on, the argument for the mode is *reference-kernel
parity*, and nothing stronger: setlec's own spike
(`spike/inferonly-metatheory`) mechanized the refutation of the
tempting metatheorem `Typable e → InferOnly e t → HasType e t`, so
"infer-only still derives a real typing" is **false** as a general
claim about arbitrary terms, for the reference kernels exactly as for
setlec.  What the mode rests on instead is the operational invariant
the reference kernels rest on: every term whose type is re-derived
internally is a reduct of a term the front door checked.  That is an
argument about the *engine*, not a theorem about the *terms*, and it
is stated here as such.

**Not `SETLEC_NO_PROOF_CERTS`.**  That flag (task #76,
`Setlec/Kernel/CoreNC.lean`) is an *unverified measurement mode*: it
switches off whole certificate families at once — the iota telescope
certifications, the beta re-checks, the eta/unit-like certifications —
to price the verification tax against the reference kernels.  It is
for measuring, never for judging a stream.  This flag switches off
*one* re-check, at *internal invocations only*, keeps every
certificate family running, and keeps the front door in full checking
mode; it is meant to be used on real streams.  The two are mutually
exclusive on the command line for exactly that reason.
-/

namespace Setlec

/-- Infer-only twin of `inferSpineI`: walk the Π-telescope against the
argument spine with **no per-argument re-check** — the reference
kernels' `infer_app` at `infer_only` (lean4lean's `inferApp`, which
performs no argument checks at all; the official kernel's
`infer_app`'s `infer_only` branch).  Everything else — the telescope
step, the deferred substitution, the non-syntactic whnf step and the
"function expected" rejection — is `inferSpineI` unchanged. -/
def inferSpineIO (r : CoreFnsI) (depth : Nat) :
    EIdx → Array EIdx → List EIdx → CheckIM EIdx
  | ty, acc, [] => instListRevM ty acc
  | ty, acc, a :: rest => do
    match ← viewI ty with
    | some (.forallE _ _dom body _mt) =>
      inferSpineIO r depth body (acc.push a) rest
    | _ => do
      let ty' ← instListRevM ty acc
      let w ← r.whnf depth ty'
      match ← viewI w with
      | some (.forallE _ _dom body _mt) =>
        inferSpineIO r depth body #[a] rest
      | _ => throw (.invalid "function expected")

/-- Infer-only twin of `inferBodyI`: identical clause by clause, with
`inferSpineIO` in the application clause.  In particular the λ/∀
domain-sort checks, the `letE` value conformance and the projection
parameter certification (`projParamCertI`, task #129) are **kept**,
though the reference kernels skip the first two at `infer_only` — this
mode narrows exactly one site, and a deviation in the strict direction
needs no argument. -/
def inferBodyIO (r : CoreFnsI) (fe : FEnv) : Nat → EIdx → CheckIM EIdx :=
  fun depth e => do
    match ← viewI e with
    | some (.sort u) => do
      let su ← internLM (.succ u)
      internI (.sort su)
    | some (.fvar idx _ ty) =>
      if idx < depth then pure ty
      else throw (.invalid "free variable out of scope")
    | some (.const n us) => do
      let nm ← readbackNM n
      match fe.find? nm with
      | none => throw (.invalid s!"unknown constant {nm}")
      | some ci =>
        let cv := ci.toConstantVal
        unless us.length = cv.levelParams.length do
          throw (.invalid s!"incorrect number of universe levels for {nm}")
        constTyAtM fe n nm us
    | some (.lit (.natVal _)) => do
      if natLitSupportedF fe then do
        let ni ← internNameM natName
        internI (.const ni [])
      else throw (.invalid "Nat literal without the Nat basis declarations")
    | some (.lit (.strVal _)) => do
      if strLitSupportedF fe then do
        let si ← internNameM stringName
        internI (.const si [])
      else throw (.notImplemented
        "string literals before the String support declarations")
    | some (.forallE n ty body _mb) => do
      let tty ← r.infer depth ty
      let wtty ← r.whnf depth tty
      match ← viewI wtty with
      | some (.sort u) => do
        let fv ← internI (.fvar depth n ty)
        let fuel ← withStore (·.nodes.size)
        inferPisI r depth fuel body 1 #[fv] [u]
      | _ => throw (.invalid "expected a sort")
    | some (.lam n ty body mb) => do
      let tty ← r.infer depth ty
      let wtty ← r.whnf depth tty
      match ← viewI wtty with
      | some (.sort _) => do
        let fv ← internI (.fvar depth n ty)
        let fuel ← withStore (·.nodes.size)
        inferLamsI r depth fuel body 1 #[fv] [(n, ty, mb)]
      | _ => throw (.invalid "expected a sort")
    | some (.app _ _) => do
      -- THE infer-only site: the spine is walked, the arguments are
      -- not re-checked (`inferSpineIO` vs `inferSpineI`).
      let h ← withStore (fun st => st.getAppFnI e)
      let args ← withStore (·.getAppArgsI e)
      let tf ← r.infer depth h
      inferSpineIO r depth tf #[] args
    | some (.proj _sn i pe) => do
      let tpe ← r.infer depth pe
      let te ← r.whnf depth tpe
      match ← withStore (fun st => st.getNode (st.getAppFnI te)) with
      | some (.const T us) => do
        let Tn ← readbackNM T
        match fe.findProj? Tn i with
        | some entry => do
          let targs ← withStore (·.getAppArgsI te)
          if entry.native ∧ targs.length = entry.numParams ∧
              us.length = entry.levelParams.length then do
            let pf ← projFnIdxM T i
            let pty ← constTyAtM fe pf (projFnName Tn i) us
            unless ← projParamCertI r fe depth pty targs do
              throw (.invalid "projection parameter type mismatch")
            match ← piResidualM pty (targs ++ [pe]) with
            | some resTy => pure resTy
            | none => throw (.internal "malformed projection entry")
          else throw (.notImplemented "projection without a native entry")
        | none => throw (.notImplemented "projection without a native entry")
      | _ => throw (.notImplemented "projection without a native entry")
    | some (.letE _ ty v b) => do
      let _ ← ensureSortI r depth (← r.infer depth ty)
      let tv ← r.infer depth v
      unless ← r.defeq depth tv ty do
        throw (.invalid "let value type mismatch")
      let e' ← inst1M b v
      r.infer depth e'
    | some (.bvar _) =>
      throw (.notImplemented "inferType beyond the supported fragment")
    | none => throw (.internal "interned node missing")

/-- Memoize the infer-only inference, reading the *checking-mode* memo
first.  The two bodies return the same type wherever both succeed —
`inferBodyIO` is `inferBodyI` minus checks, and a check never changes
the value the telescope walk returns — so a checking-mode entry
answers an infer-only query exactly, while the converse is forbidden
(that is what `inferFC` is for).  The official kernel keeps its two
caches strictly apart and simply recomputes; this is a one-directional
share, in the safe direction. -/
def memoEIO (f : Nat → EIdx → CheckIM EIdx) : Nat → EIdx → CheckIM EIdx :=
  fun d e => do
    let st ← get
    match st.inferFC[e]? with
    | some r => pure r
    | none =>
      match st.inferC[e]? with
      | some r => pure r
      | none =>
        let r ← f d e
        modify fun st =>
            let mp := st.inferC
            let st := { st with inferC := ∅ }
            { st with inferC := mp.insert e r }
        pure r

/-- The **infer-only** knot: every body is the certified one except
`infer`, which is `inferBodyIO`.  This is what reduction, definitional
equality and every certificate call when they need a type. -/
def coreKnotIO (fe : FEnv) : Nat → CoreFnsI
  | 0 =>
    { whnfCore := fun _ _ => throw (.internal "fuel exhausted: whnfCore")
      whnf := fun _ _ => throw (.internal "fuel exhausted: whnf")
      infer := fun _ _ => throw (.internal "fuel exhausted: infer")
      defeq := fun _ _ _ => throw (.internal "fuel exhausted: defeq")
      annotate := fun _ _ => throw (.internal "fuel exhausted: annotate") }
  | fuel + 1 =>
    { whnfCore := memoEI (·.whnfCoreC)
        (fun st mp => { st with whnfCoreC := mp })
        (fun d e => whnfCoreBodyI (coreKnotIO fe fuel) fe d e)
      whnf := memoEI (·.whnfC) (fun st mp => { st with whnfC := mp })
        (fun d e => whnfBodyI (coreKnotIO fe fuel) fe d e)
      infer := memoEIO (fun d e => inferBodyIO (coreKnotIO fe fuel) fe d e)
      defeq := memoBI
        (fun d a b => defeqBodyI (coreKnotIO fe fuel) fe d a b)
      annotate := memoEI (·.annotC) (fun st mp => { st with annotC := mp })
        (fun d e => annotateBodyI (coreKnotIO fe fuel) fe d e) }

/-- The **checking-mode** knot — the front door.  `infer` is the
certified `inferBodyI` (per-argument re-check included) tied to itself,
so checking mode propagates through the declaration's own term;
`annotate` likewise.  `whnfCore`/`whnf`/`defeq` are `coreKnotIO`'s, so
the inferences performed *inside* reduction and definitional equality
are infer-only.  The checking-mode inference memo is `inferFC`, kept
apart from the infer-only `inferC`. -/
def coreKnotF (fe : FEnv) : Nat → CoreFnsI
  | 0 =>
    { whnfCore := fun _ _ => throw (.internal "fuel exhausted: whnfCore")
      whnf := fun _ _ => throw (.internal "fuel exhausted: whnf")
      infer := fun _ _ => throw (.internal "fuel exhausted: infer")
      defeq := fun _ _ _ => throw (.internal "fuel exhausted: defeq")
      annotate := fun _ _ => throw (.internal "fuel exhausted: annotate") }
  | fuel + 1 =>
    { whnfCore := (coreKnotIO fe (fuel + 1)).whnfCore
      whnf := (coreKnotIO fe (fuel + 1)).whnf
      defeq := (coreKnotIO fe (fuel + 1)).defeq
      infer := memoEI (·.inferFC) (fun st mp => { st with inferFC := mp })
        (fun d e => inferBodyI (coreKnotF fe fuel) fe d e)
      annotate := memoEI (·.annotC) (fun st mp => { st with annotC := mp })
        (fun d e => annotateBodyI (coreKnotF fe fuel) fe d e) }

/-- Drop the checking-mode inference memo.  Its keys are arena
indices, so it must go wherever the index-carrying memos go: at a
declaration boundary (`IState.flushed`'s job on the default path) and
at every snapshot close that truncates tier two. -/
def flushInferFC : CheckIM Unit :=
  modify fun s => { s with inferFC := {} }

end Setlec

import Setlec.Cached.StateC
import Setlec.Kernel.CoreCfg

/-!
# The cached-clone checker core

A twin of the interned core (`Setlec/Kernel/CoreI.lean`) over `ExprC`:
**every function below mirrors its interned original clause by
clause** — same order of record calls, same short-circuits, same
caches, same loops — with the arena replaced by the computed-field
representation.  The correspondence is deliberately literal (the store
wrappers survive as `CStore` no-ops, the interning wrappers as smart
constructors, the name/level interning as identities) so the two cores
can be diffed against each other; that is what makes a verdict-parity
claim auditable.

Unverified pilot code.  See DESIGN.md, "The cached-clone pilot".
-/

namespace Setlec.Cached

open Setlec

variable {m : Type → Type}

/-! ## The interned core record and helper twins -/

/-- The record of mutually recursive interned entry points. -/
structure CoreFnsI where
  whnfCore : Nat → ExprC → CheckCM ExprC
  whnf : Nat → ExprC → CheckCM ExprC
  infer : Nat → ExprC → CheckCM ExprC
  defeq : Nat → ExprC → ExprC → CheckCM Bool
  annotate : Nat → ExprC → CheckCM ExprC
  /-- Type inference at the **infer-only grade** (task #170 / #172 B4)
  — the twin of `CoreFns.inferIO` (`Setlec/Kernel/Core.lean`): what
  every internal inference call site runs.  The knot selects the
  grade's meaning per config (`cfg.ioGate`): the full `infer` at the
  R/parity configs, the io body (own memo, `CState.inferFC`) at the P
  config. -/
  inferIO : Nat → ExprC → CheckCM ExprC

/-- The io-grade view (twin of `CoreFns.ioView`): the record whose
full-grade `infer` slot is the io slot, so a body written against
`r.infer` recurses at the io grade when handed `r.ioView`. -/
def CoreFnsI.ioView (r : CoreFnsI) : CoreFnsI :=
  { r with infer := r.inferIO }

/-- Twin of `unfoldDefinition` (monadic: the unfolded value is interned
through the `(name, levels)` cache).  Like the spec, theorem values
unfold too. -/
def unfoldDefinitionI (fe : FEnv) (e : ExprC) : CheckCM (Option ExprC) := do
  match ← withStore (fun st => st.getNode (st.getAppFnI e)) with
  | some (.const n us) => do
    let nm ← readbackNM n
    match fe.find? nm with
    | some (.defnInfo cv _ _) =>
      if us.length = cv.levelParams.length then do
        let v ← constValAtM fe n nm us
        let args ← withStore (·.getAppArgsI e)
        let r ← mkAppNM v args
        pure (some r)
      else pure none
    | some (.thmInfo cv _) =>
      if us.length = cv.levelParams.length then do
        let v ← constValAtM fe n nm us
        let args ← withStore (·.getAppArgsI e)
        let r ← mkAppNM v args
        pure (some r)
      else pure none
    | _ => pure none
  | _ => pure none

/-- Twin of `litToCtorIfNat`. -/
def litToCtorIfNatI (fe : FEnv) (e : ExprC) : CheckCM ExprC := do
  match ← viewI e with
  | some (.lit (.natVal n)) =>
    if natLitSupportedF fe then internExprM (natLitToConstructor n)
    else pure e
  | _ => pure e

/-- Twin of `reduceNat`. -/
def reduceNatI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (e : ExprC) :
    CheckCM (Option ExprC) := do
  match ← viewI e with
  | some (.app f₁ b) =>
    match ← viewI f₁ with
    | some (.const c us) =>
      match us with
      | _ :: _ => pure none
      | [] => do
        let cn ← readbackNM c
        if cn = natSuccName ∧ natLitSupportedF fe then do
          let w ← r.whnf depth b
          match ← withStore (rawNatLitI? · w) with
          | some n => do
            let r ← internExprM (.lit (.natVal (n + 1)))
            pure (some r)
          | none => pure none
        else if cn = natPredName ∧ natOpStoredF fe cn = true then do
          let w ← r.whnf depth b
          match ← withStore (rawNatLitI? · w) with
          | some n =>
            match natOpResult cn n 0 with
            | some x => do
              let r ← internExprM x
              pure (some r)
            | none => pure none
          | none => pure none
        else if cn = natLog2Name ∧ natOpStoredF fe cn = true then do
          let w ← r.whnf depth b
          match ← withStore (rawNatLitI? · w) with
          | some n =>
            match natOpResult cn n 0 with
            | some x => do
              let r ← internExprM x
              pure (some r)
            | none => pure none
          | none => pure none
        else if cn = natLog2Name ∧ natLitSupportedF fe then do
          let w ← r.whnf depth b
          match ← withStore (rawNatLitI? · w) with
          | some _ => throw (.notImplemented
              s!"native Nat computation on literals ({cn})")
          | none => pure none
        else pure none
    | some (.app f₂ a) =>
      match ← viewI f₂ with
      | some (.const c us) =>
        match us with
        | _ :: _ => pure none
        | [] => do
          let cn ← readbackNM c
          if (cn = natAddName ∨ cn = natSubName ∨ cn = natMulName ∨
              cn = natPowName ∨ cn = natBeqName ∨ cn = natBleName ∨
              cn = natDivName ∨ cn = natModName ∨ cn = natGcdName ∨
              cn = natLandName ∨ cn = natLorName ∨ cn = natXorName ∨
              cn = natShiftLeftName ∨ cn = natShiftRightName) ∧
              natOpStoredF fe cn = true then do
            let w₁ ← r.whnf depth a
            let w₂ ← r.whnf depth b
            match ← withStore (rawNatLitI? · w₁),
                ← withStore (rawNatLitI? · w₂) with
            | some n₁, some n₂ =>
              match natOpResult cn n₁ n₂ with
              | some x => do
              let r ← internExprM x
              pure (some r)
              | none => pure none
            | _, _ => pure none
          else if natOpWfNames.contains cn ∧ natLitSupportedF fe then do
            let w₁ ← r.whnf depth a
            let w₂ ← r.whnf depth b
            match ← withStore (rawNatLitI? · w₁),
                ← withStore (rawNatLitI? · w₂) with
            | some _, some _ => throw (.notImplemented
                s!"native Nat computation on literals ({cn})")
            | _, _ => pure none
          else pure none
      | _ => pure none
    | _ => pure none
  | _ => pure none

/-- Twin of `iotaCerts`, bulk form (task #50): peel the raw telescope
while accumulating the certified arguments, substituting only each
binder's *domain* (small) instead of copying the whole residual
telescope per argument.  A raw `bvar` body (whose substitution could
expose further `∀`-binders — the fold semantics) substitutes the
accumulator and re-enters. -/
def iotaCertsIAux (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    ExprC → List ExprC → List ExprC → CheckCM Bool
  | _, _, [] => pure true
  | ty, acc, arg :: rest => do
    match ← viewI ty with
    | some (.forallE _ dom body _) => do
      let dom' ← instListM dom acc
      let ta ← r.inferIO depth arg
      if ← r.defeq depth ta dom' then
        iotaCertsIAux r fe depth body (arg :: acc) rest
      else pure false
    | some (.bvar _) =>
      match acc with
      | [] => pure false
      | _ :: _ => do
        let ty' ← instListM ty acc
        iotaCertsIAux r fe depth ty' [] (arg :: rest)
    | _ => pure false
termination_by _ acc args => (args.length, acc.length)
decreasing_by
  · apply Prod.Lex.left; simp
  · apply Prod.Lex.right' <;> simp

/-- Twin of `iotaCerts` (certify a spine against a recursor telescope);
the bulk-instantiating accumulator loop at the empty accumulator. -/
def iotaCertsI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (ty : ExprC) (args : List ExprC) : CheckCM Bool :=
  iotaCertsIAux r fe depth ty [] args

/-- Twin of `defEqList`. -/
def defEqListI (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    List ExprC → List ExprC → CheckCM Bool
  | [], [] => pure true
  | a :: as, b :: bs => do
    if ← r.defeq depth a b then
      defEqListI r fe depth as bs
    else pure false
  | _, _ => pure false

/-- Twin of `defeqSpine`. -/
def defeqSpineI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : ExprC) :
    CheckCM Bool := do
  match ← withStore (fun st => st.getNode (st.getAppFnI a)) with
  | some (.const n us) =>
    match ← withStore (fun st => st.getNode (st.getAppFnI b)) with
    | some (.const n' us') => do
      let aargs ← withStore (·.getAppArgsI a)
      let bargs ← withStore (·.getAppArgsI b)
      if n = n' ∧ aargs.length = bargs.length then
        match ← isEquivListLM us us' with
        | some true => defEqListI r fe depth aargs bargs
        | _ => pure false
      else pure false
    | _ => pure false
  | _ => pure false

/-- Twin of `proofIrrel`. -/
def proofIrrelI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : ExprC) :
    CheckCM Bool := do
  let ta ← r.inferIO depth a
  let wta ← r.whnf depth ta
  if ← withStore (fun st => isUnitLikeTyI fe st wta) then do
    let tb ← r.inferIO depth b
    let wtb ← r.whnf depth tb
    if ← withStore (fun st => isUnitLikeTyI fe st wtb) then
      pure true
    else
      pure false
  else do
    let tta ← r.inferIO depth ta
    let wtta ← r.whnf depth tta
    match ← viewI wtta with
    | some (.sort uT) => do
      let z ← internLM .zero
      let okA ← liftFueled "level comparison" (← isEquivLM uT z)
      let tb ← r.inferIO depth b
      let ttb ← r.inferIO depth tb
      let wttb ← r.whnf depth ttb
      match ← viewI wttb with
      | some (.sort vT) => do
        let z ← internLM .zero
        let okB ← liftFueled "level comparison" (← isEquivLM vT z)
        pure (okA && okB)
      | _ => pure false
    | _ => pure false

/- Task #147: functions below that mention `mode` take the
three-mode setting as their first explicit argument; only the seven
TT-lane check sites branch on it (`CheckMode.ttChecks`). -/
variable (mode : CheckMode)

/- Task #172 batch B2 — **THE BODY TEMPLATE'S PARAMETER.**  The
`whnfCore` clause family below (`whnfAppI`, `betaPeelI`,
`whnfCoreStepI`, `whnfCoreLoopI`, `whnfCoreBodyI`) takes `cfg :
CoreCfg` instead of `mode : CheckMode`, and is instantiated at the two
named flag-free concrete cores `whnfCoreBodyRC` / `whnfCoreBodyPC` at
the end of this module.  Nothing in the family branches on a
`CheckMode`; the ι cone's transitional `cfg.iotaMode` is a literal at
each core and its one downstream read (`ttChecks`) is definitionally
eliminated there (`Setlec/Kernel/CoreCfg.lean`). -/
variable (cfg : CoreCfg)

/-- Twin of `pairEtaCert`. -/
def pairEtaCertI (_cfg : CoreCfg) (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (a b : ExprC) :
    CheckCM Bool := do
  match ← viewI a with
  | some (.app f₄ s₂) =>
    match ← viewI f₄ with
    | some (.app f₃ s₁) =>
      match ← viewI f₃ with
      | some (.app f₂ pβ) =>
        match ← viewI f₂ with
        | some (.app f₁ pα) =>
          match ← viewI f₁ with
          | some (.const c us) => do
            let cn ← readbackNM c
            match fe.find? cn with
            | some (.ctorInfo _cvm 2 2) => do
              let tb ← r.inferIO depth b
              let wtb ← r.whnf depth tb
              match ← viewI wtb with
              | some (.app g₂ B) =>
                match ← viewI g₂ with
                | some (.app g₁ A) =>
                  match ← viewI g₁ with
                  | some (.const c' us') => do
                    let c'n ← readbackNM c'
                    match fe.find? c'n with
                    | some (.indInfo _ _) =>
                      match fe.find? (c'n.str "rec") with
                      | some (.recInfo _ mI rP [rr]) =>
                        if rr.ctor = cn ∧ rr.nfields = 2 ∧ mI = rP ∧
                            reservedBasisNames.contains (c'n.str "rec")
                              = true then do
                          if ← liftFueled "level comparison"
                              (← isEquivListLM us us') then do
                            if ← r.defeq depth pα A then do
                              if ← r.defeq depth pβ B then do
                                let p₀ ← internI (.proj c' 0 b)
                                if ← r.defeq depth s₁ p₀ then do
                                  let p₁ ← internI (.proj c' 1 b)
                                  if ← r.defeq depth s₂ p₁ then do
                                    pure true
                                  else pure false
                                else pure false
                              else pure false
                            else pure false
                          else pure false
                        else pure false
                      | _ => pure false
                    | _ => pure false
                  | _ => pure false
                | _ => pure false
              | _ => pure false
            | _ => pure false
          | _ => pure false
        | _ => pure false
      | _ => pure false
    | _ => pure false
  | _ => pure false

/-- The interned projection-application spine
`[proj_0 targs b, …]` (structural recursion; the spec side is a pure
`List.map`). -/
def projAppsFnI (T : Name) (us' : List Level) (targs : List ExprC)
    (b : ExprC) : List Nat → CheckCM (List ExprC)
  | [] => pure []
  | i :: rest => do
    let pf ← projFnIdxM T i
    let h ← internI (.const pf us')
    let r ← mkAppNM h (targs ++ [b])
    let rs ← projAppsFnI T us' targs b rest
    pure (r :: rs)

/-- The interned `.proj T i b` spine (the tower spelling, task #175
W4c). -/
def projNodesI (T : Name) (b : ExprC) : List Nat → CheckCM (List ExprC)
  | [] => pure []
  | i :: rest => do
    let r ← internI (.proj T i b)
    let rs ← projNodesI T b rest
    pure (r :: rs)

/-- Twin of `etaProjs`: the tower spelling at an all-tower slot family
(`towerSlotsAll` through the index), the projection-function spelling
otherwise.  `Tn` is the readback name, `T` the interned one. -/
def projAppsI (fe : FEnv) (Tn T : Name) (us' : List Level)
    (targs : List ExprC) (b : ExprC) (idxs : List Nat) :
    CheckCM (List ExprC) :=
  if idxs.all (fun j => match fe.findProj? Tn j with
      | some e => e.tower
      | none => false) then
    projNodesI T b idxs
  else projAppsFnI T us' targs b idxs

/-- Twin of `structEtaProjCerts`. -/
def structEtaProjCertsI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (TI : Name) (T : Name) (us' : List Level) (targs : List ExprC)
    (b : ExprC)
    (lpsT : List Name) : List Nat → CheckCM Bool
  | [] => pure true
  | i :: rest => do
    match fe.find? (projFnName T i) with
    | some (.recInfo cvp _ _ _) =>
      if cvp.levelParams = lpsT ∧
          (cvp.type.stripPis (targs.length + 1)).isSome = true then do
        let pf ← projFnIdxM TI i
        let pty ← constTyAtM fe pf (projFnName T i) us'
        if ← iotaCertsI r fe depth pty (targs ++ [b]) then
          structEtaProjCertsI r fe depth TI T us' targs b lpsT rest
        else pure false
      else pure false
    | some (.projInfo entry) =>
      -- a tower-backed entry (task #175 W4c), as in the spec body
      if entry.tower = true ∧ entry.levelParams = lpsT ∧
          (entry.ty.stripPis (targs.length + 1)).isSome = true then do
        let pf ← projFnIdxM TI i
        let pty ← constTyAtM fe pf (projFnName T i) us'
        if ← iotaCertsI r fe depth pty (targs ++ [b]) then
          structEtaProjCertsI r fe depth TI T us' targs b lpsT rest
        else pure false
      else pure false
    | _ => pure false

/-- Twin of `structEtaCertWith`. -/
def structEtaCertWithI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (a b wtb : ExprC) : CheckCM Bool := do
  match ← withStore (fun st => st.getNode (st.getAppFnI a)) with
  | some (.const c us) => do
    let cn ← readbackNM c
    match fe.find? cn with
    | some (.ctorInfo cvc cnP cnF) => do
      let aargs ← withStore (·.getAppArgsI a)
      if aargs.length = cnP + cnF then
        match ← withStore (fun st => st.getNode (st.getAppFnI wtb)) with
        | some (.const T us') => do
          let Tn ← readbackNM T
          match fe.find? Tn with
          | some (.indInfo cvT caps) => do
            let targs ← withStore (·.getAppArgsI wtb)
            if caps.eta = true ∧ caps.etaCtor = cn ∧
                caps.etaParams = cnP ∧ caps.etaFields = cnF ∧
                reservedBasisNames.contains Tn = false ∧
                reservedBasisNames.contains cn = false ∧
                targs.length = cnP ∧
                us'.length = cvT.levelParams.length ∧
                cvc.levelParams = cvT.levelParams ∧
                (cvT.type.stripPis cnP).isSome = true ∧
                (towerSlotsAllF fe Tn cnF || recSlotsAllF fe Tn cnF) = true then do
              if ← liftFueled "level comparison"
                  (← isEquivListLM us us') then do
                let tyT ← constTyAtM fe T Tn us'
                if ← iotaCertsI r fe depth tyT targs then do
                  if ← structEtaProjCertsI r fe depth T Tn us'
                      targs b cvT.levelParams (List.range cnF) then do
                    if ← defEqListI r fe depth (aargs.take cnP) targs then do
                      let projs ← projAppsI fe Tn T us' targs b (List.range cnF)
                      -- synthetic-spine certification (task #137): the
                      -- fabricated constructor application
                      -- `c targs (proj_i … b)` is certified against the
                      -- constructor's own telescope, here rather than at
                      -- the callers, so that BOTH consumers get it —
                      -- `majorToCtorI`'s eta rescue ran it already
                      -- (task #71), `defeq`'s `structEtaCertI` did not.
                      -- TT-lane check (task #147): skipped unless
                      -- `mode.ttChecks`.
                      if ← (if mode.ttChecks then do
                          let tyCtor ← constTyAtM fe c cn us
                          iotaCertsI r fe depth tyCtor (targs ++ projs)
                        else pure true) then
                        defEqListI r fe depth (aargs.drop cnP) projs
                      else pure false
                    else pure false
                  else pure false
                else pure false
              else pure false
            else pure false
          | _ => pure false
        | _ => pure false
      else pure false
    | _ => pure false
  | _ => pure false

/-- Twin of `structEtaCert`. -/
def structEtaCertI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : ExprC) :
    CheckCM Bool := do
  let tb ← r.inferIO depth b
  let wtb ← r.whnf depth tb
  structEtaCertWithI cfg.iotaMode r fe depth a b wtb

/-- Twin of `structUnitCert`. -/
def structUnitCertI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : ExprC) :
    CheckCM Bool := do
  let ta ← r.inferIO depth a
  let wta ← r.whnf depth ta
  match ← withStore (fun st => st.getNode (st.getAppFnI wta)) with
  | some (.const T us') => do
    let Tn ← readbackNM T
    match fe.find? Tn with
    | some (.indInfo cvT caps) => do
      let targs ← withStore (·.getAppArgsI wta)
      if caps.unitlike = true ∧
          reservedBasisNames.contains Tn = false ∧
          targs.length = caps.unitParams ∧
          us'.length = cvT.levelParams.length ∧
          (cvT.type.stripPis caps.unitParams).isSome = true then do
        let tb ← r.inferIO depth b
        let wtb ← r.whnf depth tb
        if ← r.defeq depth wta wtb then do
          let tyT ← constTyAtM fe T Tn us'
          iotaCertsI r fe depth tyT targs
        else pure false
      else pure false
    | _ => pure false
  | _ => pure false

/-- Twin of `etaCert` (the λ's pieces come pre-destructured, as in the
spec). -/
def etaCertI (r : CoreFnsI) (_fe : FEnv) (depth : Nat)
    (n₁ : Name) (ty₁ body₁ : ExprC) (m₁ : BinderMeta) (b : ExprC) :
    CheckCM Bool := do
  let tb ← r.inferIO depth b
  let wtb ← r.whnf depth tb
  match ← viewI wtb with
  | some (.forallE _ ty₂ _ m₂) => do
    -- prop-ness agreement checked LAST (task #161); see `etaCert`
    if ← r.defeq depth ty₂ ty₁ then do
      let fv ← internI (.fvar depth n₁ ty₁)
      let b₁ ← inst1M body₁ fv
      let ba ← internI (.app b fv)
      unless ← r.defeq (depth + 1) b₁ ba do return false
      if cfg.verified && !(m₁.pw.equiv m₂.pw) then
        throw (.notImplemented "sort-annotation mismatch (eta)")
      pure true
    else pure false
  | _ => pure false

/-- Twin of `stuckIrrel`. -/
def stuckIrrelI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : ExprC) :
    CheckCM Bool := do
  if ← pairEtaCertI cfg r fe depth a b then pure true
  else if ← pairEtaCertI cfg r fe depth b a then pure true
  else if ← structEtaCertI cfg r fe depth a b then pure true
  else if ← structEtaCertI cfg r fe depth b a then pure true
  else if ← structUnitCertI r fe depth a b then pure true
  else proofIrrelI r fe depth a b

/-- Twin of `majorToCtor`. -/
def majorToCtorI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (recName : Name) (rules : List RecRule) (major : ExprC) :
    CheckCM ExprC := do
  if ← withStore (fun st => isCtorAppI fe st major) then pure major else
  match rules with
  | [rl] =>
    match fe.find? rl.ctor with
    | some (.ctorInfo cvj cnP cnF) =>
      match (cvj.type.piResult).getAppFn with
      | .const T _ =>
        match fe.find? T with
        | some (.indInfo cvT caps) =>
          if caps.ruleK = true ∧ cnF = 0 then do
            let tmaj₀ ← r.inferIO depth major
            let tmaj ← r.whnf depth tmaj₀
            match ← withStore (fun st => st.getNode (st.getAppFnI tmaj)) with
            | some (.const T' ust) =>
              if (← beqNameM T' T) ∧ cvj.levelParams.length = ust.length then do
                let margs ← withStore (·.getAppArgsI tmaj)
                if cnP ≤ margs.length ∧
                    (cvj.type.stripPis cnP).isSome = true then do
                  let ctorI ← internNameM rl.ctor
                  let h ← internI (.const ctorI ust)
                  let fab ← mkAppNM h (margs.take cnP)
                  if ← withStore (fun st => st.wscopedBI depth fab &&
                      st.looseBVarsBoundedI 0 fab &&
                      st.leafGuardI fab major) then do
                    -- synthetic-spine certification (task #71): a
                    -- fabricated constructor spine keeps the ungated
                    -- telescope certificate, relocated here from the
                    -- fire path
                    let tyCtor ← constTyAtM fe ctorI rl.ctor ust
                    if ← iotaCertsI r fe depth tyCtor
                        (margs.take cnP) then do
                      -- official `to_cnstr_when_K` fabrication type
                      -- check (load-bearing with the major-slot
                      -- certificate gated at nonzero motives, tasks
                      -- #49/#71; arena bad/098_ruleKbad);
                      -- `proofIrrelI` stays as the soundness
                      -- certificate
                      let tfab ← r.inferIO depth fab
                      if ← r.defeq depth tmaj tfab then
                        if ← proofIrrelI r fe depth fab major then
                          pure fab
                        else pure major
                      else pure major
                    else pure major
                  else pure major
                else pure major
              else pure major
            | _ => pure major
          else if caps.eta = true ∧ rl.ctor = caps.etaCtor ∧
              Name.isProjFnShape recName = false then do
            let tmaj₀ ← r.inferIO depth major
            let tmaj ← r.whnf depth tmaj₀
            match ← withStore (fun st => st.getNode (st.getAppFnI tmaj)) with
            | some (.const T' ust) => do
              let margs ← withStore (·.getAppArgsI tmaj)
              let ustL ← readbackLevelsM ust
              -- instantiated non-Prop guard, as in the spec body
              -- `majorToCtor` (task #61)
              if (← beqNameM T' T) ∧ margs.length = caps.etaParams ∧
                  ust.length = cvT.levelParams.length ∧
                  piResultNeverZero cvT.levelParams ustL cvT.type = true then do
                if cvj.levelParams.length = ust.length ∧
                    (cvj.type.stripPis
                      (caps.etaParams + caps.etaFields)).isSome
                      = true then do
                  let TI ← internNameM T
                  let projs ← projAppsI fe T TI ust margs major
                    (List.range caps.etaFields)
                  let ctorI ← internNameM caps.etaCtor
                  let h ← internI (.const ctorI ust)
                  let fab ← mkAppNM h (margs ++ projs)
                  if ← withStore (fun st => st.wscopedBI depth fab &&
                      st.looseBVarsBoundedI 0 fab &&
                      st.leafGuardI fab major) then do
                    -- synthetic-spine certification, as in the K
                    -- branch (task #71)
                    let tyCtor ← constTyAtM fe ctorI rl.ctor ust
                    if ← iotaCertsI r fe depth tyCtor
                        (margs ++ projs) then do
                      if ← structEtaCertWithI mode r fe depth fab major
                          tmaj then
                        pure fab
                      else if caps.etaFields = 0 ∧
                          cvj.levelParams.length = ust.length then
                        if ← proofIrrelI r fe depth fab major then
                          pure fab
                        else pure major
                      else pure major
                    else pure major
                  else pure major
                else pure major
              else pure major
            | _ => pure major
          else pure major
        | _ => pure major
      | _ => pure major
    | _ => pure major
  | _ => pure major

/-- Twin of `litMajorToCtor`. -/
def litMajorToCtorI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (e : ExprC) :
    CheckCM ExprC := do
  match ← viewI e with
  | some (.lit (.strVal s)) =>
    if strLitSupportedF fe then do
      let x ← internExprM (strLitToConstructor s)
      r.whnf depth x
    else pure e
  | _ => litToCtorIfNatI fe e

/-- Twin of `projLitToCtor`. -/
def projLitToCtorI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (e : ExprC) :
    CheckCM ExprC := do
  match ← viewI e with
  | some (.lit (.strVal s)) =>
    if strLitSupportedF fe then do
      let x ← internExprM (strLitToConstructor s)
      r.whnf depth x
    else pure e
  | _ => pure e

/-- The interned nested-rule pin instantiations (structural recursion;
the spec side is `(recFireComparands …).2`'s `List.map`). -/
def pinArgsI (lps : List Name) (us : List Level) (args : List ExprC)
    (t : Nat) : List Expr → CheckCM (List ExprC)
  | [] => pure []
  | p :: ps => do
    let praw ← internExprM p
    let pi ← instLevelParamsM lps us praw
    let r ← instSpineM args t pi
    let rs ← pinArgsI lps us args t ps
    pure (r :: rs)

/-- Twin of `iotaRec`. -/
def iotaRecI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (e : ExprC) :
    CheckCM (Option ExprC) := do
  match ← withStore (fun st => st.getNode (st.getAppFnI e)) with
  | some (.const c us) => do
    let cn ← readbackNM c
    match fe.find? cn with
    | some (.recInfo cv mI rP rules) => do
      let args ← withStore (·.getAppArgsI e)
      -- checker change #9 (twin of `Core.lean`'s `iotaRec`): guard the
      -- recursor's level arity before the rule's RHS is instantiated.
      if args.length = mI + 1 ∧ us.length = cv.levelParams.length then do
        let bvar0 ← internI (.bvar 0)
        let major₀ ← r.whnf depth (args.getD mI bvar0)
        let major₁ ← litMajorToCtorI r fe depth major₀
        let major ← majorToCtorI mode r fe depth cn rules major₁
        match ← withStore (fun st => st.getNode (st.getAppFnI major)) with
        | some (.const cj usj) => do
          let cjn ← readbackNM cj
          match fe.find? cjn with
          | some (.ctorInfo cvj _ _) =>
            match rules.find? (fun r' => r'.ctor == cjn) with
            | some rl => do
              let margs ← withStore (·.getAppArgsI major)
              if margs.length = rl.ctorParams + rl.nfields then
               if rl.fire = .inert then
                 throw (.notImplemented
                   "iota reduction over a nested auxiliary recursor rule")
               else
               if (cv.type.stripPis (mI + 1)).isSome ∧
                  (cvj.type.stripPis (rl.ctorParams + rl.nfields)).isSome
                  then do
                -- the comparands (canonical: recursor's levels/args;
                -- nested: the stored major-domain instantiations)
                let cmpLvls : List Level ←
                  match rl.fire with
                  | .nested lvls _ => substLevelTreesM cv.levelParams us lvls
                  | _ =>
                    substLevelTreesM cv.levelParams us
                      (cvj.levelParams.map Level.param)
                let cmpArgs : List ExprC ←
                  match rl.fire with
                  | .nested _ pins =>
                    pinArgsI cv.levelParams us (args.take rP) (rP - 1) pins
                  | _ => pure (args.take rl.ctorParams)
                if ← liftFueled "level comparison"
                    (← isEquivListLM usj cmpLvls) then do
                 if ← defEqListI r fe depth (margs.take rl.ctorParams)
                    cmpArgs then do
                  let tyRec ← constTyAtM fe c cn us
                  if ← iotaCertsI r fe depth tyRec
                     (args.take mI ++ [major]) then do
                   let tyCtor ← constTyAtM fe cj cjn usj
                   if ← iotaCertsI r fe depth tyCtor margs then do
                    match ← withStore (fun st =>
                          st.stripPisBodyI (rl.ctorParams + rl.nfields)
                            tyCtor),
                        ← piResidualM tyCtor margs with
                    | some cbody, some residual =>
                      match ← withStore (fun st =>
                          st.getNode (st.getAppFnI cbody)) with
                      | some (.const _ _) => do
                        let resArgs ← withStore (·.getAppArgsI residual)
                        if ← defEqListI r fe depth
                            (resArgs.drop rl.ctorParams)
                            ((args.take mI).drop rP) then do
                          let rhs ← ruleRhsAtM fe c cj cn cjn us
                          let red ← mkAppNM rhs
                            (args.take rP ++ margs.drop rl.ctorParams)
                          pure (some red)
                        else pure none
                      | _ => pure none
                    | _, _ => pure none
                   else pure none
                  else pure none
                 else pure none
                else pure none
               else pure none
              else pure none
            | none => pure none
          | _ => pure none
        | _ => pure none
      else pure none
    | _ => pure none
  | _ => pure none

/-- Twin of `projCert`. -/
def projCertI (r : CoreFnsI) (_fe : FEnv) (depth : Nat)
    (e₂ : ExprC) (i : Nat) (nP : Nat) : CheckCM Bool := do
  let bvar0 ← internI (.bvar 0)
  let args ← withStore (·.getAppArgsI e₂)
  let arg := args.getD (nP + i) bvar0
  let _ta ← r.inferIO depth arg
  let _te ← r.inferIO depth e₂
  pure true

mutual

/-- Bulk-beta argument loop (task #50): consume the whole application
spine against the whnf'd head `v`.  A lambda head enters the peel loop
(first binder inline, which keeps the argument count decreasing);
other heads try iota with one more argument and otherwise accumulate a
stuck application — exactly the per-level `whnfCoreBody` app clauses,
but with the chained per-argument `instantiate1` of the beta path
replaced by one bulk substitution per peeled group
(`Setlec/Verify/BetaSpine.lean` proves the identification).  The
head-normalization loop's continuation `k` is threaded through
(task #106). -/
def whnfAppI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : ExprC → CheckCM ExprC) :
    ExprC → List ExprC → CheckCM ExprC
  | v, [] => pure v
  | v, a :: rest => do
    match ← viewI v with
    | some (.lam _ ty body mb) => do
        -- task #161: the β gate is a pure early return; the `else`
        -- arm is the pre-gate clause, verbatim (`betaGateFires`)
        if cfg.betaSkip mb.pw then
          betaPeelI r fe depth k body [a] rest
        else do
          -- task #172 B4: the β certificate's inference at the io grade
          let ta ← r.inferIO depth a
          if ← r.defeq depth ta ty then
            betaPeelI r fe depth k body [a] rest
          else do
            let fa ← internI (.app v a)
            mkAppNM fa rest
    | _ => do
      let fa ← internI (.app v a)
      match ← iotaRecI cfg.iotaMode r fe depth fa with
      | some e'' => do
        let v' ← k e''
        whnfAppI r fe depth k v' rest
      | none => whnfAppI r fe depth k fa rest
termination_by _ args => (args.length, 0)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

/-- Peel loop of `whnfAppI`: `t` is the raw (unsubstituted) lambda body
after the binders consumed so far, `acc` their arguments (innermost
first).  Each binder's argument certificate (unconditional since the
task-#100 de-gating) substitutes only the *domain*; the body is
substituted once, when peeling stops. -/
def betaPeelI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : ExprC → CheckCM ExprC) :
    ExprC → List ExprC → List ExprC → CheckCM ExprC
  | t, acc, [] => do
    let e' ← instListM t acc
    k e'
  | t, acc, a :: rest => do
    match ← viewI t with
    | some (.lam _ ty body mb) => do
        -- task #161: the β gate is a pure early return; the `else`
        -- arm is the pre-gate clause, verbatim (`betaGateFires`)
        if cfg.betaSkip mb.pw then
          betaPeelI r fe depth k body (a :: acc) rest
        else do
          let ty' ← instListM ty acc
          -- task #172 B4: the io grade (see `whnfAppI`)
          let ta ← r.inferIO depth a
          if ← r.defeq depth ta ty' then
            betaPeelI r fe depth k body (a :: acc) rest
          else do
            let f' ← instListM t acc
            let fa ← internI (.app f' a)
            mkAppNM fa rest
    | _ => do
      let e' ← instListM t acc
      let v ← k e'
      whnfAppI r fe depth k v (a :: rest)
termination_by _ _acc args => (args.length, 1)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

end

/-- Twin of `whnfCoreStep`: one head-normalization step (beta, iota,
zeta, projection) with the loop's continuation `k` abstracted, in the
open-recursion style of the whole module.  Only the spine head's
normalization stays a knot call (genuine nesting, bounded by the
term's depth); every *reduction* step is iteration, so a chain no
longer charges the shared recursion-depth budget one unit per step
(task #106 — that is what made the `Nat.brecOn` grind of
`Std.Time…toDays._proof_1` exhaust `checkFuel`). -/
def whnfCoreStepI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : ExprC → CheckCM ExprC) (e : ExprC) : CheckCM ExprC := do
    match ← viewI e with
    | some (.sort _) | some (.fvar ..) | some (.forallE ..)
    | some (.lam ..) | some (.const ..) | some (.lit _) => pure e
    | some (.app _ _) => do
      -- Bulk beta (task #50): normalize the spine head once and run the
      -- argument loop over the whole spine, batching consecutive
      -- lambda binders into one substitution.
      let h ← withStore (fun st => st.getAppFnI e)
      let args ← withStore (·.getAppArgsI e)
      let v ← r.whnfCore depth h
      whnfAppI cfg r fe depth k v args
    | some (.proj sn i pe) => do
      let e' ← r.whnf depth pe
      let e' ← projLitToCtorI r fe depth e'
      let snn ← readbackNM sn
      match fe.findProj? snn i with
      | some entry =>
        match ← withStore (fun st => st.getNode (st.getAppFnI e')) with
        | some (.const c us) => do
          let args ← withStore (·.getAppArgsI e')
          if entry.native ∧ (← beqNameM c entry.ctor) ∧ i < entry.numFields ∧
              args.length = entry.numParams + entry.numFields ∧
              us.length = entry.levelParams.length then do
            let bvar0 ← internI (.bvar 0)
            let arg := args.getD (entry.numParams + i) bvar0
            -- task #100 de-gating: the certificate runs
            -- unconditionally (the former nonzero-sort gate is
            -- unsound-to-model under the domain-relative collapse).
            -- Task #161 item B1: the two sort legs, their two
            -- `Level` arguments and the two `substLevelTreeM` calls
            -- that fed them are gone (see `projCert`).
            if ← projCertI r fe depth e' i entry.numParams then
              k arg
            else internI (.proj sn i e')
          else internI (.proj sn i e')
        | _ => internI (.proj sn i e')
      | none => internI (.proj sn i e')
    | some (.letE _ _ v b) => do
      -- zeta on demand (official `whnf_core` Let case); `inst1M` is the
      -- sharing-preserving arena substitution
      let e' ← inst1M b v
      k e'
    | some (.bvar _) =>
      throw (.notImplemented "whnf beyond the supported fragment")
    | none => throw (.internal "interned node missing")

/-- Twin of `whnfCoreLoop`: iterate `whnfCoreStepI` on its own step
budget. -/
def whnfCoreLoopI (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    Nat → ExprC → CheckCM ExprC
  | 0, _ => throw (.internal "fuel exhausted: whnfCore loop")
  | n + 1, e =>
    whnfCoreStepI cfg r fe depth (whnfCoreLoopI r fe depth n) e

/-- Twin of `whnfCoreBody`: the head-normalization loop at its own step
budget. -/
def whnfCoreBodyI (r : CoreFnsI) (fe : FEnv) : Nat → ExprC → CheckCM ExprC :=
  fun depth e => whnfCoreLoopI cfg r fe depth whnfCoreLoopFuel e

/-- Application-inference spine loop (task #50): walk the raw
Π-telescope against the arguments with deferred substitution — each
argument's certificate substitutes only its *domain*; the codomain is
substituted once per peeled group.  A non-syntactic telescope step
substitutes and normalizes, exactly like the chained `inferBody`
recursion (`Setlec/Verify/BetaSpine.lean` proves the
identification). -/
def inferSpineI (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    ExprC → Array ExprC → List ExprC → CheckCM ExprC
  | ty, acc, [] => instListRevM ty acc
  | ty, acc, a :: rest => do
    match ← viewI ty with
    | some (.forallE _ dom body _mt) => do
      -- per-argument re-check (task #100 de-gating: the former
      -- possibly-Prop gate of task #49 is unsound-to-model under the
      -- domain-relative collapse; the certificate runs
      -- unconditionally, as in the spec body `inferBody`)
      let dom' ← instListRevM dom acc
      let ta ← r.infer depth a
      unless ← r.defeq depth ta dom' do
        throw (.invalid "application type mismatch")
      inferSpineI r fe depth body (acc.push a) rest
    | _ => do
      let ty' ← instListRevM ty acc
      let w ← r.whnf depth ty'
      match ← viewI w with
      | some (.forallE _ dom body _mt) => do
        let ta ← r.infer depth a
        unless ← r.defeq depth ta dom do
          throw (.invalid "application type mismatch")
        inferSpineI r fe depth body #[a] rest
      | _ => throw (.invalid "function expected")

/-- **The io-grade spine walk** (task #172 B4): `inferSpineI` with the
per-argument certificate gated — the ONE io-graded check
(`inferBodyIO`'s app clause, `Setlec/Kernel/Core.lean`), in the bulk
telescope form.  At a ∀ step whose validated annotation datum is
`.never` (and only at a verified config — `cfg.verified` is law 1's
mode gate) the argument's inference and the domain comparison are
skipped; the returned type is the same telescope walk either way, so
the lane is annotation-blind in its results.  A syntactic `.forallE`
is its own whnf, so the syntactic step's datum is the datum the pure
io body reads off the whnf'd type. -/
def inferSpineIOI (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    ExprC → Array ExprC → List ExprC → CheckCM ExprC
  | ty, acc, [] => instListRevM ty acc
  | ty, acc, a :: rest => do
    match ← viewI ty with
    | some (.forallE _ dom body mt) => do
      unless cfg.verified && mt.pw.isNever do
        let dom' ← instListRevM dom acc
        let ta ← r.infer depth a
        unless ← r.defeq depth ta dom' do
          throw (.invalid "application type mismatch")
      inferSpineIOI r fe depth body (acc.push a) rest
    | _ => do
      let ty' ← instListRevM ty acc
      let w ← r.whnf depth ty'
      match ← viewI w with
      | some (.forallE _ dom body mt) => do
        unless cfg.verified && mt.pw.isNever do
          let ta ← r.infer depth a
          unless ← r.defeq depth ta dom do
            throw (.invalid "application type mismatch")
        inferSpineIOI r fe depth body #[a] rest
      | _ => throw (.invalid "function expected")

/-- Twin of `whnfStep`. -/
def whnfStepI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : ExprC → CheckCM ExprC) (e : ExprC) : CheckCM ExprC := do
  let e₁ ← r.whnfCore depth e
  match ← reduceNatI r fe depth e₁ with
  | some e₂ => k e₂
  | none =>
    match ← unfoldDefinitionI fe e₁ with
    | some e₂ => k e₂
    | none => pure e₁

/-- Twin of `whnfLoop`. -/
def whnfLoopI (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    Nat → ExprC → CheckCM ExprC
  | 0, _ => throw (.internal "fuel exhausted: whnf loop")
  | n + 1, e => whnfStepI r fe depth (whnfLoopI r fe depth n) e

/-- Twin of `whnfBody`. -/
def whnfBodyI (r : CoreFnsI) (fe : FEnv) : Nat → ExprC → CheckCM ExprC :=
  fun depth e => whnfLoopI r fe depth whnfLoopFuel e

/-- Twin of `ensureSort` (returns the level; no readback needed). -/
def ensureSortI (r : CoreFnsI) (depth : Nat) (e : ExprC) : CheckCM Level := do
  let w ← r.whnf depth e
  match ← viewI w with
  | some (.sort u) => pure u
  | _ => throw (.invalid "expected a sort")

/-! ### Binder-telescope loops (task #72)

The official-kernel discipline (lean4lean's `inferLambda`/`inferForall`
loops): peel a whole binder telescope accumulating opened free
variables, substituting only each binder's *domain* on the way in
(domains are small; `instListM` against the accumulator), infer or
annotate the leaf once on the bulk-opened body, then rebuild with one
`abstractRange` per domain and one over the leaf.  Each loop replays
exactly the per-binder checks of the chained recursion, in order; the
value-level identification with the chained spec bodies is
`Setlec/Verify/BinderLoop.lean` (the `DiscI` walks relate the interned
loops to their pure mirrors, and `_sound_body` theorems reproduce a
mirror run in the original one-binder-at-a-time body at some fuel).
The peel fuel (arena size, an upper bound for any chain in a canonical
arena) is semantically transparent: on exhaustion the leaf phase hands
the residual binder chain back to the knot, which is exactly the
chained spec's next step. -/

/-- Stack entry of `inferLamsI`: binder name, opened domain and binder
meta. -/
abbrev InferLamEntry := Name × ExprC × BinderMeta

/-- Rebuild loop of `inferLamsI`: fold the stack (innermost binder
first, `j` its binder level relative to the ambient depth `d`).  The
intermediate `∀`-node inferences of the chained body are
value-determined by the peel phase's domain sorts and the leaf phase's
body-type sort and cannot fail (task #100 stage 6: the per-level
λ-annotation re-check is gone with the stored annotations). -/
def inferLamsOutI (d : Nat) :
    List InferLamEntry → Nat → ExprC → PropWhen → CheckCM ExprC
  | [], _j, cur, _prevPw => pure cur
  | (n, tyo, mb) :: rest, j, cur, prevPw => do
    -- Task #161, the chain rule (see `inferBody`'s `.lam` clause): a
    -- node's prop-ness annotation must agree with its inner
    -- neighbour's (the innermost step compares the entry with itself
    -- — vacuously true).
    if cfg.verified && !(mb.pw.equiv prevPw) then
      throw (.notImplemented "sort-annotation mismatch (lam-cod-chain)")
    let tyAbs ← abstractRangeM tyo d j
    let node ← internI (.forallE n tyAbs cur mb)
    inferLamsOutI d rest (j - 1) node mb.pw

/-- Leaf phase of `inferLamsI`: bulk-open the residual body, infer it,
then rebuild outward.

Task #152: at the verified modes the chain's body type is
sort-checked here — the spec's codomain check (`inferBody`'s `.lam`
clause), which fires at the innermost binder of a λ-chain, i.e.
exactly when the peel stops on a non-λ residual.  The guard is the
same one the spec uses, on the same term. -/
def inferLamsLeafI (r : CoreFnsI) (d : Nat) (t : ExprC) (k : Nat)
    (fvs : Array ExprC) (stk : List InferLamEntry) : CheckCM ExprC := do
  let ob ← instListRevM t fvs
  let bt ← r.infer (d + k) ob
  match ← viewI t with
  | some (.lam ..) => pure ()
  | _ =>
    if cfg.verified then
      let btt ← r.inferIO (d + k) bt
      let wbtt ← r.whnf (d + k) btt
      match ← viewI wbtt with
      | some (.sort vb) =>
        -- Task #161: validate the innermost binder's prop-ness
        -- annotation against the chain's body-type sort — the leaf
        -- half of the spec's `.lam` clause check.
        match stk with
        | (_, _, mb₀) :: _ => do
          let pv ← withStore fun st => (st.zeronessOfLIGo {} vb).1
          unless pv.equiv mb₀.pw do
            throw (.notImplemented
              "sort-annotation mismatch (lam-cod-leaf)")
        | [] => pure ()
      | _ => throw (.invalid "expected a sort")
  let cur ← abstractRangeM bt d k
  -- The fold's initial neighbour: a λ residual (the fuel-exhausted
  -- path) supplies its own annotation — the head entry's chain check
  -- then compares against it, exactly as the spec's per-node clause
  -- does; a non-λ residual makes the head entry's step vacuous (its
  -- codomain fact is the leaf check above).
  let prevPw ← do
    match ← viewI t with
    | some (.lam _ _ _ mbT) => pure mbT.pw
    | _ =>
      pure (match stk with
        | (_, _, mb₀) :: _ => mb₀.pw
        | [] => .never)
  inferLamsOutI cfg d stk (k - 1) cur prevPw

/-- λ-telescope inference loop (task #72; used by `inferBodyI`'s and
`inferBodyNC`'s lam cases): peel the raw λ-chain, checking each opened
domain to be a type on the way in.  `k` counts the opened binders
(`≥ 1`: the caller peels the first binder inline), `fvs` their free
variables innermost-first. -/
def inferLamsI (r : CoreFnsI) (d : Nat) :
    Nat → ExprC → Nat → Array ExprC → List InferLamEntry → CheckCM ExprC
  | fuel + 1, t, k, fvs, stk => do
    match ← viewI t with
    | some (.lam n ty body mb) => do
      let tyo ← instListRevM ty fvs
      let tty ← r.infer (d + k) tyo
      let wtty ← r.whnf (d + k) tty
      match ← viewI wtty with
      | some (.sort _) => do
        let fv ← internI (.fvar (d + k) n tyo)
        inferLamsI r d fuel body (k + 1) (fvs.push fv)
          ((n, tyo, mb) :: stk)
      | _ => throw (.invalid "expected a sort")
    | _ => inferLamsLeafI cfg r d t k fvs stk
  | 0, t, k, fvs, stk => inferLamsLeafI cfg r d t k fvs stk

/-- Rebuild loop of `inferPisI`: fold the accumulated domain sorts by
`imax`, innermost binder first — exactly the chained `∀`-rule's result
value. -/
def inferPisOutI : List (Level × PropWhen) → Level → CStore.PWMemo → CheckCM Level
  | [], v, _memo => pure v
  | (u, pw) :: rest, v, memo => do
    -- Task #161: validate the node's prop-ness annotation against its
    -- inferred codomain sort (`v` is exactly the spec `∀`-clause's
    -- `v` at this node); the readout is memoized across the fold.
    let (pv, memo) ← withStore fun st => st.zeronessOfLIGo memo v
    if cfg.verified && !(pv.equiv pw) then
      throw (.notImplemented "sort-annotation mismatch (forall-cod)")
    let v' ← internLM (.imax u v)
    inferPisOutI rest v' memo

/-- Leaf phase of `inferPisI`: bulk-open the residual body, infer its
sort, then fold the domain sorts outward. -/
def inferPisLeafI (r : CoreFnsI) (d : Nat) (t : ExprC) (k : Nat)
    (fvs : Array ExprC) (stk : List (Level × PropWhen)) : CheckCM ExprC := do
  let ob ← instListRevM t fvs
  let bt ← r.infer (d + k) ob
  let wbt ← r.whnf (d + k) bt
  match ← viewI wbt with
  | some (.sort v) => do
    let iv ← inferPisOutI cfg stk v ({} : CStore.PWMemo)
    internI (.sort iv)
  | _ => throw (.invalid "expected a sort")

/-- ∀-telescope inference loop (task #100 stage 6: the `∀`-rule infers
its codomain sort — the stored annotation is not read): peel the raw
∀-chain, checking each opened domain to be a type on the way in and
accumulating its sort, infer the bulk-opened leaf's sort once, and
fold `imax` outward. -/
def inferPisI (r : CoreFnsI) (d : Nat) :
    Nat → ExprC → Nat → Array ExprC → List (Level × PropWhen) →
      CheckCM ExprC
  | fuel + 1, t, k, fvs, stk => do
    match ← viewI t with
    | some (.forallE n ty body mb) => do
      let tyo ← instListRevM ty fvs
      let tty ← r.infer (d + k) tyo
      let wtty ← r.whnf (d + k) tty
      match ← viewI wtty with
      | some (.sort u) => do
        let fv ← internI (.fvar (d + k) n tyo)
        inferPisI r d fuel body (k + 1) (fvs.push fv)
          ((u, mb.pw) :: stk)
      | _ => throw (.invalid "expected a sort")
    | _ => inferPisLeafI cfg r d t k fvs stk
  | 0, t, k, fvs, stk => inferPisLeafI cfg r d t k fvs stk

/-- Twin of `inferBody`. -/
def inferBodyI (r : CoreFnsI) (fe : FEnv) : Nat → ExprC → CheckCM ExprC :=
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
    | some (.forallE n ty body mb) => do
      -- Binder-telescope loop (task #72 discipline; the codomain sort
      -- is inferred; task #161: each node's prop-ness annotation is
      -- validated against it in the rebuild fold).
      let tty ← r.infer depth ty
      let wtty ← r.whnf depth tty
      match ← viewI wtty with
      | some (.sort u) => do
        let fv ← internI (.fvar depth n ty)
        let fuel ← peelFuelM
        inferPisI cfg r depth fuel body 1 #[fv] [(u, mb.pw)]
      | _ => throw (.invalid "expected a sort")
    | some (.lam n ty body mb) => do
      let tty ← r.infer depth ty
      let wtty ← r.whnf depth tty
      match ← viewI wtty with
      | some (.sort _) => do
        -- Binder-telescope loop (task #72): peel the whole λ-chain,
        -- open in bulk, rebuild with `abstractRange`.
        let fv ← internI (.fvar depth n ty)
        let fuel ← peelFuelM
        inferLamsI cfg r depth fuel body 1 #[fv] [(n, ty, mb)]
      | _ => throw (.invalid "expected a sort")
    | some (.app _ _) => do
      -- Bulk telescope consumption (task #50): infer the spine head
      -- once and walk its Π-telescope against the whole spine.
      let h ← withStore (fun st => st.getAppFnI e)
      let args ← withStore (·.getAppArgsI e)
      let tf ← r.infer depth h
      inferSpineI r fe depth tf #[] args
    | some (.proj sn i pe) => do
      let tpe ← r.infer depth pe
      let te ← r.whnf depth tpe
      match ← withStore (fun st => st.getNode (st.getAppFnI te)) with
      | some (.const T us) => do
        let Tn ← readbackNM T
        match fe.findProj? Tn i with
        | some entry => do
          let targs ← withStore (·.getAppArgsI te)
          if entry.native ∧ T = sn ∧ targs.length = entry.numParams ∧
              us.length = entry.levelParams.length then do
            if entry.tower then
              -- the official `infer_proj` restriction (task #175
              -- W4c/O4), as in the spec body
              if Level.isEquiv entry.structSort .zero == some true then
                unless Level.isEquiv
                    (Level.subst entry.levelParams us entry.fieldSort) .zero
                    == some true do
                  throw (.invalid
                    "projection from a propositional structure must be a proposition")
              -- task #175 wiring W2c: the tower-backed residual, as in
              -- the spec body — since B3a `ExprC = Expr` and the store
              -- is a unit, so the level-instantiated peel runs
              -- directly on the entry type and the interned spine.
              let tyI := entry.ty.instantiateLevelParams
                entry.levelParams us
              match Expr.instPisAt (targs ++ [pe]) tyI with
              | some (_, resid) => internExprM resid
              | none => throw (.internal "malformed projection entry")
            else
            -- Task #161 item B2 (harvest site 21 / P10): at a
            -- pair-backed entry the residual is computed, not walked
            -- — see the spec body.
            match targs, i with
            | [A, _], 0 => pure A
            | [_, B], 1 => do
              let p₀ ← internI (.proj T 0 pe)
              internI (.app B p₀)
            | _, _ => throw (.internal "malformed projection entry")
          else throw (.notImplemented "projection without a native entry")
        | none => throw (.notImplemented "projection without a native entry")
      | _ => throw (.notImplemented "projection without a native entry")
    | some (.letE _ ty v b) => do
      -- The official kernel's `infer_let` check order (`!infer_only`):
      -- the annotation is a type, the value's inferred type matches it,
      -- then the body with the value transparent (nanoda `infer_let`;
      -- task #100 stage 6: the checks moved here from the deleted
      -- annotation pass).
      let _ ← ensureSortI r depth (← r.infer depth ty)
      let tv ← r.infer depth v
      unless ← r.defeq depth tv ty do
        throw (.invalid "let value type mismatch")
      let e' ← inst1M b v
      r.infer depth e'
    | some (.bvar _) =>
      throw (.notImplemented "inferType beyond the supported fragment")
    | none => throw (.internal "interned node missing")

/-- **The io-grade inference body** (task #172 B4): `inferBodyI` with
exactly the application clause changed — the spine walk is the gated
`inferSpineIOI` (the ONE io-graded check).  Every non-application
view dispatches to `inferBodyI`'s own clause, so there is no textual
clone to drift: the two bodies differ in one clause by construction.
Recursion grade is the record's: the knot ties this body to
`CoreFnsI.ioView`, so `r.infer` here is the io slot one level down —
the grade propagates exactly as official's `infer_only` does. -/
def inferBodyIOI (r : CoreFnsI) (fe : FEnv) : Nat → ExprC → CheckCM ExprC :=
  fun depth e => do
    match ← viewI e with
    | some (.app _ _) => do
      let h ← withStore (fun st => st.getAppFnI e)
      let args ← withStore (·.getAppArgsI e)
      let tf ← r.infer depth h
      inferSpineIOI cfg r fe depth tf #[] args
    | some (.forallE n ty body mb) => do
      -- the pure io ∀ clause, **chained** (deliberately not the
      -- task-#72 telescope loop: the loops are the front door's
      -- optimization, and looping the io lane would owe the whole
      -- loop-identification walk family a second, io-graded instance
      -- for a lane whose subjects are internal re-inferences —
      -- recorded in the B4 seal as a measured-need follow-up)
      let tty ← r.infer depth ty
      let wtty ← r.whnf depth tty
      match ← viewI wtty with
      | some (.sort u) => do
        let fv ← internI (.fvar depth n ty)
        let ob ← inst1M body fv
        let bt ← r.infer (depth + 1) ob
        let v ← ensureSortI r (depth + 1) bt
        if cfg.verified then
          unless (Level.zeronessOf v).equiv mb.pw do
            throw (.notImplemented "sort-annotation mismatch (forall-cod)")
        let iu ← internLM (.imax u v)
        internI (.sort iu)
      | _ => throw (.invalid "expected a sort")
    | some (.lam n ty body mb) => do
      -- the pure io λ clause, chained
      let tty ← r.infer depth ty
      let wtty ← r.whnf depth tty
      match ← viewI wtty with
      | some (.sort _) => do
        let fv ← internI (.fvar depth n ty)
        let ob ← inst1M body fv
        let bt ← r.infer (depth + 1) ob
        if cfg.verified then
          match body.lamPw with
          | some pwI =>
            unless mb.pw.equiv pwI do
              throw (.notImplemented
                "sort-annotation mismatch (lam-cod-chain)")
          | none =>
            let btt ← r.infer (depth + 1) bt
            let vb ← ensureSortI r (depth + 1) btt
            unless (Level.zeronessOf vb).equiv mb.pw do
              throw (.notImplemented
                "sort-annotation mismatch (lam-cod-leaf)")
        let bAbs ← abstract1M bt depth
        internI (.forallE n ty bAbs mb)
      | _ => throw (.invalid "expected a sort")
    | _ => inferBodyI cfg r fe depth e

/-- Twin of `defeqStep`. -/
def defeqStepI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : ExprC → ExprC → CheckCM Bool) (a b : ExprC) : CheckCM Bool := do
    if a == b then pure true else
    let a' ← r.whnfCore depth a
    let b' ← r.whnfCore depth b
    if a' == b' then pure true else
    -- proof irrelevance hoisted before lazy delta, as in the spec
    -- (and the official kernel)
    if ← proofIrrelI r fe depth a' b' then pure true else
    -- Literal folding only when both sides are fvar-free, mirroring
    -- the official kernel (`type_checker.cpp`, `lazy_delta_reduction`)
    -- and lean4lean (`TypeChecker.lean:782`); see `defeqBody` for the
    -- full rationale.  `hasFvarI` is an `O(1)` read of the eager
    -- per-node fvar-range array.
    let fold ← withStore fun st => !st.hasFvarI a' && !st.hasFvarI b'
    match ← (if fold then reduceNatI r fe depth a' else pure none) with
    | some a₂ => k a₂ b'
    | none =>
    match ← (if fold then reduceNatI r fe depth b' else pure none) with
    | some b₂ => k a' b₂
    | none =>
    -- lazy delta, decision before materialization; see `defeqBody`
    match ← withStore (fun st => unfoldableHeadI fe st a'),
        ← withStore (fun st => unfoldableHeadI fe st b') with
    | true, false =>
      match ← unfoldDefinitionI fe a' with
      | some a₂ => k a₂ b'
      | none => pure false
    | false, true =>
      match ← unfoldDefinitionI fe b' with
      | some b₂ => k a' b₂
      | none => pure false
    | true, true => do
      let ha ← withStore (fun st => headHintI fe st a')
      let hb ← withStore (fun st => headHintI fe st b')
      if ReducibilityHint.lt hb ha then
        match ← unfoldDefinitionI fe a' with
        | some a₂ => k a₂ b'
        | none => pure false
      else if ReducibilityHint.lt ha hb then
        match ← unfoldDefinitionI fe b' with
        | some b₂ => k a' b₂
        | none => pure false
      else if ReducibilityHint.sameRegular ha hb &&
          (← withStore (sameConstHeadsI · a' b')) then do
        if ← defeqSpineI r fe depth a' b' then pure true
        else
          match ← unfoldDefinitionI fe a', ← unfoldDefinitionI fe b' with
          | some a₂, some b₂ => k a₂ b₂
          | _, _ => pure false
      else
        match ← unfoldDefinitionI fe a', ← unfoldDefinitionI fe b' with
        | some a₂, some b₂ => k a₂ b₂
        | _, _ => pure false
    | false, false =>
    match ← viewI a', ← viewI b' with
    | some (.sort u), some (.sort v) => do
      liftFueled "level comparison" (← isEquivLM u v)
    | some (.lit l₁), some (.lit l₂) => pure (l₁ == l₂)
    | some (.lit (.natVal n)), some (.const c us) =>
      if (← beqNameM c natZeroName) ∧ us = [] then pure (n == 0)
      else stuckIrrelI cfg r fe depth a' b'
    | some (.const c us), some (.lit (.natVal n)) =>
      if (← beqNameM c natZeroName) ∧ us = [] then pure (n == 0)
      else stuckIrrelI cfg r fe depth a' b'
    | some (.lit (.natVal nn)), some (.app f x) => do
      match nn, ← viewI f with
      | k + 1, some (.const c []) =>
        if ← beqNameM c natSuccName then do
          let kl ← internI (.lit (.natVal k))
          r.defeq depth kl x
        else stuckIrrelI cfg r fe depth a' b'
      | _, _ => stuckIrrelI cfg r fe depth a' b'
    | some (.app f x), some (.lit (.natVal nn)) => do
      match nn, ← viewI f with
      | k + 1, some (.const c []) =>
        if ← beqNameM c natSuccName then do
          let kl ← internI (.lit (.natVal k))
          r.defeq depth x kl
        else stuckIrrelI cfg r fe depth a' b'
      | _, _ => stuckIrrelI cfg r fe depth a' b'
    | some (.lit (.strVal s)), some (.app fO _x) => do
      match ← viewI fO with
      | some (.const cO usO) =>
        if (← beqNameM cO stringOfListName) ∧ usO = [] ∧ strLitSupportedF fe then do
          let sc ← internExprM (strLitToConstructor s)
          r.defeq depth sc b'
        else stuckIrrelI cfg r fe depth a' b'
      | _ => stuckIrrelI cfg r fe depth a' b'
    | some (.app fO _x), some (.lit (.strVal s)) => do
      match ← viewI fO with
      | some (.const cO usO) =>
        if (← beqNameM cO stringOfListName) ∧ usO = [] ∧ strLitSupportedF fe then do
          let sc ← internExprM (strLitToConstructor s)
          r.defeq depth a' sc
        else stuckIrrelI cfg r fe depth a' b'
      | _ => stuckIrrelI cfg r fe depth a' b'
    | some (.fvar i _ _), some (.fvar j _ _) =>
      if i == j then pure true
      else stuckIrrelI cfg r fe depth a' b'
    | some (.const n us), some (.const n' us') =>
      if n = n' then do
        if ← liftFueled "level comparison" (← isEquivListLM us us') then
          pure true
        else stuckIrrelI cfg r fe depth a' b'
      else stuckIrrelI cfg r fe depth a' b'
    | some (.forallE n₁ ty₁ body₁ m₁), some (.forallE n₂ ty₂ body₂ m₂) => do
      -- prop-ness agreement checked LAST (task #161); see `defeqBody`
      unless ← r.defeq depth ty₁ ty₂ do return false
      let fv₁ ← internI (.fvar depth n₁ ty₁)
      let b₁ ← inst1M body₁ fv₁
      let fv₂ ← internI (.fvar depth n₂ ty₂)
      let b₂ ← inst1M body₂ fv₂
      unless ← r.defeq (depth + 1) b₁ b₂ do return false
      if cfg.verified && !(m₁.pw.equiv m₂.pw) then
        throw (.notImplemented "sort-annotation mismatch (defeq-forall)")
      pure true
    | some (.lam n₁ ty₁ body₁ m₁), some (.lam n₂ ty₂ body₂ m₂) => do
      unless ← r.defeq depth ty₁ ty₂ do return false
      let fv₁ ← internI (.fvar depth n₁ ty₁)
      let b₁ ← inst1M body₁ fv₁
      let fv₂ ← internI (.fvar depth n₂ ty₂)
      let b₂ ← inst1M body₂ fv₂
      unless ← r.defeq (depth + 1) b₁ b₂ do return false
      if cfg.verified && !(m₁.pw.equiv m₂.pw) then
        throw (.notImplemented "sort-annotation mismatch (defeq-lam)")
      pure true
    | some (.app _f₁ _a₁), some (.app _f₂ _a₂) => do
      -- spine-wise congruence, as in the spec body `defeqBody`
      -- (official `is_def_eq_app`)
      let as₁ ← withStore (·.getAppArgsI a')
      let as₂ ← withStore (·.getAppArgsI b')
      if as₁.length = as₂.length then do
        let h₁ ← withStore (fun st => st.getAppFnI a')
        let h₂ ← withStore (fun st => st.getAppFnI b')
        if ← r.defeq depth h₁ h₂ then do
          if ← defEqListI r fe depth as₁ as₂ then pure true
          else stuckIrrelI cfg r fe depth a' b'
        else stuckIrrelI cfg r fe depth a' b'
      else stuckIrrelI cfg r fe depth a' b'
    | some (.proj s₁ i₁ e₁), some (.proj s₂ i₂ e₂) => do
      if s₁ == s₂ && i₁ == i₂ then do
        if ← r.defeq depth e₁ e₂ then pure true
        else stuckIrrelI cfg r fe depth a' b'
      else stuckIrrelI cfg r fe depth a' b'
    | some (.lam n₁ ty₁ body₁ m₁), _ => do
      if ← etaCertI cfg r fe depth n₁ ty₁ body₁ m₁ b' then pure true
      else stuckIrrelI cfg r fe depth a' b'
    | _, some (.lam n₂ ty₂ body₂ m₂) => do
      if ← etaCertI cfg r fe depth n₂ ty₂ body₂ m₂ a' then pure true
      else stuckIrrelI cfg r fe depth a' b'
    | some _, some _ => stuckIrrelI cfg r fe depth a' b'
    | _, _ => throw (.internal "interned node missing")

/-- Twin of `defeqLoop`. -/
def defeqLoopI (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    Nat → ExprC → ExprC → CheckCM Bool
  | 0, _, _ => throw (.internal "fuel exhausted: defeq loop")
  | fl + 1, a, b =>
    defeqStepI cfg r fe depth (defeqLoopI r fe depth fl) a b

/-- Twin of `defeqBody`. -/
def defeqBodyI (r : CoreFnsI) (fe : FEnv) : Nat → ExprC → ExprC → CheckCM Bool :=
  fun depth a b => defeqLoopI cfg r fe depth defeqLoopFuel a b

/-- Twin of `isPropType`. -/
def isPropTypeI (r : CoreFnsI) (_fe : FEnv) (depth : Nat) (ty : ExprC) :
    CheckCM Bool := do
  let ty' ← r.annotate depth ty
  let tty ← r.inferIO depth ty'
  let s ← ensureSortI r depth tty
  let z ← internLM .zero
  liftFueled "level comparison" (← isEquivLM s z)

/-- Twin of `projFieldDom`. -/
def projFieldDomI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (structProp : Bool) (sn : Name) (e' : ExprC) :
    Nat → Nat → ExprC → CheckCM ExprC
  | _j, 0, tel => do
    match ← viewI tel with
    | some (.forallE _ dom _ _) => pure dom
    | _ => throw (.invalid "projection index out of range")
  | j, k + 1, tel => do
    match ← viewI tel with
    | some (.forallE _ dom rest _) => do
      if ← withStore (fun st => st.looseBVarsBoundedI 0 rest) then
        projFieldDomI r fe depth structProp sn e' (j + 1) k rest
      else do
        if structProp then do
          unless ← isPropTypeI r fe depth dom do
            throw (.invalid
              "projection through a non-Prop field of a Prop structure")
        let pj ← internI (.proj sn j e')
        let rest' ← inst1M rest pj
        projFieldDomI r fe depth structProp sn e' (j + 1) k rest'
    | _ => throw (.invalid "projection index out of range")

/-- Twin of `annotateProjRec`. -/
def annotateProjRecI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (entry : ProjEntry) (i : Nat) (te e' : ExprC) (us : List Level) :
    CheckCM ExprC := do
  match fe.find? entry.ctor with
  | some (.ctorInfo _cvC _ cnF) => do
    let params ← withStore (·.getAppArgsI te)
    if params.length = entry.numParams then do
      let ctorI ← internNameM entry.ctor
      let ctorTy ← constTyAtM fe ctorI entry.ctor us
      match ← piResidualM ctorTy params with
      | some tel => do
        let structProp ← isPropTypeI r fe depth te
        let snI ← internNameM entry.structName
        let fi ← projFieldDomI r fe depth structProp snI e'
          0 i tel
        let fieldBvar ← internI (.bvar (cnF - 1 - i))
        match ← pisToLamsM cnF tel fieldBvar with
        | some minor => do
          let fi' ← r.annotate depth fi
          let tfi ← r.inferIO depth fi'
          let sfi ← ensureSortI r depth tfi
          if structProp then do
            let z ← internLM .zero
            unless ← liftFueled "level comparison"
                (← isEquivLM sfi z) do
              throw (.invalid "non-Prop projection from a Prop structure")
          let uf := if entry.recExtraLevel then [sfi] else []
          let recI ← internNameM (entry.structName.str "rec")
          let recC ← internI (.const recI (uf ++ us))
          let tI ← internNameM (.str .anonymous "t")
          let motive ← internI
            (.lam tI te fi ⟨.default, .never⟩)
          let raw ← mkAppNM recC (params ++ [motive, minor, e'])
          if ← withStore (fun st => st.wscopedBI depth raw &&
              st.looseBVarsBoundedI 0 raw &&
              st.leafGuardI raw e') then
            r.annotate depth raw
          else throw (.notImplemented "projection elimination scoping")
        | none => throw (.invalid "projection index out of range")
      | none => throw (.invalid "projection index out of range")
    else throw (.notImplemented "projection parameter mismatch")
  | _ => throw (.notImplemented
      "projection constructor not stored")

/-- Twin of `annotateProjElim`. -/
def annotateProjElimI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (sn : Name)
    (i : Nat) (te e' : ExprC) : CheckCM ExprC := do
  match ← withStore (fun st => st.getNode (st.getAppFnI te)) with
  | some (.const T us) => do
    let Tn ← readbackNM T
    if T = sn then
      match fe.find? (projFnName Tn i) with
      | some (.recInfo _ _ rP _) => do
        let targs ← withStore (·.getAppArgsI te)
        if targs.length = rP then do
          let pf ← projFnIdxM T i
          let h ← internI (.const pf us)
          let raw ← mkAppNM h (targs ++ [e'])
          if ← withStore (fun st => st.wscopedBI depth raw &&
              st.looseBVarsBoundedI 0 raw &&
              st.leafGuardI raw e') then
            r.annotate depth raw
          else throw (.notImplemented "projection elimination scoping")
        else throw (.notImplemented "projection parameter mismatch")
      | some (.projInfo entry) =>
        if entry.native then
          throw (.internal "native projection entry reached the fallback")
        else annotateProjRecI r fe depth entry i te e' us
      | _ =>
        throw (if (fe.find? (projFnName Tn 0)).isSome then
            CheckError.invalid "projection index out of range"
          else .notImplemented "projection on a non-structure-like type")
    else throw (.invalid "projection structure mismatch")
  | _ => throw (.notImplemented "projection on a non-structure type")

/-! ### Annotation binder-telescope loops (task #72; see the
`inferLamsI` block comment) -/

/-- Stack entry of the annotation loops: binder name, annotated opened
domain, binder info. -/
abbrev AnnotBinderEntry := Name × ExprC × BinderMeta

/-- The interned twin of `annotBinderMeta`. -/
def annotBinderMetaI (pw? : Option PropWhen) (mb : BinderMeta) : BinderMeta :=
  match pw? with
  | some pw => if pwWritten mb.pw then mb else ⟨mb.bi, pw⟩
  | none => mb

/-- Rebuild loop of the annotation binder-telescope loops: fold the
stack (innermost binder first, `j` its binder level), rebuilding one
binder node per entry.

Task #161 P5 — the untrusted write: `pw?` is the datum written just
below, threaded outward (`zeronessOf (imax u v) = zeronessOf v` makes
every ∀ node's codomain-sort zero-ness its inner neighbour's, and the
λ chain rule says the same of λ nodes — so the telescope pays one
computation, in the leaf phase, and every node above reads).  `none` =
no write (unverified mode).  A node whose input datum is a real
annotation (`pwWritten`) is left alone — validation judges it, and it
is that datum that travels on. -/
def annotateBindersOutI (mk : Name → ExprC → ExprC → BinderMeta → ExprView ExprC)
    (d : Nat) (pw? : Option PropWhen) :
    List AnnotBinderEntry → Nat → ExprC → CheckCM ExprC
  | [], _j, cur => pure cur
  | (n, ty', mb) :: rest, j, cur => do
    let tyAbs ← abstractRangeM ty' d j
    let node ← internI (mk n tyAbs cur (annotBinderMetaI pw? mb))
    -- Task #161 P5 (proof-lane repair): thread the datum *just
    -- written* outward rather than re-stamping the leaf's.  The two
    -- differ only above an explicitly-annotated binder, and there the
    -- chain rule is what the spec's `annotPwPi`/`annotPwLam` read —
    -- they see the rebuilt inner node, not the leaf.  One fold, one
    -- rule, both passes.
    annotateBindersOutI mk d
      (pw?.map fun _ => (annotBinderMetaI pw? mb).pw)
      rest (j - 1) node

/-- The ∀ telescope's datum (task #161 P5), computed once: the leaf
codomain sort's zero-ness — shared by every node of the telescope
because `zeronessOf (imax u v) = zeronessOf v`.  A ∀ residual (the fuel
path, or a `letE` whose zeta reduct is a ∀) supplies its own
already-written datum instead, exactly as `annotPwPi` reads it. -/
def annotPwPiI (r : CoreFnsI) (depth : Nat) (body' : ExprC) :
    CheckCM PropWhen := do
  match ← viewI body' with
  | some (.forallE _ _ _ mbT) => pure mbT.pw
  | _ => do
    let bt ← r.inferIO depth body'
    let v ← ensureSortI r depth bt
    withStore fun st => (st.zeronessOfLIGo {} v).1

/-- Gated for the telescope loop: `none` = no write. -/
def annotatePisPwI (r : CoreFnsI) (d k : Nat) (leaf' : ExprC) :
    CheckCM (Option PropWhen) :=
  if cfg.verified then do
    let p ← annotPwPiI r (d + k) leaf'
    pure (some p)
  else pure none

/-- Leaf phase of `annotatePisI`: bulk-open and annotate the residual
body, then rebuild outward. -/
def annotatePisLeafI (r : CoreFnsI) (d : Nat) (t : ExprC) (k : Nat)
    (fvs : Array ExprC) (stk : List AnnotBinderEntry) : CheckCM ExprC := do
  let to ← instListRevM t fvs
  let leaf' ← r.annotate (d + k) to
  let pw? ← annotatePisPwI cfg r d k leaf'
  let cur ← abstractRangeM leaf' d k
  annotateBindersOutI (fun n ty b mb => .forallE n ty b mb) d pw?
    stk (k - 1) cur

/-- ∀-telescope annotation loop (task #72; `annotateBodyI`'s forallE
case): peel the raw ∀-chain, annotating each opened domain on the way
in.  `k ≥ 1` counts the opened binders (first binder peeled inline by
the caller), `fvs` their free variables innermost-first. -/
def annotatePisI (r : CoreFnsI) (d : Nat) :
    Nat → ExprC → Nat → Array ExprC → List AnnotBinderEntry → CheckCM ExprC
  | fuel + 1, t, k, fvs, stk => do
    match ← viewI t with
    | some (.forallE n ty body mb) => do
      let tyo ← instListRevM ty fvs
      let ty' ← r.annotate (d + k) tyo
      let fv ← internI (.fvar (d + k) n ty')
      annotatePisI r d fuel body (k + 1) (fvs.push fv)
        ((n, ty', mb) :: stk)
    | _ => annotatePisLeafI cfg r d t k fvs stk
  | 0, t, k, fvs, stk => annotatePisLeafI cfg r d t k fvs stk

/-- The λ chain's datum (task #161 P5): the zero-ness of the sort of
the innermost body's TYPE; every λ node of the chain shares it (the
`(lam-cod-chain)` rule).  A λ residual supplies its own already-written
datum, exactly as `inferLamsLeafI` reads it. -/
def annotPwLamI (r : CoreFnsI) (depth : Nat) (body' : ExprC) :
    CheckCM PropWhen := do
  match ← viewI body' with
  | some (.lam _ _ _ mbT) => pure mbT.pw
  | _ => do
    let bt ← r.inferIO depth body'
    let btt ← r.inferIO depth bt
    let vb ← ensureSortI r depth btt
    withStore fun st => (st.zeronessOfLIGo {} vb).1

/-- Gated for the telescope loop: `none` = no write. -/
def annotateLamsPwI (r : CoreFnsI) (d k : Nat) (leaf' : ExprC) :
    CheckCM (Option PropWhen) :=
  if cfg.verified then do
    let p ← annotPwLamI r (d + k) leaf'
    pure (some p)
  else pure none

/-- Leaf phase of `annotateLamsI` (as `annotatePisLeafI`, rebuilding
λ-nodes). -/
def annotateLamsLeafI (r : CoreFnsI) (d : Nat) (t : ExprC) (k : Nat)
    (fvs : Array ExprC) (stk : List AnnotBinderEntry) : CheckCM ExprC := do
  let to ← instListRevM t fvs
  let leaf' ← r.annotate (d + k) to
  let pw? ← annotateLamsPwI cfg r d k leaf'
  let cur ← abstractRangeM leaf' d k
  annotateBindersOutI (fun n ty b mb => .lam n ty b mb) d pw?
    stk (k - 1) cur

/-- λ-telescope annotation loop (task #72; `annotateBodyI`'s lam
case). -/
def annotateLamsI (r : CoreFnsI) (d : Nat) :
    Nat → ExprC → Nat → Array ExprC → List AnnotBinderEntry → CheckCM ExprC
  | fuel + 1, t, k, fvs, stk => do
    match ← viewI t with
    | some (.lam n ty body mb) => do
      let tyo ← instListRevM ty fvs
      let ty' ← r.annotate (d + k) tyo
      let fv ← internI (.fvar (d + k) n ty')
      annotateLamsI r d fuel body (k + 1) (fvs.push fv)
        ((n, ty', mb) :: stk)
    | _ => annotateLamsLeafI cfg r d t k fvs stk
  | 0, t, k, fvs, stk => annotateLamsLeafI cfg r d t k fvs stk

/-- Twin of `annotateBody`. -/
def annotateBodyI (r : CoreFnsI) (fe : FEnv) : Nat → ExprC → CheckCM ExprC :=
  fun depth e => do
    match ← viewI e with
    | some (.bvar _) => pure e
    | some (.fvar idx _ _) =>
      if idx < depth then pure e
      else throw (.invalid "free variable out of scope")
    | some (.sort _) => pure e
    | some (.const ..) => pure e
    | some (.lit (.natVal _)) => do
      if natLitSupportedF fe then pure e
      else throw (.invalid "Nat literal without the Nat basis declarations")
    | some (.lit (.strVal _)) => do
      if strLitSupportedF fe then pure e
      else throw (.notImplemented
        "string literals before the String support declarations")
    | some (.app f a) => do
      -- structural (task #100 stage 6: the application checks moved to
      -- the driver's inference sweep)
      let f' ← r.annotate depth f
      let a' ← r.annotate depth a
      internI (.app f' a')
    | some (.forallE n ty body mb) => do
      -- Binder-telescope loop (task #72): peel the whole ∀-chain,
      -- open in bulk, rebuild with `abstractRange`.
      let ty' ← r.annotate depth ty
      let fv ← internI (.fvar depth n ty')
      let fuel ← peelFuelM
      annotatePisI cfg r depth fuel body 1 #[fv] [(n, ty', mb)]
    | some (.lam n ty body mb) => do
      -- The λ-loop is chain-identical only on bvar-closed nodes (the
      -- chained tails re-open exactly what they closed); disciplined
      -- inputs always are, and the cached bound decides in O(1).
      if (← bvarBoundM e) = 0 then do
        let ty' ← r.annotate depth ty
        let fv ← internI (.fvar depth n ty')
        let fuel ← peelFuelM
        annotateLamsI cfg r depth fuel body 1 #[fv] [(n, ty', mb)]
      else do
        let ty' ← r.annotate depth ty
        let fv ← internI (.fvar depth n ty')
        let ob ← inst1M body fv
        let body' ← r.annotate (depth + 1) ob
        let bAbs ← abstract1M body' depth
        -- task #161 P5: the single-binder write (the λ-loop's rule at
        -- a chain of length one; see `annotateLamsLeafI`)
        let pw ← if cfg.verified && !pwWritten mb.pw then
            annotPwLamI r (depth + 1) body'
          else pure mb.pw
        internI (.lam n ty' bAbs ⟨mb.bi, pw⟩)
    | some (.letE _ ty v b) => do
      -- the body with the value transparent (zeta at annotate;
      -- `inst1M` keeps the substitution sharing-preserving).  Task #161
      -- item C2 (harvest site 6): the redundant `infer_let` triple was
      -- deleted here — `inferBodyC`'s own `.letE` clause runs it (see
      -- the spec body).
      let _ ← r.annotate depth ty
      let _ ← r.annotate depth v
      let ob ← inst1M b v
      r.annotate depth ob
    | some (.proj sn i pe) => do
      let e' ← r.annotate depth pe
      let tpe ← r.inferIO depth e'
      let te ← r.whnf depth tpe
      match ← withStore (fun st => st.getNode (st.getAppFnI te)) with
      | some (.const T _) => do
        let Tn ← readbackNM T
        match fe.findProj? Tn i with
        | some entry =>
          if entry.native then do
            let targs ← withStore (·.getAppArgsI te)
            unless targs.length = entry.numParams do
              throw (.invalid "projection parameter mismatch")
            internI (.proj T i e')
          else annotateProjElimI r fe depth sn i te e'
        | none => annotateProjElimI r fe depth sn i te e'
      | _ => annotateProjElimI r fe depth sn i te e'
    | none => throw (.internal "interned node missing")

/-! ## The interned memoized knot -/

/-- Memoize a unary interned entry point under its index (`O(1)` key). -/
def memoEI (get' : CState → Std.HashMap ExprC ExprC)
    (set' : CState → Std.HashMap ExprC ExprC → CState)
    (f : Nat → ExprC → CheckCM ExprC) : Nat → ExprC → CheckCM ExprC :=
  fun d e => do
    match (get' (← get))[e]? with
    | some r => pure r
    | none =>
      let r ← f d e
      modify fun st =>
          let mp := get' st
        let st := set' st ∅
        set' st (mp.insert e r)
      pure r

/-- Memoize the interned definitional-equality entry point under the
index pair. -/
def memoBI (f : Nat → ExprC → ExprC → CheckCM Bool) :
    Nat → ExprC → ExprC → CheckCM Bool :=
  fun d a b => do
    match (← get).defeqC[(a, b)]? with
    | some r => pure r
    | none =>
      let r ← f d a b
      modify fun st =>
        let mp := st.defeqC
        let st := { st with defeqC := ∅ }
        { st with defeqC := mp.insert (a, b) r }
      pure r

/-- Tie the interned bodies at the memoizing state monad (fuel only
here, as in `coreKnot`; levels built lazily). -/
def coreKnotI (fe : FEnv) : Nat → CoreFnsI
  | 0 =>
    { whnfCore := fun _ _ => throw (.internal "fuel exhausted: whnfCore")
      whnf := fun _ _ => throw (.internal "fuel exhausted: whnf")
      infer := fun _ _ => throw (.internal "fuel exhausted: infer")
      defeq := fun _ _ _ => throw (.internal "fuel exhausted: defeq")
      annotate := fun _ _ => throw (.internal "fuel exhausted: annotate")
      inferIO := fun _ _ => throw (.internal "fuel exhausted: infer") }
  | fuel + 1 =>
    -- perf-eng E6 (EXPERIMENT, exe-only pricing — reverted before
    -- landing: 194 Verify/Cached references unfold this knot's
    -- equations, a real proof-adaptation bill): Thunk-cache the
    -- previous fuel level, as `coreKnotNC`'s E1.
    let prev : Thunk CoreFnsI := ⟨fun _ => coreKnotI fe fuel⟩
    -- task #172 B2: the template's config is built ONCE per knot
    -- level, not per `whnfCore` call.  Measured: leaving `cfgOf mode`
    -- inside the closure costs +0.155 % on `init-prelude` — a record
    -- allocation at every head-normalization entry.
    let cfg := cfgOf mode
    { whnfCore := memoEI (·.whnfCoreC)
        (fun st mp => { st with whnfCoreC := mp })
        (fun d e => whnfCoreBodyI cfg prev.get fe d e)
      whnf := memoEI (·.whnfC) (fun st mp => { st with whnfC := mp })
        (fun d e => whnfBodyI prev.get fe d e)
      infer := memoEI (·.inferC) (fun st mp => { st with inferC := mp })
        (fun d e => inferBodyI cfg prev.get fe d e)
      defeq := memoBI
        (fun d a b => defeqBodyI cfg prev.get fe d a b)
      annotate := memoEI (·.annotC) (fun st mp => { st with annotC := mp })
        (fun d e => annotateBodyI cfg prev.get fe d e)
      -- **The io slot** (task #170 / #172 B4), selected once per knot
      -- level: at the gated config the io body under its OWN memo
      -- (`CState.inferIOC` — the task-#170 memo ruling: a hit in the io
      -- memo never serves a full-infer query), tied to the io-grade
      -- view of the previous level (the grade propagates); at every
      -- other config the full inference closure, verbatim — one memo,
      -- because the two grades are the same function there (task #170:
      -- "in R mode infer_only is just equivalent to infer").
      inferIO := if cfg.ioGate then
          memoEI (·.inferIOC) (fun st mp => { st with inferIOC := mp })
            (fun d e => inferBodyIOI cfg prev.get.ioView fe d e)
        else
          memoEI (·.inferC) (fun st mp => { st with inferC := mp })
            (fun d e => inferBodyI cfg prev.get fe d e) }

/-! ## The named concrete cores (task #172, batches B2 and B3)

The template's whole point, spelled out: these are **definitions, not
clones** — one body, two names per family, and each unfolds to a term
with no `CheckMode` branch left in it.

* `whnfCoreBodyRC` is the R core's head normalization: `cfgR.betaSkip`
  is `fun _ => false`, so the β `if` **is** its `else` arm — the
  per-redex argument certificate, unconditional — by `rfl`, not by a
  collapse lemma;
* `whnfCoreBodyPC` is the P core's: `cfgP.betaSkip` is
  `PropWhen.isNever`, so the surviving branch reads the redex's
  **validated annotation datum**.  That is data, and it is the
  licence's own subject (`AnnotOkP_beta_gate`), not a flag.

B3 adds the remaining three configured families.  Their config read is
`cfg.verified` — the λ-codomain sort check and the ∀/λ annotation
validation — which is `true` at **both** `cfgR` and `cfgP`, so at each
named core the `if` is its own *then* arm by `rfl` and the check is
unconditionally present.  That is the R core's definition (census part
2 §2(b): *"every certificate unconditional"*), now true of the shipped
body by construction rather than by a hypothesis:

* `inferBodyRC` / `inferBodyPC` — the λ-chain codomain sort check and
  the ∀/λ chain-rule `pw` agreement, both unconditional;
* `defeqBodyRC` / `defeqBodyPC` — the `pw`-agreement comparisons at the
  ∀/λ conversion clauses and inside `etaCertI`, unconditional;
* `annotateBodyRC` / `annotateBodyPC` — the two annotation `pw` writes,
  unconditional.

**`whnf` needs no instantiation and that is a finding, not an
omission.**  `whnfBodyI` (and `whnfStepI`/`whnfLoopI` under it) reads
no configuration field at all: the whole δ/ι/β content sits in
`whnfCore`, which `whnf` reaches through the knot.  So the R and P
`whnf` are *the same function*, and naming it twice would assert a
distinction that does not exist.

The `rfl` identities against the mode-parametric spelling are in
`Setlec/Verify/BetaGate.lean` (the implementation tier may not import
`Verify`); they are what keeps the transition free: every landed
statement about `inferBodyI (cfgOf mode)` (etc.) is a statement about
these cores at the two concrete modes, definitionally. -/

/-- **The R core's head-normalization body.**  Flag-free by
construction. -/
def whnfCoreBodyRC (r : CoreFnsI) (fe : FEnv) : Nat → ExprC → CheckCM ExprC :=
  whnfCoreBodyI cfgR r fe

/-- **The P core's head-normalization body.**  Flag-free by
construction; the one surviving branch reads the validated annotation
datum. -/
def whnfCoreBodyPC (r : CoreFnsI) (fe : FEnv) : Nat → ExprC → CheckCM ExprC :=
  whnfCoreBodyI cfgP r fe

/-- **The R core's inference body.**  Flag-free: `cfgR.verified` is
`true`, so the λ-codomain sort check and the chain-rule annotation
agreement are unconditional. -/
def inferBodyRC (r : CoreFnsI) (fe : FEnv) : Nat → ExprC → CheckCM ExprC :=
  inferBodyI cfgR r fe

/-- **The P core's inference body.**  Flag-free, and identical in
shape to `inferBodyRC`: the io-graded skips are B4's, not this
field's. -/
def inferBodyPC (r : CoreFnsI) (fe : FEnv) : Nat → ExprC → CheckCM ExprC :=
  inferBodyI cfgP r fe

/-- **The R core's conversion body.**  Flag-free: the ∀/λ `pw`
agreement checks are unconditional. -/
def defeqBodyRC (r : CoreFnsI) (fe : FEnv) :
    Nat → ExprC → ExprC → CheckCM Bool :=
  defeqBodyI cfgR r fe

/-- **The P core's conversion body.**  Flag-free. -/
def defeqBodyPC (r : CoreFnsI) (fe : FEnv) :
    Nat → ExprC → ExprC → CheckCM Bool :=
  defeqBodyI cfgP r fe

/-- **The R core's annotation pass.**  Flag-free: the two `pw` writes
are unconditional.  (Annotation stays its own pass in every core — the
user's concession; what the template removes is the *flag*, not the
pass.) -/
def annotateBodyRC (r : CoreFnsI) (fe : FEnv) :
    Nat → ExprC → CheckCM ExprC :=
  annotateBodyI cfgR r fe

/-- **The P core's annotation pass.**  Flag-free. -/
def annotateBodyPC (r : CoreFnsI) (fe : FEnv) :
    Nat → ExprC → CheckCM ExprC :=
  annotateBodyI cfgP r fe

end Setlec.Cached

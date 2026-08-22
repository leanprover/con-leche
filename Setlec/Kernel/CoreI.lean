import Setlec.Kernel.Core
import Setlec.Kernel.IExpr

/-!
# The interned checker core (task #26)

Hand-written interned twins of the core bodies (`Setlec/Kernel/Core.lean`),
operating on arena indices (`EIdx` into an `EStore`, `Setlec/Kernel/
IExpr.lean`) instead of `Expr` trees.  Equality of interned terms is index
comparison, memo keys are indices (`O(1)` hash/compare), and the syntactic
operations are DAG-memoized — nanoda's expression-pointer design.

The state (`IState`) carries the arena, the id-keyed memo caches for the
five entry points, and lazy interning caches for level-instantiated stored
constants; its lifetime is one top-level entry-point call (exactly the
lifetime of the Expr-level `KCache`, and of nanoda's per-`TypeChecker`
temporary dag), so the environment is fixed while any cache lives.

Environment lookups go through `FEnv`: the spec environment plus a name
index built once per entry call by folding the constant list from the back
(newest insert wins), so the index's lookup function *is* `Env.find?`
(`Setlec/Verify/IExprOps.lean`, `mkFEnv_find?`).

Every twin mirrors its `Core.lean` original clause by clause — same order
of record calls, same short-circuits; the only extra effects are node
views, interning, and the caches.  Faithfulness (a successful interned run
is reproduced by the pure fueled knot under the denotation) is proven in
`Setlec/Verify/SimI.lean` / `Setlec/Verify/DiscI*.lean`.

Linearity: every mutation of a state component detaches the component from
the state record before updating (`let mp := s.f; let s := { s with f := ∅ };
… mp.insert …`), so the backing stores are uniquely referenced at each
update — the `memoE` discipline of `Setlec/Kernel/TypeCheckerC.lean`.
-/

namespace Setlec

/-! ## The indexed environment -/

/-- The spec environment together with a name index whose lookup function
agrees with `Env.find?` (built once per top-level entry call). -/
structure FEnv where
  env : Env
  idx : Std.HashMap Name ConstantInfo

/-- Build the index by folding from the back: the newest (front) constant
is inserted last and wins, exactly as `List.find?` takes the first match —
so the agreement with `Env.find?` is unconditional (no freshness
assumption). -/
def mkFEnv (env : Env) : FEnv :=
  ⟨env, env.consts.foldr (fun ci m => m.insert ci.name ci) ∅⟩

namespace FEnv

/-- Indexed lookup (`= Env.find?` for `mkFEnv`). -/
def find? (fe : FEnv) (n : Name) : Option ConstantInfo := fe.idx[n]?

/-- Indexed projection-table lookup (`= Env.findProj?` for `mkFEnv`). -/
def findProj? (fe : FEnv) (T : Name) (i : Nat) : Option ProjEntry :=
  match fe.find? (projFnName T i) with
  | some (.projInfo e) => some e
  | _ => none

end FEnv

/-! ### Indexed guard twins (same result as the `Env` versions) -/

/-- `natLitSupported` through the index. -/
def natLitSupportedF (fe : FEnv) : Bool :=
  natIndOk (fe.find? natName) && natZeroOk (fe.find? natZeroName) &&
    natSuccOk (fe.find? natSuccName)

/-- `strLitSupported` through the index. -/
def strLitSupportedF (fe : FEnv) : Bool :=
  natLitSupportedF fe &&
    stringTyOk (fe.find? stringName) &&
    stringOfListTyOk (fe.find? stringOfListName) &&
    listTyOk (fe.find? listName) &&
    listNilTyOk (fe.find? listNilName) &&
    listConsTyOk (fe.find? listConsName) &&
    charTyOk (fe.find? charName) &&
    charOfNatTyOk (fe.find? charOfNatName)

/-- `natOpGuard` through the index. -/
def natOpGuardF (fe : FEnv) (c : Name) : Bool :=
  natLitSupportedF fe &&
  (natOpDeps c).all (fun n => match fe.find? n with
    | some (.defnInfo cv _ _) => cv.levelParams.isEmpty
    | _ => false) &&
  (if c = natBeqName || c = natBleName || c = natDivName || c = natModName then
    (match fe.find? boolTrueName with
      | some ci => ci.toConstantVal.levelParams.isEmpty
      | none => false) &&
    (match fe.find? boolFalseName with
      | some ci => ci.toConstantVal.levelParams.isEmpty
      | none => false)
   else true)

/-- `isUnitLikeTy` through the index, on an interned (whnf'd) type. -/
def isUnitLikeTyI (fe : FEnv) (st : EStore) (e : EIdx) : Bool :=
  match st.nodes[e]? with
  | some (.const c _) =>
    (match fe.find? c with
      | some (.indInfo _ _) => true
      | _ => false) &&
    (match fe.find? (c.str "rec") with
      | some (.recInfo _ mI rP [r]) => mI == rP && r.nfields == 0
      | _ => false) &&
    reservedBasisNames.contains (c.str "rec")
  | _ => false

/-- `isCtorApp` through the index. -/
def isCtorAppI (fe : FEnv) (st : EStore) (e : EIdx) : Bool :=
  match st.nodes[st.getAppFnI e]? with
  | some (.const c _) =>
    match fe.find? c with
    | some (.ctorInfo _ _ _) => true
    | _ => false
  | _ => false

/-- `headHint` through the index. -/
def headHintI (fe : FEnv) (st : EStore) (e : EIdx) : ReducibilityHint :=
  match st.nodes[st.getAppFnI e]? with
  | some (.const n _) =>
    match fe.find? n with
    | some (.defnInfo _ _ hint) => hint
    | _ => .opaque
  | _ => .opaque

/-- `sameConstHeads` on indices. -/
def sameConstHeadsI (st : EStore) (a b : EIdx) : Bool :=
  match st.nodes[a]?, st.nodes[b]? with
  | some (.app f₁ _), some (.app f₂ _) =>
    match st.nodes[st.getAppFnI f₁]?, st.nodes[st.getAppFnI f₂]? with
    | some (.const n₁ _), some (.const n₂ _) => n₁ == n₂
    | _, _ => false
  | _, _ => false

/-- `rawNatLit?` on an index. -/
def rawNatLitI? (st : EStore) (e : EIdx) : Option Nat :=
  match st.nodes[e]? with
  | some (.lit (.natVal n)) => some n
  | some (.const c []) => if c = natZeroName then some 0 else none
  | _ => none

/-! ## The interned checker state and monad -/

/-- Per-entry-call state: the arena, id-keyed memo caches for the five
entry points, and lazy caches for level-instantiated stored constants
(type / definition value / recursor-rule right-hand side), keyed by name
and level instantiation. -/
structure IState where
  store : EStore := .empty
  constTyAt : Std.HashMap (Name × List Level) EIdx := {}
  constValAt : Std.HashMap (Name × List Level) EIdx := {}
  ruleRhsAt : Std.HashMap (Name × Name × List Level) EIdx := {}
  whnfCoreC : Std.HashMap EIdx EIdx := {}
  whnfC : Std.HashMap EIdx EIdx := {}
  inferC : Std.HashMap EIdx EIdx := {}
  defeqC : Std.HashMap (EIdx × EIdx) Bool := {}
  annotC : Std.HashMap EIdx EIdx := {}

instance : Inhabited IState := ⟨{}⟩

/-- The interned checker monad. -/
abbrev CheckIM := StateT IState CheckM

/-! ### Store access (linear discipline: detach before update) -/

/-- Read a node (no store change). -/
@[inline] def viewI (e : EIdx) : CheckIM (Option ENode) :=
  (fun s => s.store.nodes[e]?) <$> get

/-- Run a read-only store query. -/
@[inline] def withStore {α : Type} (f : EStore → α) : CheckIM α :=
  (fun s => f s.store) <$> get

/-- Intern one node. -/
@[inline] def internI (n : ENode) : CheckIM EIdx :=
  modifyGet fun s =>
    let store := s.store
    let s := { s with store := EStore.empty }
    let (i, store) := store.intern n
    (i, { s with store := store })

/-- Intern a whole `Expr` (used for small fabricated terms and for
stored-constant instantiations entering the arena). -/
@[inline] def internExprM (x : Expr) : CheckIM EIdx :=
  modifyGet fun s =>
    let store := s.store
    let s := { s with store := EStore.empty }
    let (i, store) := store.internExpr x
    (i, { s with store := store })

/-- Memoized interned `Expr.instantiate1`. -/
@[inline] def inst1M (e v : EIdx) (d : Nat := 0) : CheckIM EIdx :=
  modifyGet fun s =>
    let store := s.store
    let s := { s with store := EStore.empty }
    let (r, store) := store.instantiate1I e v d
    (r, { s with store := store })

/-- Memoized interned `Expr.abstract1`. -/
@[inline] def abstract1M (e : EIdx) (d : Nat) : CheckIM EIdx :=
  modifyGet fun s =>
    let store := s.store
    let s := { s with store := EStore.empty }
    let (r, store) := store.abstract1I e d
    (r, { s with store := store })

/-- Interned `Expr.mkAppN`. -/
@[inline] def mkAppNM (f : EIdx) (args : List EIdx) : CheckIM EIdx :=
  modifyGet fun s =>
    let store := s.store
    let s := { s with store := EStore.empty }
    let (r, store) := store.mkAppNI f args
    (r, { s with store := store })

/-- Interned `Expr.instSpine`. -/
@[inline] def instSpineM (args : List EIdx) (t : Nat) (e : EIdx) :
    CheckIM EIdx :=
  modifyGet fun s =>
    let store := s.store
    let s := { s with store := EStore.empty }
    let (r, store) := store.instSpineI args t e
    (r, { s with store := store })

/-- Interned `Expr.piResidual`/`Expr.instPis`. -/
@[inline] def piResidualM (e : EIdx) (args : List EIdx) :
    CheckIM (Option EIdx) :=
  modifyGet fun s =>
    let store := s.store
    let s := { s with store := EStore.empty }
    let (r, store) := store.piResidualI e args
    (r, { s with store := store })

/-- Interned `Expr.pisToLams`. -/
@[inline] def pisToLamsM (k : Nat) (e body : EIdx) : CheckIM (Option EIdx) :=
  modifyGet fun s =>
    let store := s.store
    let s := { s with store := EStore.empty }
    let (r, store) := store.pisToLamsI k e body
    (r, { s with store := store })

/-! ### Lazy interned stored-constant instantiations -/

/-- The interned level-instantiated *type* of the stored constant `n`
(cached by `(n, us)`; the constant must be stored — callers have already
matched the lookup). -/
def constTyAtM (fe : FEnv) (n : Name) (us : List Level) : CheckIM EIdx := do
  match (← get).constTyAt[(n, us)]? with
  | some i => pure i
  | none =>
    match fe.find? n with
    | some ci =>
      let cv := ci.toConstantVal
      let i ← internExprM (cv.type.instantiateLevelParams cv.levelParams us)
      modify fun s =>
        let mp := s.constTyAt
        let s := { s with constTyAt := ∅ }
        { s with constTyAt := mp.insert (n, us) i }
      pure i
    | none => throw (.internal "constTyAtM: unknown constant")

/-- The interned level-instantiated *value* of the stored definition `n`
(cached by `(n, us)`). -/
def constValAtM (fe : FEnv) (n : Name) (us : List Level) : CheckIM EIdx := do
  match (← get).constValAt[(n, us)]? with
  | some i => pure i
  | none =>
    match fe.find? n with
    | some (.defnInfo cv v _) =>
      let i ← internExprM (v.instantiateLevelParams cv.levelParams us)
      modify fun s =>
        let mp := s.constValAt
        let s := { s with constValAt := ∅ }
        { s with constValAt := mp.insert (n, us) i }
      pure i
    | _ => throw (.internal "constValAtM: not a stored definition")

/-- The interned level-instantiated right-hand side of the rule for
constructor `j` of the stored recursor `c` (cached by `(c, j, us)`). -/
def ruleRhsAtM (fe : FEnv) (c j : Name) (us : List Level) : CheckIM EIdx := do
  match (← get).ruleRhsAt[(c, j, us)]? with
  | some i => pure i
  | none =>
    match fe.find? c with
    | some (.recInfo cv _ _ rules) =>
      match rules.find? (fun r' => r'.ctor == j) with
      | some rl =>
        let i ← internExprM (rl.rhs.instantiateLevelParams cv.levelParams us)
        modify fun s =>
          let mp := s.ruleRhsAt
          let s := { s with ruleRhsAt := ∅ }
          { s with ruleRhsAt := mp.insert (c, j, us) i }
        pure i
      | none => throw (.internal "ruleRhsAtM: no rule for constructor")
    | _ => throw (.internal "ruleRhsAtM: not a stored recursor")

/-! ## The interned core record and helper twins -/

/-- The record of mutually recursive interned entry points. -/
structure CoreFnsI where
  whnfCore : Nat → EIdx → CheckIM EIdx
  whnf : Nat → EIdx → CheckIM EIdx
  infer : Nat → EIdx → CheckIM EIdx
  defeq : Nat → EIdx → EIdx → CheckIM Bool
  annotate : Nat → EIdx → CheckIM EIdx

/-- Twin of `unfoldDefinition` (monadic: the unfolded value is interned
through the `(name, levels)` cache). -/
def unfoldDefinitionI (fe : FEnv) (e : EIdx) : CheckIM (Option EIdx) := do
  match ← withStore (fun st => st.nodes[st.getAppFnI e]?) with
  | some (.const n us) =>
    match fe.find? n with
    | some (.defnInfo cv _ _) =>
      if us.length = cv.levelParams.length then do
        let v ← constValAtM fe n us
        let args ← withStore (·.getAppArgsI e)
        some <$> mkAppNM v args
      else pure none
    | _ => pure none
  | _ => pure none

/-- Twin of `litToCtorIfNat`. -/
def litToCtorIfNatI (fe : FEnv) (e : EIdx) : CheckIM EIdx := do
  match ← viewI e with
  | some (.lit (.natVal n)) =>
    if natLitSupportedF fe then internExprM (natLitToConstructor n)
    else pure e
  | _ => pure e

/-- Twin of `reduceNat`. -/
def reduceNatI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (e : EIdx) :
    CheckIM (Option EIdx) := do
  match ← viewI e with
  | some (.app f₁ b) =>
    match ← viewI f₁ with
    | some (.const c us) =>
      match us with
      | _ :: _ => pure none
      | [] =>
        if c = natSuccName ∧ natLitSupportedF fe then do
          let w ← r.whnf depth b
          match ← withStore (rawNatLitI? · w) with
          | some n => some <$> internExprM (.lit (.natVal (n + 1)))
          | none => pure none
        else if c = natPredName ∧ natOpGuardF fe c = true then do
          let w ← r.whnf depth b
          match ← withStore (rawNatLitI? · w) with
          | some n =>
            match natOpResult c n 0 with
            | some x => some <$> internExprM x
            | none => pure none
          | none => pure none
        else if c = natName.str "log2" ∧ natLitSupportedF fe then do
          let w ← r.whnf depth b
          match ← withStore (rawNatLitI? · w) with
          | some _ => throw (.notImplemented
              s!"native Nat computation on literals ({c})")
          | none => pure none
        else pure none
    | some (.app f₂ a) =>
      match ← viewI f₂ with
      | some (.const c us) =>
        match us with
        | _ :: _ => pure none
        | [] =>
          if (c = natAddName ∨ c = natSubName ∨ c = natMulName ∨
              c = natPowName ∨ c = natBeqName ∨ c = natBleName ∨
              c = natDivName ∨ c = natModName) ∧
              natOpGuardF fe c = true then do
            let w₁ ← r.whnf depth a
            let w₂ ← r.whnf depth b
            match ← withStore (rawNatLitI? · w₁),
                ← withStore (rawNatLitI? · w₂) with
            | some n₁, some n₂ =>
              match natOpResult c n₁ n₂ with
              | some x => some <$> internExprM x
              | none => pure none
            | _, _ => pure none
          else if natOpWfNames.contains c ∧ natLitSupportedF fe then do
            let w₁ ← r.whnf depth a
            let w₂ ← r.whnf depth b
            match ← withStore (rawNatLitI? · w₁),
                ← withStore (rawNatLitI? · w₂) with
            | some _, some _ => throw (.notImplemented
                s!"native Nat computation on literals ({c})")
            | _, _ => pure none
          else pure none
      | _ => pure none
    | _ => pure none
  | _ => pure none

/-- Twin of `iotaCerts`. -/
def iotaCertsI (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    EIdx → List EIdx → CheckIM Bool
  | _, [] => pure true
  | ty, arg :: rest => do
    match ← viewI ty with
    | some (.forallE _ dom body _) => do
      let ta ← r.infer depth arg
      if ← r.defeq depth ta dom then do
        let body' ← inst1M body arg
        iotaCertsI r fe depth body' rest
      else pure false
    | _ => pure false

/-- Twin of `defEqList`. -/
def defEqListI (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    List EIdx → List EIdx → CheckIM Bool
  | [], [] => pure true
  | a :: as, b :: bs => do
    if ← r.defeq depth a b then
      defEqListI r fe depth as bs
    else pure false
  | _, _ => pure false

/-- Twin of `defeqSpine`. -/
def defeqSpineI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : EIdx) :
    CheckIM Bool := do
  match ← withStore (fun st => st.nodes[st.getAppFnI a]?) with
  | some (.const n us) =>
    match ← withStore (fun st => st.nodes[st.getAppFnI b]?) with
    | some (.const n' us') => do
      let aargs ← withStore (·.getAppArgsI a)
      let bargs ← withStore (·.getAppArgsI b)
      if n = n' ∧ aargs.length = bargs.length then
        match Level.isEquivList us us' with
        | some true => defEqListI r fe depth aargs bargs
        | _ => pure false
      else pure false
    | _ => pure false
  | _ => pure false

/-- Twin of `proofIrrel`. -/
def proofIrrelI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : EIdx) :
    CheckIM Bool := do
  let ta ← r.infer depth a
  let wta ← r.whnf depth ta
  if ← withStore (fun st => isUnitLikeTyI fe st wta) then do
    let tb ← r.infer depth b
    let wtb ← r.whnf depth tb
    if ← withStore (fun st => isUnitLikeTyI fe st wtb) then
      pure true
    else
      pure false
  else do
    let tta ← r.infer depth ta
    let wtta ← r.whnf depth tta
    match ← viewI wtta with
    | some (.sort uT) => do
      let okA ← liftFueled "level comparison" (Level.isEquiv uT .zero)
      let tb ← r.infer depth b
      let ttb ← r.infer depth tb
      let wttb ← r.whnf depth ttb
      match ← viewI wttb with
      | some (.sort vT) => do
        let okB ← liftFueled "level comparison" (Level.isEquiv vT .zero)
        pure (okA && okB)
      | _ => pure false
    | _ => pure false

/-- Twin of `pairEtaCert`. -/
def pairEtaCertI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : EIdx) :
    CheckIM Bool := do
  match ← viewI a with
  | some (.app f₄ s₂) =>
    match ← viewI f₄ with
    | some (.app f₃ s₁) =>
      match ← viewI f₃ with
      | some (.app f₂ _pβ) =>
        match ← viewI f₂ with
        | some (.app f₁ _pα) =>
          match ← viewI f₁ with
          | some (.const c us) =>
            match fe.find? c with
            | some (.ctorInfo _cvm 2 2) => do
              let tb ← r.infer depth b
              let wtb ← r.whnf depth tb
              match ← viewI wtb with
              | some (.app g₂ _B) =>
                match ← viewI g₂ with
                | some (.app g₁ _A) =>
                  match ← viewI g₁ with
                  | some (.const c' us') =>
                    match fe.find? c' with
                    | some (.indInfo _ _) =>
                      match fe.find? (c'.str "rec") with
                      | some (.recInfo _ mI rP [rr]) =>
                        if rr.ctor = c ∧ rr.nfields = 2 ∧ mI = rP ∧
                            reservedBasisNames.contains (c'.str "rec")
                              = true then do
                          if ← liftFueled "level comparison"
                              (Level.isEquivList us us') then do
                            let p₀ ← internI (.proj c' 0 b)
                            if ← r.defeq depth s₁ p₀ then do
                              let p₁ ← internI (.proj c' 1 b)
                              r.defeq depth s₂ p₁
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

/-- Twin of `structEtaProjCerts`. -/
def structEtaProjCertsI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (T : Name) (us' : List Level) (targs : List EIdx) (b : EIdx)
    (lpsT : List Name) : List Nat → CheckIM Bool
  | [] => pure true
  | i :: rest => do
    match fe.find? (projFnName T i) with
    | some (.recInfo cvp _ _ _) =>
      if cvp.levelParams = lpsT ∧
          (cvp.type.stripPis (targs.length + 1)).isSome = true then do
        let pty ← constTyAtM fe (projFnName T i) us'
        if ← iotaCertsI r fe depth pty (targs ++ [b]) then
          structEtaProjCertsI r fe depth T us' targs b lpsT rest
        else pure false
      else pure false
    | _ => pure false

/-- Twin of `structEtaCertWith`. -/
def structEtaCertWithI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (a b wtb : EIdx) : CheckIM Bool := do
  match ← withStore (fun st => st.nodes[st.getAppFnI a]?) with
  | some (.const c us) =>
    match fe.find? c with
    | some (.ctorInfo cvc cnP cnF) => do
      let aargs ← withStore (·.getAppArgsI a)
      if aargs.length = cnP + cnF then
        match ← withStore (fun st => st.nodes[st.getAppFnI wtb]?) with
        | some (.const T us') =>
          match fe.find? T with
          | some (.indInfo cvT caps) => do
            let targs ← withStore (·.getAppArgsI wtb)
            if caps.eta = true ∧ caps.etaCtor = c ∧
                caps.etaParams = cnP ∧ caps.etaFields = cnF ∧
                reservedBasisNames.contains T = false ∧
                reservedBasisNames.contains c = false ∧
                targs.length = cnP ∧
                us'.length = cvT.levelParams.length ∧
                cvc.levelParams = cvT.levelParams ∧
                (cvT.type.stripPis cnP).isSome = true then do
              if ← liftFueled "level comparison"
                  (Level.isEquivList us us') then do
                let tyT ← constTyAtM fe T us'
                if ← iotaCertsI r fe depth tyT targs then do
                  if ← structEtaProjCertsI r fe depth T us'
                      targs b cvT.levelParams (List.range cnF) then do
                    if ← defEqListI r fe depth (aargs.take cnP) targs then do
                      let projs ← (List.range cnF).mapM fun i => do
                        let h ← internI (.const (projFnName T i) us')
                        mkAppNM h (targs ++ [b])
                      defEqListI r fe depth (aargs.drop cnP) projs
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
def structEtaCertI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : EIdx) :
    CheckIM Bool := do
  let tb ← r.infer depth b
  let wtb ← r.whnf depth tb
  structEtaCertWithI r fe depth a b wtb

/-- Twin of `structUnitCert`. -/
def structUnitCertI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : EIdx) :
    CheckIM Bool := do
  let ta ← r.infer depth a
  let wta ← r.whnf depth ta
  match ← withStore (fun st => st.nodes[st.getAppFnI wta]?) with
  | some (.const T us') =>
    match fe.find? T with
    | some (.indInfo cvT caps) => do
      let targs ← withStore (·.getAppArgsI wta)
      if caps.unitlike = true ∧
          reservedBasisNames.contains T = false ∧
          targs.length = caps.unitParams ∧
          us'.length = cvT.levelParams.length ∧
          (cvT.type.stripPis caps.unitParams).isSome = true then do
        let tb ← r.infer depth b
        let wtb ← r.whnf depth tb
        if ← r.defeq depth wta wtb then do
          let tyT ← constTyAtM fe T us'
          iotaCertsI r fe depth tyT targs
        else pure false
      else pure false
    | _ => pure false
  | _ => pure false

/-- Twin of `etaCert` (the λ's pieces come pre-destructured, as in the
spec). -/
def etaCertI (r : CoreFnsI) (_fe : FEnv) (depth : Nat)
    (n₁ : Name) (ty₁ body₁ : EIdx) (m₁ : BinderMeta) (b : EIdx) :
    CheckIM Bool := do
  let tb ← r.infer depth b
  let wtb ← r.whnf depth tb
  match ← viewI wtb with
  | some (.forallE _ ty₂ _ m₂) =>
    match m₁.cod, m₂.cod with
    | some v₁, some v₂ => do
      if ← liftFueled "level comparison" (Level.isEquiv v₁ v₂) then do
        if ← r.defeq depth ty₂ ty₁ then do
          let fv ← internI (.fvar depth n₁ ty₁)
          let b₁ ← inst1M body₁ fv
          let ba ← internI (.app b fv)
          r.defeq (depth + 1) b₁ ba
        else pure false
      else pure false
    | _, _ => pure false
  | _ => pure false

/-- Twin of `stuckIrrel`. -/
def stuckIrrelI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : EIdx) :
    CheckIM Bool := do
  if ← pairEtaCertI r fe depth a b then pure true
  else if ← pairEtaCertI r fe depth b a then pure true
  else if ← structEtaCertI r fe depth a b then pure true
  else if ← structEtaCertI r fe depth b a then pure true
  else if ← structUnitCertI r fe depth a b then pure true
  else proofIrrelI r fe depth a b

/-- Twin of `majorToCtor`. -/
def majorToCtorI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (recName : Name) (rules : List RecRule) (major : EIdx) :
    CheckIM EIdx := do
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
            let tmaj₀ ← r.infer depth major
            let tmaj ← r.whnf depth tmaj₀
            match ← withStore (fun st => st.nodes[st.getAppFnI tmaj]?) with
            | some (.const T' ust) =>
              if T' = T ∧ cvj.levelParams.length = ust.length then do
                let margs ← withStore (·.getAppArgsI tmaj)
                let h ← internI (.const rl.ctor ust)
                let fab ← mkAppNM h (margs.take cnP)
                if ← withStore (fun st => st.wscopedBI depth fab &&
                    st.looseBVarsBoundedI 0 fab &&
                    (st.fvarLeavesI fab).all
                      (fun l => (st.fvarLeavesI major).contains l)) then do
                  if ← proofIrrelI r fe depth fab major then pure fab
                  else pure major
                else pure major
              else pure major
            | _ => pure major
          else if caps.eta = true ∧ rl.ctor = caps.etaCtor ∧
              Name.isProjFnShape recName = false ∧
              piResultIsProp cvT.type = false then do
            let tmaj₀ ← r.infer depth major
            let tmaj ← r.whnf depth tmaj₀
            match ← withStore (fun st => st.nodes[st.getAppFnI tmaj]?) with
            | some (.const T' ust) => do
              let margs ← withStore (·.getAppArgsI tmaj)
              if T' = T ∧ margs.length = caps.etaParams ∧
                  ust.length = cvT.levelParams.length then do
                let projs ← (List.range caps.etaFields).mapM fun j => do
                  let h ← internI (.const (projFnName T j) ust)
                  mkAppNM h (margs ++ [major])
                let h ← internI (.const caps.etaCtor ust)
                let fab ← mkAppNM h (margs ++ projs)
                if ← withStore (fun st => st.wscopedBI depth fab &&
                    st.looseBVarsBoundedI 0 fab &&
                    (st.fvarLeavesI fab).all
                      (fun l => (st.fvarLeavesI major).contains l)) then do
                  if ← structEtaCertWithI r fe depth fab major tmaj then
                    pure fab
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
def litMajorToCtorI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (e : EIdx) :
    CheckIM EIdx := do
  match ← viewI e with
  | some (.lit (.strVal s)) =>
    if strLitSupportedF fe then do
      let x ← internExprM (strLitToConstructor s)
      r.whnf depth x
    else pure e
  | _ => litToCtorIfNatI fe e

/-- Twin of `iotaRec`. -/
def iotaRecI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (e : EIdx) :
    CheckIM (Option EIdx) := do
  match ← withStore (fun st => st.nodes[st.getAppFnI e]?) with
  | some (.const c us) =>
    match fe.find? c with
    | some (.recInfo cv mI rP rules) => do
      let args ← withStore (·.getAppArgsI e)
      if args.length = mI + 1 then do
        let bvar0 ← internI (.bvar 0)
        let major₀ ← r.whnf depth (args.getD mI bvar0)
        let major₁ ← litMajorToCtorI r fe depth major₀
        let major ← majorToCtorI r fe depth c rules major₁
        match ← withStore (fun st => st.nodes[st.getAppFnI major]?) with
        | some (.const cj usj) =>
          match fe.find? cj with
          | some (.ctorInfo cvj _ _) =>
            match rules.find? (fun r' => r'.ctor == cj) with
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
                let cmpLvls : List Level :=
                  match rl.fire with
                  | .nested lvls _ => lvls.map (Level.subst cv.levelParams us)
                  | _ => cvj.levelParams.map fun p =>
                      Level.subst cv.levelParams us (.param p)
                let cmpArgs : List EIdx ←
                  match rl.fire with
                  | .nested _ pins => pins.mapM fun p => do
                      let pi ← internExprM
                        (p.instantiateLevelParams cv.levelParams us)
                      instSpineM (args.take mI) (mI - 1) pi
                  | _ => pure (args.take rl.ctorParams)
                if ← liftFueled "level comparison"
                    (Level.isEquivList usj cmpLvls) then do
                 if ← defEqListI r fe depth (margs.take rl.ctorParams)
                    cmpArgs then do
                  let tyRec ← constTyAtM fe c us
                  if ← iotaCertsI r fe depth tyRec
                     (args.take mI ++ [major]) then do
                   let tyCtor ← constTyAtM fe cj usj
                   if ← iotaCertsI r fe depth tyCtor margs then do
                    match ← withStore (fun st =>
                          st.stripPisBodyI (rl.ctorParams + rl.nfields)
                            tyCtor),
                        ← piResidualM tyCtor margs with
                    | some cbody, some residual =>
                      match ← withStore (fun st =>
                          st.nodes[st.getAppFnI cbody]?) with
                      | some (.const _ _) => do
                        let resArgs ← withStore (·.getAppArgsI residual)
                        if ← defEqListI r fe depth
                            (resArgs.drop rl.ctorParams)
                            ((args.take mI).drop rP) then do
                          let rhs ← ruleRhsAtM fe c cj us
                          some <$> mkAppNM rhs
                            (args.take rP ++ margs.drop rl.ctorParams)
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
    (e₂ : EIdx) (i : Nat) (fieldLvl structLvl : Level) (nP : Nat) :
    CheckIM Bool := do
  let bvar0 ← internI (.bvar 0)
  let args ← withStore (·.getAppArgsI e₂)
  let arg := args.getD (nP + i) bvar0
  let ta ← r.infer depth arg
  let tta ← r.infer depth ta
  let wtta ← r.whnf depth tta
  match ← viewI wtta with
  | some (.sort uT) => do
    let okT ← liftFueled "level comparison" (Level.isEquiv uT fieldLvl)
    let te ← r.infer depth e₂
    let tte ← r.infer depth te
    let wtte ← r.whnf depth tte
    match ← viewI wtte with
    | some (.sort wT) => do
      let okW ← liftFueled "level comparison"
        (Level.isEquiv wT structLvl)
      pure (okT && okW)
    | _ => pure false
  | _ => pure false

/-- Twin of `whnfCoreBody`. -/
def whnfCoreBodyI (r : CoreFnsI) (fe : FEnv) : Nat → EIdx → CheckIM EIdx :=
  fun depth e => do
    match ← viewI e with
    | some (.sort _) | some (.fvar ..) | some (.forallE ..)
    | some (.lam ..) | some (.const ..) | some (.lit _) => pure e
    | some (.app f a) => do
      let f' ← r.whnfCore depth f
      match ← viewI f' with
      | some (.lam _ ty body mb) =>
        match mb.cod with
        | some v =>
          if v.isNonZero then do
            let e' ← inst1M body a
            r.whnfCore depth e'
          else do
            let ta ← r.infer depth a
            if ← r.defeq depth ta ty then do
              let e' ← inst1M body a
              r.whnfCore depth e'
            else internI (.app f' a)
        | none => internI (.app f' a)
      | _ => do
        let fa ← internI (.app f' a)
        match ← iotaRecI r fe depth fa with
        | some e'' => r.whnfCore depth e''
        | none => pure fa
    | some (.proj sn i pe) => do
      let e' ← r.whnf depth pe
      match fe.findProj? sn i with
      | some entry =>
        match ← withStore (fun st => st.nodes[st.getAppFnI e']?) with
        | some (.const c us) => do
          let args ← withStore (·.getAppArgsI e')
          if entry.native ∧ c = entry.ctor ∧ i < entry.numFields ∧
              args.length = entry.numParams + entry.numFields ∧
              us.length = entry.levelParams.length then do
            let mx : Level := Level.subst entry.levelParams us
              entry.structSort
            let bvar0 ← internI (.bvar 0)
            let arg := args.getD (entry.numParams + i) bvar0
            if mx.isNonZero then r.whnfCore depth arg
            else do
              if ← projCertI r fe depth e' i
                  (Level.subst entry.levelParams us entry.fieldSort)
                  mx entry.numParams then
                r.whnfCore depth arg
              else internI (.proj sn i e')
          else internI (.proj sn i e')
        | _ => internI (.proj sn i e')
      | none => internI (.proj sn i e')
    | some (.bvar _) | some (.letE ..) =>
      throw (.notImplemented "whnf beyond the supported fragment")
    | none => throw (.internal "interned node missing")

/-- Twin of `whnfBody`. -/
def whnfBodyI (r : CoreFnsI) (fe : FEnv) : Nat → EIdx → CheckIM EIdx :=
  fun depth e => do
    let e₁ ← r.whnfCore depth e
    match ← reduceNatI r fe depth e₁ with
    | some e₂ => r.whnf depth e₂
    | none =>
      match ← unfoldDefinitionI fe e₁ with
      | some e₂ => r.whnf depth e₂
      | none => pure e₁

/-- Twin of `ensureSort` (returns the level; no readback needed). -/
def ensureSortI (r : CoreFnsI) (depth : Nat) (e : EIdx) : CheckIM Level := do
  let w ← r.whnf depth e
  match ← viewI w with
  | some (.sort u) => pure u
  | _ => throw (.invalid "expected a sort")

/-- Twin of `inferBody`. -/
def inferBodyI (r : CoreFnsI) (fe : FEnv) : Nat → EIdx → CheckIM EIdx :=
  fun depth e => do
    match ← viewI e with
    | some (.sort u) => internI (.sort (.succ u))
    | some (.fvar idx _ ty) =>
      if idx < depth then pure ty
      else throw (.invalid "free variable out of scope")
    | some (.const n us) => do
      match fe.find? n with
      | none => throw (.invalid s!"unknown constant {n}")
      | some ci =>
        let cv := ci.toConstantVal
        unless us.length = cv.levelParams.length do
          throw (.invalid s!"incorrect number of universe levels for {n}")
        constTyAtM fe n us
    | some (.lit (.natVal _)) => do
      if natLitSupportedF fe then internI (.const natName [])
      else throw (.invalid "Nat literal without the Nat basis declarations")
    | some (.lit (.strVal _)) => do
      if strLitSupportedF fe then internI (.const stringName [])
      else throw (.notImplemented
        "string literals before the String support declarations")
    | some (.forallE _ ty _ mb) => do
      match mb.cod with
      | some v => do
        let tty ← r.infer depth ty
        let wtty ← r.whnf depth tty
        match ← viewI wtty with
        | some (.sort u) => internI (.sort (.imax u v))
        | _ => throw (.invalid "expected a sort")
      | none => throw (.internal "unannotated ∀-binder reached inferType")
    | some (.lam n ty body mb) => do
      match mb.cod with
      | some v => do
        let tty ← r.infer depth ty
        let wtty ← r.whnf depth tty
        match ← viewI wtty with
        | some (.sort _) => do
          let fv ← internI (.fvar depth n ty)
          let ob ← inst1M body fv
          let bt ← r.infer (depth + 1) ob
          let tbt ← r.infer (depth + 1) bt
          let wtbt ← r.whnf (depth + 1) tbt
          match ← viewI wtbt with
          | some (.sort v') => do
            unless ← liftFueled "level comparison" (Level.isEquiv v v') do
              throw (.invalid "λ-annotation does not match the body's sort")
            let btAbs ← abstract1M bt depth
            internI (.forallE n ty btAbs mb)
          | _ => throw (.invalid "expected a sort")
        | _ => throw (.invalid "expected a sort")
      | none => throw (.internal "unannotated λ-binder reached inferType")
    | some (.app f a) => do
      let tf ← r.infer depth f
      let wtf ← r.whnf depth tf
      match ← viewI wtf with
      | some (.forallE _ ty body _) => do
        let ta ← r.infer depth a
        unless ← r.defeq depth ta ty do
          throw (.invalid "application type mismatch")
        inst1M body a
      | _ => throw (.invalid "function expected")
    | some (.proj _sn i pe) => do
      let tpe ← r.infer depth pe
      let te ← r.whnf depth tpe
      match ← withStore (fun st => st.nodes[st.getAppFnI te]?) with
      | some (.const T us) =>
        match fe.findProj? T i with
        | some entry => do
          let targs ← withStore (·.getAppArgsI te)
          if entry.native ∧ targs.length = entry.numParams ∧
              us.length = entry.levelParams.length then do
            let pty ← constTyAtM fe (projFnName T i) us
            match ← piResidualM pty (targs ++ [pe]) with
            | some resTy => pure resTy
            | none => throw (.internal "malformed projection entry")
          else throw (.notImplemented "projection without a native entry")
        | none => throw (.notImplemented "projection without a native entry")
      | _ => throw (.notImplemented "projection without a native entry")
    | some (.bvar _) | some (.letE ..) =>
      throw (.notImplemented "inferType beyond the supported fragment")
    | none => throw (.internal "interned node missing")

/-- Twin of `defeqBody`. -/
def defeqBodyI (r : CoreFnsI) (fe : FEnv) : Nat → EIdx → EIdx → CheckIM Bool :=
  fun depth a b => do
    if a == b then pure true else
    let a' ← r.whnfCore depth a
    let b' ← r.whnfCore depth b
    if a' == b' then pure true else
    match ← reduceNatI r fe depth a' with
    | some a₂ => r.defeq depth a₂ b'
    | none =>
    match ← reduceNatI r fe depth b' with
    | some b₂ => r.defeq depth a' b₂
    | none =>
    match ← unfoldDefinitionI fe a', ← unfoldDefinitionI fe b' with
    | some a₂, none => r.defeq depth a₂ b'
    | none, some b₂ => r.defeq depth a' b₂
    | some a₂, some b₂ => do
      let ha ← withStore (fun st => headHintI fe st a')
      let hb ← withStore (fun st => headHintI fe st b')
      if ReducibilityHint.lt hb ha then r.defeq depth a₂ b'
      else if ReducibilityHint.lt ha hb then r.defeq depth a' b₂
      else if ReducibilityHint.sameRegular ha hb &&
          (← withStore (sameConstHeadsI · a' b')) then do
        if ← defeqSpineI r fe depth a' b' then pure true
        else r.defeq depth a₂ b₂
      else r.defeq depth a₂ b₂
    | none, none =>
    match ← viewI a', ← viewI b' with
    | some (.sort u), some (.sort v) =>
      liftFueled "level comparison" (Level.isEquiv u v)
    | some (.lit l₁), some (.lit l₂) => pure (l₁ == l₂)
    | some (.lit (.natVal n)), some (.const c us) =>
      if c = natZeroName ∧ us = [] then pure (n == 0)
      else stuckIrrelI r fe depth a' b'
    | some (.const c us), some (.lit (.natVal n)) =>
      if c = natZeroName ∧ us = [] then pure (n == 0)
      else stuckIrrelI r fe depth a' b'
    | some (.lit (.natVal nn)), some (.app f x) => do
      match nn, ← viewI f with
      | k + 1, some (.const c []) =>
        if c = natSuccName then do
          let kl ← internI (.lit (.natVal k))
          r.defeq depth kl x
        else stuckIrrelI r fe depth a' b'
      | _, _ => stuckIrrelI r fe depth a' b'
    | some (.app f x), some (.lit (.natVal nn)) => do
      match nn, ← viewI f with
      | k + 1, some (.const c []) =>
        if c = natSuccName then do
          let kl ← internI (.lit (.natVal k))
          r.defeq depth x kl
        else stuckIrrelI r fe depth a' b'
      | _, _ => stuckIrrelI r fe depth a' b'
    | some (.lit (.strVal s)), some (.app fO _x) => do
      match ← viewI fO with
      | some (.const cO usO) =>
        if cO = stringOfListName ∧ usO = [] ∧ strLitSupportedF fe then do
          let sc ← internExprM (strLitToConstructor s)
          r.defeq depth sc b'
        else stuckIrrelI r fe depth a' b'
      | _ => stuckIrrelI r fe depth a' b'
    | some (.app fO _x), some (.lit (.strVal s)) => do
      match ← viewI fO with
      | some (.const cO usO) =>
        if cO = stringOfListName ∧ usO = [] ∧ strLitSupportedF fe then do
          let sc ← internExprM (strLitToConstructor s)
          r.defeq depth a' sc
        else stuckIrrelI r fe depth a' b'
      | _ => stuckIrrelI r fe depth a' b'
    | some (.fvar i _ _), some (.fvar j _ _) =>
      if i == j then pure true
      else stuckIrrelI r fe depth a' b'
    | some (.const n us), some (.const n' us') =>
      if n = n' then do
        if ← liftFueled "level comparison" (Level.isEquivList us us') then
          pure true
        else stuckIrrelI r fe depth a' b'
      else stuckIrrelI r fe depth a' b'
    | some (.forallE n₁ ty₁ body₁ m₁), some (.forallE n₂ ty₂ body₂ m₂) => do
      unless ← r.defeq depth ty₁ ty₂ do return false
      let fv₁ ← internI (.fvar depth n₁ ty₁)
      let b₁ ← inst1M body₁ fv₁
      let fv₂ ← internI (.fvar depth n₂ ty₂)
      let b₂ ← inst1M body₂ fv₂
      unless ← r.defeq (depth + 1) b₁ b₂ do return false
      match m₁.cod, m₂.cod with
      | some v₁, some v₂ =>
        liftFueled "level comparison" (Level.isEquiv v₁ v₂)
      | _, _ => throw (.internal "unannotated ∀-binder reached isDefEq")
    | some (.lam n₁ ty₁ body₁ m₁), some (.lam n₂ ty₂ body₂ m₂) => do
      unless ← r.defeq depth ty₁ ty₂ do return false
      let fv₁ ← internI (.fvar depth n₁ ty₁)
      let b₁ ← inst1M body₁ fv₁
      let fv₂ ← internI (.fvar depth n₂ ty₂)
      let b₂ ← inst1M body₂ fv₂
      unless ← r.defeq (depth + 1) b₁ b₂ do return false
      match m₁.cod, m₂.cod with
      | some v₁, some v₂ =>
        liftFueled "level comparison" (Level.isEquiv v₁ v₂)
      | _, _ => throw (.internal "unannotated λ-binder reached isDefEq")
    | some (.app f₁ a₁), some (.app f₂ a₂) => do
      if ← r.defeq depth f₁ f₂ then do
        if ← r.defeq depth a₁ a₂ then
          pure true
        else stuckIrrelI r fe depth a' b'
      else stuckIrrelI r fe depth a' b'
    | some (.proj _s₁ i₁ e₁), some (.proj _s₂ i₂ e₂) => do
      if i₁ == i₂ then do
        if ← r.defeq depth e₁ e₂ then pure true
        else stuckIrrelI r fe depth a' b'
      else stuckIrrelI r fe depth a' b'
    | some (.lam n₁ ty₁ body₁ m₁), _ => do
      if ← etaCertI r fe depth n₁ ty₁ body₁ m₁ b' then pure true
      else stuckIrrelI r fe depth a' b'
    | _, some (.lam n₂ ty₂ body₂ m₂) => do
      if ← etaCertI r fe depth n₂ ty₂ body₂ m₂ a' then pure true
      else stuckIrrelI r fe depth a' b'
    | some _, some _ => stuckIrrelI r fe depth a' b'
    | _, _ => throw (.internal "interned node missing")

/-- Twin of `isPropType`. -/
def isPropTypeI (r : CoreFnsI) (_fe : FEnv) (depth : Nat) (ty : EIdx) :
    CheckIM Bool := do
  let ty' ← r.annotate depth ty
  let tty ← r.infer depth ty'
  let s ← ensureSortI r depth tty
  liftFueled "level comparison" (Level.isEquiv s Level.zero)

/-- Twin of `projFieldDom`. -/
def projFieldDomI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (structProp : Bool) (sn : Name) (e' : EIdx) :
    Nat → Nat → EIdx → CheckIM EIdx
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
    (entry : ProjEntry) (i : Nat) (te e' : EIdx) (us : List Level) :
    CheckIM EIdx := do
  match fe.find? entry.ctor with
  | some (.ctorInfo _cvC _ cnF) => do
    let params ← withStore (·.getAppArgsI te)
    if params.length = entry.numParams then do
      let ctorTy ← constTyAtM fe entry.ctor us
      match ← piResidualM ctorTy params with
      | some tel => do
        let structProp ← isPropTypeI r fe depth te
        let fi ← projFieldDomI r fe depth structProp entry.structName e'
          0 i tel
        let fieldBvar ← internI (.bvar (cnF - 1 - i))
        match ← pisToLamsM cnF tel fieldBvar with
        | some minor => do
          let fi' ← r.annotate depth fi
          let tfi ← r.infer depth fi'
          let sfi ← ensureSortI r depth tfi
          if structProp then do
            unless ← liftFueled "level comparison"
                (Level.isEquiv sfi Level.zero) do
              throw (.invalid "non-Prop projection from a Prop structure")
          let uf := if entry.recExtraLevel then [sfi] else []
          let recC ← internI
            (.const (entry.structName.str "rec") (uf ++ us))
          let motive ← internI
            (.lam (.str .anonymous "t") te fi ⟨.default, none⟩)
          let raw ← mkAppNM recC (params ++ [motive, minor, e'])
          if ← withStore (fun st => st.wscopedBI depth raw &&
              st.looseBVarsBoundedI 0 raw &&
              (st.fvarLeavesI raw).all
                (fun l => (st.fvarLeavesI e').contains l)) then
            r.annotate depth raw
          else throw (.notImplemented "projection elimination scoping")
        | none => throw (.invalid "projection index out of range")
      | none => throw (.invalid "projection index out of range")
    else throw (.notImplemented "projection parameter mismatch")
  | _ => throw (.notImplemented
      "projection constructor not stored")

/-- Twin of `annotateProjElim`. -/
def annotateProjElimI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (sn : Name)
    (i : Nat) (te e' : EIdx) : CheckIM EIdx := do
  match ← withStore (fun st => st.nodes[st.getAppFnI te]?) with
  | some (.const T us) =>
    if T = sn then
      match fe.find? (projFnName T i) with
      | some (.recInfo _ _ rP _) => do
        let targs ← withStore (·.getAppArgsI te)
        if targs.length = rP then do
          let h ← internI (.const (projFnName T i) us)
          let raw ← mkAppNM h (targs ++ [e'])
          if ← withStore (fun st => st.wscopedBI depth raw &&
              st.looseBVarsBoundedI 0 raw &&
              (st.fvarLeavesI raw).all
                (fun l => (st.fvarLeavesI e').contains l)) then
            r.annotate depth raw
          else throw (.notImplemented "projection elimination scoping")
        else throw (.notImplemented "projection parameter mismatch")
      | some (.projInfo entry) =>
        if entry.native then
          throw (.internal "native projection entry reached the fallback")
        else annotateProjRecI r fe depth entry i te e' us
      | _ =>
        throw (if (fe.find? (projFnName T 0)).isSome then
            CheckError.invalid "projection index out of range"
          else .notImplemented "projection on a non-structure-like type")
    else throw (.invalid "projection structure mismatch")
  | _ => throw (.notImplemented "projection on a non-structure type")

/-- Twin of `annotateBody`. -/
def annotateBodyI (r : CoreFnsI) (fe : FEnv) : Nat → EIdx → CheckIM EIdx :=
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
      let f' ← r.annotate depth f
      let a' ← r.annotate depth a
      let tf ← r.infer depth f'
      let wtf ← r.whnf depth tf
      match ← viewI wtf with
      | some (.forallE _ ty _ _) => do
        let ta ← r.infer depth a'
        unless ← r.defeq depth ta ty do
          throw (.invalid "application argument type mismatch")
        internI (.app f' a')
      | _ => throw (.invalid "function expected")
    | some (.forallE n ty body mb) => do
      let ty' ← r.annotate depth ty
      let fv ← internI (.fvar depth n ty')
      let ob ← inst1M body fv
      let body' ← r.annotate (depth + 1) ob
      let tb ← r.infer (depth + 1) body'
      let v ← ensureSortI r (depth + 1) tb
      let bAbs ← abstract1M body' depth
      internI (.forallE n ty' bAbs ⟨mb.bi, some v⟩)
    | some (.lam n ty body mb) => do
      let ty' ← r.annotate depth ty
      let fv ← internI (.fvar depth n ty')
      let ob ← inst1M body fv
      let body' ← r.annotate (depth + 1) ob
      let bt ← r.infer (depth + 1) body'
      let tbt ← r.infer (depth + 1) bt
      let v ← ensureSortI r (depth + 1) tbt
      let bAbs ← abstract1M body' depth
      internI (.lam n ty' bAbs ⟨mb.bi, some v⟩)
    | some (.letE ..) => throw (.notImplemented "annotate: let-expressions")
    | some (.proj sn i pe) => do
      let e' ← r.annotate depth pe
      let tpe ← r.infer depth e'
      let te ← r.whnf depth tpe
      match ← withStore (fun st => st.nodes[st.getAppFnI te]?) with
      | some (.const T _) =>
        match fe.findProj? T i with
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
def memoEI (get' : IState → Std.HashMap EIdx EIdx)
    (set' : IState → Std.HashMap EIdx EIdx → IState)
    (f : Nat → EIdx → CheckIM EIdx) : Nat → EIdx → CheckIM EIdx :=
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
def memoBI (f : Nat → EIdx → EIdx → CheckIM Bool) :
    Nat → EIdx → EIdx → CheckIM Bool :=
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
      annotate := fun _ _ => throw (.internal "fuel exhausted: annotate") }
  | fuel + 1 =>
    { whnfCore := memoEI (·.whnfCoreC)
        (fun st mp => { st with whnfCoreC := mp })
        (fun d e => whnfCoreBodyI (coreKnotI fe fuel) fe d e)
      whnf := memoEI (·.whnfC) (fun st mp => { st with whnfC := mp })
        (fun d e => whnfBodyI (coreKnotI fe fuel) fe d e)
      infer := memoEI (·.inferC) (fun st mp => { st with inferC := mp })
        (fun d e => inferBodyI (coreKnotI fe fuel) fe d e)
      defeq := memoBI
        (fun d a b => defeqBodyI (coreKnotI fe fuel) fe d a b)
      annotate := memoEI (·.annotC) (fun st mp => { st with annotC := mp })
        (fun d e => annotateBodyI (coreKnotI fe fuel) fe d e) }

/-! ## Entry runners

Each entry interns its argument into a fresh arena, runs the interned
knot, and reads the result back (`readbackI`, memoized so the rebuilt
tree shares subterms in memory).  State lifetime = one entry call,
exactly like the Expr-level `KCache`.  The `CheckerOps` record over
these lives in `Setlec/Kernel/Checker.lean`. -/

/-- Run a unary interned entry point on an `Expr`. -/
def runEntryE (env : Env)
    (pick : CoreFnsI → Nat → EIdx → CheckIM EIdx)
    (d : Nat) (e : Expr) : CheckM Expr := do
  let fe := mkFEnv env
  let (i, store) := EStore.empty.internExpr e
  let (j, s) ← (pick (coreKnotI fe checkFuel) d i).run { store := store }
  match s.store.readbackI j with
  | some v => pure v
  | none => throw (.internal "interned readback failed")

/-- Run the interned definitional-equality entry on two `Expr`s. -/
def runEntryB (env : Env) (d : Nat) (a b : Expr) : CheckM Bool := do
  let fe := mkFEnv env
  let (i, store) := EStore.empty.internExpr a
  let (j, store) := store.internExpr b
  ((coreKnotI fe checkFuel).defeq d i j).run' { store := store }

/-- Run the interned sort-ensuring entry on an `Expr`. -/
def runEntryS (env : Env) (d : Nat) (e : Expr) : CheckM Level := do
  let fe := mkFEnv env
  let (i, store) := EStore.empty.internExpr e
  (ensureSortI (coreKnotI fe checkFuel) d i).run' { store := store }

end Setlec

module

public import ConLeche.Kernel.Checker
public import ConLeche.Kernel.FEnv

@[expose] public section

/-!
# The declaration checker through the environment index (task #63)

The `FEnv`-indexed guard twins and the `F`-mirrors of every
`ConLeche/Kernel/Checker.lean` declaration-level function.  Each mirror
is its generic counterpart with every environment lookup
(`Env.find?`, `Env.findCV?`, `Expr.constsResolve` and the compound
guards built from them) routed through the index; under `mkFEnv` the
two are equal (`ConLeche/Verify/CheckerF.lean`), and environment-
extending mirrors return the pushed index (`FEnv.push`, definitionally
`mkFEnv` of the cons-extended environment).

**Representation-free.**  Everything here is `Expr`-typed and
monad-polymorphic over `CheckerOps m`: no core, no state, no
expression representation.  Both executable drivers instantiate these
same functions.

It lived in `ConLeche/Kernel/CheckerS.lean` until task #172's interned
removal took that file's shared-state drivers with the arena.
-/

namespace ConLeche

variable (mode : CheckMode)

/-- Indexed `Env.findCV?`. -/
def FEnv.findCV? (fe : FEnv) (n : Name) : Option ConstantVal :=
  (fe.find? n).map (·.toConstantVal)

/-- Indexed `Expr.constsResolve` (same clauses, lookups through the
index). -/
def Expr.constsResolveF (fe : FEnv) : Expr → Bool
  | .bvar _ | .sort _ => true
  | .lit (.natVal _) =>
    (fe.find? natName).isSome && (fe.find? natZeroName).isSome &&
      (fe.find? natSuccName).isSome
  | .lit (.strVal _) =>
    (fe.find? natName).isSome && (fe.find? natZeroName).isSome &&
      (fe.find? natSuccName).isSome && (fe.find? stringName).isSome &&
      (fe.find? stringOfListName).isSome && (fe.find? listName).isSome &&
      (fe.find? listNilName).isSome && (fe.find? listConsName).isSome &&
      (fe.find? charName).isSome && (fe.find? charOfNatName).isSome
  | .const n _ => (fe.find? n).isSome
  | .fvar _ ty => ty.constsResolveF fe
  | .app f a => f.constsResolveF fe && a.constsResolveF fe
  | .lam ty body _ | .forallE ty body _ =>
    ty.constsResolveF fe && body.constsResolveF fe
  | .letE ty val body =>
    ty.constsResolveF fe && val.constsResolveF fe &&
      body.constsResolveF fe
  | .proj s _ e => (fe.find? s).isSome && e.constsResolveF fe

/-! ### `constsResolveF`, memoized (task #210 Part B)

Every direct-install stage asks it of the block's types; a tree walk
does not finish on a DAG-shared field type (task #215's
`tower_struct`).  Swapped in by `@[csimp]` (the arrangement of
`ConLeche/Kernel/ExprOps.lean`): kernel-checked, no trust point, the
pure walk stays the spec.  Keyed by the node, dropped after each call
(the answer depends on `fe`); the cached checker's `constsResolveFC`
keeps its cross-call memo on top. -/

/-- The memo's invariant: every recorded answer is the real one. -/
def CRFMemoInv (fe : FEnv) (memo : Std.HashMap Expr Bool) : Prop :=
  ∀ (k : Expr) (r : Bool), memo[k]? = some r → r = k.constsResolveF fe

theorem CRFMemoInv.empty {fe : FEnv} : CRFMemoInv fe {} := by
  intro k r h; simp at h

theorem CRFMemoInv.insert {fe : FEnv} {memo : Std.HashMap Expr Bool}
    (hm : CRFMemoInv fe memo) {e : Expr} {r : Bool} (heq : r = e.constsResolveF fe) :
    CRFMemoInv fe (memo.insert e r) := by
  intro k r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact heq
  · exact hm k r' hk

/-- Memoized `constsResolveF`. -/
def Expr.constsResolveFGo (fe : FEnv) (memo : Std.HashMap Expr Bool) :
    Expr → Bool × Std.HashMap Expr Bool
  | .bvar i => ((Expr.bvar i).constsResolveF fe, memo)
  | .sort u => ((Expr.sort u).constsResolveF fe, memo)
  | .lit l => ((Expr.lit l).constsResolveF fe, memo)
  | .const n us => ((Expr.const n us).constsResolveF fe, memo)
  | e =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Bool × Std.HashMap Expr Bool :=
        match e with
        | .fvar _ ty => constsResolveFGo fe memo ty
        | .app f a =>
          let (b₁, memo) := constsResolveFGo fe memo f
          let (b₂, memo) := constsResolveFGo fe memo a
          (b₁ && b₂, memo)
        | .lam ty body _ =>
          let (b₁, memo) := constsResolveFGo fe memo ty
          let (b₂, memo) := constsResolveFGo fe memo body
          (b₁ && b₂, memo)
        | .forallE ty body _ =>
          let (b₁, memo) := constsResolveFGo fe memo ty
          let (b₂, memo) := constsResolveFGo fe memo body
          (b₁ && b₂, memo)
        | .letE ty val body =>
          let (b₁, memo) := constsResolveFGo fe memo ty
          let (b₂, memo) := constsResolveFGo fe memo val
          let (b₃, memo) := constsResolveFGo fe memo body
          (b₁ && b₂ && b₃, memo)
        | .proj s _ sub =>
          let (b, memo) := constsResolveFGo fe memo sub
          ((fe.find? s).isSome && b, memo)
        | e => (e.constsResolveF fe, memo)
      (r, memo.insert e r)

/-- **The memoized walk is `constsResolveF`.** -/
theorem Expr.constsResolveFGo_spec {fe : FEnv} :
    ∀ (e : Expr) (memo : Std.HashMap Expr Bool), CRFMemoInv fe memo →
      (constsResolveFGo fe memo e).1 = e.constsResolveF fe ∧
        CRFMemoInv fe (constsResolveFGo fe memo e).2 := by
  intro e
  induction e with
  | bvar i => intro memo hm; exact ⟨rfl, hm⟩
  | sort u => intro memo hm; exact ⟨rfl, hm⟩
  | const n us => intro memo hm; exact ⟨rfl, hm⟩
  | lit l => intro memo hm; exact ⟨rfl, hm⟩
  | fvar i ty ih =>
    intro memo hm
    rw [constsResolveFGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := ih memo hm
      refine ⟨by simp [constsResolveF, h1], ?_⟩
      exact h2.insert (by simp [constsResolveF, h1])
  | app a b iha ihb =>
    intro memo hm
    rw [constsResolveFGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iha memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      refine ⟨by simp [constsResolveF, h1, h3], ?_⟩
      exact h4.insert (by simp [constsResolveF, h1, h3])
  | lam ty body bi iht ihb =>
    intro memo hm
    rw [constsResolveFGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      refine ⟨by simp [constsResolveF, h1, h3], ?_⟩
      exact h4.insert (by simp [constsResolveF, h1, h3])
  | forallE ty body bi iht ihb =>
    intro memo hm
    rw [constsResolveFGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      refine ⟨by simp [constsResolveF, h1, h3], ?_⟩
      exact h4.insert (by simp [constsResolveF, h1, h3])
  | letE ty val body iht ihv ihb =>
    intro memo hm
    rw [constsResolveFGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihv _ h2
      obtain ⟨h5, h6⟩ := ihb _ h4
      refine ⟨by simp [constsResolveF, h1, h3, h5], ?_⟩
      exact h6.insert (by simp [constsResolveF, h1, h3, h5])
  | proj s i sub ih =>
    intro memo hm
    rw [constsResolveFGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := ih memo hm
      refine ⟨by simp [constsResolveF, h1], ?_⟩
      exact h2.insert (by simp [constsResolveF, h1])

/-- The executed `constsResolveF` (one memoized DAG walk). -/
def Expr.constsResolveFFast (fe : FEnv) (e : Expr) : Bool :=
  (constsResolveFGo fe {} e).1

@[csimp] theorem Expr.constsResolveF_eq_constsResolveFFast :
    @Expr.constsResolveF = @Expr.constsResolveFFast := by
  funext fe e
  exact (constsResolveFGo_spec e {} CRFMemoInv.empty).1.symm

/-! ## Indexed guard twins (same result as the `Env` versions under
`mkFEnv`; agreement lemmas in `ConLeche/Verify/CheckerF.lean`) -/

/-- `natOpCod` through the index. -/
def natOpCodF (fe : FEnv) (c : Name) (e : Expr) : Bool :=
  if c = natBeqName || c = natBleName then
    e == .const boolName [] &&
    (match fe.find? boolName with
     | some ci => ci.toConstantVal.levelParams.isEmpty &&
         ci.toConstantVal.type == .sort (.succ .zero)
     | none => false)
  else e == .const natName []

/-- `natOpTyPinned` through the index. -/
def natOpTyPinnedF (fe : FEnv) (c : Name) (ty : Expr) : Bool :=
  if c = natPredName then
    match ty with
    | .forallE dom body _mb =>
      dom == .const natName [] && natOpCodF fe c body
    | _ => false
  else
    match ty with
    | .forallE dom (.forallE dom2 body _mb2) _mb =>
      dom == .const natName [] && dom2 == .const natName [] &&
      natOpCodF fe c body
    | _ => false

/-- `natOpStoredOk` through the index. -/
def natOpStoredOkF (fe : FEnv) (n : Name) : Bool :=
  match fe.find? n with
  | some (.defnInfo cv _ _) =>
    cv.levelParams.isEmpty && natOpTyPinnedF fe n cv.type
  | _ => false

/-- `stdAxiomOk` through the index. -/
def stdAxiomOkF (fe : FEnv) (cvA : ConstantVal) : Bool :=
  if cvA.name = propextName then
    decide (fe.find? eqName = some eqA) &&
    (match fe.find? iffName with
     | some (.indInfo cvI _) => ConstantVal.matchesPin cvI iffA.toConstantVal
     | _ => false) &&
    (match fe.find? iffIntroName with
     | some (.ctorInfo cvIi 2 2) =>
       ConstantVal.matchesPin cvIi iffIntroA.toConstantVal
     | _ => false) &&
    (match fe.find? iffRecName with
     | some (.recInfo cvIr 4 4 _) =>
       ConstantVal.matchesPin cvIr iffRecA.toConstantVal
     | _ => false) &&
    ConstantVal.matchesPin cvA propextA
  else if cvA.name = choiceName then
    (match fe.find? nonemptyName with
     | some (.indInfo cvN _) =>
       ConstantVal.matchesPin cvN nonemptyA.toConstantVal
     | _ => false) &&
    (match fe.find? nonemptyIntroName with
     | some (.ctorInfo cvNi 1 1) =>
       ConstantVal.matchesPin cvNi nonemptyIntroA.toConstantVal
     | _ => false) &&
    (match fe.find? nonemptyRecName with
     | some (.recInfo cvNr 3 3 _) =>
       ConstantVal.matchesPin cvNr nonemptyRecA.toConstantVal
     | _ => false) &&
    ConstantVal.matchesPin cvA choiceA
  else false

/-- `trustCompilerOk` through the index. -/
def trustCompilerOkF (fe : FEnv) (cvA : ConstantVal) : Bool :=
  (match fe.find? trueName with
   | some (.indInfo cvT _) => ConstantVal.matchesPin cvT trueCvA
   | _ => false) &&
  (match fe.find? trueIntroName with
   | some (.ctorInfo cvTi 0 0) => ConstantVal.matchesPin cvTi trueIntroCvA
   | _ => false) &&
  ConstantVal.matchesPin cvA trustCompilerA

/-- `reduceStoredOk` through the index. -/
def reduceStoredOkF (fe : FEnv) (c : Name) : Bool :=
  match fe.find? c with
  | some (.axiomInfo cvR) => ConstantVal.matchesPin cvR (reduceOpCvA c)
  | _ => false

/-- `reduceElemOk` through the index. -/
def reduceElemOkF (fe : FEnv) (c : Name) : Bool :=
  if c = reduceNatName then decide (fe.find? natName = some natA)
  else
    match fe.find? boolName with
    | some (.indInfo cvB _) => ConstantVal.matchesPin cvB boolCvA
    | _ => false

/-- `ofReduceAxOk` through the index. -/
def ofReduceAxOkF (fe : FEnv) (cvA : ConstantVal) : Bool :=
  let c := ofReduceOp cvA.name
  decide (fe.find? eqName = some eqA) &&
  reduceElemOkF fe c &&
  reduceStoredOkF fe c &&
  ConstantVal.matchesPin cvA (ofReducePinA cvA.name)

/-- `reducePinGuard` through the index. -/
def reducePinGuardF (fe : FEnv) (c : Name) : Bool :=
  (reduceDeclPin c).looseBVarsBounded 0 && !(reduceDeclPin c).hasFvar &&
  (reduceDeclPin c).allLevelParamsDefined [] &&
  (reduceDeclPin c).constsResolveF fe

/-- `divModEnvGuard` through the index. -/
def divModEnvGuardF (fe2 : FEnv) (c : Name) : Bool :=
  natOpGuardF fe2 c && (natOpDeps c).all (natOpStoredOkF fe2) &&
  fe2.find? eqName == some eqA &&
  (match fe2.find? boolTrueName with
    | some ci => ci.toConstantVal.type == .const boolName []
    | none => false) &&
  (match fe2.find? boolFalseName with
    | some ci => ci.toConstantVal.type == .const boolName []
    | none => false)

/-- `divModCertGuard` through the index. -/
def divModCertGuardF (fe : FEnv) (c : Name) (annVal : Expr)
    (hyps : List Expr) (eqE proof : Expr) : Bool :=
  (Expr.substConstAll c annVal proof).looseBVarsBounded 0 &&
  !(Expr.substConstAll c annVal proof).hasFvar &&
  (Expr.substConstAll c annVal proof).allLevelParamsDefined [] &&
  (Expr.substConstAll c annVal proof).constsResolveF fe &&
  (hyps.map (Expr.substConst0 c annVal)).all
    (fun h => h.constsResolveF fe) &&
  (Expr.substConst0 c annVal eqE).constsResolveF fe

/-- `divModPinGuard` through the index. -/
def divModPinGuardF (ps : NatOpPinSet) (fe : FEnv) (c : Name) : Bool :=
  (divModDeclPin ps c).looseBVarsBounded 0 && !(divModDeclPin ps c).hasFvar &&
  (divModDeclPin ps c).allLevelParamsDefined [] &&
  (divModDeclPin ps c).constsResolveF fe

/-- `divModCertsGuard` through the index. -/
def divModCertsGuardF (ps : NatOpPinSet) (fe : FEnv) (c : Name)
    (annVal : Expr) : Bool :=
  ((divModCertStmts c).zip (divModCertProofs ps c)).all
    (fun p => divModCertGuardF fe c annVal p.1.1 p.1.2 p.2)

/-! ## Indexed mirrors of the declaration-checker functions (task #63)

Each mirrors its `ConLeche/Kernel/Checker.lean` counterpart clause by
clause; the only difference is that every environment lookup
(`Env.find?`, `Env.findCV?`, `Expr.constsResolve` and the compound
guards built from them) goes through the `FEnv` index.  Under
`mkFEnv` each mirror *is* its generic counterpart
(`ConLeche/Verify/CheckerF.lean`); environment-extending mirrors return
the pushed index (`FEnv.push`, definitionally `mkFEnv` of the
cons-extended environment). -/

section Mirrors

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- `checkConstantVal` through the index. -/
def checkConstantValF (ops : CheckerOps m) (fe : FEnv)
    (cv : ConstantVal) : m ConstantVal := do
  if (fe.find? cv.name).isSome then
    throw (.invalid s!"duplicate declaration {cv.name}")
  if reservedBasisNames.contains cv.name then
    throw (.invalid s!"reserved basis name {cv.name}")
  if cv.name.isProjFnShape then
    throw (.invalid s!"reserved projection name {cv.name}")
  unless Name.nodup cv.levelParams do
    throw (.invalid s!"duplicate universe parameters in {cv.name}")
  unless cv.type.looseBVarsBounded 0 do
    throw (.invalid s!"loose bound variable in type of {cv.name}")
  if cv.type.hasFvar then
    throw (.invalid s!"unexpected free variable in type of {cv.name}")
  let type ← ops.annotate fe.env 0 cv.type
  unless type.allLevelParamsDefined cv.levelParams do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  unless type.constsResolveF fe do
    throw (unresolvedConstsError s!"type of {cv.name}" type)
  let stype ← ops.inferType fe.env 0 type
  let _u ← ops.ensureSort fe.env 0 stype
  pure { cv with type := type }

/-- `checkDefnVal` through the index, returning the pushed index. -/
def checkDefnValF (ops : CheckerOps m) (fe : FEnv) (cv : ConstantVal)
    (value : Expr) (hint : ReducibilityHint) : m FEnv := do
  unless value.looseBVarsBounded 0 do
    throw (.invalid s!"loose bound variable in value of {cv.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cv.name}")
  let value ← ops.annotate fe.env 0 value
  unless value.allLevelParamsDefined cv.levelParams do
    throw (.invalid s!"undeclared universe parameter in value of {cv.name}")
  unless value.constsResolveF fe do
    throw (unresolvedConstsError s!"value of {cv.name}" value)
  let vtype ← ops.inferType fe.env 0 value
  unless ← ops.isDefEq fe.env 0 vtype cv.type do
    throw (.invalid s!"type mismatch in definition {cv.name}")
  pure (fe.push (.defnInfo cv value hint))

/-- `installBasisDecl` through the index, returning the pushed index. -/
def installBasisDeclF (fe : FEnv) (ci : ConstantInfo) : m FEnv := do
  unless (fe.find? ci.name).isNone do
    throw (.invalid s!"duplicate declaration {ci.name}")
  pure (fe.push ci)

/-- `checkDivModCerts` through the index. -/
def checkDivModCertsF (ops : CheckerOps m) (fe : FEnv) (c : Name)
    (annVal : Expr) : List (List Expr × Expr) → List Expr → m Bool
  | [], [] => pure true
  | (hyps, eqE) :: srest, proof :: prest => do
    if divModCertGuardF fe c annVal hyps eqE proof then
      let appliedA ← ops.annotate fe.env 4
        (divModCertApplied (Expr.substConstAll c annVal proof)
          (hyps.map (Expr.substConst0 c annVal)))
      let tp ← ops.inferType fe.env 4 appliedA
      if ← ops.isDefEq fe.env 4 tp (Expr.substConst0 c annVal eqE) then
        checkDivModCertsF ops fe c annVal srest prest
      else pure false
    else pure false
  | _, _ => pure false

/-- `checkDivModPinAt` through the index. -/
def checkDivModPinAtF (ops : CheckerOps m) (fe : FEnv) (c : Name)
    (value' : Expr) (ps : NatOpPinSet) : m Bool := do
  let pinA ← ops.annotate fe.env 0 (divModDeclPin ps c)
  let okPin ← ops.isDefEq fe.env 0 value' pinA
  if okPin then
    checkDivModCertsF ops fe c value' (divModCertStmts c)
      (divModCertProofs ps c)
  else pure false

/-- `checkDivModPinLoop` through the index. -/
def checkDivModPinLoopF (ops : CheckerOps m) (fe : FEnv) (c : Name)
    (value' : Expr) : List NatOpPinSet → List String → m Unit
  | [], tried =>
    throw (.notImplemented s!"unsupported Nat.div/mod spelling ({c}: no \
      pin variant matched — {String.intercalate "; " tried})")
  | ps :: rest, tried =>
    if divModPinGuardF ps fe c && divModCertsGuardF ps fe c value' then
      ops.orElse (checkDivModPinAtF ops fe c value' ps) fun r =>
        checkDivModPinLoopF ops fe c value' rest
          (tried ++ [divModAttemptReason ps r])
    else
      checkDivModPinLoopF ops fe c value' rest
        (tried ++ [s!"{ps.toolchain}: pin or certificate ground constants \
          absent"])

/-- `checkDivModPin` through the index — the variant list is its
parameter too (task #304). -/
def checkDivModPinF (ops : CheckerOps m) (pins : List NatOpPinSet)
    (fe fe2 : FEnv) (c : Name) : m Unit := do
  if divModEnvGuardF fe2 c then
    match fe2.find? c with
    | some (.defnInfo _ value' _) =>
      checkDivModPinLoopF ops fe c value' pins []
    | _ => throw (.internal s!"Nat.div/mod operation not stored ({c})")
  else throw (.notImplemented
    s!"unsupported Nat.div/mod environment ({c})")

/-- `checkReducePin` through the index. -/
def checkReducePinF (ops : CheckerOps m) (fe fe2 : FEnv) (c : Name)
    (value : Expr) : m Unit := do
  if reduceStoredOkF fe2 c && reduceElemOkF fe c then
    if reducePinGuardF fe c then do
      let valA ← ops.annotate fe.env 0 value
      let pinA ← ops.annotate fe.env 0 (reduceDeclPin c)
      let okPin ← ops.isDefEq fe.env 0 valA pinA
      if okPin then do
        let x := reduceCertVar c
        let ok ← ops.isDefEq fe.env 1 (.app valA x) x
        if ok then pure ()
        else throw (.internal
          s!"pinned compiler-trust opaque is not the identity ({c})")
      else throw (.notImplemented
        s!"unsupported compiler-trust opaque spelling ({c})")
    else throw (.notImplemented
      s!"unsupported compiler-trust opaque spelling ({c}: pin ground constants absent)")
  else throw (.notImplemented
    s!"unsupported compiler-trust opaque declaration ({c})")

end Mirrors

end ConLeche

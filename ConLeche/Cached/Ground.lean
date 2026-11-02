module

public import ConLeche.Cached.StateC

@[expose] public section

/-!
# The ground engine (task #423, spike)

A call-by-need abstract machine for closed terms: environments of heap
addresses instead of substitution, a heap of thunks updated in place
(`Array`, threaded linearly through `EStateM`), constructors and
literals as values, weak head evaluation only.  It is run where the
checker would otherwise head-normalise a closed term completely (the
`Bool.true` comparison of a reflection certificate), and its answer is
a `Bool.true` or `Bool.false` constructor or an abort.

**Every step is a step of `Red`** (`ConLeche/Rules/Rel.lean`) under
the *origin denotation* (task #307): a heap cell denotes the term it
was created for, `⟦thunk (ρ, e)⟧ = e[⟦ρ⟧]`; a forced cell keeps that
denotation and its value is a `Red` reduct of it.  Forcing happens
only where `Red` has a premise that reduces a subterm: the head of an
application (`appFn`, β), a recursor's major (`iota`), a projection's
scrutinee (`projArg`), the arguments of literal acceleration
(`natSucc`, `natOp`).  No argument is ever reduced in place, so no
congruence beyond the existing rules is needed (`Red.appArg` is not
used).

Not handled (an abort, `GErr`): a K rule or a structure-η rule whose
major does not evaluate to a constructor (the rescues need
inference), case 3 of the ι split (its certificates need inference and
definitional equality), anything with a free variable in a scrutinised
position.

The fuel is a recursion budget for the termination proof only
(effectively unbounded, as `checkFuel`).
-/

namespace ConLeche.Cached

open ConLeche

/-- **The spike's switch** (task #423): `0` the incumbent path only,
`1` the ground engine at the `Bool.true` comparison (both
orientations), `2` as 1 with a per-call trace on stderr (`dbgTrace`,
probe builds only), `3` the incumbent path with the eligible
comparisons wrapped in a `noinline` marker (the opportunity probe). -/
@[noinline] def groundMode : Nat := 0

/-- Why a ground evaluation stopped without a constructor value. -/
inductive GErr where
  | abort (why : String)
  deriving Inhabited

/-- A weak head value of the ground machine. -/
inductive GVal where
  /-- a λ-closure: the λ's domain and body, under an environment -/
  | lam (env : List Nat) (ty body : Expr)
  /-- a constructor applied to (heap addresses of) its arguments,
  parameters included -/
  | ctor (c : Name) (us : List Level) (args : Array Nat)
  | lit (l : Literal)
  /-- a recursor short of its major: waits for more arguments -/
  | pap (c : Name) (us : List Level) (args : Array Nat)
  /-- an irreducible head (a type former, an axiom, a theorem, a sort,
  a Π-type), with or without arguments: never scrutinised -/
  | neutral
  deriving Inhabited

/-- A heap cell. -/
inductive GCell where
  | thunk (env : List Nat) (e : Expr)
  | busy
  | val (v : GVal)
  deriving Inhabited

structure GState where
  heap : Array GCell := #[]
  vals : Std.HashMap (Name × List Level) Expr := {}
  rhss : Std.HashMap (Name × Name × List Level) (Expr × Bool) := {}
  steps : Nat := 0

abbrev GM := EStateM GErr GState

@[inline] def gAbort (why : String) : GM α := throw (.abort why)

@[inline] def gRead (a : Nat) : GM GCell :=
  modifyGet fun s => (s.heap[a]!, s)

@[inline] def gWrite (a : Nat) (c : GCell) : GM Unit :=
  modify fun s =>
    let h := s.heap
    let s := { s with heap := #[] }
    { s with heap := h.set! a c }

@[inline] def gAlloc (c : GCell) : GM Nat :=
  modifyGet fun s =>
    let h := s.heap
    let n := h.size
    let s := { s with heap := #[] }
    (n, { s with heap := h.push c })

@[inline] def gTick : GM Unit :=
  modify fun s => { s with steps := s.steps + 1 }

/-- The level-instantiated value of a stored definition, memoised for
the evaluation. -/
def gVal (c : Name) (lps : List Name) (us : List Level) (v : Expr) : GM Expr := do
  let hit? ← modifyGet fun s => (s.vals[(c, us)]?, s)
  match hit? with
  | some e => pure e
  | none =>
    let e := v.instantiateLevelParams lps us
    modify fun s =>
      let mp := s.vals
      let s := { s with vals := ∅ }
      { s with vals := mp.insert (c, us) e }
    pure e

/-- The comparand levels of a firing rule (`recFireComparands`'s first
component, which needs no arguments). -/
def gCmpLevels (rl : RecRule) (lps : List Name) (us : List Level)
    (cvjLps : List Name) : List Level :=
  match rl.fire with
  | .nested lvls _ => lvls.map (Level.subst lps us)
  | .plain => cvjLps.map fun p => Level.subst lps us (.param p)

/-- An argument's heap address: an environment entry is shared, a
literal or a λ is a value, anything else a thunk. -/
@[inline] def gArg (env : List Nat) (a : Expr) : GM Nat :=
  match a with
  | .bvar i =>
    match env[i]? with
    | some x => pure x
    | none => gAbort "loose bvar"
  | .lit l => gAlloc (.val (.lit l))
  | .lam ty b => gAlloc (.val (.lam env ty b))
  | .const .. | .sort _ | .forallE .. => gAlloc (.thunk [] a)
  | _ => gAlloc (.thunk env a)

def natBin14 (c : Name) : Bool :=
  c == natAddName || c == natSubName || c == natMulName ||
    c == natPowName || c == natBeqName || c == natBleName ||
    c == natDivName || c == natModName || c == natGcdName ||
    c == natLandName || c == natLorName || c == natXorName ||
    c == natShiftLeftName || c == natShiftRightName

section
variable (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)
  (natOk strOk : Bool)

/-- The level-instantiated rule rhs and the case-3 bit, memoised. -/
def gRhs (c : Name) (cv : ConstantVal) (cj : Name) (rl : RecRule)
    (us : List Level) : GM (Expr × Bool) := do
  let hit? ← modifyGet fun s => (s.rhss[(c, cj, us)]?, s)
  match hit? with
  | some r => pure r
  | none =>
    let case3 := match find? cj with
      | some (.ctorInfo cvj _ _) =>
        iotaCase3 find? rl cvj (gCmpLevels rl cv.levelParams us cvj.levelParams)
      | _ => true
    let r := (rl.rhs.instantiateLevelParams cv.levelParams us, case3)
    modify fun s =>
      let mp := s.rhss
      let s := { s with rhss := ∅ }
      { s with rhss := mp.insert (c, cj, us) r }
    pure r


mutual

/-- Evaluate `e` under `env` applied to the argument stack `stk`. -/
def gEval : Nat → List Nat → Expr → List Nat → GM GVal
  | 0, _, _, _ => gAbort "fuel"
  | n + 1, env, e, stk => do
    match e with
    | .bvar i =>
      match env[i]? with
      | some a => do
        let v ← gForce n a
        gApply n v stk
      | none => gAbort "loose bvar"
    | .app f a => do
      let x ← gArg env a
      gEval n env f (x :: stk)
    | .lam ty b =>
      match stk with
      | x :: rest => gEval n (x :: env) b rest
      | [] => pure (.lam env ty b)
    | .letE _ v b => do
      let x ← gArg env v
      gEval n (x :: env) b stk
    | .const c us => gConst n c us stk
    | .lit l =>
      match stk with
      | [] => pure (.lit l)
      | _ => gAbort "literal applied"
    | .proj sn i s => do
      let v ← gEval n env s []
      let v ← gStrCtor n v
      match v with
      | .ctor k us args =>
        match findProj? sn i with
        | some entry =>
          if k == entry.ctor && i < entry.numFields &&
              args.size == entry.numParams + entry.numFields &&
              us.length == entry.levelParams.length && entry.fireOk us then
            match find? k with
            | some (.ctorInfo cvC _ _) =>
              if (Expr.peelPis args.size cvC.type).isSome then do
                let a := args[entry.numParams + i]!
                let w ← gForce n a
                gApply n w stk
              else gAbort "proj cert"
            | _ => gAbort "proj ctor"
          else gAbort "proj shape"
        | none => gAbort "proj table"
      | _ => gAbort "proj of non-constructor"
    | .sort _ | .forallE .. =>
      match stk with
      | [] => pure .neutral
      | _ => gAbort "type applied"
    | .fvar .. => pure .neutral

/-- Force a heap cell (call-by-need: the value replaces the thunk). -/
def gForce : Nat → Nat → GM GVal
  | 0, _ => gAbort "fuel"
  | n + 1, a => do
    match ← gRead a with
    | .val v => pure v
    | .thunk env e => do
      gWrite a .busy
      let v ← gEval n env e []
      gWrite a (.val v)
      pure v
    | .busy => gAbort "black hole"

/-- Apply a value to an argument stack. -/
def gApply : Nat → GVal → List Nat → GM GVal
  | 0, _, _ => gAbort "fuel"
  | _, v, [] => pure v
  | n + 1, v, x :: rest =>
    match v with
    | .lam env _ b => gEval n (x :: env) b rest
    | .ctor c us args => pure (.ctor c us (args ++ (x :: rest).toArray))
    | .pap c us args => gConst n c us (args.toList ++ x :: rest)
    | .neutral => pure .neutral
    | .lit _ => gAbort "literal applied"

/-- A string literal in a scrutinised position becomes its constructor
form (`Red.strLit`). -/
def gStrCtor : Nat → GVal → GM GVal
  | 0, _ => gAbort "fuel"
  | n + 1, v =>
    match v with
    | .lit (.strVal s) =>
      if strOk then gEval n [] (strLitToConstructor s) [] else gAbort "string literal"
    | _ => pure v

/-- The literal reading of a value (`rawNatLit?` after head
normalisation, with the `Nat.succ` packing of `Red.natSucc`). -/
def gNatLit : Nat → GVal → GM (Option Nat)
  | 0, _ => gAbort "fuel"
  | n + 1, v =>
    match v with
    | .lit (.natVal k) => pure (some k)
    | .ctor c [] args =>
      if c == natZeroName && args.size == 0 then pure (some 0)
      else if c == natSuccName && args.size == 1 && natOk then do
        let w ← gForce n args[0]!
        match ← gNatLit n w with
        | some k => pure (some (k + 1))
        | none => pure none
      else pure none
    | _ => pure none

/-- A constant applied to an argument stack: literal acceleration,
δ, a constructor value, ι, or a neutral. -/
def gConst : Nat → Name → List Level → List Nat → GM GVal
  | 0, _, _, _ => gAbort "fuel"
  | n + 1, c, us, stk => do
    gTick
    match find? c with
    | some (.defnInfo cv v _) => do
      -- literal acceleration (`reduceNat`): the first argument, and the
      -- second only behind a literal
      let acc? : Option Expr ← match us, stk with
        | [], [a, b] =>
          if natBin14 c && natOk then do
            match ← gNatLit n (← gForce n a) with
            | some k₁ =>
              match ← gNatLit n (← gForce n b) with
              | some k₂ => pure (natOpResult c k₁ k₂)
              | none => pure none
            | none => pure none
          else if natOpWfNames.contains c then gAbort "wf nat op"
          else pure none
        | _, _ => pure none
      match acc? with
      | some r => gEval n [] r []
      | none =>
        if us.length == cv.levelParams.length then do
          let body ← gVal c cv.levelParams us v
          gEval n [] body stk
        else gAbort "level arity"
    | some (.ctorInfo ..) => pure (.ctor c us stk.toArray)
    | some (.recInfo cv mI rP rules) =>
      if stk.length < mI + 1 then pure (.pap c us stk.toArray) else
      if us.length != cv.levelParams.length then gAbort "rec level arity" else
      if !(Expr.peelPis (mI + 1) cv.type).isSome then gAbort "rec type" else do
      let args := stk.toArray
      let mv ← gForce n args[mI]!
      let mv ← gStrCtor n mv
      let mv ← match mv with
        | .lit (.natVal k) =>
          if natOk then
            match k with
            | 0 => pure (GVal.ctor natZeroName [] #[])
            | k + 1 => do
              let x ← gAlloc (.val (.lit (.natVal k)))
              pure (GVal.ctor natSuccName [] #[x])
          else gAbort "nat literal"
        | v => pure v
      match mv with
      | .ctor cj usj margs =>
        match rules.find? (fun r' => r'.ctor == cj) with
        | some rl =>
          if margs.size != rl.ctorParams + rl.nfields then gAbort "ctor arity" else do
          let (rhs, case3) ← gRhs find? c cv cj rl us
          if case3 then gAbort "case 3" else
          let _ := usj
          let stk' := (args.extract 0 rP).toList ++
            (margs.extract rl.ctorParams margs.size).toList ++
            (args.extract (mI + 1) args.size).toList
          gEval n [] rhs stk'
        | none => gAbort "no rule"
      | _ => if recRuleK rules then gAbort "K major" else gAbort "major not a constructor"
    | some _ => pure .neutral
    | none => gAbort "unknown constant"

end

end

/-- The effectively unbounded recursion budget of the ground machine
(a termination device, as `checkFuel`). -/
@[irreducible, noinline] def groundFuel : Nat := 4611686018427387904  -- 2^62

/-- The outcome of a ground evaluation at the `Bool.true` comparison:
`some true`/`some false` for a `Bool` constructor, `none` otherwise,
with the step count and the abort reason (for the probe trace). -/
def groundBool (fe : FEnv) (e : Expr) : Option Bool × Nat × String :=
  let natOk := natLitSupportedF fe
  let strOk := strLitSupportedF fe
  match (gEval fe.find? fe.findProj? natOk strOk groundFuel [] e []).run {} with
  | .ok v s =>
    match v with
    | .ctor c [] args =>
      if c == boolTrueName && args.size == 0 then (some true, s.steps, "")
      else if c == boolFalseName && args.size == 0 then (some false, s.steps, "")
      else (none, s.steps, "not a Bool")
    | _ => (none, s.steps, "not a constructor")
  | .error (.abort why) s => (none, s.steps, why)

end ConLeche.Cached

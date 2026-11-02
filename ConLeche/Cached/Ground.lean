module

public import ConLeche.Kernel.FEnv

@[expose] public section

/-!
# The ground engine (task #423, spike)

A call-by-need abstract machine for closed terms, in the style of
Sestoft's lazy machine: environments of heap addresses instead of
substitution, a heap of thunks updated in place (an `Array` threaded
through the loop), constructors and literals as values, an explicit
continuation stack (argument, update, ι, projection and literal
frames), weak head evaluation only.  The machine is ONE tail-recursive
function (`gRun`), so it runs in constant native stack and allocates
nothing per transition beyond the frames, environments and cells it
builds.  It is run where the checker would otherwise head-normalise a
closed term completely (the `Bool.true` comparison of a reflection
certificate); its answer is a value or an abort.

**Every transition is a step of `Red`** (`ConLeche/Rules/Rel.lean`)
under the *origin denotation* (task #307): a heap cell denotes the
term it was created for, `⟦thunk (ρ, e)⟧ = e[⟦ρ⟧]`; an updated cell
keeps that denotation and its value is a `Red` reduct of it.  A cell
is forced only where `Red` has a premise that reduces a subterm: the
head of an application (`appFn`, β), a recursor's major (`iota`), a
projection's scrutinee (`projArg`), the arguments of literal
acceleration (`natSucc`, `natOp`).  No argument is ever reduced in
place, so no congruence beyond the existing rules is needed.

Not handled (an abort): a K rule or a structure-η rule whose major does
not evaluate to a constructor (the rescues need inference), case 3 of
the ι split (its certificates need inference and definitional
equality), a free variable in a scrutinised position.

The fuel is a step budget for the termination proof only (effectively
unbounded, as `checkFuel`).
-/

namespace ConLeche.Cached

open ConLeche

/-- **The spike's switch** (task #423): `0` the incumbent path only,
`1` the round-1 machine (this file) at the `Bool.true` comparison (both
orientations), `2` as 1 with a per-call trace on stderr (`dbgTrace`,
probe builds only), `3` the round-2 flat machine (`Ground2.lean`), `4`
as 3 with the trace, `5`/`6` as 1/3 with the engine run twice (its own
cost is the difference), `7` the round-3 machine (`Ground3.lean`), `8`
as 7 with the trace, `9` as 7 run twice. -/
@[noinline] def groundMode : Nat := 0

/-- A weak head value of the ground machine. -/
inductive GVal where
  /-- a closure: a lambda's domain and body, under an environment -/
  | lam (env : List Nat) (ty body : Expr)
  /-- a constructor applied to (heap addresses of) its arguments,
  parameters included -/
  | ctor (c : Name) (us : List Level) (args : Array Nat)
  | lit (l : Literal)
  /-- a constant short of the arguments its reduction needs (a
  recursor short of its major, an accelerated `Nat` operation short of
  its two arguments): waits for more -/
  | pap (c : Name) (us : List Level) (args : Array Nat)
  /-- an irreducible head (a type former, an axiom, a theorem, a sort,
  a Π-type, a free variable), with or without arguments: never
  scrutinised -/
  | neutral
  deriving Inhabited

/-- A heap cell. -/
inductive GCell where
  | thunk (env : List Nat) (e : Expr)
  | busy
  | val (v : GVal)
  deriving Inhabited

/-- The continuation frames. -/
inductive GFrame where
  /-- a pending application argument -/
  | arg (a : Nat)
  /-- write the value into this cell -/
  | upd (a : Nat)
  /-- the major of a recursor application is being evaluated -/
  | iota (c : Name) (us : List Level) (lps : List Name) (mI rP : Nat)
      (rules : List RecRule) (args : Array Nat)
  /-- the scrutinee of a projection is being evaluated -/
  | proj (sn : Name) (i : Nat)
  /-- the first argument of an accelerated operation is being read -/
  | natA (c : Name) (a b : Nat)
  /-- the second argument, behind a first literal `n₁` -/
  | natB (c : Name) (n₁ : Nat) (a b : Nat)
  /-- add one to the literal reading returned (`Nat.succ` packing) -/
  | plus1
  deriving Inhabited

/-- What the machine does next. -/
inductive GCtrl where
  | eval (env : List Nat) (e : Expr)
  | ret (v : GVal)
  | enter (a : Nat)
  /-- a constant at the head, its arguments still on the stack -/
  | const (c : Name) (us : List Level)

/-- The effectively unbounded step budget of the ground machine (a
termination device, as `checkFuel`). -/
@[irreducible, noinline] def groundFuel : Nat := 4611686018427387904  -- 2^62

/-- The machine's final state (`steps`: constant dispatches; `left`:
the fuel left, so the transitions are `groundFuel - left`). -/
inductive GOut where
  | done (v : GVal) (heap : Array GCell) (steps left : Nat)
  | abort (why : String) (steps : Nat)

/-- The level-instantiation memos of a run: definition values, and
rule right-hand sides with their case-3 bit. -/
structure GCache where
  vals : Std.HashMap (Name × List Level) Expr := {}
  rhss : Std.HashMap (Name × Name × List Level) (Expr × Bool) := {}
  /-- the cell of each closed argument term (origin sharing: one closed
  term, one cell) -/
  closed : Std.HashMap Expr Nat := {}
  /-- the cell of each recursor or definition application, keyed by its
  head and its argument cells (origin sharing: equal cells, equal
  origins) -/
  apps : Std.HashMap (Name × List Level × Array Nat) Nat := {}

@[inline] def GCache.insVal (cc : GCache) (k : Name × List Level) (e : Expr) : GCache :=
  let m := cc.vals; let cc := { cc with vals := {} }; { cc with vals := m.insert k e }
@[inline] def GCache.insRhs (cc : GCache) (k : Name × Name × List Level) (e : Expr × Bool) :
    GCache :=
  let m := cc.rhss; let cc := { cc with rhss := {} }; { cc with rhss := m.insert k e }
@[inline] def GCache.insClosed (cc : GCache) (k : Expr) (a : Nat) : GCache :=
  let m := cc.closed; let cc := { cc with closed := {} }; { cc with closed := m.insert k a }
@[inline] def GCache.insApp (cc : GCache) (k : Name × List Level × Array Nat) (a : Nat) :
    GCache :=
  let m := cc.apps; let cc := { cc with apps := {} }; { cc with apps := m.insert k a }

/-- **The sharing switch** (task #423 probe): `0` thunks only, `1` one
cell per closed argument term, `2` as 1 and one cell per recursor or
definition application on equal argument cells. -/
@[noinline] def groundMemo : Nat := 2

/-- The hashes of the fourteen accelerated operations' names and the
well-founded ones: a cheap prefilter before the name comparisons. -/
def natBin14Names : List Name :=
  [natAddName, natSubName, natMulName, natPowName, natBeqName, natBleName,
   natDivName, natModName, natGcdName, natLandName, natLorName, natXorName,
   natShiftLeftName, natShiftRightName]

def natOpHashes : Array UInt64 :=
  (natBin14Names ++ natOpWfNames).toArray.map Name.hashData

def natBin14Slow (c : Name) : Bool :=
  c == natAddName || c == natSubName || c == natMulName ||
    c == natPowName || c == natBeqName || c == natBleName ||
    c == natDivName || c == natModName || c == natGcdName ||
    c == natLandName || c == natLorName || c == natXorName ||
    c == natShiftLeftName || c == natShiftRightName

def natBin14 (c : Name) : Bool :=
  natOpHashes.contains c.hashData && natBin14Slow c

/-- The comparand levels of a firing rule (`recFireComparands`'s first
component, which needs no arguments). -/
def gCmpLevels (rl : RecRule) (lps : List Name) (us : List Level)
    (cvjLps : List Name) : List Level :=
  match rl.fire with
  | .nested lvls _ => lvls.map (Level.subst lps us)
  | .plain => cvjLps.map fun p => Level.subst lps us (.param p)

/-- The leading argument frames of a stack, at most `k` of them, in
order, and the rest. -/
def gTakeArgs : Nat → List GFrame → Array Nat → Array Nat × List GFrame
  | 0, k, acc => (acc, k)
  | n + 1, .arg a :: k, acc => gTakeArgs n k (acc.push a)
  | _, k, acc => (acc, k)

/-- All the leading argument frames of a stack, in order, and the
rest. -/
def gTakeAll : List GFrame → Array Nat → Array Nat × List GFrame
  | .arg a :: k, acc => gTakeAll k (acc.push a)
  | k, acc => (acc, k)

/-- Push the addresses as argument frames, the first on top. -/
def gPushArgs (xs : Array Nat) (k : List GFrame) : List GFrame :=
  xs.foldr (fun a k => .arg a :: k) k

/-- Is the frame stack's top exactly two argument frames, then no
third? -/
def gTwoArgs : List GFrame → Option (Nat × Nat × List GFrame)
  | .arg _ :: .arg _ :: .arg _ :: _ => none
  | .arg a :: .arg b :: k => some (a, b, k)
  | _ => none

/-- The literal reading of a value that is already a numeral or a
`Nat` constructor application: `.inl n` a literal, `.inr t` a
`Nat.succ` of the cell `t`, `none` no reading. -/
@[inline] def gNatHead (natOk : Bool) : GVal → Option (Sum Nat Nat)
  | .lit (.natVal n) => some (.inl n)
  | .ctor c [] args =>
    if c == natZeroName && args.size == 0 then some (.inl 0)
    else if natOk && c == natSuccName && args.size == 1 then some (.inr args[0]!)
    else none
  | _ => none

section
variable (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)
  (natOk strOk : Bool)

/-- **The machine.**  `n` is the fuel, `h` the heap, `c` the control,
`k` the continuation. -/
def gRun : Nat → Array GCell → GCache → GCtrl → List GFrame → Nat → GOut
  | 0, _, _, _, _, st => .abort "fuel" st
  | n + 1, h, cc, ctrl, k, st =>
    match ctrl with
    | .eval env e =>
      match e with
      | .bvar i =>
        match env[i]? with
        | some a => gRun n h cc (.enter a) k st
        | none => .abort "loose bvar" st
      | .app f a =>
        match a with
        | .bvar i =>
          match env[i]? with
          | some x => gRun n h cc (.eval env f) (.arg x :: k) st
          | none => .abort "loose bvar" st
        | .lit l =>
          let x := h.size
          gRun n (h.push (.val (.lit l))) cc (.eval env f) (.arg x :: k) st
        | .lam ty b =>
          let x := h.size
          gRun n (h.push (.val (.lam env ty b))) cc (.eval env f) (.arg x :: k) st
        | _ =>
          if groundMemo != 0 && a.bvarBRaw == 0 then
            match cc.closed[a]? with
            | some x => gRun n h cc (.eval env f) (.arg x :: k) st
            | none =>
              let x := h.size
              gRun n (h.push (.thunk [] a)) (cc.insClosed a x) (.eval env f) (.arg x :: k) st
          else
            let x := h.size
            gRun n (h.push (.thunk env a)) cc (.eval env f) (.arg x :: k) st
      | .lam ty b =>
        match k with
        | .arg x :: k' => gRun n h cc (.eval (x :: env) b) k' st
        | _ => gRun n h cc (.ret (.lam env ty b)) k st
      | .letE _ v b =>
        let x := h.size
        gRun n (h.push (.thunk env v)) cc (.eval (x :: env) b) k st
      | .const c us => gRun n h cc (.const c us) k (st + 1)
      | .lit l => gRun n h cc (.ret (.lit l)) k st
      | .proj sn i s => gRun n h cc (.eval env s) (.proj sn i :: k) st
      | .sort _ | .forallE .. | .fvar .. => gRun n h cc (.ret .neutral) k st
    | .enter a =>
      match h[a]! with
      | .val v => gRun n h cc (.ret v) k st
      | .thunk env e => gRun n (h.set! a .busy) cc (.eval env e) (.upd a :: k) st
      | .busy => .abort "black hole" st
    | .const c us =>
      match find? c with
      | some (.defnInfo cv v _) =>
        -- literal acceleration first (`reduceNat`): exactly two
        -- arguments; short of them, the operation waits for them (the
        -- incumbent meets it as a spine, after substitution)
        let accel : Nat :=
          if us.isEmpty && natOk && natBin14 c then
            match gTwoArgs k with
            | some _ => 1
            | none => match k with
              | .arg _ :: .arg _ :: _ => 0
              | _ => 2
          else if us.isEmpty && natOpHashes.contains c.hashData && natOpWfNames.contains c &&
              (gTwoArgs k).isSome then 3
          else 0
        match accel, gTwoArgs k with
        | 1, some (a, b, k') => gRun n h cc (.enter a) (.natA c a b :: k') st
        | 2, _ =>
          let (xs, k') := gTakeArgs 2 k #[]
          gRun n h cc (.ret (.pap c us xs)) k' st
        | 3, _ => .abort "wf nat op" st
        | _, _ =>
          if groundMemo ≥ 2 then
            let (xs, k') := gTakeAll k #[]
            match cc.apps[(c, us, xs)]? with
            | some r => gRun n h cc (.enter r) k' st
            | none =>
              if us.length == cv.levelParams.length then
                let (body, cc) := if cv.levelParams.isEmpty then (v, cc) else
                  match cc.vals[(c, us)]? with
                  | some body => (body, cc)
                  | none =>
                    let body := v.instantiateLevelParams cv.levelParams us
                    (body, cc.insVal (c, us) body)
                let r := h.size
                gRun n (h.push .busy) (cc.insApp (c, us, xs) r) (.eval [] body)
                  (gPushArgs xs (.upd r :: k')) st
              else .abort "level arity" st
          else if cv.levelParams.isEmpty && us.isEmpty then
            gRun n h cc (.eval [] v) k st
          else if us.length == cv.levelParams.length then
            match cc.vals[(c, us)]? with
            | some body => gRun n h cc (.eval [] body) k st
            | none =>
              let body := v.instantiateLevelParams cv.levelParams us
              gRun n h (cc.insVal (c, us) body) (.eval [] body) k st
          else .abort "level arity" st
      | some (.ctorInfo ..) =>
        let (xs, k') := gTakeAll k #[]
        gRun n h cc (.ret (.ctor c us xs)) k' st
      | some (.recInfo cv mI rP rules) =>
        let (xs, k') := gTakeArgs (mI + 1) k #[]
        if xs.size < mI + 1 then gRun n h cc (.ret (.pap c us xs)) k' st
        else if us.length != cv.levelParams.length then .abort "rec level arity" st
        else if !(Expr.peelPis (mI + 1) cv.type).isSome then .abort "rec type" st
        else if groundMemo ≥ 2 then
          match cc.apps[(c, us, xs)]? with
          | some r => gRun n h cc (.enter r) k' st
          | none =>
            let r := h.size
            gRun n (h.push .busy) (cc.insApp (c, us, xs) r) (.enter xs[mI]!)
              (.iota c us cv.levelParams mI rP rules xs :: .upd r :: k') st
        else
          gRun n h cc (.enter xs[mI]!) (.iota c us cv.levelParams mI rP rules xs :: k') st
      | some _ =>
        let (_, k') := gTakeAll k #[]
        gRun n h cc (.ret .neutral) k' st
      | none => .abort "unknown constant" st
    | .ret v =>
      match k with
      | [] => .done v h st n
      | .upd a :: k' => gRun n (h.set! a (.val v)) cc (.ret v) k' st
      | .arg x :: k' =>
        match v with
        | .lam env _ b => gRun n h cc (.eval (x :: env) b) k' st
        | .ctor c us args =>
          let (xs, k'') := gTakeAll k' (args.push x)
          gRun n h cc (.ret (.ctor c us xs)) k'' st
        | .pap c us args => gRun n h cc (.const c us) (gPushArgs (args.push x) k') st
        | .neutral =>
          let (_, k'') := gTakeAll k' #[]
          gRun n h cc (.ret .neutral) k'' st
        | .lit _ => .abort "literal applied" st
      | .iota c us lps mI rP rules xs :: k' =>
        match v with
        | .lit (.natVal m) =>
          if natOk then
            match m with
            | 0 => gRun n h cc (.ret (.ctor natZeroName [] #[])) k st
            | m + 1 =>
              let x := h.size
              gRun n (h.push (.val (.lit (.natVal m)))) cc
                (.ret (.ctor natSuccName [] #[x])) k st
          else .abort "nat literal" st
        | .lit (.strVal s) =>
          if strOk then gRun n h cc (.eval [] (strLitToConstructor s)) k st
          else .abort "string literal" st
        | .ctor cj _ margs =>
          match rules.find? (fun r' => r'.ctor == cj) with
          | some rl =>
            if margs.size != rl.ctorParams + rl.nfields then .abort "ctor arity" st else
            let (rhs, case3, cc) := match cc.rhss[(c, cj, us)]? with
              | some (rhs, case3) => (rhs, case3, cc)
              | none =>
                let case3 := match find? cj with
                  | some (.ctorInfo cvj _ _) =>
                    iotaCase3 find? rl cvj (gCmpLevels rl lps us cvj.levelParams)
                  | _ => true
                let rhs := rl.rhs.instantiateLevelParams lps us
                (rhs, case3, cc.insRhs (c, cj, us) (rhs, case3))
            if case3 then .abort "case 3" st else
            let k₁ := gPushArgs (xs.extract (mI + 1) xs.size) k'
            let k₂ := gPushArgs (margs.extract rl.ctorParams margs.size) k₁
            let k₃ := gPushArgs (xs.extract 0 rP) k₂
            gRun n h cc (.eval [] rhs) k₃ st
          | none => .abort "no rule" st
        | _ =>
          if recRuleK rules then .abort "K major" st
          else .abort "major not a constructor" st
      | .proj sn i :: k' =>
        match v with
        | .lit (.strVal s) =>
          if strOk then gRun n h cc (.eval [] (strLitToConstructor s)) k st
          else .abort "string literal" st
        | .ctor kc us args =>
          match findProj? sn i with
          | some entry =>
            if kc == entry.ctor && i < entry.numFields &&
                args.size == entry.numParams + entry.numFields &&
                us.length == entry.levelParams.length && entry.fireOk us then
              match find? kc with
              | some (.ctorInfo cvC _ _) =>
                if (Expr.peelPis args.size cvC.type).isSome then
                  gRun n h cc (.enter args[entry.numParams + i]!) k' st
                else .abort "proj cert" st
              | _ => .abort "proj ctor" st
            else .abort "proj shape" st
          | none => .abort "proj table" st
        | _ => .abort "proj of non-constructor" st
      | .plus1 :: k' =>
        match gNatHead natOk v with
        | some (.inl m) => gRun n h cc (.ret (.lit (.natVal (m + 1)))) k' st
        | some (.inr t) => gRun n h cc (.enter t) (.plus1 :: k) st
        | none => gRun n h cc (.ret .neutral) k' st
      | .natA c a b :: k' =>
        match gNatHead natOk v with
        | some (.inl m) => gRun n h cc (.enter b) (.natB c m a b :: k') st
        | some (.inr t) => gRun n h cc (.enter t) (.plus1 :: k) st
        | none =>
          -- no literal: unfold the operation (`reduceNat` fails, δ)
          gRun n h cc (.const c []) (.arg a :: .arg b :: k') st
      | .natB c m a b :: k' =>
        match gNatHead natOk v with
        | some (.inl m₂) =>
          match natOpResult c m m₂ with
          | some r => gRun n h cc (.eval [] r) k' st
          | none => .abort "nat op" st
        | some (.inr t) => gRun n h cc (.enter t) (.plus1 :: k) st
        | none => gRun n h cc (.const c []) (.arg a :: .arg b :: k') st

end


/-- The outcome of a ground evaluation at the `Bool.true` comparison:
`some true`/`some false` for a `Bool` constructor, `none` otherwise,
with the step count and the abort reason (for the probe trace). -/
def groundBool (fe : FEnv) (e : Expr) : Option Bool × (Nat × Nat) × String :=
  let natOk := natLitSupportedF fe
  let strOk := strLitSupportedF fe
  match gRun fe.find? fe.findProj? natOk strOk groundFuel #[] {} (.eval [] e) [] 0 with
  | .done v _ st left =>
    let tr := groundFuel - left
    match v with
    | .ctor c [] args =>
      if c == boolTrueName && args.size == 0 then (some true, (st, tr), "")
      else if c == boolFalseName && args.size == 0 then (some false, (st, tr), "")
      else (none, (st, tr), "not a Bool")
    | _ => (none, (st, tr), "not a constructor")
  | .abort why st => (none, (st, 0), why)

end ConLeche.Cached

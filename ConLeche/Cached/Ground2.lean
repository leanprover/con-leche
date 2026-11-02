module

public import ConLeche.Cached.Ground

@[expose] public section

/-!
# The flat ground machine (task #423, round 2)

The machine of `Ground.lean` (round 1) with its state FLAT: no Lean
object is allocated per transition.  Every definition body and rule
right-hand side the site reaches is compiled once per run into a code
array (`Array Nat`, constants resolved to entries of a per-run
constant table, closed argument terms given a sharing slot), and the
machine's state is a handful of `Array Nat`s threaded linearly through
one tail-recursive loop (`g2Run`) and mutated in place:

* `cel` — cells, stride 3: `[state, code, env]`; state `0` an
  unevaluated thunk, `1` busy, `v + 2` evaluated to value `v`;
* `val` — values, stride 4: `[tag, a, b, c]` (a closure `[0, lamNode,
  env, _]`, a constructor `[1, entry, argStart, argLen]`, a `Nat`
  literal `[2, n, _, _]`, a string `[3, strIdx, _, _]`, a partial
  application `[4, entry, argStart, argLen]`, the neutral `[5, …]`);
* `ev` — environments, stride 2: `[cell, next]` (environment `0` is
  empty, `e + 1` the record at `2e`);
* `fs` — the frame stack, tag on top: `[cell, 1]` argument, `[cell, 2]`
  update, `[entry, argStart, argLen, 3]` ι, `[proj, 4]` projection,
  `[entry, a, b, 5]` and `[entry, n₁, a, b, 6]` literal acceleration,
  `[7]` `Nat.succ` packing;
* `argA` — argument spans of constructors, partial applications and
  memo keys;
* `slots` — the shared cell of each closed argument term and of each
  constant entry (`0` none yet);
* `mem` / `mH` — the application memo: records `[entry, argStart,
  argLen, cell, next]`, chained from a hash map of the key's hash.  An
  entry is a heap index, so it survives every in-place mutation.

The moves are round 1's (`Ground.lean`'s docstring has the `Red` reading
of each).  The differences: types (sorts, Π-types) are compiled to the
neutral, binder domains are dropped (read-back is never needed: the
answer is a `Bool` constructor), and a stuck scrutinee makes the
redex stuck (the neutral) instead of aborting.  Aborts remain where
the incumbent's answer needs type information (§ the K and η rules,
case 3), a decline (a well-founded `Nat` operation on two literals), or
an unknown constant.
-/

namespace ConLeche.Cached

open ConLeche

/-- Per-entry information of the run's constant table. -/
inductive G2Info where
  | defn (name : Name) (lps : List Name) (us : List Level) (v : Expr)
  | ctor (name : Name) (us : List Level) (nP nF : Nat)
  /-- `kEta`: the single rule of a structure-like recursor; `kK`: K -/
  | recr (lps : List Name) (us : List Level) (mI rP ruleBase nRules : Nat) (kK kEta : Bool)
  | neutral
  deriving Inhabited

/-- A recursor rule of the table. -/
structure G2Rule where
  ctor : Name
  nfields : Nat
  ctorParams : Nat
  case3 : Bool
  rhs : Expr
  deriving Inhabited

/-- A projection of the table (`none`: no projection table, stuck). -/
structure G2Proj where
  ctor : Name
  idx : Nat
  numParams : Nat
  numFields : Nat
  nlps : Nat
  always : Bool
  entry : ProjEntry
  deriving Inhabited

/-- The compiled program of a run: the code, the constant table, the
rules and projections, and the number of sharing slots. -/
structure G2Prog where
  code : Array Nat := #[]
  kTag : Array Nat := #[]
  kCode : Array Nat := #[]
  kArity : Array Nat := #[]
  kSlot : Array Nat := #[]
  kInfo : Array G2Info := #[]
  kMap : Std.HashMap (Name × List Level) Nat := {}
  rules : Array G2Rule := #[]
  ruleCode : Array Nat := #[]
  projs : Array G2Proj := #[]
  strs : Array String := #[]
  nslots : Nat := 1
  natOk : Bool := false
  strOk : Bool := false
  kTrue : Nat := 0
  kFalse : Nat := 0
  kZero : Nat := 0
  kSucc : Nat := 0
  deriving Inhabited

/-- The number of leading Π-binders of a type. -/
def g2Pis : Expr → Nat → Nat
  | .forallE _ b, n => g2Pis b (n + 1)
  | _, n => n

section
variable (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)

/-- The table entry of the constant `c` at levels `us`, created on first
use.  Kinds: `0` definition, `1` constructor, `2` recursor, `3` an
accelerated `Nat` operation (a definition too), `4` a well-founded
`Nat` operation (a definition too), `5` neutral. -/
def g2Resolve (P : G2Prog) (c : Name) (us : List Level) : Nat × G2Prog :=
  match P.kMap[(c, us)]? with
  | some k => (k, P)
  | none =>
    let k := P.kTag.size
    let (tag, ar, info, P) : Nat × Nat × G2Info × G2Prog :=
      match find? c with
      | some (.defnInfo cv v _) =>
        if us.length != cv.levelParams.length then (5, 0, .neutral, P)
        else
          let tag := if us.isEmpty && P.natOk && natBin14 c then 3
            else if us.isEmpty && natOpWfNames.contains c then 4 else 0
          (tag, 0, .defn c cv.levelParams us v, P)
      | some (.ctorInfo cv nP nF) => (1, g2Pis cv.type 0, .ctor c us nP nF, P)
      | some (.recInfo cv mI rP rules) =>
        if us.length != cv.levelParams.length || !(Expr.peelPis (mI + 1) cv.type).isSome then
          (5, 0, .neutral, P)
        else
          let base := P.rules.size
          let P := rules.foldl (fun P rl =>
            let case3 := match find? rl.ctor with
              | some (.ctorInfo cvj _ _) =>
                iotaCase3 find? rl cvj (gCmpLevels rl cv.levelParams us cvj.levelParams)
              | _ => true
            { P with rules := P.rules.push ⟨rl.ctor, rl.nfields, rl.ctorParams, case3, rl.rhs⟩,
                     ruleCode := P.ruleCode.push 0 }) P
          let isEta := match rules with | [rl] => rl.eta | _ => false
          (2, mI, .recr cv.levelParams us mI rP base rules.length (recRuleK rules) isEta, P)
      | _ => (5, 0, .neutral, P)
    (k, { P with kTag := P.kTag.push tag, kCode := P.kCode.push 0, kArity := P.kArity.push ar,
                 kSlot := P.kSlot.push P.nslots, nslots := P.nslots + 1,
                 kInfo := P.kInfo.push info, kMap := P.kMap.insert (c, us) k })

mutual
/-- Compile `e` (closed under the binders the code will be run under);
the result is the node's offset.  Code tags: `0` bvar `[0, i]`, `1`
spine `[1, head, n, a₁ … aₙ]`, `2` λ `[2, body]`, `3` let `[3, v, body]`,
`4` constant `[4, entry]`, `5` `Nat` literal `[5, n]`, `6` string `[6,
s]`, `7` projection `[7, proj + 1 or 0, e]`, `8` neutral `[8]`, `9`
shared closed argument `[9, slot, e]`. -/
def g2Comp : Nat → G2Prog → Expr → Nat × G2Prog
  | 0, P, _ => let o := P.code.size; (o, { P with code := P.code.push 8 })
  | f + 1, P, e =>
    match e with
    | .bvar i => let o := P.code.size; (o, { P with code := (P.code.push 0).push i })
    | .lam _ b =>
      let (bo, P) := g2Comp f P b
      let o := P.code.size; (o, { P with code := (P.code.push 2).push bo })
    | .letE _ v b =>
      let (vo, P) := g2CompArg f P v
      let (bo, P) := g2Comp f P b
      let o := P.code.size; (o, { P with code := ((P.code.push 3).push vo).push bo })
    | .const c us =>
      let (k, P) := g2Resolve find? P c us
      let o := P.code.size; (o, { P with code := (P.code.push 4).push k })
    | .lit (.natVal n) => let o := P.code.size; (o, { P with code := (P.code.push 5).push n })
    | .lit (.strVal s) =>
      let o := P.code.size
      (o, { P with code := (P.code.push 6).push P.strs.size, strs := P.strs.push s })
    | .proj sn i s =>
      let (so, P) := g2Comp f P s
      let (pi, P) := match findProj? sn i with
        | some en =>
          let pj : G2Proj := ⟨en.ctor, i, en.numParams, en.numFields, en.levelParams.length,
             !(Level.isEquiv en.structSort .zero == some true), en⟩
          (P.projs.size + 1, { P with projs := P.projs.push pj })
        | none => (0, P)
      let o := P.code.size; (o, { P with code := ((P.code.push 7).push pi).push so })
    | .app .. =>
      let (ho, args) := (e.getAppFn, e.getAppArgs)
      let (ho, P) := g2Comp f P ho
      let (aos, P) := args.foldl (fun (acc : Array Nat × G2Prog) a =>
        let (ao, P) := g2CompArg f acc.2 a; (acc.1.push ao, P)) (#[], P)
      let o := P.code.size
      let code := ((P.code.push 1).push ho).push aos.size
      (o, { P with code := aos.foldl (fun c a => c.push a) code })
    | .sort _ | .forallE .. | .fvar .. => let o := P.code.size; (o, { P with code := P.code.push 8 })

/-- An argument position: a closed application, `let` or projection
gets a sharing slot. -/
def g2CompArg : Nat → G2Prog → Expr → Nat × G2Prog
  | 0, P, _ => let o := P.code.size; (o, { P with code := P.code.push 8 })
  | f + 1, P, a =>
    match a with
    | .app .. | .letE .. | .proj .. =>
      let (ao, P) := g2Comp f P a
      if a.bvarBRaw == 0 then
        let o := P.code.size
        (o, { P with code := ((P.code.push 9).push P.nslots).push ao, nslots := P.nslots + 1 })
      else (ao, P)
    | _ => g2Comp f P a
end
end

/-- The compiler's recursion budget (a termination device, as
`checkFuel`). -/
@[irreducible, noinline] def g2CompFuel : Nat := 4611686018427387904  -- 2^62

/-! ## Flat-state helpers (each returns one array: no tuple per call) -/

@[inline] def g2EnvGet (ev : Array Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | e + 1, 0 => ev[2 * e]!
  | e + 1, i + 1 => g2EnvGet ev ev[2 * e + 1]! i

/-- The number of argument frames on top of the stack. -/
def g2CountArgs (fs : Array Nat) : Nat → Nat → Nat
  | 0, n => n
  | top + 1, n =>
    if fs[top]! == 1 then match top with
      | t + 1 => g2CountArgs fs t (n + 1)
      | 0 => n
    else n

/-- The `j`-th argument cell from the top. -/
@[inline] def g2ArgAt (fs : Array Nat) (j : Nat) : Nat := fs[fs.size - 2 - 2 * j]!

/-- Append the top `n` argument cells, first argument first. -/
def g2CopyArgs (fs : Array Nat) (argA : Array Nat) : Nat → Nat → Array Nat
  | 0, _ => argA
  | n + 1, j => g2CopyArgs fs (argA.push (g2ArgAt fs j)) n (j + 1)

/-- Append `argA[start, start + len)` to itself. -/
def g2CopyFrom (argA : Array Nat) (start : Nat) : Nat → Nat → Array Nat
  | 0, _ => argA
  | n + 1, j => g2CopyFrom (argA.push argA[start + j]!) start n (j + 1)

@[inline] def g2SlotGet (slots : Array Nat) (s : Nat) : Nat :=
  if s < slots.size then slots[s]! else 0

def g2SlotSet (slots : Array Nat) (s c : Nat) : Array Nat :=
  if s < slots.size then slots.set! s c
  else (slots ++ Array.replicate (s + 1 - slots.size) 0).set! s c

def g2PopN (fs : Array Nat) : Nat → Array Nat
  | 0 => fs
  | n + 1 => g2PopN fs.pop n

/-- Push `argA[start, start + len)` as argument frames, the first on
top. -/
def g2PushArgs (argA : Array Nat) (start : Nat) (fs : Array Nat) : Nat → Array Nat
  | 0 => fs
  | len + 1 => g2PushArgs argA start ((fs.push argA[start + len]!).push 1) len

/-- The memo key's hash. -/
def g2Hash (fs : Array Nat) (k : Nat) : Nat → Nat → UInt64 → UInt64
  | 0, _, h => h
  | n + 1, j, h => g2Hash fs k n (j + 1) (mixHash h (g2ArgAt fs j).toUInt64)

/-- Does the memo record's key span equal the top `n` arguments? -/
def g2SpanEq (fs argA : Array Nat) (start : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, j => argA[start + j]! == g2ArgAt fs j && g2SpanEq fs argA start n (j + 1)

/-- Walk a memo chain for the entry `k` and the top `n` arguments; the
result cell, or `0`. -/
def g2MemoFind (mem fs argA : Array Nat) (k n : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, r =>
    if r == 0 then 0 else
    let b := 5 * (r - 1)
    if mem[b]! == k && mem[b + 2]! == n && g2SpanEq fs argA mem[b + 1]! n 0 then mem[b + 3]!
    else g2MemoFind mem fs argA k n f mem[b + 4]!

/-- Find the rule of constructor `c` among `n` rules from `base`. -/
def g2FindRule (P : G2Prog) (c : Name) : Nat → Nat → Option Nat
  | 0, _ => none
  | n + 1, i => if P.rules[i]!.ctor == c then some i else g2FindRule P c n (i + 1)

/-- The application memo switch (task #423 probe): `0` none, `1`
recursor applications only, `2` recursors and definitions. -/
@[noinline] def g2Memo : Nat := 2

section
variable (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)

/-- The machine's outcome: a value (with the value array to read it),
or an abort; the constant dispatches and the fuel left. -/
inductive G2Out where
  | done (v : Nat) (val : Array Nat) (P : G2Prog) (steps left : Nat)
  | abort (why : String) (steps : Nat)

/-- **The machine.**  Modes: `0` evaluate node `pc` under `env`, `1`
return value `x`, `2` enter cell `x`, `3` dispatch constant entry `x` (`pc = 1`: as a plain definition),
`4` push the arguments of spine `pc` from the `x`-th down. -/
def g2Run : Nat → G2Prog → (cel val ev fs argA slots mem : Array Nat) →
    Std.HashMap UInt64 Nat → (mode pc env x st : Nat) → G2Out
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, st => .abort "fuel" st
  | n + 1, P, cel, val, ev, fs, argA, slots, mem, mH, mode, pc, env, x, st =>
    match mode with
    | 0 => -- evaluate
      match P.code[pc]! with
      | 0 => g2Run n P cel val ev fs argA slots mem mH 2 0 0 (g2EnvGet ev env P.code[pc + 1]!) st
      | 1 => g2Run n P cel val ev fs argA slots mem mH 4 pc env P.code[pc + 2]! st
      | 2 =>
        if fs.size > 0 && fs[fs.size - 1]! == 1 then
          let c := fs[fs.size - 2]!
          let e' := ev.size / 2 + 1
          g2Run n P cel val ((ev.push c).push env) fs.pop.pop argA slots mem mH 0
            P.code[pc + 1]! e' 0 st
        else
          let v := val.size / 4
          g2Run n P cel ((((val.push 0).push pc).push env).push 0) ev fs argA slots mem mH 1 0 0 v st
      | 3 =>
        -- `let`: the value as an argument cell, then the body
        let vo := P.code[pc + 1]!
        let c := cel.size / 3
        let e' := ev.size / 2 + 1
        g2Run n P (((cel.push 0).push vo).push env) val ((ev.push c).push env) fs argA slots mem mH
          0 P.code[pc + 2]! e' 0 st
      | 4 => g2Run n P cel val ev fs argA slots mem mH 3 0 0 P.code[pc + 1]! (st + 1)
      | 5 =>
        let v := val.size / 4
        g2Run n P cel ((((val.push 2).push P.code[pc + 1]!).push 0).push 0) ev fs argA slots mem mH
          1 0 0 v st
      | 6 =>
        let v := val.size / 4
        g2Run n P cel ((((val.push 3).push P.code[pc + 1]!).push 0).push 0) ev fs argA slots mem mH
          1 0 0 v st
      | 7 => g2Run n P cel val ev ((fs.push P.code[pc + 1]!).push 4) argA slots mem mH 0
          P.code[pc + 2]! env 0 st
      | 9 => -- a shared closed term at the head: its slot's cell
        let s := P.code[pc + 1]!
        let c := g2SlotGet slots s
        if c != 0 then g2Run n P cel val ev fs argA slots mem mH 2 0 0 c st
        else
          let c := cel.size / 3
          g2Run n P (((cel.push 0).push P.code[pc + 2]!).push 0) val ev fs argA (g2SlotSet slots s c)
            mem mH 2 0 0 c st
      | _ => g2Run n P cel val ev fs argA slots mem mH 1 0 0 0 st
    | 4 => -- push the spine's arguments, the last first
      match x with
      | 0 => g2Run n P cel val ev fs argA slots mem mH 0 P.code[pc + 1]! env 0 st
      | j + 1 =>
        let ao := P.code[pc + 3 + j]!
        match P.code[ao]! with
        | 0 =>
          g2Run n P cel val ev ((fs.push (g2EnvGet ev env P.code[ao + 1]!)).push 1) argA slots mem mH
            4 pc env j st
        | 2 =>
          let v := val.size / 4
          let c := cel.size / 3
          g2Run n P (((cel.push (v + 2)).push ao).push env)
            ((((val.push 0).push ao).push env).push 0) ev ((fs.push c).push 1) argA slots mem mH
            4 pc env j st
        | 5 =>
          let v := val.size / 4
          let c := cel.size / 3
          g2Run n P (((cel.push (v + 2)).push ao).push 0)
            ((((val.push 2).push P.code[ao + 1]!).push 0).push 0) ev ((fs.push c).push 1) argA
            slots mem mH 4 pc env j st
        | 8 => g2Run n P cel val ev ((fs.push 0).push 1) argA slots mem mH 4 pc env j st
        | 4 => -- a constant: its entry's shared cell
          let s := P.kSlot[P.code[ao + 1]!]!
          let c := g2SlotGet slots s
          if c != 0 then
            g2Run n P cel val ev ((fs.push c).push 1) argA slots mem mH 4 pc env j st
          else
            let c := cel.size / 3
            g2Run n P (((cel.push 0).push ao).push 0) val ev ((fs.push c).push 1) argA
              (g2SlotSet slots s c) mem mH 4 pc env j st
        | 9 =>
          let s := P.code[ao + 1]!
          let c := g2SlotGet slots s
          if c != 0 then
            g2Run n P cel val ev ((fs.push c).push 1) argA slots mem mH 4 pc env j st
          else
            let c := cel.size / 3
            g2Run n P (((cel.push 0).push P.code[ao + 2]!).push 0) val ev ((fs.push c).push 1) argA
              (g2SlotSet slots s c) mem mH 4 pc env j st
        | _ =>
          let c := cel.size / 3
          g2Run n P (((cel.push 0).push ao).push env) val ev ((fs.push c).push 1) argA slots mem mH
            4 pc env j st
    | 2 => -- enter a cell
      let s := cel[3 * x]!
      if s ≥ 2 then g2Run n P cel val ev fs argA slots mem mH 1 0 0 (s - 2) st
      else if s == 0 then
        g2Run n P (cel.set! (3 * x) 1) val ev ((fs.push x).push 2) argA slots mem mH 0
          cel[3 * x + 1]! cel[3 * x + 2]! 0 st
      else .abort "black hole" st
    | 3 => -- dispatch a constant
      let k := x
      -- `pc = 1`: a plain δ (an accelerated operation whose argument read no literal)
      match (if pc == 1 then 0 else P.kTag[k]!) with
      | 1 =>
        let na := g2CountArgs fs fs.size 0
        let start := argA.size
        let v := val.size / 4
        g2Run n P cel ((((val.push 1).push k).push start).push na) ev (g2PopN fs (2 * na))
          (g2CopyArgs fs argA na 0) slots mem mH 1 0 0 v st
      | 2 =>
        match P.kInfo[k]! with
        | .recr _ _ mI _ _ _ _ _ =>
          let na := g2CountArgs fs fs.size 0
          if na < mI + 1 then
            let start := argA.size
            let v := val.size / 4
            g2Run n P cel ((((val.push 4).push k).push start).push na) ev (g2PopN fs (2 * na))
              (g2CopyArgs fs argA na 0) slots mem mH 1 0 0 v st
          else
            let h := g2Hash fs k (mI + 1) 0 (UInt64.ofNat k)
            let hit := if g2Memo ≥ 1 then g2MemoFind mem fs argA k (mI + 1) mem.size (mH.getD h 0)
              else 0
            if hit != 0 then
              g2Run n P cel val ev (g2PopN fs (2 * (mI + 1))) argA slots mem mH 2 0 0 hit st
            else
              let start := argA.size
              let argA := g2CopyArgs fs argA (mI + 1) 0
              let fs := g2PopN fs (2 * (mI + 1))
              let r := cel.size / 3
              let (mem, mH) := if g2Memo ≥ 1 then
                  let rec_ := mem.size / 5 + 1
                  (((((mem.push k).push start).push (mI + 1)).push r).push (mH.getD h 0),
                   mH.insert h rec_)
                else (mem, mH)
              g2Run n P (((cel.push 1).push 0).push 0) val ev
                ((((((fs.push r).push 2).push k).push start).push (mI + 1)).push 3) argA slots
                mem mH 2 0 0 argA[start + mI]! st
        | _ => .abort "rec info" st
      | 5 =>
        let na := g2CountArgs fs fs.size 0
        g2Run n P cel val ev (g2PopN fs (2 * na)) argA slots mem mH 1 0 0 0 st
      | t =>
        -- a definition; tags 3 and 4 try literal acceleration first
        let na := g2CountArgs fs fs.size 0
        if (t == 3 || t == 4) && na == 2 then
          let a := g2ArgAt fs 0
          let b := g2ArgAt fs 1
          g2Run n P cel val ev ((((((g2PopN fs 4).push k).push a).push b).push (if t == 3 then 5 else 15)))
            argA slots mem mH 2 0 0 a st
        else if t == 3 && na < 2 then
          let start := argA.size
          let v := val.size / 4
          g2Run n P cel ((((val.push 4).push k).push start).push na) ev (g2PopN fs (2 * na))
            (g2CopyArgs fs argA na 0) slots mem mH 1 0 0 v st
        else
          -- δ: the compiled body, memoised on the argument cells
          let (body, P) :=
            if P.kCode[k]! != 0 then (P.kCode[k]! - 1, P) else
            match P.kInfo[k]! with
            | .defn _ lps us v =>
              let (o, P) := g2Comp find? findProj? g2CompFuel P (v.instantiateLevelParams lps us)
              (o, { P with kCode := P.kCode.set! k (o + 1) })
            | _ => (0, P)
          if g2Memo ≥ 2 && na > 0 then
            let h := g2Hash fs k na 0 (UInt64.ofNat k)
            let hit := g2MemoFind mem fs argA k na mem.size (mH.getD h 0)
            if hit != 0 then
              g2Run n P cel val ev (g2PopN fs (2 * na)) argA slots mem mH 2 0 0 hit st
            else
              let start := argA.size
              let argA := g2CopyArgs fs argA na 0
              let fs := g2PopN fs (2 * na)
              let r := cel.size / 3
              let rec_ := mem.size / 5 + 1
              let mem := ((((mem.push k).push start).push na).push r).push (mH.getD h 0)
              let mH := mH.insert h rec_
              g2Run n P (((cel.push 1).push 0).push 0) val ev
                (g2PushArgs argA start ((fs.push r).push 2) na) argA slots mem mH 0 body 0 0 st
          else g2Run n P cel val ev fs argA slots mem mH 0 body 0 0 st
    | _ => -- return value `x`
      let v := x
      if fs.size == 0 then .done v val P st n else
      match fs[fs.size - 1]! with
      | 2 =>
        let c := fs[fs.size - 2]!
        g2Run n P (cel.set! (3 * c) (v + 2)) val ev fs.pop.pop argA slots mem mH 1 0 0 v st
      | 1 =>
        let c := fs[fs.size - 2]!
        match val[4 * v]! with
        | 0 =>
          let e' := ev.size / 2 + 1
          g2Run n P cel val ((ev.push c).push val[4 * v + 2]!) fs.pop.pop argA slots mem mH 0
            P.code[val[4 * v + 1]! + 1]! e' 0 st
        | 1 =>
          let na := g2CountArgs fs fs.size 0
          let start := argA.size
          let len := val[4 * v + 3]!
          let argA := g2CopyArgs fs (g2CopyFrom argA val[4 * v + 2]! len 0) na 0
          let w := val.size / 4
          g2Run n P cel ((((val.push 1).push val[4 * v + 1]!).push start).push (len + na)) ev
            (g2PopN fs (2 * na)) argA slots mem mH 1 0 0 w st
        | 4 =>
          g2Run n P cel val ev (g2PushArgs argA val[4 * v + 2]! fs val[4 * v + 3]!) argA slots mem mH
            3 0 0 val[4 * v + 1]! st
        | _ =>
          let na := g2CountArgs fs fs.size 0
          g2Run n P cel val ev (g2PopN fs (2 * na)) argA slots mem mH 1 0 0 0 st
      | 3 =>
        let _len := fs[fs.size - 2]!
        let start := fs[fs.size - 3]!
        let k := fs[fs.size - 4]!
        match val[4 * v]! with
        | 2 =>
          if !P.natOk then .abort "nat literal" st else
          let m := val[4 * v + 1]!
          match m with
          | 0 =>
            let w := val.size / 4
            g2Run n P cel ((((val.push 1).push P.kZero).push 0).push 0) ev fs argA slots mem mH
              1 0 0 w st
          | m + 1 =>
            let c := cel.size / 3
            let u := val.size / 4
            let w := u + 1
            let sa := argA.size
            g2Run n P (((cel.push (u + 2)).push 0).push 0)
              ((((((((val.push 2).push m).push 0).push 0).push 1).push P.kSucc).push sa).push 1)
              ev fs (argA.push c) slots mem mH 1 0 0 w st
        | 3 =>
          if !P.strOk then .abort "string literal" st else
          let (o, P) := g2Comp find? findProj? g2CompFuel P (strLitToConstructor P.strs[val[4 * v + 1]!]!)
          g2Run n P cel val ev fs argA slots mem mH 0 o 0 0 st
        | 1 =>
          let kc := val[4 * v + 1]!
          match P.kInfo[k]!, P.kInfo[kc]! with
          | .recr lps us mI rP base nr _ _, .ctor cname _ _ _ =>
            match g2FindRule P cname nr base with
            | some ri =>
              let rl := P.rules[ri]!
              let margs := val[4 * v + 3]!
              let ms := val[4 * v + 2]!
              if margs != rl.ctorParams + rl.nfields then .abort "ctor arity" st
              else if rl.case3 then .abort "case 3" st
              else
                let (rhs, P) :=
                  if P.ruleCode[ri]! != 0 then (P.ruleCode[ri]! - 1, P) else
                  let (o, P) := g2Comp find? findProj? g2CompFuel P
                    (rl.rhs.instantiateLevelParams lps us)
                  (o, { P with ruleCode := P.ruleCode.set! ri (o + 1) })
                let fs := g2PopN fs 4
                let fs := g2PushArgs argA (ms + rl.ctorParams) fs rl.nfields
                let fs := g2PushArgs argA start fs rP
                let _ := mI
                g2Run n P cel val ev fs argA slots mem mH 0 rhs 0 0 st
            | none => .abort "no rule" st
          | _, _ => .abort "iota info" st
        | 5 =>
          match P.kInfo[k]! with
          | .recr _ _ _ _ _ _ kK kEta =>
            if kK then .abort "K major" st
            else if kEta then .abort "struct-eta major" st
            else g2Run n P cel val ev (g2PopN fs 4) argA slots mem mH 1 0 0 0 st
          | _ => .abort "iota info" st
        | _ => g2Run n P cel val ev (g2PopN fs 4) argA slots mem mH 1 0 0 0 st
      | 4 =>
        let pi := fs[fs.size - 2]!
        let fs := fs.pop.pop
        if pi == 0 then g2Run n P cel val ev fs argA slots mem mH 1 0 0 0 st else
        let pj := P.projs[pi - 1]!
        match val[4 * v]! with
        | 1 =>
          let kc := val[4 * v + 1]!
          let len := val[4 * v + 3]!
          match P.kInfo[kc]! with
          | .ctor cname us _ _ =>
            if cname == pj.ctor && pj.idx < pj.numFields && len == pj.numParams + pj.numFields &&
                len ≤ P.kArity[kc]! && us.length == pj.nlps &&
                (pj.always || pj.entry.fireOk us) then
              g2Run n P cel val ev fs argA slots mem mH 2 0 0
                argA[val[4 * v + 2]! + pj.numParams + pj.idx]! st
            else .abort "proj shape" st
          | _ => .abort "proj ctor" st
        | 3 =>
          if !P.strOk then .abort "string literal" st else
          let (o, P) := g2Comp find? findProj? g2CompFuel P (strLitToConstructor P.strs[val[4 * v + 1]!]!)
          g2Run n P cel val ev ((fs.push pi).push 4) argA slots mem mH 0 o 0 0 st
        | _ => g2Run n P cel val ev fs argA slots mem mH 1 0 0 0 st
      | 7 =>
        match val[4 * v]! with
        | 2 =>
          let w := val.size / 4
          g2Run n P cel ((((val.push 2).push (val[4 * v + 1]! + 1)).push 0).push 0) ev fs.pop
            argA slots mem mH 1 0 0 w st
        | 1 =>
          let kc := val[4 * v + 1]!
          if kc == P.kZero && val[4 * v + 3]! == 0 then
            let w := val.size / 4
            g2Run n P cel ((((val.push 2).push 1).push 0).push 0) ev fs.pop argA slots mem mH 1 0 0 w st
          else if kc == P.kSucc && val[4 * v + 3]! == 1 then
            g2Run n P cel val ev (fs.push 7) argA slots mem mH 2 0 0 argA[val[4 * v + 2]!]! st
          else g2Run n P cel val ev fs.pop argA slots mem mH 1 0 0 0 st
        | _ => g2Run n P cel val ev fs.pop argA slots mem mH 1 0 0 0 st
      | t =>
        -- literal acceleration: `[k, a, b, 5|15]` reads the first
        -- argument, `[k, n₁, a, b, 6|16]` the second
        let first := t == 5 || t == 15
        let wf := t == 15 || t == 16
        let lit? : Option Nat ⊕ Nat := match val[4 * v]! with
          | 2 => .inl (some val[4 * v + 1]!)
          | 1 =>
            let kc := val[4 * v + 1]!
            if kc == P.kZero && val[4 * v + 3]! == 0 then .inl (some 0)
            else if kc == P.kSucc && val[4 * v + 3]! == 1 then .inr argA[val[4 * v + 2]!]!
            else .inl none
          | _ => .inl none
        match lit? with
        | .inr cellT => g2Run n P cel val ev (fs.push 7) argA slots mem mH 2 0 0 cellT st
        | .inl (some m) =>
          if first then
            let b := fs[fs.size - 2]!
            let a := fs[fs.size - 3]!
            let k := fs[fs.size - 4]!
            let fs := g2PopN fs 4
            g2Run n P cel val ev (((((fs.push k).push m).push a).push b).push (if wf then 16 else 6))
              argA slots mem mH 2 0 0 b st
          else
            let k := fs[fs.size - 5]!
            let m₁ := fs[fs.size - 4]!
            let fs := g2PopN fs 5
            if wf then .abort "wf nat op" st else
            match P.kInfo[k]! with
            | .defn c _ _ _ =>
              match natOpResult c m₁ m with
              | some (.lit (.natVal r)) =>
                let w := val.size / 4
                g2Run n P cel ((((val.push 2).push r).push 0).push 0) ev fs argA slots mem mH
                  1 0 0 w st
              | some (.const c []) =>
                let kb := if c == boolTrueName then P.kTrue else P.kFalse
                let w := val.size / 4
                g2Run n P cel ((((val.push 1).push kb).push 0).push 0) ev fs argA slots mem mH
                  1 0 0 w st
              | _ => .abort "nat op" st
            | _ => .abort "nat op info" st
        | .inl none =>
          -- no literal: unfold the operation (`reduceNat` fails, δ)
          let (k, a, b, fs) :=
            if first then (fs[fs.size - 4]!, fs[fs.size - 3]!, fs[fs.size - 2]!, g2PopN fs 4)
            else (fs[fs.size - 5]!, fs[fs.size - 3]!, fs[fs.size - 2]!, g2PopN fs 5)
          -- the operation's tag is 3 or 4; dispatch it as a plain definition
          g2Run n P cel val ev
            ((((fs.push b).push 1).push a).push 1) argA slots mem mH 3 1 0 k st
end

end ConLeche.Cached

namespace ConLeche.Cached
open ConLeche

/-- The outcome of a round-2 evaluation at the `Bool.true` comparison,
as `groundBool`'s. -/
def ground2BoolCore (find? : Name → Option ConstantInfo)
    (findProj? : Name → Nat → Option ProjEntry) (natOk strOk : Bool) (e : Expr) :
    Option Bool × (Nat × Nat) × String :=
  let P : G2Prog := { natOk := natOk, strOk := strOk }
  let (kT, P) := g2Resolve find? P boolTrueName []
  let (kF, P) := g2Resolve find? P boolFalseName []
  let (kZ, P) := g2Resolve find? P natZeroName []
  let (kS, P) := g2Resolve find? P natSuccName []
  let P := { P with kTrue := kT, kFalse := kF, kZero := kZ, kSucc := kS }
  let (o, P) := g2Comp find? findProj? g2CompFuel P e
  match g2Run find? findProj? groundFuel P #[2, 0, 0] #[5, 0, 0, 0] #[] #[] #[] #[] #[] {}
      0 o 0 0 0 with
  | .done v val P st left =>
    let tr := groundFuel - left
    if val[4 * v]! == 1 && val[4 * v + 3]! == 0 then
      let k := val[4 * v + 1]!
      if k == P.kTrue then (some true, (st, tr), "")
      else if k == P.kFalse then (some false, (st, tr), "")
      else (none, (st, tr), "not a Bool")
    else (none, (st, tr), "not a constructor")
  | .abort why st => (none, (st, 0), why)

def ground2Bool (fe : FEnv) (e : Expr) : Option Bool × (Nat × Nat) × String :=
  ground2BoolCore fe.find? fe.findProj? (natLitSupportedF fe) (strLitSupportedF fe) e

/-- **The ground shortcut** (task #423, spike; `groundMode ≠ 0`): a
comparison with `Bool.true` on either side whose other side is closed
evaluates that side on the ground machine: `Bool.true` answers `true`,
`Bool.false` answers `false` (the two constructors are not
definitionally equal), anything else (an abort) leaves the comparison
to the incumbent path (`none`).  Read by `defeqBodyI`
(`ConLeche/Cached/CoreC.lean`). -/
def groundShortcut (mode : CheckMode) (fe : FEnv) (a b : Expr) : Option Bool :=
  let t? : Option Expr :=
    if Expr.isBoolTrue b && (mode.eager || !(Expr.hasFvar a)) then some a
    else if Expr.isBoolTrue a && (mode.eager || !(Expr.hasFvar b)) then some b
    else none
  match t? with
  | none => none
  | some t =>
    if Expr.hasFvar t then none else
    let r2 := groundMode ≥ 3 && groundMode != 5
    let eng := fun t => if r2 then ground2Bool fe t else groundBool fe t
    let (r, steps, why) := eng t
    -- probes 5 and 6: the engine twice (its own cost is the difference)
    let r := if groundMode == 5 || groundMode == 6 then
        (if (eng (dbgTrace "" fun _ => t)).1 == r then r else none) else r
    if groundMode == 2 || groundMode == 4 then
      dbgTrace s!"GROUND {repr r} {steps.1} {steps.2} {why}" fun _ => r
    else r

/-- The shortcut behind the switch: `none` (the incumbent path) at
`groundMode = 0`. -/
@[inline] def groundGate (mode : CheckMode) (fe : FEnv) (a b : Expr) : Option Bool :=
  if groundMode == 0 then none else groundShortcut mode fe a b

/-- The ground shortcut reads `fe` only through `find?` and
`findTable?` (for `ConLeche/Verify/Cached/KnotCongr.lean`). -/
theorem groundShortcut_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (mode : CheckMode) :
    groundShortcut mode fe₁ = groundShortcut mode fe₂ := by
  have hp : fe₁.findProj? = fe₂.findProj? := by
    funext T i; unfold FEnv.findProj?; rw [htb]
  have hg : groundBool fe₁ = groundBool fe₂ := by
    funext e; unfold groundBool strLitSupportedF natLitSupportedF; rw [hfe, hp]
  have hn : natLitSupportedF fe₁ = natLitSupportedF fe₂ := by
    unfold natLitSupportedF; rw [hfe]
  have hs : strLitSupportedF fe₁ = strLitSupportedF fe₂ := by
    unfold strLitSupportedF; rw [hn, hfe]
  have hg2 : ground2Bool fe₁ = ground2Bool fe₂ := by
    funext e; unfold ground2Bool; rw [hfe, hp, hn, hs]
  funext a b; unfold groundShortcut; rw [hg, hg2]

theorem groundGate_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (mode : CheckMode) :
    groundGate mode fe₁ = groundGate mode fe₂ := by
  funext a b; unfold groundGate; rw [groundShortcut_congr hfe htb]

end ConLeche.Cached

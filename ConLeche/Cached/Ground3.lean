module

public import ConLeche.Cached.Ground2

@[expose] public section

/-!
# The flat ground machine, round 3 (task #423): direct `.rec` code

The machine of `Ground.lean` (round 1) with its state FLAT: no Lean
object is allocated per transition.  Every definition body and rule
right-hand side the site reaches is compiled once per run into a code
array (`Array Nat`, constants resolved to entries of a per-run
constant table, closed argument terms given a sharing slot), and the
machine's state is a handful of `Array Nat`s threaded linearly through
one tail-recursive loop (`g3Run`) and mutated in place:

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
inductive G3Info where
  | defn (name : Name) (lps : List Name) (us : List Level) (v : Expr)
  | ctor (name : Name) (us : List Level) (nP nF : Nat)
  /-- `kEta`: the single rule of a structure-like recursor; `kK`: K -/
  | recr (lps : List Name) (us : List Level) (mI rP ruleBase nRules : Nat) (kK kEta : Bool)
  | neutral
  deriving Inhabited

/-- A recursor rule of the table. -/
structure G3Rule where
  ctor : Name
  nfields : Nat
  ctorParams : Nat
  case3 : Bool
  rhs : Expr
  deriving Inhabited

/-- A projection of the table (`none`: no projection table, stuck). -/
structure G3Proj where
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
structure G3Prog where
  code : Array Nat := #[]
  kTag : Array Nat := #[]
  kCode : Array Nat := #[]
  kArity : Array Nat := #[]
  kSlot : Array Nat := #[]
  /-- recursor: `rulePrefix`; constructor: its name's id -/
  kB : Array Nat := #[]
  /-- recursor: first rule -/
  kC : Array Nat := #[]
  /-- recursor: number of rules; constructor: number of levels -/
  kD : Array Nat := #[]
  /-- recursor: bit 1 K, bit 2 structure η -/
  kE : Array Nat := #[]
  kInfo : Array G3Info := #[]
  nids : Std.HashMap Name Nat := {}
  /-- the erasure mask of each constant applied (§ erasure) -/
  masks : Std.HashMap Name (Array Bool) := {}
  kMap : Std.HashMap (Name × List Level) Nat := {}
  rules : Array G3Rule := #[]
  ruleCode : Array Nat := #[]
  /-- per rule: the constructor's name id, fields, parameters, case 3 -/
  rNid : Array Nat := #[]
  rNF : Array Nat := #[]
  rCP : Array Nat := #[]
  rC3 : Array Nat := #[]
  projs : Array G3Proj := #[]
  /-- per projection: constructor name id, index, parameters, fields,
  levels, always-fires -/
  pNid : Array Nat := #[]
  pIdx : Array Nat := #[]
  pNP : Array Nat := #[]
  pNF : Array Nat := #[]
  pNl : Array Nat := #[]
  pAlw : Array Nat := #[]
  strs : Array String := #[]
  nslots : Nat := 1
  natOk : Bool := false
  strOk : Bool := false
  kTrue : Nat := 0
  kFalse : Nat := 0
  kZero : Nat := 0
  kSucc : Nat := 0
  deriving Inhabited

/-- Append to the code in place (the array is detached from the record
first, so it is unshared when pushed). -/
@[inline] def G3Prog.emit (P : G3Prog) (f : Array Nat → Array Nat) : G3Prog :=
  let c := P.code; let P := { P with code := #[] }; { P with code := f c }

/-- The id of a name (constructor matching by `Nat` comparison). -/
def G3Prog.nid (P : G3Prog) (c : Name) : Nat × G3Prog :=
  match P.nids[c]? with
  | some i => (i, P)
  | none =>
    let m := P.nids; let i := m.size
    let P := { P with nids := {} }
    (i, { P with nids := m.insert c i })

/-- `natOpResult` by operation index (the order of `natBin14Names`):
`0` a literal result, `1` a `Bool` result (`0`/`1`), `2` no result
(`Nat.pow` beyond official's exponent bound). -/
@[inline] def g3NatKind (op b : Nat) : Nat :=
  if op == 4 || op == 5 then 1 else if op == 3 && b > 16777216 then 2 else 0

def g3NatVal (op a b : Nat) : Nat :=
  match op with
  | 0 => a + b | 1 => a - b | 2 => a * b | 3 => a ^ b
  | 4 => if a == b then 1 else 0 | 5 => if a ≤ b then 1 else 0
  | 6 => a / b | 7 => a % b | 8 => Nat.gcd a b | 9 => Nat.land a b | 10 => Nat.lor a b
  | 11 => Nat.xor a b | 12 => Nat.shiftLeft a b | 13 => Nat.shiftRight a b | _ => 0

/-- Strip the Π-binders of a type. -/
def g3PiBody : Expr → Expr
  | .forallE _ b => g3PiBody b
  | e => e

/-- **Erasure** (task #423 round 3): the argument positions of a constant
whose argument is never scrutinised by the machine — a type former (the
domain is, after its Π-binders, a sort: types, motives) and, except at a
recursor, a proof (the domain's head constant's type ends in `Prop`).
Such an argument is bound to the neutral cell and never compiled. -/
def g3Mask (find? : Name → Option ConstantInfo) (isRec : Bool) : Expr → Array Bool → Array Bool
  | .forallE d b, acc =>
    let tf := match g3PiBody d with | .sort _ => true | _ => false
    let pf := !isRec && (match (g3PiBody d).getAppFn with
      | .const c _ => match find? c with
        | some ci => (match g3PiBody ci.toConstantVal.type with
          | .sort .zero => true | _ => false)
        | none => false
      | _ => false)
    g3Mask find? isRec b (acc.push (tf || pf))
  | _, acc => acc

/-- The number of leading Π-binders of a type. -/
def g3Pis : Expr → Nat → Nat
  | .forallE _ b, n => g3Pis b (n + 1)
  | _, n => n

/-- The erasure switch (task #423 round 3 probe). -/
@[noinline] def g3Erase : Bool := true

section
variable (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)

/-- The table entry of the constant `c` at levels `us`, created on first
use.  Kinds: `0` definition, `1` constructor, `2` recursor, `3` an
accelerated `Nat` operation (a definition too), `4` a well-founded
`Nat` operation (a definition too), `5` neutral. -/
def g3Resolve (P : G3Prog) (c : Name) (us : List Level) : Nat × G3Prog :=
  match P.kMap[(c, us)]? with
  | some k => (k, P)
  | none =>
    let k := P.kTag.size
    let (tag, ar, b, c', d, e', info, P) : Nat × Nat × Nat × Nat × Nat × Nat × G3Info × G3Prog :=
      match find? c with
      | some (.defnInfo cv v _) =>
        if us.length != cv.levelParams.length then (5, 0, 0, 0, 0, 0, .neutral, P)
        else
          let tag := if us.isEmpty && P.natOk && natBin14 c then 3
            else if us.isEmpty && natOpWfNames.contains c then 4 else 0
          let op := (natBin14Names.idxOf? c).getD 0
          (tag, 0, 0, 0, 0, op, .defn c cv.levelParams us v, P)
      | some (.ctorInfo cv nP nF) =>
        let (ni, P) := P.nid c
        (1, g3Pis cv.type 0, ni, 0, us.length, 0, .ctor c us nP nF, P)
      | some (.recInfo cv mI rP rules) =>
        if us.length != cv.levelParams.length || !(Expr.peelPis (mI + 1) cv.type).isSome then
          (5, 0, 0, 0, 0, 0, .neutral, P)
        else
          let base := P.rules.size
          let P := rules.foldl (fun P rl =>
            let case3 := match find? rl.ctor with
              | some (.ctorInfo cvj _ _) =>
                iotaCase3 find? rl cvj (gCmpLevels rl cv.levelParams us cvj.levelParams)
              | _ => true
            let (ni, P) := P.nid rl.ctor
            let (r1, r2, r3, r4, r5, r6) := (P.rules, P.ruleCode, P.rNid, P.rNF, P.rCP, P.rC3)
            let P := { P with rules := #[], ruleCode := #[], rNid := #[], rNF := #[], rCP := #[],
                              rC3 := #[] }
            { P with rules := r1.push ⟨rl.ctor, rl.nfields, rl.ctorParams, case3, rl.rhs⟩,
                     ruleCode := r2.push 0, rNid := r3.push ni, rNF := r4.push rl.nfields,
                     rCP := r5.push rl.ctorParams, rC3 := r6.push (if case3 then 1 else 0) }) P
          let isEta := match rules with | [rl] => rl.eta | _ => false
          let fl := (if recRuleK rules then 1 else 0) + (if isEta then 2 else 0)
          (2, mI, rP, base, rules.length, fl,
            .recr cv.levelParams us mI rP base rules.length (recRuleK rules) isEta, P)
      | _ => (5, 0, 0, 0, 0, 0, .neutral, P)
    let (t1, t2, t3, t4, t5, t6, ns) := (P.kTag, P.kCode, P.kArity, P.kSlot, P.kInfo, P.kMap, P.nslots)
    let (u1, u2, u3, u4) := (P.kB, P.kC, P.kD, P.kE)
    let P := { P with kTag := #[], kCode := #[], kArity := #[], kSlot := #[], kInfo := #[], kMap := {},
                      kB := #[], kC := #[], kD := #[], kE := #[] }
    (k, { P with kTag := t1.push tag, kCode := t2.push 0, kArity := t3.push ar,
                 kSlot := t4.push ns, nslots := ns + 1,
                 kInfo := t5.push info, kMap := t6.insert (c, us) k,
                 kB := u1.push b, kC := u2.push c', kD := u3.push d, kE := u4.push e' })

mutual
/-- Compile `e` (closed under the binders the code will be run under);
the result is the node's offset.  Code tags: `0` bvar `[0, i]`, `1`
spine `[1, head, n, a₁ … aₙ]`, `2` λ `[2, body]`, `3` let `[3, v, body]`,
`4` constant `[4, entry]`, `5` `Nat` literal `[5, n]`, `6` string `[6,
s]`, `7` projection `[7, proj + 1 or 0, e]`, `8` neutral `[8]`, `9`
shared closed argument `[9, slot, e]`. -/
def g3Comp : Nat → G3Prog → Expr → Nat × G3Prog
  | 0, P, _ => let o := P.code.size; (o, P.emit (fun c => c.push 8))
  | f + 1, P, e =>
    match e with
    | .bvar i => let o := P.code.size; (o, P.emit (fun c => (c.push 0).push i))
    | .lam _ b =>
      -- `[2, body, n, inner]`: `n` the λ-telescope's length from here,
      -- `inner` the innermost body (all of them bound in one step)
      let (bo, P) := g3Comp f P b
      let (tn, inner) := if P.code[bo]! == 2 then (P.code[bo + 2]! + 1, P.code[bo + 3]!) else (1, bo)
      let o := P.code.size; (o, P.emit (fun c => (((c.push 2).push bo).push tn).push inner))
    | .letE _ v b =>
      let (vo, P) := g3CompArg f P v
      let (bo, P) := g3Comp f P b
      let o := P.code.size; (o, P.emit (fun c => ((c.push 3).push vo).push bo))
    | .const c us =>
      let (k, P) := g3Resolve find? P c us
      let o := P.code.size; (o, P.emit (fun c => (c.push 4).push k))
    | .lit (.natVal n) => let o := P.code.size; (o, P.emit (fun c => (c.push 5).push n))
    | .lit (.strVal s) =>
      let o := P.code.size
      let si := P.strs.size
      let P := P.emit (fun c => (c.push 6).push si)
      let ss := P.strs; let P := { P with strs := #[] }
      (o, { P with strs := ss.push s })
    | .proj sn i s =>
      let (so, P) := g3Comp f P s
      let (pi, P) := match findProj? sn i with
        | some en =>
          let pj : G3Proj := ⟨en.ctor, i, en.numParams, en.numFields, en.levelParams.length,
             !(Level.isEquiv en.structSort .zero == some true), en⟩
          let (ni, P) := P.nid en.ctor
          let (q1, q2, q3, q4, q5, q6, q7) := (P.projs, P.pNid, P.pIdx, P.pNP, P.pNF, P.pNl, P.pAlw)
          let P := { P with projs := #[], pNid := #[], pIdx := #[], pNP := #[], pNF := #[],
                            pNl := #[], pAlw := #[] }
          let P := { P with projs := q1.push pj, pNid := q2.push ni, pIdx := q3.push i }
          let P := { P with pNP := q4.push en.numParams, pNF := q5.push en.numFields }
          let P := { P with pNl := q6.push en.levelParams.length,
                            pAlw := q7.push (if pj.always then 1 else 0) }
          (q1.size + 1, P)
        | none => (0, P)
      let o := P.code.size; (o, P.emit (fun c => ((c.push 7).push pi).push so))
    | .app .. =>
      let (hd, args) := (e.getAppFn, e.getAppArgs)
      let (mask, P) : Array Bool × G3Prog := match hd with
        | .const c _ =>
          match P.masks[c]? with
          | some m => (m, P)
          | none =>
            let m := match find? c with
              | some ci => g3Mask find? (match ci with | .recInfo .. => true | _ => false)
                  ci.toConstantVal.type #[]
              | none => #[]
            let ms := P.masks; let P := { P with masks := {} }
            (m, { P with masks := ms.insert c m })
        | _ => (#[], P)
      let (ho, P) := g3Comp f P hd
      let (aos, P) := args.foldl (fun (acc : Array Nat × G3Prog) a =>
        if g3Erase && mask.getD acc.1.size false then
          let o := acc.2.code.size; (acc.1.push o, acc.2.emit (fun c => c.push 8))
        else
        let (ao, P) := g3CompArg f acc.2 a; (acc.1.push ao, P)) (#[], P)
      let o := P.code.size
      (o, P.emit (fun c => aos.foldl (fun c a => c.push a) (((c.push 1).push ho).push aos.size)))
    | .sort _ | .forallE .. | .fvar .. => let o := P.code.size; (o, P.emit (fun c => c.push 8))

/-- An argument position: a closed application, `let` or projection
gets a sharing slot. -/
def g3CompArg : Nat → G3Prog → Expr → Nat × G3Prog
  | 0, P, _ => let o := P.code.size; (o, P.emit (fun c => c.push 8))
  | f + 1, P, a =>
    match a with
    | .app .. | .letE .. | .proj .. =>
      let (ao, P) := g3Comp f P a
      if a.bvarBRaw == 0 then
        let o := P.code.size
        let ns := P.nslots
        (o, { P.emit (fun c => ((c.push 9).push ns).push ao) with nslots := ns + 1 })
      else (ao, P)
    | _ => g3Comp f P a
end
end

/-- The compiler's recursion budget (a termination device, as
`checkFuel`). -/
@[irreducible, noinline] def g3CompFuel : Nat := 4611686018427387904  -- 2^62

/-! ## Flat-state helpers (each returns one array: no tuple per call) -/

@[inline] def g3EnvGet (ev : Array Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | e + 1, 0 => ev[e + e]!
  | e + 1, i + 1 => g3EnvGet ev ev[e + e + 1]! i

/-- `4 n` and `16 n + t` by additions (`Nat.mul`'s overflow check is a
division; `<<<` is out of line). -/
@[inline] def g3X4 (n : Nat) : Nat := let d := n + n; d + d
@[inline] def g3Tag (c t : Nat) : Nat := let d := g3X4 c; let e := g3X4 d; e + t

/-- Bind the top `k` argument frames (the first argument first) as
environment records over `env`; the new environment is the last record.
The frames are not popped. -/
def g3BindFrames (fs : Array Nat) (ev : Array Nat) : Nat → Nat → Nat → Array Nat
  | 0, _, _ => ev
  | k + 1, j, env =>
    let e' := (ev.size >>> 1) + 1
    g3BindFrames fs ((ev.push (fs[fs.size - 1 - j]! >>> 4)).push env) k (j + 1) e'

/-- Bind `argA[start, start + k)` (in order) over `env`. -/
def g3BindSpan (argA : Array Nat) (start : Nat) (ev : Array Nat) : Nat → Nat → Nat → Array Nat
  | 0, _, _ => ev
  | k + 1, j, env =>
    let e' := (ev.size >>> 1) + 1
    g3BindSpan argA start ((ev.push argA[start + j]!).push env) k (j + 1) e'

/-- The body of the `k`-th nested λ from node `p`. -/
def g3LamWalk (code : Array Nat) : Nat → Nat → Nat
  | 0, p => p
  | k + 1, p => g3LamWalk code k code[p + 1]!

/-- The number of argument frames on top of the stack. -/
def g3CountArgs (fs : Array Nat) : Nat → Nat → Nat
  | 0, n => n
  | top + 1, n =>
    if fs[top]! &&& 15 == 1 then g3CountArgs fs top (n + 1) else n

/-- The `j`-th argument cell from the top. -/
@[inline] def g3ArgAt (fs : Array Nat) (j : Nat) : Nat := fs[fs.size - 1 - j]! >>> 4

/-- Append the top `n` argument cells, first argument first. -/
def g3CopyArgs (fs : Array Nat) (argA : Array Nat) : Nat → Nat → Array Nat
  | 0, _ => argA
  | n + 1, j => g3CopyArgs fs (argA.push (g3ArgAt fs j)) n (j + 1)

/-- Append `argA[start, start + len)` to itself. -/
def g3CopyFrom (argA : Array Nat) (start : Nat) : Nat → Nat → Array Nat
  | 0, _ => argA
  | n + 1, j => g3CopyFrom (argA.push argA[start + j]!) start n (j + 1)

/-- Extend with zeros to `n` entries, in place. -/
def g3Grow (a : Array Nat) (n : Nat) : Array Nat :=
  if a.size < n then g3GrowGo a (n - a.size) else a
where g3GrowGo (a : Array Nat) : Nat → Array Nat
  | 0 => a
  | k + 1 => g3GrowGo (a.push 0) k

@[inline] def g3SlotGet (slots : Array Nat) (s : Nat) : Nat :=
  if s < slots.size then slots[s]! else 0

def g3SlotSet (slots : Array Nat) (s c : Nat) : Array Nat :=
  if s < slots.size then slots.set! s c
  else (g3Grow slots (max (s + 1) (2 * slots.size))).set! s c

def g3PopN (fs : Array Nat) : Nat → Array Nat
  | 0 => fs
  | n + 1 => g3PopN fs.pop n

/-- Push `argA[start, start + len)` as argument frames, the first on
top. -/
def g3PushArgs (argA : Array Nat) (start : Nat) (fs : Array Nat) : Nat → Array Nat
  | 0 => fs
  | len + 1 => g3PushArgs argA start (fs.push (g3Tag argA[start + len]! 1)) len

/-- A hash finalizer for slot selection (the low bits of `mixHash` over
small integers cluster). -/
@[inline] def g3Slot (h : UInt64) (size : Nat) : Nat :=
  (((h * 0x9E3779B97F4A7C15) >>> 29) % size.toUInt64).toNat

/-- The memo key's hash. -/
def g3Hash (fs : Array Nat) (k : Nat) : Nat → Nat → UInt64 → UInt64
  | 0, _, h => h
  | n + 1, j, h => g3Hash fs k n (j + 1) (mixHash h (g3ArgAt fs j).toUInt64)

/-- Does the memo record's key span equal the top `n` arguments? -/
def g3SpanEq (fs argA : Array Nat) (start : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, j => argA[start + j]! == g3ArgAt fs j && g3SpanEq fs argA start n (j + 1)

/-- Probe the open-addressing memo table `mT` (a power-of-two size;
`0` empty, `r + 1` record `r` of `mem`, stride 4 `[entry, argStart,
argLen, cell]`) for the entry `k` and the top `n` arguments; the
result cell, or `0`. -/
def g3MemoFind (mem mT fs argA : Array Nat) (k n : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, i =>
    let r := mT[i]!
    if r == 0 then 0 else
    let b := g3X4 (r - 1)
    if mem[b]! == k && mem[b + 2]! == n && g3SpanEq fs argA mem[b + 1]! n 0 then mem[b + 3]!
    else g3MemoFind mem mT fs argA k n f ((i + 1) % mT.size)

/-- The hash of a record's key, from its span. -/
def g3HashSpan (argA : Array Nat) (start : Nat) : Nat → Nat → UInt64 → UInt64
  | 0, _, h => h
  | n + 1, j, h => g3HashSpan argA start n (j + 1) (mixHash h argA[start + j]!.toUInt64)

/-- Put record `r` at the first empty slot from `i`. -/
def g3Place (mT : Array Nat) (r : Nat) : Nat → Nat → Array Nat
  | 0, _ => mT
  | f + 1, i => if mT[i]! == 0 then mT.set! i (r + 1) else g3Place mT r f ((i + 1) % mT.size)

/-- Re-insert records `0 … n-1` into a table of the given size. -/
def g3Rehash (mem argA : Array Nat) (mT : Array Nat) : Nat → Nat → Array Nat
  | 0, _ => mT
  | f + 1, r =>
    let b := g3X4 r
    let h := g3HashSpan argA mem[b + 1]! mem[b + 2]! 0 (UInt64.ofNat mem[b]!)
    g3Rehash mem argA (g3Place mT r mT.size (g3Slot h mT.size)) f (r + 1)

/-- Insert record `r` (already in `mem`) under hash `h`, growing the
table to keep it at most half full. -/
def g3MemoIns (mem argA mT : Array Nat) (r : Nat) (h : UInt64) : Array Nat :=
  let mT := if 2 * (r + 1) > mT.size then
      g3Rehash mem argA (Array.replicate (2 * mT.size) 0) r 0 else mT
  g3Place mT r mT.size (g3Slot h mT.size)

/-- The rule of constructor name id `c` among `n` rules from `i`; the
index past the rules if none. -/
def g3FindRule (rNid : Array Nat) (c : Nat) : Nat → Nat → Nat
  | 0, i => i
  | n + 1, i => if rNid[i]! == c then i else g3FindRule rNid c n (i + 1)

/-- The application memo switch (task #423 probe): `0` none, `1`
recursor applications only, `2` recursors and definitions. -/
@[noinline] def g3Memo : Nat := 2

section
variable (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)

/-- The machine's outcome: a value (with the value array to read it),
or an abort; the constant dispatches and the fuel left. -/
inductive G3Out where
  | done (v : Nat) (val : Array Nat) (P : G3Prog) (steps left : Nat)
  | abort (why : String) (steps : Nat)

/-- **The machine.**  Modes: `0` evaluate node `pc` under `env`, `1`
return value `x`, `2` enter cell `x`, `3` dispatch constant entry `x` (`pc = 1`: as a plain definition),
`4` push the arguments of spine `pc` from the `x`-th down. -/
def g3Run : Nat → G3Prog → (cel val ev fs argA slots mem mH : Array Nat) →
    (mode pc env x st : Nat) → G3Out
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, st => .abort "fuel" st
  | n + 1, P, cel, val, ev, fs, argA, slots, mem, mH, mode, pc, env, x, st =>
    match mode with
    | 0 => -- evaluate
      match P.code[pc]! with
      | 0 => g3Run n P cel val ev fs argA slots mem mH 2 0 0 (g3EnvGet ev env P.code[pc + 1]!) st
      | 1 => g3Run n P cel val ev fs argA slots mem mH 4 pc env P.code[pc + 2]! st
      | 2 =>
        if fs.size > 0 && fs[fs.size - 1]! &&& 15 == 1 then
          -- a known call: bind as many arguments as the telescope has, at once
          let na := g3CountArgs fs fs.size 0
          let tn := P.code[pc + 2]!
          let k := if na < tn then na else tn
          let body := if k == tn then P.code[pc + 3]! else g3LamWalk P.code k pc
          let ev := g3BindFrames fs ev k 0 env
          let e' := ev.size >>> 1
          g3Run n P cel val ev (g3PopN fs k) argA slots mem mH 0 body e' 0 st
        else
          let v := (val.size >>> 2)
          g3Run n P cel ((((val.push 0).push pc).push env).push 0) ev fs argA slots mem mH 1 0 0 v st
      | 3 =>
        -- `let`: the value as an argument cell, then the body
        let vo := P.code[pc + 1]!
        let c := (cel.size >>> 2)
        let e' := (ev.size >>> 1) + 1
        g3Run n P ((((cel.push 0).push vo).push env).push 0) val ((ev.push c).push env) fs argA slots mem mH
          0 P.code[pc + 2]! e' 0 st
      | 4 => g3Run n P cel val ev fs argA slots mem mH 3 0 0 P.code[pc + 1]! (st + 1)
      | 5 =>
        let v := (val.size >>> 2)
        g3Run n P cel ((((val.push 2).push P.code[pc + 1]!).push 0).push 0) ev fs argA slots mem mH
          1 0 0 v st
      | 6 =>
        let v := (val.size >>> 2)
        g3Run n P cel ((((val.push 3).push P.code[pc + 1]!).push 0).push 0) ev fs argA slots mem mH
          1 0 0 v st
      | 7 => g3Run n P cel val ev ((fs.push P.code[pc + 1]!).push 4) argA slots mem mH 0
          P.code[pc + 2]! env 0 st
      | 9 => -- a shared closed term at the head: its slot's cell
        let s := P.code[pc + 1]!
        let c := g3SlotGet slots s
        if c != 0 then g3Run n P cel val ev fs argA slots mem mH 2 0 0 c st
        else
          let c := (cel.size >>> 2)
          g3Run n P ((((cel.push 0).push P.code[pc + 2]!).push 0).push 0) val ev fs argA (g3SlotSet slots s c)
            mem mH 2 0 0 c st
      | _ => g3Run n P cel val ev fs argA slots mem mH 1 0 0 0 st
    | 4 => -- push the spine's arguments, the last first
      match x with
      | 0 => g3Run n P cel val ev fs argA slots mem mH 0 P.code[pc + 1]! env 0 st
      | j + 1 =>
        let ao := P.code[pc + 3 + j]!
        match P.code[ao]! with
        | 0 =>
          g3Run n P cel val ev (fs.push (g3Tag (g3EnvGet ev env P.code[ao + 1]!) 1)) argA slots mem mH
            4 pc env j st
        | 2 =>
          let v := (val.size >>> 2)
          let c := (cel.size >>> 2)
          g3Run n P ((((cel.push (v + 2)).push ao).push env).push 0)
            ((((val.push 0).push ao).push env).push 0) ev (fs.push (g3Tag c 1)) argA slots mem mH
            4 pc env j st
        | 5 =>
          let v := (val.size >>> 2)
          let c := (cel.size >>> 2)
          g3Run n P ((((cel.push (v + 2)).push ao).push 0).push 0)
            ((((val.push 2).push P.code[ao + 1]!).push 0).push 0) ev (fs.push (g3Tag c 1)) argA
            slots mem mH 4 pc env j st
        | 8 => g3Run n P cel val ev (fs.push 1) argA slots mem mH 4 pc env j st
        | 4 => -- a constant: its entry's shared cell
          let s := P.kSlot[P.code[ao + 1]!]!
          let c := g3SlotGet slots s
          if c != 0 then
            g3Run n P cel val ev (fs.push (g3Tag c 1)) argA slots mem mH 4 pc env j st
          else
            let c := (cel.size >>> 2)
            g3Run n P ((((cel.push 0).push ao).push 0).push 0) val ev (fs.push (g3Tag c 1)) argA
              (g3SlotSet slots s c) mem mH 4 pc env j st
        | 9 =>
          let s := P.code[ao + 1]!
          let c := g3SlotGet slots s
          if c != 0 then
            g3Run n P cel val ev (fs.push (g3Tag c 1)) argA slots mem mH 4 pc env j st
          else
            let c := (cel.size >>> 2)
            g3Run n P ((((cel.push 0).push P.code[ao + 2]!).push 0).push 0) val ev (fs.push (g3Tag c 1)) argA
              (g3SlotSet slots s c) mem mH 4 pc env j st
        | _ =>
          let c := (cel.size >>> 2)
          g3Run n P ((((cel.push 0).push ao).push env).push 0) val ev (fs.push (g3Tag c 1)) argA slots mem mH
            4 pc env j st
    | 2 => -- enter a cell
      let s := cel[g3X4 x]!
      if s ≥ 2 then g3Run n P cel val ev fs argA slots mem mH 1 0 0 (s - 2) st
      else if s == 0 then
        let co := cel[g3X4 x + 1]!
        let ce := cel[g3X4 x + 2]!
        g3Run n P (cel.set! (g3X4 x) 1) val ev (fs.push (g3Tag x 2)) argA slots mem mH 0 co ce 0 st
      else .abort "black hole" st
    | 3 => -- dispatch a constant
      let k := x
      -- `pc = 1`: a plain δ (an accelerated operation whose argument read no literal)
      match (if pc == 1 then 0 else P.kTag[k]!) with
      | 1 =>
        let na := g3CountArgs fs fs.size 0
        let start := argA.size
        let v := (val.size >>> 2)
        let argA := g3CopyArgs fs argA na 0
        g3Run n P cel ((((val.push 1).push k).push start).push na) ev (g3PopN fs na)
          argA slots mem mH 1 0 0 v st
      | 2 =>
          let mI := P.kArity[k]!
          let na := g3CountArgs fs fs.size 0
          if na < mI + 1 then
            let start := argA.size
            let v := (val.size >>> 2)
            let argA := g3CopyArgs fs argA na 0
            g3Run n P cel ((((val.push 4).push k).push start).push na) ev (g3PopN fs na)
              argA slots mem mH 1 0 0 v st
          else
            let h := g3Hash fs k (mI + 1) 0 (UInt64.ofNat k)
            let hit := if g3Memo ≥ 1 then
                g3MemoFind mem mH fs argA k (mI + 1) mH.size (g3Slot h mH.size) else 0
            if hit != 0 then
              g3Run n P cel val ev (g3PopN fs (mI + 1)) argA slots mem mH 2 0 0 hit st
            else
              let start := argA.size
              let argA := g3CopyArgs fs argA (mI + 1) 0
              let fs := g3PopN fs (mI + 1)
              let r := (cel.size >>> 2)
              let maj := argA[start + mI]!
              let rr := (mem.size >>> 2)
              let mem := if g3Memo ≥ 1 then (((mem.push k).push start).push (mI + 1)).push r else mem
              let mH := if g3Memo ≥ 1 then g3MemoIns mem argA mH rr h else mH
              g3Run n P ((((cel.push 1).push 0).push 0).push 0) val ev
                (((((fs.push (g3Tag r 2)).push k).push start).push (mI + 1)).push 3) argA slots
                mem mH 2 0 0 maj st
      | 5 =>
        let na := g3CountArgs fs fs.size 0
        g3Run n P cel val ev (g3PopN fs na) argA slots mem mH 1 0 0 0 st
      | t =>
        -- a definition; tags 3 and 4 try literal acceleration first
        let na := g3CountArgs fs fs.size 0
        if (t == 3 || t == 4) && na == 2 then
          let a := g3ArgAt fs 0
          let b := g3ArgAt fs 1
          g3Run n P cel val ev ((((((g3PopN fs 2).push k).push a).push b).push (if t == 3 then 5 else 8)))
            argA slots mem mH 2 0 0 a st
        else if t == 3 && na < 2 then
          let start := argA.size
          let v := (val.size >>> 2)
          let argA := g3CopyArgs fs argA na 0
          g3Run n P cel ((((val.push 4).push k).push start).push na) ev (g3PopN fs na)
            argA slots mem mH 1 0 0 v st
        else
          -- δ: the compiled body (compiled on first use, then the
          -- dispatch is repeated), memoised on the argument cells
          if P.kCode[k]! == 0 then
            match P.kInfo[k]! with
            | .defn _ lps us v =>
              let (o, P) := g3Comp find? findProj? g3CompFuel P (v.instantiateLevelParams lps us)
              let P := let kc := P.kCode; let P := { P with kCode := #[] }
                { P with kCode := kc.set! k (o + 1) }
              g3Run n P cel val ev fs argA slots mem mH 3 pc env k st
            | _ => .abort "defn info" st
          else
          let body := P.kCode[k]! - 1
          if g3Memo ≥ 2 && na > 0 then
            let h := g3Hash fs k na 0 (UInt64.ofNat k)
            let hit := g3MemoFind mem mH fs argA k na mH.size (g3Slot h mH.size)
            if hit != 0 then
              g3Run n P cel val ev (g3PopN fs na) argA slots mem mH 2 0 0 hit st
            else
              let start := argA.size
              let argA := g3CopyArgs fs argA na 0
              let fs := g3PopN fs na
              let r := (cel.size >>> 2)
              let rr := (mem.size >>> 2)
              let mem := (((mem.push k).push start).push na).push r
              let mH := g3MemoIns mem argA mH rr h
              g3Run n P ((((cel.push 1).push 0).push 0).push 0) val ev
                (g3PushArgs argA start (fs.push (g3Tag r 2)) na) argA slots mem mH 0 body 0 0 st
          else g3Run n P cel val ev fs argA slots mem mH 0 body 0 0 st
    | _ => -- return value `x`
      let v := x
      if fs.size == 0 then .done v val P st n else
      match fs[fs.size - 1]! &&& 15 with
      | 2 =>
        let c := fs[fs.size - 1]! >>> 4
        g3Run n P (cel.set! (g3X4 c) (v + 2)) val ev fs.pop argA slots mem mH 1 0 0 v st
      | 1 =>
        let c := fs[fs.size - 1]! >>> 4
        match val[g3X4 v]! with
        | 0 =>
          let _ := c
          let lp := val[g3X4 v + 1]!
          let na := g3CountArgs fs fs.size 0
          let tn := P.code[lp + 2]!
          let k := if na < tn then na else tn
          let body := if k == tn then P.code[lp + 3]! else g3LamWalk P.code k lp
          let ev := g3BindFrames fs ev k 0 val[g3X4 v + 2]!
          let e' := ev.size >>> 1
          g3Run n P cel val ev (g3PopN fs k) argA slots mem mH 0 body e' 0 st
        | 1 =>
          let na := g3CountArgs fs fs.size 0
          let start := argA.size
          let len := val[g3X4 v + 3]!
          let argA := g3CopyArgs fs (g3CopyFrom argA val[g3X4 v + 2]! len 0) na 0
          let w := (val.size >>> 2)
          let kc := val[g3X4 v + 1]!
          g3Run n P cel ((((val.push 1).push kc).push start).push (len + na)) ev
            (g3PopN fs na) argA slots mem mH 1 0 0 w st
        | 4 =>
          g3Run n P cel val ev (g3PushArgs argA val[g3X4 v + 2]! fs val[g3X4 v + 3]!) argA slots mem mH
            3 0 0 val[g3X4 v + 1]! st
        | _ =>
          let na := g3CountArgs fs fs.size 0
          g3Run n P cel val ev (g3PopN fs na) argA slots mem mH 1 0 0 0 st
      | 3 =>
        let _len := fs[fs.size - 2]!
        let start := fs[fs.size - 3]!
        let k := fs[fs.size - 4]!
        match val[g3X4 v]! with
        | 2 =>
          if !P.natOk then .abort "nat literal" st else
          let m := val[g3X4 v + 1]!
          match m with
          | 0 =>
            let w := (val.size >>> 2)
            g3Run n P cel ((((val.push 1).push P.kZero).push 0).push 0) ev fs argA slots mem mH
              1 0 0 w st
          | m + 1 =>
            let c := (cel.size >>> 2)
            let u := (val.size >>> 2)
            let w := u + 1
            let sa := argA.size
            g3Run n P ((((cel.push (u + 2)).push 0).push 0).push 0)
              ((((((((val.push 2).push m).push 0).push 0).push 1).push P.kSucc).push sa).push 1)
              ev fs (argA.push c) slots mem mH 1 0 0 w st
        | 3 =>
          if !P.strOk then .abort "string literal" st else
          let sE := strLitToConstructor P.strs[val[g3X4 v + 1]!]!
          let (o, P) := g3Comp find? findProj? g3CompFuel P sE
          g3Run n P cel val ev fs argA slots mem mH 0 o 0 0 st
        | 1 =>
          let kc := val[g3X4 v + 1]!
          let base := P.kC[k]!
          let nr := P.kD[k]!
          let ri := g3FindRule P.rNid P.kB[kc]! nr base
          if P.kTag[kc]! != 1 || ri == base + nr then .abort "no rule" st else
          let nf := P.rNF[ri]!
          let cp := P.rCP[ri]!
          let ms := val[g3X4 v + 2]!
          if val[g3X4 v + 3]! != cp + nf then .abort "ctor arity" st
          else if P.rC3[ri]! != 0 then .abort "case 3" st
          else if P.ruleCode[ri]! == 0 then
            -- compile the rule's right-hand side, then return again
            match P.kInfo[k]! with
            | .recr lps us _ _ _ _ _ _ =>
              let rhsE := P.rules[ri]!.rhs.instantiateLevelParams lps us
              let (o, P) := g3Comp find? findProj? g3CompFuel P rhsE
              let P := let rc := P.ruleCode; let P := { P with ruleCode := #[] }
                { P with ruleCode := rc.set! ri (o + 1) }
              g3Run n P cel val ev fs argA slots mem mH 1 0 0 v st
            | _ => .abort "iota info" st
          else
            let rhs := P.ruleCode[ri]! - 1
            let rP := P.kB[k]!
            let fs := g3PopN fs 4
            if P.code[rhs]! == 2 && P.code[rhs + 2]! == rP + nf then
              -- the rule's right-hand side binds the leading arguments and
              -- the fields at once: no frame is pushed
              let ev := g3BindSpan argA start ev rP 0 0
              let e1 := ev.size >>> 1
              let ev := g3BindSpan argA (ms + cp) ev nf 0 (if rP == 0 then 0 else e1)
              let e2 := if rP + nf == 0 then 0 else ev.size >>> 1
              g3Run n P cel val ev fs argA slots mem mH 0 P.code[rhs + 3]! e2 0 st
            else
              let fs := g3PushArgs argA (ms + cp) fs nf
              let fs := g3PushArgs argA start fs rP
              g3Run n P cel val ev fs argA slots mem mH 0 rhs 0 0 st
        | 5 =>
          let fl := P.kE[k]!
          if fl % 2 == 1 then .abort "K major" st
          else if fl / 2 % 2 == 1 then .abort "struct-eta major" st
          else g3Run n P cel val ev (g3PopN fs 4) argA slots mem mH 1 0 0 0 st
        | _ => g3Run n P cel val ev (g3PopN fs 4) argA slots mem mH 1 0 0 0 st
      | 4 =>
        let pi := fs[fs.size - 2]!
        let fs := fs.pop.pop
        if pi == 0 then g3Run n P cel val ev fs argA slots mem mH 1 0 0 0 st else
        let q := pi - 1
        match val[g3X4 v]! with
        | 1 =>
          let kc := val[g3X4 v + 1]!
          let len := val[g3X4 v + 3]!
          let np := P.pNP[q]!
          let idx := P.pIdx[q]!
          if P.kTag[kc]! == 1 && P.kB[kc]! == P.pNid[q]! && idx < P.pNF[q]! &&
              len == np + P.pNF[q]! && len ≤ P.kArity[kc]! && P.kD[kc]! == P.pNl[q]! &&
              (P.pAlw[q]! == 1 || (match P.kInfo[kc]! with
                | .ctor _ us _ _ => P.projs[q]!.entry.fireOk us
                | _ => false)) then
            g3Run n P cel val ev fs argA slots mem mH 2 0 0 argA[val[g3X4 v + 2]! + np + idx]! st
          else .abort "proj shape" st
        | 3 =>
          if !P.strOk then .abort "string literal" st else
          let sE := strLitToConstructor P.strs[val[g3X4 v + 1]!]!
          let (o, P) := g3Comp find? findProj? g3CompFuel P sE
          g3Run n P cel val ev ((fs.push pi).push 4) argA slots mem mH 0 o 0 0 st
        | _ => g3Run n P cel val ev fs argA slots mem mH 1 0 0 0 st
      | 7 =>
        match val[g3X4 v]! with
        | 2 =>
          let w := (val.size >>> 2)
          let m := val[g3X4 v + 1]!
          g3Run n P cel ((((val.push 2).push (m + 1)).push 0).push 0) ev fs.pop
            argA slots mem mH 1 0 0 w st
        | 1 =>
          let kc := val[g3X4 v + 1]!
          if kc == P.kZero && val[g3X4 v + 3]! == 0 then
            let w := (val.size >>> 2)
            g3Run n P cel ((((val.push 2).push 1).push 0).push 0) ev fs.pop argA slots mem mH 1 0 0 w st
          else if kc == P.kSucc && val[g3X4 v + 3]! == 1 then
            g3Run n P cel val ev (fs.push 7) argA slots mem mH 2 0 0 argA[val[g3X4 v + 2]!]! st
          else g3Run n P cel val ev fs.pop argA slots mem mH 1 0 0 0 st
        | _ => g3Run n P cel val ev fs.pop argA slots mem mH 1 0 0 0 st
      | t =>
        -- literal acceleration: `[k, a, b, 5|15]` reads the first
        -- argument, `[k, n₁, a, b, 6|16]` the second
        let first := t == 5 || t == 8
        let wf := t == 8 || t == 9
        -- the reading: `0` a literal `m`, `1` a `Nat.succ` of cell `m`, `2` none
        let tg := val[g3X4 v]!
        let kc := val[g3X4 v + 1]!
        let rd : Nat := if tg == 2 then 0
          else if tg == 1 && kc == P.kZero && val[g3X4 v + 3]! == 0 then 0
          else if tg == 1 && kc == P.kSucc && val[g3X4 v + 3]! == 1 then 1 else 2
        let m : Nat := if tg == 2 then kc else if rd == 0 then 0
          else if rd == 1 then argA[val[g3X4 v + 2]!]! else 0
        match rd with
        | 1 => g3Run n P cel val ev (fs.push 7) argA slots mem mH 2 0 0 m st
        | 0 =>
          if first then
            let b := fs[fs.size - 2]!
            let a := fs[fs.size - 3]!
            let k := fs[fs.size - 4]!
            let fs := g3PopN fs 4
            g3Run n P cel val ev (((((fs.push k).push m).push a).push b).push (if wf then 9 else 6))
              argA slots mem mH 2 0 0 b st
          else
            let k := fs[fs.size - 5]!
            let m₁ := fs[fs.size - 4]!
            let fs := g3PopN fs 5
            if wf then .abort "wf nat op" st else
            let op := P.kE[k]!
            match g3NatKind op m with
            | 0 =>
              let w := (val.size >>> 2)
              g3Run n P cel ((((val.push 2).push (g3NatVal op m₁ m)).push 0).push 0) ev fs argA slots
                mem mH 1 0 0 w st
            | 1 =>
              let kb := if g3NatVal op m₁ m == 1 then P.kTrue else P.kFalse
              let w := (val.size >>> 2)
              g3Run n P cel ((((val.push 1).push kb).push 0).push 0) ev fs argA slots mem mH
                1 0 0 w st
            | _ =>
              -- no result (the exponent bound; the incumbent unfolds `Nat.pow`)
              .abort "nat pow bound" st
        | _ =>
          -- no literal: unfold the operation (`reduceNat` fails, δ)
          let k := fs[fs.size - (if first then 4 else 5)]!
          let a := fs[fs.size - 3]!
          let b := fs[fs.size - 2]!
          let fs := g3PopN fs (if first then 4 else 5)
          -- the operation's tag is 3 or 4; dispatch it as a plain definition
          g3Run n P cel val ev
            ((fs.push (g3Tag b 1)).push (g3Tag a 1)) argA slots mem mH 3 1 0 k st
end

end ConLeche.Cached

namespace ConLeche.Cached
open ConLeche

/-- The outcome of a round-3 evaluation at the `Bool.true` comparison,
as `groundBool`'s.  **The compiled program is kept for the declaration** (task #423
round 3): `P₀` is the program the declaration's earlier runs compiled
(empty at the first; `CState.ground3`, flushed with the other
environment-dependent memos).  The result carries the program back. -/
def ground3BoolCore (find? : Name → Option ConstantInfo)
    (findProj? : Name → Nat → Option ProjEntry) (natOk strOk : Bool) (P₀ : G3Prog) (e : Expr) :
    (Option Bool × (Nat × Nat) × String) × G3Prog :=
  let P : G3Prog := if P₀.kTag.size == 0 then
      let P : G3Prog := { natOk := natOk, strOk := strOk }
      let (kT, P) := g3Resolve find? P boolTrueName []
      let (kF, P) := g3Resolve find? P boolFalseName []
      let (kZ, P) := g3Resolve find? P natZeroName []
      let (kS, P) := g3Resolve find? P natSuccName []
      { P with kTrue := kT, kFalse := kF, kZero := kZ, kSucc := kS }
    else P₀
  let (o, P) := g3Comp find? findProj? g3CompFuel P e
  let P₁ := P
  let r : Option Bool × (Nat × Nat) × String × G3Prog :=
    match g3Run find? findProj? groundFuel P #[2, 0, 0, 0] #[5, 0, 0, 0] #[] #[] #[] #[] #[]
      (Array.replicate 1024 0) 0 o 0 0 0 with
  | .done v val P st left =>
    let tr := groundFuel - left
    if val[g3X4 v]! == 1 && val[g3X4 v + 3]! == 0 then
      let k := val[g3X4 v + 1]!
      if k == P.kTrue then (some true, (st, tr), "", P)
      else if k == P.kFalse then (some false, (st, tr), "", P)
      else (none, (st, tr), "not a Bool", P)
    else (none, (st, tr), "not a constructor", P)
  | .abort why st => (none, (st, 0), why, P₁)
  ((r.1, r.2.1, r.2.2.1), r.2.2.2)

def ground3Bool (fe : FEnv) (P₀ : G3Prog) (e : Expr) :
    (Option Bool × (Nat × Nat) × String) × G3Prog :=
  ground3BoolCore fe.find? fe.findProj? (natLitSupportedF fe) (strLitSupportedF fe) P₀ e

/-- **The ground shortcut** (task #423, spike; `groundMode ≠ 0`): a
comparison with `Bool.true` on either side whose other side is closed
evaluates that side on the ground machine: `Bool.true` answers `true`,
`Bool.false` answers `false` (the two constructors are not
definitionally equal), anything else (an abort) leaves the comparison
to the incumbent path (`none`).  Read by `defeqBodyI`
(`ConLeche/Cached/CoreC.lean`). -/
def groundShortcut (mode : CheckMode) (fe : FEnv) (P : G3Prog) (a b : Expr) :
    Option Bool × G3Prog :=
  let t? : Option Expr :=
    if Expr.isBoolTrue b && (mode.eager || !(Expr.hasFvar a)) then some a
    else if Expr.isBoolTrue a && (mode.eager || !(Expr.hasFvar b)) then some b
    else none
  match t? with
  | none => (none, P)
  | some t =>
    if Expr.hasFvar t then (none, P) else
    let eng : G3Prog → Expr → (Option Bool × (Nat × Nat) × String) × G3Prog := fun P t =>
      if groundMode ≥ 7 then ground3Bool fe P t
      else if groundMode ≥ 3 && groundMode != 5 then (ground2Bool fe t, P)
      else (groundBool fe t, P)
    let ((r, steps, why), P) := eng P t
    -- probes 5, 6 and 9: the engine twice (its own cost is the difference)
    let (r, P) := if groundMode == 5 || groundMode == 6 || groundMode == 9 then
        let ((r', _, _), P) := eng P (dbgTrace "" fun _ => t)
        (if r' == r then r else none, P) else (r, P)
    if groundMode == 2 || groundMode == 4 || groundMode == 8 then
      (dbgTrace s!"GROUND {repr r} {steps.1} {steps.2} {why}" fun _ => r, P)
    else (r, P)

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
  have hg3 : ground3Bool fe₁ = ground3Bool fe₂ := by
    funext P e; unfold ground3Bool; rw [hfe, hp, hn, hs]
  funext P a b; unfold groundShortcut; rw [hg, hg2, hg3]

end ConLeche.Cached

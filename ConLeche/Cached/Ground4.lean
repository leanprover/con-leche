module

public import ConLeche.Cached.Ground2
public import ConLeche.Cached.Ground3

@[expose] public section

/-!
# The flat ground machine, round 4 (task #423): strictness, shared closed terms

The machine of `Ground.lean` (round 1) with its state FLAT: no Lean
object is allocated per transition.  Every definition body and rule
right-hand side the site reaches is compiled once per run into a code
array (`Array Nat`, constants resolved to entries of a per-run
constant table, closed argument terms given a sharing slot), and the
machine's state is a handful of `Array Nat`s threaded linearly through
one tail-recursive loop (`g4Run`) and mutated in place:

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
inductive G4Info where
  | defn (name : Name) (lps : List Name) (us : List Level) (v : Expr)
  | ctor (name : Name) (us : List Level) (nP nF : Nat)
  /-- `kEta`: the single rule of a structure-like recursor; `kK`: K -/
  | recr (lps : List Name) (us : List Level) (mI rP ruleBase nRules : Nat) (kK kEta : Bool)
  | neutral
  /-- a typed neutral head (a theorem, an axiom, an inductive type):
  applied, it keeps its argument cells (value tag `6`), so that the K
  step can read the application's declared type (task #423 K) -/
  | head (name : Name) (lps : List Name) (us : List Level)
  deriving Inhabited

/-- A recursor rule of the table. -/
structure G4Rule where
  ctor : Name
  nfields : Nat
  ctorParams : Nat
  case3 : Bool
  rhs : Expr
  deriving Inhabited

/-- A projection of the table (`none`: no projection table, stuck). -/
structure G4Proj where
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
structure G4Prog where
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
  kInfo : Array G4Info := #[]
  nids : Std.HashMap Name Nat := {}
  /-- the erasure mask of each constant applied (§ erasure) -/
  masks : Std.HashMap Name (Array Nat) := {}
  /-- the deferred proof arguments (code `[11, i, node + 1 or 0]`): a
  proof of a K-like family's instance, compiled on first force (§ the K
  step) -/
  defer : Array Expr := #[]
  /-- per definition name: the strict-parameter bitmask and the λ arity
  (§ strictness) -/
  stricts : Std.HashMap Name (Nat × Nat) := {}
  /-- the code node of each closed argument term compiled so far (one
  closed term, one node, one sharing slot) -/
  closedNode : Std.HashMap Expr Nat := {}
  kMap : Std.HashMap (Name × List Level) Nat := {}
  rules : Array G4Rule := #[]
  ruleCode : Array Nat := #[]
  /-- per rule: the constructor's name id, fields, parameters, case 3 -/
  rNid : Array Nat := #[]
  rNF : Array Nat := #[]
  rCP : Array Nat := #[]
  rC3 : Array Nat := #[]
  projs : Array G4Proj := #[]
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
  /-- the sharing slots, kept with the program across the declaration's
  runs; an entry is `epBase + cell`, valid only in the run whose
  `epBase` it carries (no per-run clearing) -/
  slotA : Array Nat := #[]
  epBase : Nat := 0
  natOk : Bool := false
  strOk : Bool := false
  kTrue : Nat := 0
  kFalse : Nat := 0
  kZero : Nat := 0
  kSucc : Nat := 0
  deriving Inhabited

/-- Append to the code in place (the array is detached from the record
first, so it is unshared when pushed). -/
@[inline] def G4Prog.emit (P : G4Prog) (f : Array Nat → Array Nat) : G4Prog :=
  let c := P.code; let P := { P with code := #[] }; { P with code := f c }

/-- The id of a name (constructor matching by `Nat` comparison). -/
def G4Prog.nid (P : G4Prog) (c : Name) : Nat × G4Prog :=
  match P.nids[c]? with
  | some i => (i, P)
  | none =>
    let m := P.nids; let i := m.size
    let P := { P with nids := {} }
    (i, { P with nids := m.insert c i })

/-- `natOpResult` by operation index (the order of `natBin14Names`):
`0` a literal result, `1` a `Bool` result (`0`/`1`), `2` no result
(`Nat.pow` beyond official's exponent bound). -/
@[inline] def g4NatKind (op b : Nat) : Nat :=
  if op == 4 || op == 5 then 1 else if op == 3 && b > 16777216 then 2 else 0

def g4NatVal (op a b : Nat) : Nat :=
  match op with
  | 0 => a + b | 1 => a - b | 2 => a * b | 3 => a ^ b
  | 4 => if a == b then 1 else 0 | 5 => if a ≤ b then 1 else 0
  | 6 => a / b | 7 => a % b | 8 => Nat.gcd a b | 9 => Nat.land a b | 10 => Nat.lor a b
  | 11 => Nat.xor a b | 12 => Nat.shiftLeft a b | 13 => Nat.shiftRight a b | _ => 0

/-- Strip the Π-binders of a type. -/
def g4PiBody : Expr → Expr
  | .forallE _ b => g4PiBody b
  | e => e

/-- Is `c` a K-like inductive family (its recursor carries the K flag)? -/
def g4KLike (find? : Name → Option ConstantInfo) (c : Name) : Bool :=
  match find? c with
  | some (.indInfo ..) => match find? (.str c "rec") with
    | some (.recInfo _ _ _ isK _) => isK
    | _ => false
  | _ => false

/-- **Erasure** (task #423 round 3): the argument positions of a constant
whose argument is never scrutinised by the machine — a type former (the
domain is, after its Π-binders, a sort: types, motives) and, except at a
recursor, a proof (the domain's head constant's type ends in `Prop`).
Such an argument (`1`) is bound to the neutral cell and never compiled.
A proof of a K-like family's instance (`2`, task #423 K) may become a
K major, whose declared type the K step reads: it is kept, as a
deferred node compiled on first force.  `0`: compiled. -/
def g4Mask (find? : Name → Option ConstantInfo) (isRec : Bool) : Expr → Array Nat → Array Nat
  | .forallE d b, acc =>
    let tf := match g4PiBody d with | .sort _ => true | _ => false
    let hd := (g4PiBody d).getAppFn
    let pf := !isRec && (match hd with
      | .const c _ => match find? c with
        | some ci => (match g4PiBody ci.toConstantVal.type with
          | .sort .zero => true | _ => false)
        | none => false
      | _ => false)
    let kf := pf && (match hd with | .const c _ => g4KLike find? c | _ => false)
    g4Mask find? isRec b (acc.push (if tf then 1 else if kf then 2 else if pf then 1 else 0))
  | _, acc => acc

/-- Does `e` (under `d` binders) mention one of the `k` innermost
variables outside it?  (An index's type mentioning an earlier index.) -/
def g4MentionsBelow (k : Nat) : Nat → Expr → Bool
  | d, .bvar i => d ≤ i && i < d + k
  | d, .app f a => g4MentionsBelow k d f || g4MentionsBelow k d a
  | d, .lam t b => g4MentionsBelow k d t || g4MentionsBelow k (d + 1) b
  | d, .forallE t b => g4MentionsBelow k d t || g4MentionsBelow k (d + 1) b
  | d, .letE t v b => g4MentionsBelow k d t || g4MentionsBelow k d v || g4MentionsBelow k (d + 1) b
  | d, .proj _ _ e => g4MentionsBelow k d e
  | _, _ => false

/-- Strip exactly `n` Π-binders (`none`: fewer). -/
def g4StripPis : Nat → Expr → Option Expr
  | 0, e => some e
  | n + 1, .forallE _ b => g4StripPis n b
  | _ + 1, _ => none

/-- The common-type flags of a family's indices (§ the K step): index
`j`'s type mentions no earlier index, so two values of index `j` have
one type, fixed by the parameters. -/
def g4IdxFlags : Nat → Expr → Array Nat → Array Nat
  | j, .forallE d b, acc => g4IdxFlags (j + 1) b (acc.push (if g4MentionsBelow j 0 d then 0 else 1))
  | _, _, acc => acc

/-- **Strictness** (task #423 round 4), exact for direct `.rec` code: a
parameter of a definition is strict if the body (under its λ telescope)
is a recursor application whose major is that parameter, or an
accelerated `Nat` operation whose first operand is (the second is read
only behind a literal).  A saturated call evaluates a strict argument
before the call: it would be forced first anyway.  Result: the bitmask
(bit `p` for the `p`-th parameter) and the telescope's length. -/
def g4Strict (find? : Name → Option ConstantInfo) (v : Expr) : Nat × Nat :=
  let rec peel : Expr → Nat → Expr × Nat
    | .lam _ b, n => peel b (n + 1)
    | e, n => (e, n)
  let (b, n) := peel v 0
  let args := b.getAppArgs.toArray
  let bit (a : Expr) : Nat := match a with
    | .bvar i => if i < n then Nat.shiftLeft 1 (n - 1 - i) else 0
    | _ => 0
  match b.getAppFn with
  | .const r _ =>
    match find? r with
    | some (.recInfo _ mI _ _ _) => (if mI < args.size then bit args[mI]! else 0, n)
    | _ => (if natBin14 r && args.size == 2 then bit args[0]! else 0, n)
  | _ => (0, n)

/-- The number of leading Π-binders of a type. -/
def g4Pis : Expr → Nat → Nat
  | .forallE _ b, n => g4Pis b (n + 1)
  | _, n => n

/-- The strictness switch (task #423 round 4 probe). -/
@[noinline] def g4StrictOn : Bool := true

/-- The erasure switch (task #423 round 3 probe). -/
@[noinline] def g4Erase : Bool := true

section
variable (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)

/-- The table entry of the constant `c` at levels `us`, created on first
use.  Kinds: `0` definition, `1` constructor, `2` recursor, `3` an
accelerated `Nat` operation (a definition too), `4` a well-founded
`Nat` operation (a definition too), `5` neutral, `6` a typed neutral
head (`G4Info.head`; `kArity` its type's Π count, `kCode` its type's
body compiled, on first K use). -/
def g4Resolve (P : G4Prog) (c : Name) (us : List Level) : Nat × G4Prog :=
  match P.kMap[(c, us)]? with
  | some k => (k, P)
  | none =>
    let k := P.kTag.size
    let (tag, ar, b, c', d, e', info, P) : Nat × Nat × Nat × Nat × Nat × Nat × G4Info × G4Prog :=
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
        -- `kE`: the constructor's family has indices (§ the K step)
        let idxd := match cv.type.piResult.getAppFn with
          | .const T _ => match find? T with
            | some (.indInfo _ caps) => if caps.nIdx > 0 then 1 else 0
            | _ => 1
          | _ => 1
        (1, g4Pis cv.type 0, ni, 0, us.length, idxd, .ctor c us nP nF, P)
      | some (.recInfo cv mI rP isK rules) =>
        if us.length != cv.levelParams.length || !(Expr.peelPis (mI + 1) cv.type).isSome then
          (5, 0, 0, 0, 0, 0, .neutral, P)
        else
          let base := P.rules.size
          let P := rules.foldl (fun P rl =>
            let case3 := match find? rl.ctor with
              | some (.ctorInfo cvj _ _) =>
                gCase3 find? isK cvj (gCmpLevels rl cv.levelParams us cvj.levelParams)
              | _ => true
            let (ni, P) := P.nid rl.ctor
            let (r1, r2, r3, r4, r5, r6) := (P.rules, P.ruleCode, P.rNid, P.rNF, P.rCP, P.rC3)
            let P := { P with rules := #[], ruleCode := #[], rNid := #[], rNF := #[], rCP := #[],
                              rC3 := #[] }
            { P with rules := r1.push ⟨rl.ctor, rl.nfields, (gCtorParams find? rl.ctor), case3, rl.rhs⟩,
                     ruleCode := r2.push 0, rNid := r3.push ni, rNF := r4.push rl.nfields,
                     rCP := r5.push (gCtorParams find? rl.ctor), rC3 := r6.push (if case3 then 1 else 0) }) P
          let isEta := match rules with | [_] => !isK | _ => false
          let fl := (if isK then 1 else 0) + (if isEta then 2 else 0)
          (2, mI, rP, base, rules.length, fl,
            .recr cv.levelParams us mI rP base rules.length (isK) isEta, P)
      | some (.thmInfo cv) | some (.axiomInfo cv) | some (.indInfo cv _) =>
        if us.length != cv.levelParams.length then (5, 0, 0, 0, 0, 0, .neutral, P)
        else (6, g4Pis cv.type 0, 0, 0, 0, 0, .head c cv.levelParams us, P)
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
shared closed argument `[9, slot, e]`, `10` strict argument `[10, e]`,
`11` deferred K-like proof `[11, i, e + 1 or 0]` (§ the K step). -/
def g4Comp : Nat → G4Prog → Expr → Nat × G4Prog
  | 0, P, _ => let o := P.code.size; (o, P.emit (fun c => c.push 8))
  | f + 1, P, e =>
    match e with
    | .bvar i => let o := P.code.size; (o, P.emit (fun c => (c.push 0).push i))
    | .lam _ b =>
      -- `[2, body, n, inner]`: `n` the λ-telescope's length from here,
      -- `inner` the innermost body (all of them bound in one step)
      let (bo, P) := g4Comp f P b
      let (tn, inner) := if P.code[bo]! == 2 then (P.code[bo + 2]! + 1, P.code[bo + 3]!) else (1, bo)
      let o := P.code.size; (o, P.emit (fun c => (((c.push 2).push bo).push tn).push inner))
    | .letE _ v b =>
      let (vo, P) := g4CompArg f P v
      let (bo, P) := g4Comp f P b
      let o := P.code.size; (o, P.emit (fun c => ((c.push 3).push vo).push bo))
    | .const c us =>
      let (k, P) := g4Resolve find? P c us
      let o := P.code.size; (o, P.emit (fun c => (c.push 4).push k))
    | .lit (.natVal n) => let o := P.code.size; (o, P.emit (fun c => (c.push 5).push n))
    | .lit (.strVal s) =>
      let o := P.code.size
      let si := P.strs.size
      let P := P.emit (fun c => (c.push 6).push si)
      let ss := P.strs; let P := { P with strs := #[] }
      (o, { P with strs := ss.push s })
    | .proj sn i s =>
      let (so, P) := g4Comp f P s
      let (pi, P) := match findProj? sn i with
        | some en =>
          let pj : G4Proj := ⟨en.ctor, i, en.numParams, en.numFields, en.levelParams.length,
             true, en⟩
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
      let (mask, P) : Array Nat × G4Prog := match hd with
        | .const c _ =>
          match P.masks[c]? with
          | some m => (m, P)
          | none =>
            let m := match find? c with
              | some ci => g4Mask find? (match ci with | .recInfo .. => true | _ => false)
                  ci.toConstantVal.type #[]
              | none => #[]
            let ms := P.masks; let P := { P with masks := {} }
            (m, { P with masks := ms.insert c m })
        | _ => (#[], P)
      let ((smask, sn), P) : (Nat × Nat) × G4Prog := match hd with
        | .const c _ =>
          if !g4StrictOn then ((0, 0), P) else
          match P.stricts[c]? with
          | some r => (r, P)
          | none =>
            let r := match find? c with
              | some (.defnInfo _ v _) => g4Strict find? v
              | _ => (0, 0)
            let ms := P.stricts; let P := { P with stricts := {} }
            (r, { P with stricts := ms.insert c r })
        | _ => ((0, 0), P)
      let smask := if args.length ≥ sn then smask else 0
      let (ho, P) := g4Comp f P hd
      let (aos, P) := args.foldl (fun (acc : Array Nat × G4Prog) a =>
        let mk := if g4Erase then mask.getD acc.1.size 0 else 0
        if mk == 1 then
          let o := acc.2.code.size; (acc.1.push o, acc.2.emit (fun c => c.push 8))
        else if mk == 2 then
          -- a K-like proof: deferred, compiled on first force
          let P := acc.2
          let o := P.code.size
          let di := P.defer.size
          let P := P.emit (fun c => ((c.push 11).push di).push 0)
          let ds := P.defer; let P := { P with defer := #[] }
          (acc.1.push o, { P with defer := ds.push a })
        else
        let (ao, P) := g4CompArg f acc.2 a
        -- a strict argument that would become a thunk: `[10, ao]`, evaluated
        -- before the call
        if Nat.testBit smask acc.1.size && (P.code[ao]! == 1 || P.code[ao]! == 3 ||
            P.code[ao]! == 7) then
          let o := P.code.size; (acc.1.push o, P.emit (fun c => (c.push 10).push ao))
        else (acc.1.push ao, P)) (#[], P)
      let o := P.code.size
      (o, P.emit (fun c => aos.foldl (fun c a => c.push a) (((c.push 1).push ho).push aos.size)))
    | .sort _ | .forallE .. | .fvar .. => let o := P.code.size; (o, P.emit (fun c => c.push 8))

/-- An argument position: a closed application, `let` or projection
gets a sharing slot. -/
def g4CompArg : Nat → G4Prog → Expr → Nat × G4Prog
  | 0, P, _ => let o := P.code.size; (o, P.emit (fun c => c.push 8))
  | f + 1, P, a =>
    match a with
    | .app .. | .letE .. | .proj .. =>
      if a.bvarBRaw == 0 then
        match P.closedNode[a]? with
        | some o => (o, P)
        | none =>
          let (ao, P) := g4Comp f P a
          let o := P.code.size
          let ns := P.nslots
          let P := { P.emit (fun c => ((c.push 9).push ns).push ao) with nslots := ns + 1 }
          let cm := P.closedNode; let P := { P with closedNode := {} }
          (o, { P with closedNode := cm.insert a o })
      else g4Comp f P a
    | _ => g4Comp f P a
end
end

/-- The compiler's recursion budget (a termination device, as
`checkFuel`). -/
@[irreducible, noinline] def g4CompFuel : Nat := 4611686018427387904  -- 2^62

/-! ## Flat-state helpers (each returns one array: no tuple per call) -/

@[inline] def g4EnvGet (ev : Array Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | e + 1, 0 => ev[e + e]!
  | e + 1, i + 1 => g4EnvGet ev ev[e + e + 1]! i

/-- `4 n` and `16 n + t` by additions (`Nat.mul`'s overflow check is a
division; `<<<` is out of line). -/
@[inline] def g4X4 (n : Nat) : Nat := let d := n + n; d + d
@[inline] def g4Tag (c t : Nat) : Nat := let d := g4X4 c; let e := g4X4 d; e + t

/-- Bind the top `k` argument frames (the first argument first) as
environment records over `env`; the new environment is the last record.
The frames are not popped. -/
def g4BindFrames (fs : Array Nat) (ev : Array Nat) : Nat → Nat → Nat → Array Nat
  | 0, _, _ => ev
  | k + 1, j, env =>
    let e' := (ev.size >>> 1) + 1
    g4BindFrames fs ((ev.push (fs[fs.size - 1 - j]! >>> 4)).push env) k (j + 1) e'

/-- Bind `argA[start, start + k)` (in order) over `env`. -/
def g4BindSpan (argA : Array Nat) (start : Nat) (ev : Array Nat) : Nat → Nat → Nat → Array Nat
  | 0, _, _ => ev
  | k + 1, j, env =>
    let e' := (ev.size >>> 1) + 1
    g4BindSpan argA start ((ev.push argA[start + j]!).push env) k (j + 1) e'

/-- The body of the `k`-th nested λ from node `p`. -/
def g4LamWalk (code : Array Nat) : Nat → Nat → Nat
  | 0, p => p
  | k + 1, p => g4LamWalk code k code[p + 1]!

/-- The number of argument frames on top of the stack. -/
def g4CountArgs (fs : Array Nat) : Nat → Nat → Nat
  | 0, n => n
  | top + 1, n =>
    if fs[top]! &&& 15 == 1 then g4CountArgs fs top (n + 1) else n

/-- The `j`-th argument cell from the top. -/
@[inline] def g4ArgAt (fs : Array Nat) (j : Nat) : Nat := fs[fs.size - 1 - j]! >>> 4

/-- Append the top `n` argument cells, first argument first. -/
def g4CopyArgs (fs : Array Nat) (argA : Array Nat) : Nat → Nat → Array Nat
  | 0, _ => argA
  | n + 1, j => g4CopyArgs fs (argA.push (g4ArgAt fs j)) n (j + 1)

/-- Append `argA[start, start + len)` to itself. -/
def g4CopyFrom (argA : Array Nat) (start : Nat) : Nat → Nat → Array Nat
  | 0, _ => argA
  | n + 1, j => g4CopyFrom (argA.push argA[start + j]!) start n (j + 1)

/-- Extend with zeros to `n` entries, in place. -/
def g4Grow (a : Array Nat) (n : Nat) : Array Nat :=
  if a.size < n then g4GrowGo a (n - a.size) else a
where g4GrowGo (a : Array Nat) : Nat → Array Nat
  | 0 => a
  | k + 1 => g4GrowGo (a.push 0) k

/-- One run's epoch step (above every cell index of a run). -/
@[noinline] def g4EpochStep : Nat := 4294967296  -- 2^32

@[inline] def g4SlotGet (slots : Array Nat) (ep s : Nat) : Nat :=
  if s < slots.size then (let w := slots[s]!; if w > ep then w - ep else 0) else 0

def g4SlotSet (slots : Array Nat) (s c : Nat) : Array Nat :=
  if s < slots.size then slots.set! s c
  else (g4Grow slots (max (s + 1) (2 * slots.size))).set! s c

def g4PopN (fs : Array Nat) : Nat → Array Nat
  | 0 => fs
  | n + 1 => g4PopN fs.pop n

/-- Push `argA[start, start + len)` as argument frames, the first on
top. -/
def g4PushArgs (argA : Array Nat) (start : Nat) (fs : Array Nat) : Nat → Array Nat
  | 0 => fs
  | len + 1 => g4PushArgs argA start (fs.push (g4Tag argA[start + len]! 1)) len

/-- A hash finalizer for slot selection (the low bits of `mixHash` over
small integers cluster). -/
@[inline] def g4Slot (h : UInt64) (size : Nat) : Nat :=
  (((h * 0x9E3779B97F4A7C15) >>> 29) % size.toUInt64).toNat

/-- The memo key's hash. -/
def g4Hash (fs : Array Nat) (k : Nat) : Nat → Nat → UInt64 → UInt64
  | 0, _, h => h
  | n + 1, j, h => g4Hash fs k n (j + 1) (mixHash h (g4ArgAt fs j).toUInt64)

/-- Does the memo record's key span equal the top `n` arguments? -/
def g4SpanEq (fs argA : Array Nat) (start : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, j => argA[start + j]! == g4ArgAt fs j && g4SpanEq fs argA start n (j + 1)

/-- Probe the open-addressing memo table `mT` (a power-of-two size;
`0` empty, `r + 1` record `r` of `mem`, stride 4 `[entry, argStart,
argLen, cell]`) for the entry `k` and the top `n` arguments; the
result cell, or `0`. -/
def g4MemoFind (mem mT fs argA : Array Nat) (k n : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, i =>
    let r := mT[i]!
    if r == 0 then 0 else
    let b := g4X4 (r - 1)
    if mem[b]! == k && mem[b + 2]! == n && g4SpanEq fs argA mem[b + 1]! n 0 then mem[b + 3]!
    else g4MemoFind mem mT fs argA k n f ((i + 1) % mT.size)

/-- The hash of a record's key, from its span. -/
def g4HashSpan (argA : Array Nat) (start : Nat) : Nat → Nat → UInt64 → UInt64
  | 0, _, h => h
  | n + 1, j, h => g4HashSpan argA start n (j + 1) (mixHash h argA[start + j]!.toUInt64)

/-- Put record `r` at the first empty slot from `i`. -/
def g4Place (mT : Array Nat) (r : Nat) : Nat → Nat → Array Nat
  | 0, _ => mT
  | f + 1, i => if mT[i]! == 0 then mT.set! i (r + 1) else g4Place mT r f ((i + 1) % mT.size)

/-- Re-insert records `0 … n-1` into a table of the given size. -/
def g4Rehash (mem argA : Array Nat) (mT : Array Nat) : Nat → Nat → Array Nat
  | 0, _ => mT
  | f + 1, r =>
    let b := g4X4 r
    let h := g4HashSpan argA mem[b + 1]! mem[b + 2]! 0 (UInt64.ofNat mem[b]!)
    g4Rehash mem argA (g4Place mT r mT.size (g4Slot h mT.size)) f (r + 1)

/-- Insert record `r` (already in `mem`) under hash `h`, growing the
table to keep it at most half full. -/
def g4MemoIns (mem argA mT : Array Nat) (r : Nat) (h : UInt64) : Array Nat :=
  let mT := if 2 * (r + 1) > mT.size then
      g4Rehash mem argA (Array.replicate (2 * mT.size) 0) r 0 else mT
  g4Place mT r mT.size (g4Slot h mT.size)

/-- The rule of constructor name id `c` among `n` rules from `i`; the
index past the rules if none. -/
def g4FindRule (rNid : Array Nat) (c : Nat) : Nat → Nat → Nat
  | 0, i => i
  | n + 1, i => if rNid[i]! == c then i else g4FindRule rNid c n (i + 1)


/-! ## The K step (task #423 K): a K-like recursor on a typed neutral major

At a K-flagged recursor whose major evaluates to a typed neutral `c a₁ … aₙ`
(value tag `6`: a theorem, an axiom; `n` the Π count of `c`'s type), the
machine evaluates `c`'s declared type's body under the argument cells (the
type's whnf, on the machine), checks that it is the family `T` of the rule's
constructor at a level list of the constructor's length, with the
constructor's parameters and the family's indices, and compares each index
with the constructor's index expression under those parameters (official
`to_cnstr_when_K`'s `is_def_eq(app_type, new_type)`, decided by evaluation).
All equal: the major is the constructor applied to the parameters, and ι
fires.  Different first-order values: official refuses too, abort.  Anything
else (closures over other environments, types, proofs, erased positions):
abort, a completeness gap only.

Frames: `[11]` the type is being evaluated; `[c₁, c₂, common, 12]` compare
two cells; `[ctor entry, argStart, nP, 13]` all compared, fabricate.  Mode
`5` runs the comparisons.  `common`: the two sides have one type, fixed by
the parameters, so a non-indexed constructor's parameters need no
comparison (they are fixed by it; erased ones could not be compared). -/

/-- Fresh thunk cells for the constructor's non-variable index nodes. -/
def g4KCells (code : Array Nat) (e tab nI : Nat) : Nat → Nat → Array Nat → Array Nat
  | 0, _, cel => cel
  | r + 1, j, cel =>
    let node := code[tab + 1 + nI + j]!
    if code[node]! == 0 then g4KCells code e tab nI r (j + 1) cel
    else g4KCells code e tab nI r (j + 1) ((((cel.push 0).push node).push e).push 0)

/-- The comparison frames of the indices: the major's type's index `j`
against the constructor's (a variable: its environment cell; else the
next fresh cell from `c`). -/
def g4KFrames (code ev argA : Array Nat) (e tab nI mS : Nat) : Nat → Nat → Nat → Array Nat → Array Nat
  | 0, _, _, fs => fs
  | r + 1, j, c, fs =>
    let node := code[tab + 1 + nI + j]!
    let isV := code[node]! == 0
    let cC := if isV then g4EnvGet ev e code[node + 1]! else c
    g4KFrames code ev argA e tab nI mS r (j + 1) (if isV then c else c + 1)
      ((((fs.push argA[mS + j]!).push cC).push code[tab + 1 + j]!).push 12)

/-- The comparison frames of two constructor values' arguments from
position `skip` on (the fields have one type each once the parameters
agree). -/
def g4KArgs (argA : Array Nat) (s1 s2 skip : Nat) : Nat → Nat → Array Nat → Array Nat
  | 0, _, fs => fs
  | r + 1, j, fs =>
    if j < skip then g4KArgs argA s1 s2 skip r (j + 1) fs
    else g4KArgs argA s1 s2 skip r (j + 1) ((((fs.push argA[s1 + j]!).push argA[s2 + j]!).push 1).push 12)

/-- Two environments bind the same cells (none of them an erased
position's neutral cell). -/
def g4EnvEq (ev : Array Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | f + 1, e1, e2 =>
    if e1 == e2 then true else if e1 == 0 || e2 == 0 then false else
    let a := e1 - 1; let b := e2 - 1
    let c1 := ev[a + a]!
    c1 == ev[b + b]! && c1 != 0 && g4EnvEq ev f ev[a + a + 1]! ev[b + b + 1]!

/-- Compare two values: `0` equal, `1` different first-order values, `2`
unknown, `3` one constructor at the same levels (compare the arguments),
`4`/`5` a literal `n + 1` (first/second) against `Nat.succ c`. -/
def g4KCmp (P : G4Prog) (val ev : Array Nat) (v1 v2 : Nat) : Nat :=
  let b1 := g4X4 v1; let b2 := g4X4 v2
  let t1 := val[b1]!; let t2 := val[b2]!
  let natCtor (n k len : Nat) : Nat :=
    if n == 0 then (if k == P.kZero && len == 0 then 0 else if k == P.kSucc then 1 else 2)
    else if k == P.kSucc && len == 1 then 4 else if k == P.kZero then 1 else 2
  if t1 == 2 && t2 == 2 then (if val[b1 + 1]! == val[b2 + 1]! then 0 else 1)
  else if t1 == 3 && t2 == 3 then
    (if P.strs[val[b1 + 1]!]! == P.strs[val[b2 + 1]!]! then 0 else 1)
  else if t1 == 1 && t2 == 1 then
    let k1 := val[b1 + 1]!; let k2 := val[b2 + 1]!
    if k1 == k2 && val[b1 + 3]! == val[b2 + 3]! then 3
    else if P.kB[k1]! != P.kB[k2]! then 1 else 2
  else if t1 == 2 && t2 == 1 then natCtor val[b1 + 1]! val[b2 + 1]! val[b2 + 3]!
  else if t1 == 1 && t2 == 2 then
    (match natCtor val[b2 + 1]! val[b1 + 1]! val[b1 + 3]! with | 4 => 5 | r => r)
  else if t1 == 0 && t2 == 0 then
    (if val[b1 + 1]! == val[b2 + 1]! && g4EnvEq ev ev.size val[b1 + 2]! val[b2 + 2]! then 0 else 2)
  else 2

/-- The application memo switch (task #423 probe): `0` none, `1`
recursor applications only, `2` recursors and definitions. -/
@[noinline] def g4Memo : Nat := 2

section
variable (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)

/-- The machine's outcome: a value (with the value array to read it),
or an abort; the constant dispatches and the fuel left. -/
inductive G4Out where
  | done (v : Nat) (val : Array Nat) (P : G4Prog) (slots : Array Nat) (steps left : Nat)
  | abort (why : String) (steps : Nat)

/-- **The machine.**  Modes: `0` evaluate node `pc` under `env`, `1`
return value `x`, `2` enter cell `x`, `3` dispatch constant entry `x` (`pc = 1`: as a plain definition),
`4` push the arguments of spine `pc` from the `x`-th down. -/
def g4Run : Nat → G4Prog → (cel val ev fs argA slots mem mH : Array Nat) →
    (mode pc env x st : Nat) → G4Out
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, st => .abort "fuel" st
  | n + 1, P, cel, val, ev, fs, argA, slots, mem, mH, mode, pc, env, x, st =>
    match mode with
    | 0 => -- evaluate
      match P.code[pc]! with
      | 0 => g4Run n P cel val ev fs argA slots mem mH 2 0 0 (g4EnvGet ev env P.code[pc + 1]!) st
      | 1 => g4Run n P cel val ev fs argA slots mem mH 4 pc env P.code[pc + 2]! st
      | 2 =>
        if fs.size > 0 && fs[fs.size - 1]! &&& 15 == 1 then
          -- a known call: bind as many arguments as the telescope has, at once
          let na := g4CountArgs fs fs.size 0
          let tn := P.code[pc + 2]!
          let k := if na < tn then na else tn
          let body := if k == tn then P.code[pc + 3]! else g4LamWalk P.code k pc
          let ev := g4BindFrames fs ev k 0 env
          let e' := ev.size >>> 1
          g4Run n P cel val ev (g4PopN fs k) argA slots mem mH 0 body e' 0 st
        else
          let v := (val.size >>> 2)
          g4Run n P cel ((((val.push 0).push pc).push env).push 0) ev fs argA slots mem mH 1 0 0 v st
      | 3 =>
        -- `let`: the value as an argument cell, then the body
        let vo := P.code[pc + 1]!
        let c := (cel.size >>> 2)
        let e' := (ev.size >>> 1) + 1
        g4Run n P ((((cel.push 0).push vo).push env).push 0) val ((ev.push c).push env) fs argA slots mem mH
          0 P.code[pc + 2]! e' 0 st
      | 4 => g4Run n P cel val ev fs argA slots mem mH 3 0 0 P.code[pc + 1]! (st + 1)
      | 5 =>
        let v := (val.size >>> 2)
        g4Run n P cel ((((val.push 2).push P.code[pc + 1]!).push 0).push 0) ev fs argA slots mem mH
          1 0 0 v st
      | 6 =>
        let v := (val.size >>> 2)
        g4Run n P cel ((((val.push 3).push P.code[pc + 1]!).push 0).push 0) ev fs argA slots mem mH
          1 0 0 v st
      | 7 => g4Run n P cel val ev ((fs.push P.code[pc + 1]!).push 4) argA slots mem mH 0
          P.code[pc + 2]! env 0 st
      | 9 => -- a shared closed term at the head: its slot's cell
        let s := P.code[pc + 1]!
        let c := g4SlotGet slots P.epBase s
        if c != 0 then g4Run n P cel val ev fs argA slots mem mH 2 0 0 c st
        else
          let c := (cel.size >>> 2)
          g4Run n P ((((cel.push 0).push P.code[pc + 2]!).push 0).push 0) val ev fs argA (g4SlotSet slots s (P.epBase + c))
            mem mH 2 0 0 c st
      | 11 => -- a deferred K-like proof: compiled on first force
        let d := P.code[pc + 2]!
        if d != 0 then g4Run n P cel val ev fs argA slots mem mH 0 (d - 1) env 0 st
        else
          let (o, P) := g4CompArg find? findProj? g4CompFuel P P.defer[P.code[pc + 1]!]!
          let P := P.emit (fun c => c.set! (pc + 2) (o + 1))
          g4Run n P cel val ev fs argA slots mem mH 0 o env 0 st
      | _ => g4Run n P cel val ev fs argA slots mem mH 1 0 0 0 st
    | 5 => -- the K step's comparisons
      let t := fs[fs.size - 1]!
      if t == 13 then
        -- all indices agree: the major is the constructor on the parameters
        let cnP := fs[fs.size - 2]!
        let tvS := fs[fs.size - 3]!
        let kC := fs[fs.size - 4]!
        let fs := g4PopN fs 4
        let w := (val.size >>> 2)
        let r := if groundMode == 11 then dbgTrace "KSTEP" fun _ => w else w
        g4Run n P cel ((((val.push 1).push kC).push tvS).push cnP) ev fs argA slots mem mH 1 0 0 r st
      else if t != 12 then .abort "K frame" st else
      let fl := fs[fs.size - 2]!
      let c2 := fs[fs.size - 3]!
      let c1 := fs[fs.size - 4]!
      if c1 == c2 && c1 != 0 then g4Run n P cel val ev (g4PopN fs 4) argA slots mem mH 5 0 0 0 st else
      let s1 := cel[g4X4 c1]!
      if s1 < 2 then g4Run n P cel val ev fs argA slots mem mH 2 0 0 c1 st else
      let s2 := cel[g4X4 c2]!
      if s2 < 2 then g4Run n P cel val ev fs argA slots mem mH 2 0 0 c2 st else
      let v1 := s1 - 2
      let v2 := s2 - 2
      if v1 == v2 && v1 != 0 then g4Run n P cel val ev (g4PopN fs 4) argA slots mem mH 5 0 0 0 st else
      match g4KCmp P val ev v1 v2 with
      | 0 => g4Run n P cel val ev (g4PopN fs 4) argA slots mem mH 5 0 0 0 st
      | 1 => .abort "K indices differ" st
      | 3 =>
        let kc := val[g4X4 v1 + 1]!
        let nP := match P.kInfo[kc]! with | .ctor _ _ nP _ => nP | _ => 0
        let skip := if fl == 1 && P.kE[kc]! == 0 then nP else 0
        g4Run n P cel val ev
          (g4KArgs argA val[g4X4 v1 + 2]! val[g4X4 v2 + 2]! skip val[g4X4 v1 + 3]! 0 (g4PopN fs 4))
          argA slots mem mH 5 0 0 0 st
      | 4 =>
        let w := (val.size >>> 2)
        let c := (cel.size >>> 2)
        g4Run n P ((((cel.push (w + 2)).push 0).push 0).push 0)
          ((((val.push 2).push (val[g4X4 v1 + 1]! - 1)).push 0).push 0) ev
          (((((g4PopN fs 4).push c).push argA[val[g4X4 v2 + 2]!]!).push 1).push 12) argA slots mem mH
          5 0 0 0 st
      | 5 =>
        let w := (val.size >>> 2)
        let c := (cel.size >>> 2)
        g4Run n P ((((cel.push (w + 2)).push 0).push 0).push 0)
          ((((val.push 2).push (val[g4X4 v2 + 1]! - 1)).push 0).push 0) ev
          (((((g4PopN fs 4).push argA[val[g4X4 v1 + 2]!]!).push c).push 1).push 12) argA slots mem mH
          5 0 0 0 st
      | _ => .abort "K indices unknown" st
    | 4 => -- push the spine's arguments, the last first
      match x with
      | 0 => g4Run n P cel val ev fs argA slots mem mH 0 P.code[pc + 1]! env 0 st
      | j + 1 =>
        let ao := P.code[pc + 3 + j]!
        match P.code[ao]! with
        | 0 =>
          g4Run n P cel val ev (fs.push (g4Tag (g4EnvGet ev env P.code[ao + 1]!) 1)) argA slots mem mH
            4 pc env j st
        | 2 =>
          let v := (val.size >>> 2)
          let c := (cel.size >>> 2)
          g4Run n P ((((cel.push (v + 2)).push ao).push env).push 0)
            ((((val.push 0).push ao).push env).push 0) ev (fs.push (g4Tag c 1)) argA slots mem mH
            4 pc env j st
        | 5 =>
          let v := (val.size >>> 2)
          let c := (cel.size >>> 2)
          g4Run n P ((((cel.push (v + 2)).push ao).push 0).push 0)
            ((((val.push 2).push P.code[ao + 1]!).push 0).push 0) ev (fs.push (g4Tag c 1)) argA
            slots mem mH 4 pc env j st
        | 8 => g4Run n P cel val ev (fs.push 1) argA slots mem mH 4 pc env j st
        | 10 => -- a strict argument: evaluate it now, then continue the spine
          g4Run n P cel val ev ((((fs.push pc).push env).push j).push 10) argA slots mem mH 0
            P.code[ao + 1]! env 0 st
        | 4 => -- a constant: its entry's shared cell
          let s := P.kSlot[P.code[ao + 1]!]!
          let c := g4SlotGet slots P.epBase s
          if c != 0 then
            g4Run n P cel val ev (fs.push (g4Tag c 1)) argA slots mem mH 4 pc env j st
          else
            let c := (cel.size >>> 2)
            g4Run n P ((((cel.push 0).push ao).push 0).push 0) val ev (fs.push (g4Tag c 1)) argA
              (g4SlotSet slots s (P.epBase + c)) mem mH 4 pc env j st
        | 9 =>
          let s := P.code[ao + 1]!
          let c := g4SlotGet slots P.epBase s
          if c != 0 then
            g4Run n P cel val ev (fs.push (g4Tag c 1)) argA slots mem mH 4 pc env j st
          else
            let c := (cel.size >>> 2)
            g4Run n P ((((cel.push 0).push P.code[ao + 2]!).push 0).push 0) val ev (fs.push (g4Tag c 1)) argA
              (g4SlotSet slots s (P.epBase + c)) mem mH 4 pc env j st
        | _ =>
          let c := (cel.size >>> 2)
          g4Run n P ((((cel.push 0).push ao).push env).push 0) val ev (fs.push (g4Tag c 1)) argA slots mem mH
            4 pc env j st
    | 2 => -- enter a cell
      let s := cel[g4X4 x]!
      if s ≥ 2 then g4Run n P cel val ev fs argA slots mem mH 1 0 0 (s - 2) st
      else if s == 0 then
        let co := cel[g4X4 x + 1]!
        let ce := cel[g4X4 x + 2]!
        g4Run n P (cel.set! (g4X4 x) 1) val ev (fs.push (g4Tag x 2)) argA slots mem mH 0 co ce 0 st
      else .abort "black hole" st
    | 3 => -- dispatch a constant
      let k := x
      -- `pc = 1`: a plain δ (an accelerated operation whose argument read no literal)
      match (if pc == 1 then 0 else P.kTag[k]!) with
      | 1 =>
        let na := g4CountArgs fs fs.size 0
        let start := argA.size
        let v := (val.size >>> 2)
        let argA := g4CopyArgs fs argA na 0
        g4Run n P cel ((((val.push 1).push k).push start).push na) ev (g4PopN fs na)
          argA slots mem mH 1 0 0 v st
      | 2 =>
          let mI := P.kArity[k]!
          let na := g4CountArgs fs fs.size 0
          if na < mI + 1 then
            let start := argA.size
            let v := (val.size >>> 2)
            let argA := g4CopyArgs fs argA na 0
            g4Run n P cel ((((val.push 4).push k).push start).push na) ev (g4PopN fs na)
              argA slots mem mH 1 0 0 v st
          else
            let h := g4Hash fs k (mI + 1) 0 (UInt64.ofNat k)
            let hit := if g4Memo ≥ 1 then
                g4MemoFind mem mH fs argA k (mI + 1) mH.size (g4Slot h mH.size) else 0
            if hit != 0 then
              g4Run n P cel val ev (g4PopN fs (mI + 1)) argA slots mem mH 2 0 0 hit st
            else
              let start := argA.size
              let argA := g4CopyArgs fs argA (mI + 1) 0
              let fs := g4PopN fs (mI + 1)
              let r := (cel.size >>> 2)
              let maj := argA[start + mI]!
              let rr := (mem.size >>> 2)
              let mem := if g4Memo ≥ 1 then (((mem.push k).push start).push (mI + 1)).push r else mem
              let mH := if g4Memo ≥ 1 then g4MemoIns mem argA mH rr h else mH
              g4Run n P ((((cel.push 1).push 0).push 0).push 0) val ev
                (((((fs.push (g4Tag r 2)).push k).push start).push (mI + 1)).push 3) argA slots
                mem mH 2 0 0 maj st
      | 5 =>
        let na := g4CountArgs fs fs.size 0
        g4Run n P cel val ev (g4PopN fs na) argA slots mem mH 1 0 0 0 st
      | 6 =>
        -- a typed neutral head: keep the argument cells (§ the K step)
        let na := g4CountArgs fs fs.size 0
        let start := argA.size
        let v := (val.size >>> 2)
        let argA := g4CopyArgs fs argA na 0
        g4Run n P cel ((((val.push 6).push k).push start).push na) ev (g4PopN fs na)
          argA slots mem mH 1 0 0 v st
      | t =>
        -- a definition; tags 3 and 4 try literal acceleration first
        let na := g4CountArgs fs fs.size 0
        if (t == 3 || t == 4) && na == 2 then
          let a := g4ArgAt fs 0
          let b := g4ArgAt fs 1
          g4Run n P cel val ev ((((((g4PopN fs 2).push k).push a).push b).push (if t == 3 then 5 else 8)))
            argA slots mem mH 2 0 0 a st
        else if t == 3 && na < 2 then
          let start := argA.size
          let v := (val.size >>> 2)
          let argA := g4CopyArgs fs argA na 0
          g4Run n P cel ((((val.push 4).push k).push start).push na) ev (g4PopN fs na)
            argA slots mem mH 1 0 0 v st
        else
          -- δ: the compiled body (compiled on first use, then the
          -- dispatch is repeated), memoised on the argument cells
          if P.kCode[k]! == 0 then
            match P.kInfo[k]! with
            | .defn _ lps us v =>
              let (o, P) := g4Comp find? findProj? g4CompFuel P (v.instantiateLevelParams lps us)
              let P := let kc := P.kCode; let P := { P with kCode := #[] }
                { P with kCode := kc.set! k (o + 1) }
              g4Run n P cel val ev fs argA slots mem mH 3 pc env k st
            | _ => .abort "defn info" st
          else
          let body := P.kCode[k]! - 1
          if g4Memo ≥ 2 && na > 0 then
            let h := g4Hash fs k na 0 (UInt64.ofNat k)
            let hit := g4MemoFind mem mH fs argA k na mH.size (g4Slot h mH.size)
            if hit != 0 then
              g4Run n P cel val ev (g4PopN fs na) argA slots mem mH 2 0 0 hit st
            else
              let start := argA.size
              let argA := g4CopyArgs fs argA na 0
              let fs := g4PopN fs na
              let r := (cel.size >>> 2)
              let rr := (mem.size >>> 2)
              let mem := (((mem.push k).push start).push na).push r
              let mH := g4MemoIns mem argA mH rr h
              g4Run n P ((((cel.push 1).push 0).push 0).push 0) val ev
                (g4PushArgs argA start (fs.push (g4Tag r 2)) na) argA slots mem mH 0 body 0 0 st
          else g4Run n P cel val ev fs argA slots mem mH 0 body 0 0 st
    | _ => -- return value `x`
      let v := x
      if fs.size == 0 then .done v val P slots st n else
      match fs[fs.size - 1]! &&& 15 with
      | 2 =>
        let c := fs[fs.size - 1]! >>> 4
        g4Run n P (cel.set! (g4X4 c) (v + 2)) val ev fs.pop argA slots mem mH 1 0 0 v st
      | 1 =>
        let c := fs[fs.size - 1]! >>> 4
        match val[g4X4 v]! with
        | 0 =>
          let _ := c
          let lp := val[g4X4 v + 1]!
          let na := g4CountArgs fs fs.size 0
          let tn := P.code[lp + 2]!
          let k := if na < tn then na else tn
          let body := if k == tn then P.code[lp + 3]! else g4LamWalk P.code k lp
          let ev := g4BindFrames fs ev k 0 val[g4X4 v + 2]!
          let e' := ev.size >>> 1
          g4Run n P cel val ev (g4PopN fs k) argA slots mem mH 0 body e' 0 st
        | 1 =>
          let na := g4CountArgs fs fs.size 0
          let start := argA.size
          let len := val[g4X4 v + 3]!
          let argA := g4CopyArgs fs (g4CopyFrom argA val[g4X4 v + 2]! len 0) na 0
          let w := (val.size >>> 2)
          let kc := val[g4X4 v + 1]!
          g4Run n P cel ((((val.push 1).push kc).push start).push (len + na)) ev
            (g4PopN fs na) argA slots mem mH 1 0 0 w st
        | 4 =>
          g4Run n P cel val ev (g4PushArgs argA val[g4X4 v + 2]! fs val[g4X4 v + 3]!) argA slots mem mH
            3 0 0 val[g4X4 v + 1]! st
        | 6 =>
          let na := g4CountArgs fs fs.size 0
          let start := argA.size
          let len := val[g4X4 v + 3]!
          let argA := g4CopyArgs fs (g4CopyFrom argA val[g4X4 v + 2]! len 0) na 0
          let w := (val.size >>> 2)
          let kc := val[g4X4 v + 1]!
          g4Run n P cel ((((val.push 6).push kc).push start).push (len + na)) ev
            (g4PopN fs na) argA slots mem mH 1 0 0 w st
        | _ =>
          let na := g4CountArgs fs fs.size 0
          g4Run n P cel val ev (g4PopN fs na) argA slots mem mH 1 0 0 0 st
      | 3 =>
        let _len := fs[fs.size - 2]!
        let start := fs[fs.size - 3]!
        let k := fs[fs.size - 4]!
        match val[g4X4 v]! with
        | 2 =>
          if !P.natOk then .abort "nat literal" st else
          let m := val[g4X4 v + 1]!
          match m with
          | 0 =>
            let w := (val.size >>> 2)
            g4Run n P cel ((((val.push 1).push P.kZero).push 0).push 0) ev fs argA slots mem mH
              1 0 0 w st
          | m + 1 =>
            let c := (cel.size >>> 2)
            let u := (val.size >>> 2)
            let w := u + 1
            let sa := argA.size
            g4Run n P ((((cel.push (u + 2)).push 0).push 0).push 0)
              ((((((((val.push 2).push m).push 0).push 0).push 1).push P.kSucc).push sa).push 1)
              ev fs (argA.push c) slots mem mH 1 0 0 w st
        | 3 =>
          if !P.strOk then .abort "string literal" st else
          let sE := strLitToConstructor P.strs[val[g4X4 v + 1]!]!
          let (o, P) := g4Comp find? findProj? g4CompFuel P sE
          g4Run n P cel val ev fs argA slots mem mH 0 o 0 0 st
        | 1 =>
          let kc := val[g4X4 v + 1]!
          let base := P.kC[k]!
          let nr := P.kD[k]!
          let ri := g4FindRule P.rNid P.kB[kc]! nr base
          if P.kTag[kc]! != 1 || ri == base + nr then .abort "no rule" st else
          let nf := P.rNF[ri]!
          let cp := P.rCP[ri]!
          let ms := val[g4X4 v + 2]!
          if val[g4X4 v + 3]! != cp + nf then .abort "ctor arity" st
          else if P.rC3[ri]! != 0 then .abort "case 3" st
          else if P.ruleCode[ri]! == 0 then
            -- compile the rule's right-hand side, then return again
            match P.kInfo[k]! with
            | .recr lps us _ _ _ _ _ _ =>
              let rhsE := P.rules[ri]!.rhs.instantiateLevelParams lps us
              let (o, P) := g4Comp find? findProj? g4CompFuel P rhsE
              let P := let rc := P.ruleCode; let P := { P with ruleCode := #[] }
                { P with ruleCode := rc.set! ri (o + 1) }
              g4Run n P cel val ev fs argA slots mem mH 1 0 0 v st
            | _ => .abort "iota info" st
          else
            let rhs := P.ruleCode[ri]! - 1
            let rP := P.kB[k]!
            let fs := g4PopN fs 4
            if P.code[rhs]! == 2 && P.code[rhs + 2]! == rP + nf then
              -- the rule's right-hand side binds the leading arguments and
              -- the fields at once: no frame is pushed
              let ev := g4BindSpan argA start ev rP 0 0
              let e1 := ev.size >>> 1
              let ev := g4BindSpan argA (ms + cp) ev nf 0 (if rP == 0 then 0 else e1)
              let e2 := if rP + nf == 0 then 0 else ev.size >>> 1
              g4Run n P cel val ev fs argA slots mem mH 0 P.code[rhs + 3]! e2 0 st
            else
              let fs := g4PushArgs argA (ms + cp) fs nf
              let fs := g4PushArgs argA start fs rP
              g4Run n P cel val ev fs argA slots mem mH 0 rhs 0 0 st
        | 6 =>
          let fl := P.kE[k]!
          if fl % 2 == 1 then
            -- the K step: evaluate the major's declared type (§ the K step)
            let kc := val[g4X4 v + 1]!
            let s := val[g4X4 v + 2]!
            let len := val[g4X4 v + 3]!
            if len != P.kArity[kc]! then .abort "K type arity" st
            else if P.kCode[kc]! == 0 then
              match P.kInfo[kc]! with
              | .head c lps us =>
                match find? c with
                | some ci =>
                  match g4StripPis len (ci.toConstantVal.type.instantiateLevelParams lps us) with
                  | some b =>
                    -- the type is a saturated application of a constant whose
                    -- type ends in `Prop` (so the major is a proof: rescueK's
                    -- sort premises, by io inference alone)
                    let propOk := match b.getAppFn with
                      | .const h _ => match find? h with
                        | some hi => (match g4PiBody hi.toConstantVal.type with
                            | .sort .zero => true | _ => false) &&
                          b.getAppArgs.length == g4Pis hi.toConstantVal.type 0
                        | none => false
                      | _ => false
                    if !propOk then .abort "K type sort" st else
                    let (o, P) := g4Comp find? findProj? g4CompFuel P b
                    let P := let kc' := P.kCode; let P := { P with kCode := #[] }
                      { P with kCode := kc'.set! kc (o + 1) }
                    g4Run n P cel val ev fs argA slots mem mH 1 0 0 v st
                  | none => .abort "K type arity" st
                | none => .abort "K type" st
              | _ => .abort "K type" st
            else
              let ev := g4BindSpan argA s ev len 0 0
              let e := if len == 0 then 0 else ev.size >>> 1
              g4Run n P cel val ev (fs.push 11) argA slots mem mH 0 (P.kCode[kc]! - 1) e 0 st
          else if fl / 2 % 2 == 1 then .abort "struct-eta major" st
          else g4Run n P cel val ev (g4PopN fs 4) argA slots mem mH 1 0 0 0 st
        | 5 =>
          let fl := P.kE[k]!
          if fl % 2 == 1 then .abort "K major" st
          else if fl / 2 % 2 == 1 then .abort "struct-eta major" st
          else g4Run n P cel val ev (g4PopN fs 4) argA slots mem mH 1 0 0 0 st
        | _ => g4Run n P cel val ev (g4PopN fs 4) argA slots mem mH 1 0 0 0 st
      | 12 => -- a comparison's cell is forced: compare again
        g4Run n P cel val ev fs argA slots mem mH 5 0 0 0 st
      | 11 =>
        -- the K major's type, evaluated: the family at the constructor's
        -- parameters and indices?
        let fs := fs.pop
        let k := fs[fs.size - 4]!
        let tv := v
        if val[g4X4 tv]! != 6 then .abort "K type" st else
        let kT := val[g4X4 tv + 1]!
        let tvS := val[g4X4 tv + 2]!
        let tvL := val[g4X4 tv + 3]!
        let base := P.kC[k]!
        let cnP := P.rCP[base]!
        let ctor := P.rules[base]!.ctor
        match P.kInfo[kT]!, find? ctor with
        | .head T' _ ust, some (.ctorInfo cvj _ nF) =>
          let okT := match cvj.type.piResult.getAppFn with
            | .const T _ => T == T'
            | _ => false
          if !okT || ust.length != cvj.levelParams.length || nF != 0 || P.kD[k]! != 1 then
            .abort "K type" st else
          let (kC, P) := g4Resolve find? P ctor ust
          if P.kCode[kC]! == 0 then
            -- the constructor's index table `[nI, common flags…, index nodes…]`
            match g4StripPis cnP (cvj.type.instantiateLevelParams cvj.levelParams ust), find? T' with
            | some R, some (.indInfo cvT _) =>
              let rargs := R.getAppArgs.toArray
              let idx := (R.getAppArgs.drop cnP).toArray
              -- the constructor's result type applies the family to its own
              -- parameters (so the fabrication's type agrees with the major's
              -- type at the parameters syntactically)
              let parOk := rargs.size ≥ cnP && (List.range cnP).all (fun i =>
                match rargs[i]! with | .bvar b => b + i + 1 == cnP | _ => false)
              if !parOk then .abort "K type" st else
              let flags := match g4StripPis cnP cvT.type with
                | some it => g4IdxFlags 0 it #[]
                | none => #[]
              if flags.size != idx.size then .abort "K type" st else
              let (nodes, P) := idx.foldl (fun (acc : Array Nat × G4Prog) a =>
                let (o, P) := g4CompArg find? findProj? g4CompFuel acc.2 a
                (acc.1.push o, P)) (#[], P)
              let tab := P.code.size
              let P := P.emit (fun c => nodes.foldl (fun c x => c.push x)
                (flags.foldl (fun c x => c.push x) (c.push idx.size)))
              let P := let kc' := P.kCode; let P := { P with kCode := #[] }
                { P with kCode := kc'.set! kC (tab + 1) }
              g4Run n P cel val ev (fs.push 11) argA slots mem mH 1 0 0 tv st
            | _, _ => .abort "K type" st
          else
          let tab := P.kCode[kC]! - 1
          let nI := P.code[tab]!
          if tvL != cnP + nI then .abort "K type" st else
          let ev := g4BindSpan argA tvS ev cnP 0 0
          let e := if cnP == 0 then 0 else ev.size >>> 1
          let c0 := (cel.size >>> 2)
          let cel := g4KCells P.code e tab nI nI 0 cel
          let fs := (((fs.push kC).push tvS).push cnP).push 13
          let fs := g4KFrames P.code ev argA e tab nI (tvS + cnP) nI 0 c0 fs
          g4Run n P cel val ev fs argA slots mem mH 5 0 0 0 st
        | _, _ => .abort "K type" st
      | 10 =>
        -- a strict argument's value: a value cell, pushed, and the spine goes on
        let j := fs[fs.size - 2]!
        let env' := fs[fs.size - 3]!
        let pc' := fs[fs.size - 4]!
        let fs := g4PopN fs 4
        let c := (cel.size >>> 2)
        let ao := P.code[P.code[pc' + 3 + j]! + 1]!
        g4Run n P ((((cel.push (v + 2)).push ao).push env').push 0) val ev (fs.push (g4Tag c 1)) argA
          slots mem mH 4 pc' env' j st
      | 4 =>
        let pi := fs[fs.size - 2]!
        let fs := fs.pop.pop
        if pi == 0 then g4Run n P cel val ev fs argA slots mem mH 1 0 0 0 st else
        let q := pi - 1
        match val[g4X4 v]! with
        | 1 =>
          let kc := val[g4X4 v + 1]!
          let len := val[g4X4 v + 3]!
          let np := P.pNP[q]!
          let idx := P.pIdx[q]!
          if P.kTag[kc]! == 1 && P.kB[kc]! == P.pNid[q]! && idx < P.pNF[q]! &&
              len == np + P.pNF[q]! && len ≤ P.kArity[kc]! && P.kD[kc]! == P.pNl[q]! &&
              (P.pAlw[q]! == 1 || (match P.kInfo[kc]! with
                | .ctor _ _ _ _ => true
                | _ => false)) then
            g4Run n P cel val ev fs argA slots mem mH 2 0 0 argA[val[g4X4 v + 2]! + np + idx]! st
          else .abort "proj shape" st
        | 3 =>
          if !P.strOk then .abort "string literal" st else
          let sE := strLitToConstructor P.strs[val[g4X4 v + 1]!]!
          let (o, P) := g4Comp find? findProj? g4CompFuel P sE
          g4Run n P cel val ev ((fs.push pi).push 4) argA slots mem mH 0 o 0 0 st
        | _ => g4Run n P cel val ev fs argA slots mem mH 1 0 0 0 st
      | 7 =>
        match val[g4X4 v]! with
        | 2 =>
          let w := (val.size >>> 2)
          let m := val[g4X4 v + 1]!
          g4Run n P cel ((((val.push 2).push (m + 1)).push 0).push 0) ev fs.pop
            argA slots mem mH 1 0 0 w st
        | 1 =>
          let kc := val[g4X4 v + 1]!
          if kc == P.kZero && val[g4X4 v + 3]! == 0 then
            let w := (val.size >>> 2)
            g4Run n P cel ((((val.push 2).push 1).push 0).push 0) ev fs.pop argA slots mem mH 1 0 0 w st
          else if kc == P.kSucc && val[g4X4 v + 3]! == 1 then
            g4Run n P cel val ev (fs.push 7) argA slots mem mH 2 0 0 argA[val[g4X4 v + 2]!]! st
          else g4Run n P cel val ev fs.pop argA slots mem mH 1 0 0 0 st
        | _ => g4Run n P cel val ev fs.pop argA slots mem mH 1 0 0 0 st
      | t =>
        -- literal acceleration: `[k, a, b, 5|15]` reads the first
        -- argument, `[k, n₁, a, b, 6|16]` the second
        let first := t == 5 || t == 8
        let wf := t == 8 || t == 9
        -- the reading: `0` a literal `m`, `1` a `Nat.succ` of cell `m`, `2` none
        let tg := val[g4X4 v]!
        let kc := val[g4X4 v + 1]!
        let rd : Nat := if tg == 2 then 0
          else if tg == 1 && kc == P.kZero && val[g4X4 v + 3]! == 0 then 0
          else if tg == 1 && kc == P.kSucc && val[g4X4 v + 3]! == 1 then 1 else 2
        let m : Nat := if tg == 2 then kc else if rd == 0 then 0
          else if rd == 1 then argA[val[g4X4 v + 2]!]! else 0
        match rd with
        | 1 => g4Run n P cel val ev (fs.push 7) argA slots mem mH 2 0 0 m st
        | 0 =>
          if first then
            let b := fs[fs.size - 2]!
            let a := fs[fs.size - 3]!
            let k := fs[fs.size - 4]!
            let fs := g4PopN fs 4
            g4Run n P cel val ev (((((fs.push k).push m).push a).push b).push (if wf then 9 else 6))
              argA slots mem mH 2 0 0 b st
          else
            let k := fs[fs.size - 5]!
            let m₁ := fs[fs.size - 4]!
            let fs := g4PopN fs 5
            if wf then .abort "wf nat op" st else
            let op := P.kE[k]!
            match g4NatKind op m with
            | 0 =>
              let w := (val.size >>> 2)
              g4Run n P cel ((((val.push 2).push (g4NatVal op m₁ m)).push 0).push 0) ev fs argA slots
                mem mH 1 0 0 w st
            | 1 =>
              let kb := if g4NatVal op m₁ m == 1 then P.kTrue else P.kFalse
              let w := (val.size >>> 2)
              g4Run n P cel ((((val.push 1).push kb).push 0).push 0) ev fs argA slots mem mH
                1 0 0 w st
            | _ =>
              -- no result (the exponent bound; the incumbent unfolds `Nat.pow`)
              .abort "nat pow bound" st
        | _ =>
          -- no literal: unfold the operation (`reduceNat` fails, δ)
          let k := fs[fs.size - (if first then 4 else 5)]!
          let a := fs[fs.size - 3]!
          let b := fs[fs.size - 2]!
          let fs := g4PopN fs (if first then 4 else 5)
          -- the operation's tag is 3 or 4; dispatch it as a plain definition
          g4Run n P cel val ev
            ((fs.push (g4Tag b 1)).push (g4Tag a 1)) argA slots mem mH 3 1 0 k st
end

end ConLeche.Cached

namespace ConLeche.Cached
open ConLeche

/-- The outcome of a round-3 evaluation at the `Bool.true` comparison,
as `groundBool`'s.  **The compiled program is kept for the declaration** (task #423
round 3): `P₀` is the program the declaration's earlier runs compiled
(empty at the first; `CState.ground4`, flushed with the other
environment-dependent memos).  The result carries the program back. -/
def ground4BoolCore (find? : Name → Option ConstantInfo)
    (findProj? : Name → Nat → Option ProjEntry) (natOk strOk : Bool) (P₀ : G4Prog) (e : Expr) :
    (Option Bool × (Nat × Nat) × String) × G4Prog :=
  let P : G4Prog := if P₀.kTag.size == 0 then
      let P : G4Prog := { natOk := natOk, strOk := strOk }
      let (kT, P) := g4Resolve find? P boolTrueName []
      let (kF, P) := g4Resolve find? P boolFalseName []
      let (kZ, P) := g4Resolve find? P natZeroName []
      let (kS, P) := g4Resolve find? P natSuccName []
      { P with kTrue := kT, kFalse := kF, kZero := kZ, kSucc := kS }
    else P₀
  let (o, P) := g4Comp find? findProj? g4CompFuel P e
  let r : Option Bool × (Nat × Nat) × String × G4Prog :=
    let sl := P.slotA
    let P := { P with slotA := #[], epBase := P.epBase + g4EpochStep }
    match g4Run find? findProj? groundFuel P #[2, 0, 0, 0] #[5, 0, 0, 0] #[] #[] #[] sl #[]
      (Array.replicate 1024 0) 0 o 0 0 0 with
  | .done v val P sl st left =>
    let P := { P with slotA := sl }
    let tr := groundFuel - left
    if val[g4X4 v]! == 1 && val[g4X4 v + 3]! == 0 then
      let k := val[g4X4 v + 1]!
      if k == P.kTrue then (some true, (st, tr), "", P)
      else if k == P.kFalse then (some false, (st, tr), "", P)
      else (none, (st, tr), "not a Bool", P)
    else (none, (st, tr), "not a constructor", P)
  -- (an abort drops the program: keeping the pre-run one alive across the
  -- run would share it, and every compile during the run would copy it)
  | .abort why st => (none, (st, 0), why, {})
  ((r.1, r.2.1, r.2.2.1), r.2.2.2)

def ground4Bool (fe : FEnv) (P₀ : G4Prog) (e : Expr) :
    (Option Bool × (Nat × Nat) × String) × G4Prog :=
  ground4BoolCore fe.find? fe.findProj? (natLitStoredF fe) (strLitStoredF fe) P₀ e

/-- **The ground shortcut** (task #423, spike; `groundMode ≠ 0`): a
comparison with `Bool.true` on either side whose other side is closed
evaluates that side on the ground machine: `Bool.true` answers `true`,
`Bool.false` answers `false` (the two constructors are not
definitionally equal), anything else (an abort) leaves the comparison
to the incumbent path (`none`).  Read by `defeqBodyI`
(`ConLeche/Cached/CoreC.lean`). -/
def groundShortcut (eager : Bool) (fe : FEnv) (P : G3Prog × G4Prog) (a b : Expr) :
    Option Bool × (G3Prog × G4Prog) :=
  let t? : Option Expr :=
    if Expr.isBoolTrue b && (eager || !(Expr.hasFvar a)) then some a
    else if Expr.isBoolTrue a && (eager || !(Expr.hasFvar b)) then some b
    else none
  match t? with
  | none => (none, P)
  | some t =>
    if Expr.hasFvar t then (none, P) else
    let eng : G3Prog × G4Prog → Expr → (Option Bool × (Nat × Nat) × String) × (G3Prog × G4Prog) :=
      fun P t =>
      if groundMode ≥ 10 then (let (r, P4) := ground4Bool fe P.2 t; (r, (P.1, P4)))
      else if groundMode ≥ 7 then (let (r, P3) := ground3Bool fe P.1 t; (r, (P3, P.2)))
      else if groundMode ≥ 3 && groundMode != 5 then (ground2Bool fe t, P)
      else (groundBool fe t, P)
    let ((r, steps, why), P) := eng P t
    -- probes 5, 6 and 9: the engine twice (its own cost is the difference)
    let (r, P) := if groundMode == 5 || groundMode == 6 || groundMode == 9 || groundMode == 12 then
        let ((r', _, _), P) := eng P (dbgTrace "" fun _ => t)
        (if r' == r then r else none, P) else (r, P)
    if groundMode == 2 || groundMode == 4 || groundMode == 8 || groundMode == 11 then
      (dbgTrace s!"GROUND {repr r} {steps.1} {steps.2} {why}" fun _ => r, P)
    else (r, P)

/-- The ground shortcut reads `fe` only through `find?` and
`findTable?` (for `ConLeche/Verify/Cached/KnotCongr.lean`). -/
theorem groundShortcut_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (eager : Bool) :
    groundShortcut eager fe₁ = groundShortcut eager fe₂ := by
  have hp : fe₁.findProj? = fe₂.findProj? := by
    funext T i; unfold FEnv.findProj?; rw [htb]
  have hg : groundBool fe₁ = groundBool fe₂ := by
    funext e; unfold groundBool strLitStoredF natLitStoredF; rw [hfe, hp]
  have hn : natLitStoredF fe₁ = natLitStoredF fe₂ := by
    unfold natLitStoredF; rw [hfe]
  have hs : strLitStoredF fe₁ = strLitStoredF fe₂ := by
    unfold strLitStoredF; rw [hn, hfe]
  have hg2 : ground2Bool fe₁ = ground2Bool fe₂ := by
    funext e; unfold ground2Bool; rw [hfe, hp, hn, hs]
  have hg3 : ground3Bool fe₁ = ground3Bool fe₂ := by
    funext P e; unfold ground3Bool; rw [hfe, hp, hn, hs]
  have hg4 : ground4Bool fe₁ = ground4Bool fe₂ := by
    funext P e; unfold ground4Bool; rw [hfe, hp, hn, hs]
  funext P a b; unfold groundShortcut; rw [hg, hg2, hg3, hg4]

end ConLeche.Cached

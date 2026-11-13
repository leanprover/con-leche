module

public import ConLeche.Kernel.FEnv

@[expose] public section

/-!
# The ground engine (task #423): a lazy abstract machine at `t =?= Bool.true`

A call-by-need abstract machine for closed terms (Sestoft's lazy machine:
environments of heap cells instead of substitution, thunks updated in
place, an explicit continuation stack, weak head evaluation only), run
where a comparison has `Bool.true` on one side and a closed term on the
other.  It lives in the specification tier because the specification's
`defeqBody` (`Kernel/Core.lean`) calls it at that site: it is the best
code there is for the site, and there is no naive twin of it.  The cached
core calls the same engine (`ConLeche/Cached/GroundGate.lean`), with the
compiled program kept for the declaration.

The state is FLAT: no Lean object is allocated per transition.  Every
definition body and rule right-hand side the site reaches is compiled on
first use into a code array (`Array Nat`, constants resolved to entries of
a constant table, closed argument terms given a sharing slot), and the
machine's state is a handful of `Array Nat`s threaded linearly through
one tail-recursive loop (`g4Run`) and mutated in place:

* `cel` — cells, stride 4: `[state, code, env, _]`; state `0` an
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

Types (sorts, Π-types) are compiled to the neutral, binder domains are
dropped (read-back is never needed: the answer is a `Bool` constructor),
and a stuck scrutinee makes the redex stuck (the neutral).  The K step is
`Red.iotaK`.  A step with no proved rule declines (task #423 soundness, `G4Stop`): ι
case 3, and a neutral major at a single-constructor recursor (K,
structure η, the `And` rescue read its type).  The soundness reading is
erased reduction (`ConLeche/Verify/Ground/Erased.lean`): the neutral is
the forgotten term.

-/

namespace ConLeche

/-- The effectively unbounded step budget of the ground machine (a
termination device, as `checkFuel`). -/
@[irreducible, noinline] def groundFuel : Nat := 4611686018427387904  -- 2^62

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
  | .levels lvls => lvls.map (Level.subst lps us)

/-- Case 3 of the ι split, decided without reduction (task #423, on
master's `iotaCase3I`): `false` at K; at a family whose former's sort is
syntactic, its never-zero test; `true` (the engine aborts) where the
incumbent would need `whnf` to read the sort. -/
def gCase3 (find? : Name → Option ConstantInfo) (isK : Bool) (cvj : ConstantVal)
    (us : List Level) : Bool :=
  if isK then false else
  match ctorFamily find? cvj with
  | some (cvT, _) =>
    if cvT.levelParams.length == us.length then
      match formerResSort cvT.type with
      | some _ => !formerNeverZero cvT us
      | none => true
    else true
  | none => true

/-- The constructor's parameter count (master's rules no longer store it). -/
def gCtorParams (find? : Name → Option ConstantInfo) (c : Name) : Nat :=
  match find? c with
  | some (.ctorInfo _ nP _) => nP
  | _ => 0


/-- Per-entry information of the run's constant table. -/
inductive G4Info where
  | defn (name : Name) (lps : List Name) (us : List Level) (v : Expr)
  | ctor (name : Name) (us : List Level) (nP nF : Nat)
  /-- `kEta`: the single rule of a structure-like recursor; `kK`: K -/
  | recr (name : Name) (lps : List Name) (us : List Level) (mI rP ruleBase nRules : Nat)
      (kK kEta : Bool)
  /-- an entry the machine never unfolds (an axiom, a theorem, an inductive
  type, `Quot`, a wrong level count, an unknown name): still its constant,
  so every entry reads back as the term it was resolved for -/
  | neutral (name : Name) (us : List Level)
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
  /-- the structure the projection names (the node's `.proj sn i _`) -/
  sn : Name
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
  masks : Std.HashMap Name (Array Bool) := {}
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
  `epBase` it carries (no per-run clearing).  A run's `epBase` is the
  previous run's plus that run's cell count, so it is above every entry
  an earlier run wrote (task #423 soundness: a fixed epoch step would
  misread an earlier run's cell past the step as a current one) -/
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

/-- The official kernel's size of a numeral in bytes
(`lean_nat_size_in_bytes`): one machine word for a scalar, the limbs
for a GMP number — 8 bytes per started 64 bits, and at least 8. -/
def natSizeBytes (n : Nat) : Nat := 8 * (n.log2 / 64 + 1)

/-- The largest exponent / shift amount the official kernel evaluates
(`get_count_arg`: it must fit in a 32-bit unsigned integer). -/
def natCountMax : Nat := 4294967295

/-- `natOpResult` by operation index (the order of `natBin14Names`):
`0` a literal result, `1` a `Bool` result (`0`/`1`). -/
@[inline] def g4NatKind (op : Nat) : Nat :=
  if op == 4 || op == 5 then 1 else 0

def g4NatVal (op a b : Nat) : Nat :=
  match op with
  | 0 => a + b | 1 => a - b | 2 => a * b | 3 => a ^ b
  | 4 => if a == b then 1 else 0 | 5 => if a ≤ b then 1 else 0
  | 6 => a / b | 7 => a % b | 8 => Nat.gcd a b | 9 => Nat.land a b | 10 => Nat.lor a b
  | 11 => Nat.xor a b | 12 => Nat.shiftLeft a b | 13 => Nat.shiftRight a b | _ => 0

/-- `2^64`, hoisted (a literal above `2^32` is parsed at each evaluation). -/
@[noinline] def g4Word : Nat := 18446744073709551616

/-- `natSizeBytes n > M` at the maximum `Nat` size `some M` (`none`: no
bound, never), with the one-word case (`n < 2^64`: eight bytes) decided
without `Nat.log2`. -/
@[inline] def g4SizeOver (maxNat : Option Nat) (n : Nat) : Bool :=
  match maxNat with
  | some M => if n < g4Word then M < 8 else natSizeBytes n > M
  | none => false

/-- **The maximum `Nat` size** (task #423 completeness; official
`reduce_pow`/`reduce_shiftLeft`/`reduce_bin_nat_op`, the cached core's
`natOpRefusal`, task #519): does the operation `op` (index of
`natBin14Names`; `pow` or `shiftLeft`) refuse the literals `a`, `b` before
computing?  The size of the result of `add`, `sub` and `mul` is tested
after computing (`g4SizeOver`, `natResultRefused`).  A refusal is raised
at the site as the incumbent's own error.  With no maximum (`none`, the
specification's run) only the count bound `natCountMax` refuses. -/
def g4NatPreRefuses (maxNat : Option Nat) (op a b : Nat) : Bool :=
  if op == 3 then
    b > natCountMax || (a > 1 && b != 0 && match maxNat with
      | some M => natSizeBytes a > M / b
      | none => false)
  else if op == 12 then
    a != 0 && (b > natCountMax || match maxNat with
      | some M => natSizeBytes a + b / 8 + 1 > M
      | none => false)
  else false

/-- Strip the Π-binders of a type. -/
def g4PiBody : Expr → Expr
  | .forallE _ b => g4PiBody b
  | e => e

/-- **Erasure** (task #423 round 3): the argument positions of a constant
whose argument is never scrutinised by the machine — a type former (the
domain is, after its Π-binders, a sort: types, motives) and, except at a
recursor, a proof (the domain's head constant's type ends in `Prop`).
Such an argument is bound to the neutral cell and never compiled. -/
def g4Mask (find? : Name → Option ConstantInfo) (isRec : Bool) : Expr → Array Bool → Array Bool
  | .forallE d b, acc =>
    let tf := match g4PiBody d with | .sort _ => true | _ => false
    let pf := !isRec && (match (g4PiBody d).getAppFn with
      | .const c _ => match find? c with
        | some ci => (match g4PiBody ci.toConstantVal.type with
          | .sort .zero => true | _ => false)
        | none => false
      | _ => false)
    g4Mask find? isRec b (acc.push (tf || pf))
  | _, acc => acc

/-- The number of leading Π-binders of a type. -/
def g4Pis : Expr → Nat → Nat
  | .forallE _ b, n => g4Pis b (n + 1)
  | _, n => n

section
variable (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)

/-- A recursor rule's row of the table, appended to every rule array (the
rule at the recursor's levels `us`; its body compiled on first use). -/
def g4RuleRow (isK : Bool) (lps : List Name) (us : List Level) (P : G4Prog) (rl : RecRule) : G4Prog :=
  let case3 := match find? rl.ctor with
    | some (.ctorInfo cvj _ _) =>
      gCase3 find? isK cvj (gCmpLevels rl lps us cvj.levelParams)
    | _ => true
  let (ni, P) := P.nid rl.ctor
  let (r1, r2, r3, r4, r5, r6) := (P.rules, P.ruleCode, P.rNid, P.rNF, P.rCP, P.rC3)
  let P := { P with rules := #[], ruleCode := #[], rNid := #[], rNF := #[], rCP := #[],
                    rC3 := #[] }
  { P with rules := r1.push ⟨rl.ctor, rl.nfields, (gCtorParams find? rl.ctor), case3, rl.rhs⟩,
           ruleCode := r2.push 0, rNid := r3.push ni, rNF := r4.push rl.nfields,
           rCP := r5.push (gCtorParams find? rl.ctor), rC3 := r6.push (if case3 then 1 else 0) }

/-- A new table entry for the constant `c` at levels `us` (`kfab`: the K
step's constructor entry plus one, or `0`), appended to every table
array. -/
def g4Entry (P : G4Prog) (c : Name) (us : List Level) (kfab : Nat) : Nat × G4Prog :=
  let k := P.kTag.size
  let (tag, ar, b, c', d, e', info, P) : Nat × Nat × Nat × Nat × Nat × Nat × G4Info × G4Prog :=
    match find? c with
    | some (.defnInfo cv v _) =>
      if us.length != cv.levelParams.length then (5, 0, 0, 0, 0, 0, .neutral c us, P)
      else
        let tag := if us.isEmpty && P.natOk && natBin14 c then 3 else 0
        let op := (natBin14Names.idxOf? c).getD 0
        (tag, 0, 0, 0, 0, op, .defn c cv.levelParams us v, P)
    | some (.ctorInfo cv nP nF) =>
      let (ni, P) := P.nid c
      (1, g4Pis cv.type 0, ni, 0, us.length, 0, .ctor c us nP nF, P)
    | some (.recInfo cv mI rP isK rules) =>
      if us.length != cv.levelParams.length || !(Expr.peelPis (mI + 1) cv.type).isSome then
        (5, 0, 0, 0, 0, 0, .neutral c us, P)
      else
        let base := P.rules.size
        let P := rules.foldl (g4RuleRow find? isK cv.levelParams us) P
        let isEta := match rules with | [_] => !isK | _ => false
        let fl := (if isK then 1 else 0) + (if isEta then 2 else 0)
        (2, mI, rP, base, rules.length, fl + 4 * kfab,
          .recr c cv.levelParams us mI rP base rules.length (isK) isEta, P)
    | _ => (5, 0, 0, 0, 0, 0, .neutral c us, P)
  let (t1, t2, t3, t4, t5, t6, ns) := (P.kTag, P.kCode, P.kArity, P.kSlot, P.kInfo, P.kMap, P.nslots)
  let (u1, u2, u3, u4) := (P.kB, P.kC, P.kD, P.kE)
  let P := { P with kTag := #[], kCode := #[], kArity := #[], kSlot := #[], kInfo := #[], kMap := {},
                    kB := #[], kC := #[], kD := #[], kE := #[] }
  (k, { P with kTag := t1.push tag, kCode := t2.push 0, kArity := t3.push ar,
               kSlot := t4.push ns, nslots := ns + 1,
               kInfo := t5.push info, kMap := t6.insert (c, us) k,
               kB := u1.push b, kC := u2.push c', kD := u3.push d, kE := u4.push e' })

/-- The table entry of the constant `c` at levels `us`, created on first
use.  Kinds: `0` definition, `1` constructor, `2` recursor, `3` an
accelerated `Nat` operation (a definition too, with the `Nat` basis),
`5` neutral.  A recursor's `kE`
is `flags + 4 * (j + 1)` under the K step (`Red.iotaK`; the K flag, one
rule, arity, levels and `peelPis` checked), `j` the entry of its rule's
constructor at the rule's comparand levels: the dispatch then returns
that constructor on the recursor's leading arguments as the major,
without reading the major (§ the K step).  `fuel` bounds the one nested
resolution of that constructor. -/
def g4ResolveF (findProj? : Name → Nat → Option ProjEntry) : Nat → G4Prog → Name → List Level → Nat × G4Prog
  | fuel, P, c, us =>
  match P.kMap[(c, us)]? with
  | some k => (k, P)
  | none =>
    let (kfab, P) : Nat × G4Prog := match fuel, find? c with
      | f + 1, some (.recInfo cv mI _ true [rl]) =>
        if us.length == cv.levelParams.length && (Expr.peelPis (mI + 1) cv.type).isSome then
          match find? rl.ctor with
          | some (.ctorInfo cvj _ 0) =>
            let (kc, P) := g4ResolveF findProj? f P rl.ctor (gCmpLevels rl cv.levelParams us cvj.levelParams)
            -- the rule binds no field, and the constructor's arguments are
            -- among the recursor's leading ones (always so for a K-like
            -- family; checked, so the step needs no premise about the types)
            if rl.nfields == 0 && P.kArity[kc]! ≤ mI + 1 then (kc + 1, P) else (0, P)
          | _ => (0, P)
        else (0, P)
      | _, _ => (0, P)
    g4Entry find? P c us kfab

/-- `g4ResolveF` with room for the K constructor's resolution. -/
def g4Resolve (P : G4Prog) (c : Name) (us : List Level) : Nat × G4Prog :=
  g4ResolveF find? findProj? 1 P c us

/-- The erasure mask of a spine's head constant (`g4Mask`), memoised per
name. -/
def g4MaskOf (P : G4Prog) (hd : Expr) : Array Bool × G4Prog :=
  match hd with
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

/-- One argument of a spine (`acc`: the argument nodes so far and the
program): an erased argument is the neutral node; otherwise `compArg`
compiles it. -/
def g4ArgStep {α : Type} (compArg : G4Prog → α → Nat × G4Prog) (mask : Array Bool)
    (acc : Array Nat × G4Prog) (a : α) : Array Nat × G4Prog :=
  if mask.getD acc.1.size false then
    let o := acc.2.code.size; (acc.1.push o, acc.2.emit (fun c => c.push 8))
  else
  let (ao, P) := compArg acc.2 a
  (acc.1.push ao, P)

/-- A spine `hd args` with its head's erasure mask: the head compiled by
`comp`, the arguments by `compArg` (the compiler on the subterms), then
the spine node `[1, head, n, a₁ … aₙ]`.  An erased argument is the
neutral node. -/
def g4CompSpine {α : Type} (comp : G4Prog → Nat × G4Prog) (compArg : G4Prog → α → Nat × G4Prog)
    (P : G4Prog) (args : List α) (mask : Array Bool) : Nat × G4Prog :=
  let (ho, P) := comp P
  let (aos, P) := args.foldl (g4ArgStep compArg mask) (#[], P)
  let o := P.code.size
  (o, P.emit (fun c => aos.foldl (fun c a => c.push a) (((c.push 1).push ho).push aos.size)))

/-- A closed application, `let` or projection `a` in argument position
(`comp`: the compiler on `a`): one node per closed term in the program,
`[9, slot, e]`, with a sharing slot (`closedNode`, keyed pointer-first). -/
def g4CompShared (comp : G4Prog → Nat × G4Prog) (P : G4Prog) (a : Expr) : Nat × G4Prog :=
  if a.bvarBRaw == 0 then
    match P.closedNode[a]? with
    | some o => (o, P)
    | none =>
      let (ao, P) := comp P
      -- (never taken: compiling `a` registers only its proper subterms;
      -- the check keeps `closedNode` growing without that proof)
      match P.closedNode[a]? with
      | some o => (o, P)
      | none =>
      let o := P.code.size
      let ns := P.nslots
      let P := { P.emit (fun c => ((c.push 9).push ns).push ao) with nslots := ns + 1 }
      let cm := P.closedNode; let P := { P with closedNode := {} }
      (o, { P with closedNode := cm.insert a o })
  else comp P

/-- The head of a spine is smaller than the spine. -/
theorem Expr.sizeOf_getAppFn_le : ∀ (e : Expr), sizeOf e.getAppFn ≤ sizeOf e
  | .app f a => by
    have := Expr.sizeOf_getAppFn_le f
    simp only [Expr.getAppFn, Expr.app.sizeOf_spec]; omega
  | .bvar _ | .fvar .. | .sort _ | .const .. | .lam .. | .forallE .. | .letE .. | .lit _
  | .proj .. => by simp only [Expr.getAppFn]; omega

/-- A spine's argument is smaller than the spine. -/
theorem Expr.sizeOf_lt_of_mem_getAppArgs : ∀ {e a : Expr}, a ∈ e.getAppArgs → sizeOf a < sizeOf e
  | .app f x, a, h => by
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at h
    simp only [Expr.app.sizeOf_spec]
    rcases h with h | rfl
    · have := Expr.sizeOf_lt_of_mem_getAppArgs h; omega
    · omega
  | .bvar _, _, h | .fvar .., _, h | .sort _, _, h | .const .., _, h | .lam .., _, h
  | .forallE .., _, h | .letE .., _, h | .lit _, _, h | .proj .., _, h => by
    simp [Expr.getAppArgs] at h

mutual
/-- Compile `e` (closed under the binders the code will be run under);
the result is the node's offset.  Code tags: `0` bvar `[0, i]`, `1`
spine `[1, head, n, a₁ … aₙ]`, `2` λ `[2, body]`, `3` let `[3, v, body]`,
`4` constant `[4, entry]`, `5` `Nat` literal `[5, n]`, `6` string `[6,
s]`, `7` projection `[7, proj + 1, e]` (with no projection table, the neutral), `8` neutral `[8]`, `9`
shared closed argument `[9, slot, e]`. -/
def g4Comp (P : G4Prog) (e : Expr) : Nat × G4Prog :=
    match e with
    | .bvar i => let o := P.code.size; (o, P.emit (fun c => (c.push 0).push i))
    | .lam _ b =>
      -- `[2, body, n, inner]`: `n` the λ-telescope's length from here,
      -- `inner` the innermost body (all of them bound in one step)
      let (bo, P) := g4Comp P b
      let (tn, inner) := if P.code[bo]! == 2 then (P.code[bo + 2]! + 1, P.code[bo + 3]!) else (1, bo)
      let o := P.code.size; (o, P.emit (fun c => (((c.push 2).push bo).push tn).push inner))
    | .letE _ v b =>
      let (vo, P) := g4CompArg P v
      let (bo, P) := g4Comp P b
      let o := P.code.size; (o, P.emit (fun c => ((c.push 3).push vo).push bo))
    | .const c us =>
      let (k, P) := g4Resolve find? findProj? P c us
      let o := P.code.size; (o, P.emit (fun c => (c.push 4).push k))
    | .lit (.natVal n) => let o := P.code.size; (o, P.emit (fun c => (c.push 5).push n))
    | .lit (.strVal s) =>
      let o := P.code.size
      let si := P.strs.size
      let P := P.emit (fun c => (c.push 6).push si)
      let ss := P.strs; let P := { P with strs := #[] }
      (o, { P with strs := ss.push s })
    | .proj sn i s =>
      match findProj? sn i with
      | some en =>
        let (so, P) := g4Comp P s
        let pj : G4Proj := ⟨sn, en.ctor, i, en.numParams, en.numFields,
           en.levelParams.length, true, en⟩
        let (ni, P) := P.nid en.ctor
        let (q1, q2, q3, q4, q5, q6, q7) := (P.projs, P.pNid, P.pIdx, P.pNP, P.pNF, P.pNl, P.pAlw)
        let P := { P with projs := #[], pNid := #[], pIdx := #[], pNP := #[], pNF := #[],
                          pNl := #[], pAlw := #[] }
        let P := { P with projs := q1.push pj, pNid := q2.push ni, pIdx := q3.push i }
        let P := { P with pNP := q4.push en.numParams, pNF := q5.push en.numFields }
        let P := { P with pNl := q6.push en.levelParams.length,
                          pAlw := q7.push (if pj.always then 1 else 0) }
        let pi := q1.size + 1
        let o := P.code.size; (o, P.emit (fun c => ((c.push 7).push pi).push so))
      -- no projection table: the projection is stuck, the neutral
      | none => let o := P.code.size; (o, P.emit (fun c => c.push 8))
    | .app f x =>
      let (mask, P) := g4MaskOf find? P (Expr.app f x).getAppFn
      g4CompSpine (fun P => g4Comp P (Expr.app f x).getAppFn)
        (fun P (a : {a // a ∈ (Expr.app f x).getAppArgs}) => g4CompArg P a.1)
        P (Expr.app f x).getAppArgs.attach mask
    | .sort _ | .forallE .. | .fvar .. => let o := P.code.size; (o, P.emit (fun c => c.push 8))
termination_by 2 * sizeOf e
decreasing_by
  all_goals first
    | (simp only [Expr.lam.sizeOf_spec, Expr.letE.sizeOf_spec, Expr.proj.sizeOf_spec]; omega)
    | (have := Expr.sizeOf_getAppFn_le f
       simp only [Expr.getAppFn, Expr.app.sizeOf_spec]; omega)
    | (have := Expr.sizeOf_lt_of_mem_getAppArgs a.2; omega)

/-- An argument position: a closed application, `let` or projection
gets a sharing slot. -/
def g4CompArg (P : G4Prog) (a : Expr) : Nat × G4Prog :=
    match _h : a with
    | .app .. | .letE .. | .proj .. => g4CompShared (fun P => g4Comp P a) P a
    | _ => g4Comp P a
termination_by 2 * sizeOf a + 1
decreasing_by all_goals (subst _h; omega)
end
end

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

section
variable (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)
  (maxNat : Option Nat)

/-- **Why the machine stopped without a value** (task #423 soundness,
ruling 4: no hand-back to the incumbent). -/
inductive G4Stop where
  /-- a stuck redex the incumbent is stuck at too (a constructor no rule
  reads, a projection of the wrong shape, a literal without its basis):
  the site answers `false` -/
  | stuck (why : String)
  /-- a step the engine does not do, or has no proved rule for: the check
  declines (exit 2) with this message, which names the step and the
  constant -/
  | decline (msg : String)
  /-- the maximum `Nat` size refuses operation `op` (index of
  `natBin14Names`) on `a`, `b` (`post`: the result's size, after
  computing): the incumbent's own refusal, raised at the site -/
  | refuse (op a b : Nat) (post : Bool)
  /-- an invariant of the machine does not hold (exit 3) -/
  | internal (msg : String)
  deriving Inhabited

/-- The name of a table entry, for messages. -/
def G4Prog.entryName (P : G4Prog) (k : Nat) : Name :=
  match P.kInfo[k]? with
  | some (.defn c ..) | some (.ctor c ..) | some (.recr c ..) | some (.neutral c _) => c
  | none => .anonymous

/-- The declines (task #423 soundness, ruling 4): each names the step and
the constant. -/
def g4DeclineCase3 (c : Name) : G4Stop :=
  .decline s!"ground evaluation of `{c}`: the major premise is a constructor of a type that \
    may be a proposition (ι case 3), and reducing it needs typing certificates the evaluator \
    does not build"

def g4DeclineStuckMajor (c : Name) (k : Bool) : G4Stop :=
  .decline s!"ground evaluation of `{c}`: the major premise does not evaluate to a \
    constructor (it is stuck, or a proof the evaluator does not evaluate), and \
    {if k then "the K rule" else "expanding it by its one constructor (structure η, the `And` rescue)"} \
    on it needs its type, which the evaluator does not compute"

/-- The machine's outcome: a value (with the value array to read it),
or a stop; the constant dispatches and the fuel left. -/
inductive G4Out where
  | done (v : Nat) (val : Array Nat) (P : G4Prog) (slots : Array Nat) (cells steps left : Nat)
  | stop (why : G4Stop) (steps : Nat)

/-- **The machine.**  Modes: `0` evaluate node `pc` under `env`, `1`
return value `x`, `2` enter cell `x`, `3` dispatch constant entry `x` (`pc = 1`: as a plain definition),
`4` push the arguments of spine `pc` from the `x`-th down. -/
def g4Run : Nat → G4Prog → (cel val ev fs argA slots mem mH : Array Nat) →
    (mode pc env x st : Nat) → G4Out
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, st => .stop (.decline "ground evaluation did not finish within its step budget") st
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
      | _ => g4Run n P cel val ev fs argA slots mem mH 1 0 0 0 st
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
      else .stop (.decline "ground evaluation: a term's value is needed to compute itself") st
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
            let hit := g4MemoFind mem mH fs argA k (mI + 1) mH.size (g4Slot h mH.size)
            if hit != 0 then
              g4Run n P cel val ev (g4PopN fs (mI + 1)) argA slots mem mH 2 0 0 hit st
            else
              let start := argA.size
              let argA := g4CopyArgs fs argA (mI + 1) 0
              let fs := g4PopN fs (mI + 1)
              let r := (cel.size >>> 2)
              let maj := argA[start + mI]!
              let rr := (mem.size >>> 2)
              let mem := (((mem.push k).push start).push (mI + 1)).push r
              let mH := g4MemoIns mem argA mH rr h
              let cel := (((cel.push 1).push 0).push 0).push 0
              let fs := ((((fs.push (g4Tag r 2)).push k).push start).push (mI + 1)).push 3
              let ef := P.kE[k]!
              if ef ≥ 4 then
                -- the K step (`Red.iotaK`): the rule's constructor on the
                -- recursor's leading arguments is the major; the major is
                -- never read
                let kc := ef / 4 - 1
                let w := (val.size >>> 2)
                g4Run n P cel ((((val.push 1).push kc).push start).push P.kArity[kc]!) ev fs argA slots
                  mem mH 1 0 0 w st
              else g4Run n P cel val ev fs argA slots mem mH 2 0 0 maj st
      | 5 =>
        let na := g4CountArgs fs fs.size 0
        g4Run n P cel val ev (g4PopN fs na) argA slots mem mH 1 0 0 0 st
      | t =>
        -- a definition; tags 3 and 4 try literal acceleration first
        let na := g4CountArgs fs fs.size 0
        if t == 3 && na == 2 then
          let a := g4ArgAt fs 0
          let b := g4ArgAt fs 1
          g4Run n P cel val ev ((((((g4PopN fs 2).push k).push a).push b).push 5))
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
              let (o, P) := g4Comp find? findProj? P (v.instantiateLevelParams lps us)
              let P := let kc := P.kCode; let P := { P with kCode := #[] }
                { P with kCode := kc.set! k (o + 1) }
              g4Run n P cel val ev fs argA slots mem mH 3 pc env k st
            | _ => .stop (.internal "ground evaluation: a definition entry without its value") st
          else
          let body := P.kCode[k]! - 1
          if na > 0 then
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
      if fs.size == 0 then .done v val P slots (cel.size >>> 2) st n else
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
        | _ =>
          let na := g4CountArgs fs fs.size 0
          g4Run n P cel val ev (g4PopN fs na) argA slots mem mH 1 0 0 0 st
      | 3 =>
        let _len := fs[fs.size - 2]!
        let start := fs[fs.size - 3]!
        let k := fs[fs.size - 4]!
        match val[g4X4 v]! with
        | 2 =>
          if !P.natOk then .stop (.stuck "nat literal") st else
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
          if !P.strOk then .stop (.stuck "string literal") st else
          let sE := strLitToConstructor P.strs[val[g4X4 v + 1]!]!
          let (o, P) := g4Comp find? findProj? P sE
          g4Run n P cel val ev fs argA slots mem mH 0 o 0 0 st
        | 1 =>
          let kc := val[g4X4 v + 1]!
          let base := P.kC[k]!
          let nr := P.kD[k]!
          let ri := g4FindRule P.rNid P.kB[kc]! nr base
          if P.kTag[kc]! != 1 || ri == base + nr then .stop (.stuck "no rule") st else
          let nf := P.rNF[ri]!
          let cp := P.rCP[ri]!
          let ms := val[g4X4 v + 2]!
          if val[g4X4 v + 3]! != cp + nf then .stop (.stuck "ctor arity") st
          -- case 3 (a family that may be `Prop`): `Red.iota` asks for the
          -- constructor's full-grade certificates, which the engine does not
          -- build: a decline (task #423 soundness, ruling 4)
          else if P.rC3[ri]! != 0 then .stop (g4DeclineCase3 (P.entryName k)) st
          else if P.ruleCode[ri]! == 0 then
            -- compile the rule's right-hand side, then return again
            match P.kInfo[k]! with
            | .recr _ lps us _ _ _ _ _ _ =>
              let rhsE := P.rules[ri]!.rhs.instantiateLevelParams lps us
              let (o, P) := g4Comp find? findProj? P rhsE
              let P := let rc := P.ruleCode; let P := { P with ruleCode := #[] }
                { P with ruleCode := rc.set! ri (o + 1) }
              g4Run n P cel val ev fs argA slots mem mH 1 0 0 v st
            | _ => .stop (.internal "ground evaluation: a recursor entry without its rules") st
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
        | 5 =>
          -- a neutral major (stuck, or a proof the compiler erased): at a
          -- single-rule recursor the incumbent's K, structure-η or `And`
          -- rescue would read its type, which the engine does not compute;
          -- the K step (`kE`) never gets here.  A decline (task #423
          -- soundness, ruling 4); elsewhere the redex is stuck.
          let fl := P.kE[k]!
          if fl % 2 == 1 then .stop (g4DeclineStuckMajor (P.entryName k) true) st
          else if fl / 2 % 2 == 1 then .stop (g4DeclineStuckMajor (P.entryName k) false) st
          else g4Run n P cel val ev (g4PopN fs 4) argA slots mem mH 1 0 0 0 st
        | _ => g4Run n P cel val ev (g4PopN fs 4) argA slots mem mH 1 0 0 0 st
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
          else .stop (.stuck "proj shape") st
        | 3 =>
          if !P.strOk then .stop (.stuck "string literal") st else
          let sE := strLitToConstructor P.strs[val[g4X4 v + 1]!]!
          let (o, P) := g4Comp find? findProj? P sE
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
        -- literal acceleration: `[k, a, b, 5]` reads the first
        -- argument, `[k, n₁, a, b, 6]` the second
        let first := t == 5
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
            g4Run n P cel val ev (((((fs.push k).push m).push a).push b).push 6)
              argA slots mem mH 2 0 0 b st
          else
            let k := fs[fs.size - 5]!
            let m₁ := fs[fs.size - 4]!
            let fs := g4PopN fs 5
            let op := P.kE[k]!
            if (op == 3 || op == 12) && g4NatPreRefuses maxNat op m₁ m then .stop (.refuse op m₁ m false) st else
            match g4NatKind op with
            | 0 =>
              let r := g4NatVal op m₁ m
              if op ≤ 2 && g4SizeOver maxNat r then .stop (.refuse op m₁ m true) st else
              let w := (val.size >>> 2)
              g4Run n P cel ((((val.push 2).push r).push 0).push 0) ev fs argA slots
                mem mH 1 0 0 w st
            | 1 =>
              let kb := if g4NatVal op m₁ m == 1 then P.kTrue else P.kFalse
              let w := (val.size >>> 2)
              g4Run n P cel ((((val.push 1).push kb).push 0).push 0) ev fs argA slots mem mH
                1 0 0 w st
            | _ => .stop (.internal "ground evaluation: an operation of no kind") st
        | _ =>
          -- no literal: unfold the operation (`reduceNat` fails, δ)
          let k := fs[fs.size - (if first then 4 else 5)]!
          let a := fs[fs.size - 3]!
          let b := fs[fs.size - 2]!
          let fs := g4PopN fs (if first then 4 else 5)
          -- the operation's tag is 3; dispatch it as a plain definition
          g4Run n P cel val ev
            ((fs.push (g4Tag b 1)).push (g4Tag a 1)) argA slots mem mH 3 1 0 k st
end



/-- The program a site run starts from: the kept one, or (none kept) a fresh
one with the four basis entries resolved. -/
@[inline] def g4Setup (find? : Name → Option ConstantInfo)
    (findProj? : Name → Nat → Option ProjEntry) (natOk strOk : Bool) (P₀ : G4Prog) :
    G4Prog :=
  if P₀.kTag.size == 0 then
    let P : G4Prog := { natOk := natOk, strOk := strOk }
    let (kT, P) := g4Resolve find? findProj? P boolTrueName []
    let (kF, P) := g4Resolve find? findProj? P boolFalseName []
    let (kZ, P) := g4Resolve find? findProj? P natZeroName []
    let (kS, P) := g4Resolve find? findProj? P natSuccName []
    { P with kTrue := kT, kFalse := kF, kZero := kZ, kSucc := kS }
  else P₀

/-- The engine's answer at the `Bool.true` comparison: `true`, `false`, or
a stop.  **The compiled program can be kept for the declaration**: `P₀` is the program the declaration's earlier runs compiled
(empty at the first; `CState.ground4`, flushed with the other
environment-dependent memos).  The result carries the program back.
`maxNat` is the maximum `Nat` size: `some` the cached core's
`--max-nat-size`, `none` (the specification's run) no bound. -/
def ground4BoolCoreF (find? : Name → Option ConstantInfo)
    (findProj? : Name → Nat → Option ProjEntry) (natOk strOk : Bool) (maxNat : Option Nat) (fuel : Nat)
    (P₀ : G4Prog) (e : Expr) :
    (Except G4Stop Bool × (Nat × Nat)) × G4Prog :=
  let P : G4Prog := g4Setup find? findProj? natOk strOk P₀
  let (o, P) := g4Comp find? findProj? P e
  let r : Except G4Stop Bool × (Nat × Nat) × G4Prog :=
    let sl := P.slotA
    let P := { P with slotA := #[] }
    match g4Run find? findProj? maxNat fuel P #[2, 0, 0, 0] #[5, 0, 0, 0] #[] #[] #[] sl #[]
      (Array.replicate 1024 0) 0 o 0 0 0 with
  | .done v val P sl cells st left =>
    -- the next run's epoch is above every slot entry this run wrote
    -- (`epBase + c`, `c` a cell of this run)
    let P := { P with slotA := sl, epBase := P.epBase + cells }
    let tr := fuel - left
    -- `Bool.true` is the answer `true`; any other value (`Bool.false`, a
    -- stuck neutral, an ill-typed constructor) is `false`: `Bool` has no η,
    -- unit or proof-irrelevance rule
    if val[g4X4 v]! == 1 && val[g4X4 v + 3]! == 0 && val[g4X4 v + 1]! == P.kTrue then
      (.ok true, (st, tr), P)
    else (.ok false, (st, tr), P)
  -- (a stop drops the program: keeping the pre-run one alive across the
  -- run would share it, and every compile during the run would copy it)
  | .stop (.stuck _) st => (.ok false, (st, 0), {})
  | .stop why st => (.error why, (st, 0), {})
  ((r.1, r.2.1), r.2.2)

/-- `ground4BoolCoreF` at the engine's fuel (`groundFuel`). -/
def ground4BoolCore (find? : Name → Option ConstantInfo)
    (findProj? : Name → Nat → Option ProjEntry) (natOk strOk : Bool) (maxNat : Option Nat) (P₀ : G4Prog)
    (e : Expr) :
    (Except G4Stop Bool × (Nat × Nat)) × G4Prog :=
  ground4BoolCoreF find? findProj? natOk strOk maxNat groundFuel P₀ e

def ground4Bool (fe : FEnv) (maxNat : Nat) (P₀ : G4Prog) (e : Expr) :
    (Except G4Stop Bool × (Nat × Nat)) × G4Prog :=
  ground4BoolCore fe.find? fe.findProj? (natLitStoredF fe) (strLitStoredF fe) (some maxNat) P₀ e

end ConLeche

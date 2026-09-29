module
public import ConLeche.Kernel.Inductives.BlockInstallF


@[expose] public section

/-!
# The recursor stage's class kit

The pieces of the generated recursor stage (`genRecCheck`,
`GenRec.lean`, charter item 5) that concern a recursor's CLASS — the
inductive application `I.{us} D⃗` its major premise eliminates, a
member of the block or (a nested block's container) any other stored
inductive at one of the block's auxiliary types — and the recursors'
record pins:

* the member abstraction (`targetAbs`, the holes of charter item 2) and
  the per-component class match (`targetClassMatch`), which ties a class
  to the positivity check's recorded instantiations (`targetMajorNfs`)
  and a recursive field's walked leaf to its class (node agreement,
  K.53′, `targetK53`);
* a class resolved from a recursor's major domain (`targetMajorOf`,
  `TargetMajor`) and an outside class's parameters typed
  (`targetMajorPins`);
* the recursor records' pins (`targetRecPins`);
* the stored family's formats (`tgtRs`, `tgtStoredRules`,
  `consBlockRecsTF`) and the container bit (`blockNestedBit`).

Everything is written over an `FEnv`, parameterised by `ShadowOps` (the
operations at an index, a flush, the walkers), so the pure install
(`ShadowOps.ofOps`), the unit tests and the cached fold (`shadowOpsC`,
`ConLeche/Cached/CheckerC.lean`) run the same code.
-/

namespace ConLeche

/-- **The operations the shadow runs on**, per index: the checker's
entry points at an `FEnv` (`opsAt`), their rule-annotation variant
(`opsRuleR`: the cached one flushes at the two environment transitions
a rule makes, `sharedOpsRuleR`), the flush at an environment change,
and the syntactic walkers.  The pure instantiation ignores the index
(the pure operations read the `Env` they are handed); the cached one
is index-bound. -/
structure ShadowOps (m : Type → Type) where
  opsAt : FEnv → CheckerOps m
  opsRuleR : FEnv → CheckerOps m
  flush : m Unit
  walkers : StructWalkers

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- A checker's operations as shadow operations: the same at every
index, no flush, the plain walkers — how the PURE install runs the
check (`checkBlockRec`, `BlockTail.lean`). -/
def ShadowOps.ofOps (ops : CheckerOps m) : ShadowOps m :=
  ⟨fun _ => ops, fun _ => ops, Pure.pure (), .plain⟩

/-- The pure operations at fuel `F`, at every index (the fueled
instantiation the model reads a run of). -/
def ShadowOps.fueled (mode : CheckMode) (F : Nat) : ShadowOps CheckM :=
  ShadowOps.ofOps (fueledOps mode F)

/-! ## The holes: the block's members abstracted to free variables

Charter item 2: *the holes are ordinary open terms (members abstracted
to fvars)*.  A call's typing (the field is a value of the callee's
major type) is checked on the member-ABSTRACTED terms, not on the
concrete ones, because that is the only form whose soundness says
something at the model's SEPARATED tuple: a defeq run on the concrete
terms (members as constants, read as their carriers) equates the two
readings at the carrier alone, and the graph recursor's induction
(`GraphRecKit.ind`, via the recorded lfp clause) needs the called field
to land in the separated tuple — "the field is a hole at the callee's
class", which no carrier-level equation gives.  On the abstract
terms the same defeq holds at EVERY value of the holes, the separated
tuple included.

Member `t` at the block's levels becomes `.fvar (base + t) T_t.type`
(the former's own closed type, so the hole is applied to the
parameters exactly as the member was); a member at other levels stays
a constant.  A free variable's ANNOTATION is not abstracted: the
frame's fields keep their concrete types (a field's value fits them at
the carrier, and the separated tuple lies below it), so a hole occurs
in the abstract term only where the term itself names a member, and a
hole-free abstract term IS a concrete one.  Memoised on the node (tower-shaped DAG fields,
`tower_struct`).  It is NOT `replaceConsts`
(`Kernel/ExprOps.lean`) at the member map, on purpose: that one
rewrites free variables' annotations too, and here the frame's fields
must keep their concrete types (see below) — an abstracted annotation
would make every domain that names an earlier recursive field look
holed, and put hole variables into the `ih` types.  The call's TYPING,
though, reads the fields' annotations at the holes too, as the
positivity check does: it runs at the abstract frame, where each field is
moved to a copy past the holes whose annotation is abstracted
(`targetMoveF`, `targetAbsFields`, F-RPW-1). -/

/-- The member abstraction of one term: every member at the block's
levels becomes its hole; `fvar` annotations are not entered. -/
def targetAbs (names : List Name) (lvls : List Level) (holes : List Expr) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar i ty => .fvar i ty
  | .sort u => .sort u
  | .lit l => .lit l
  | e@(.const n us) =>
    if us == lvls then
      match names.findIdx? (· == n) with
      | some t => holes.getD t e
      | none => e
    else e
  | .app a b => .app (targetAbs names lvls holes a) (targetAbs names lvls holes b)
  | .lam ty body bm => .lam (targetAbs names lvls holes ty) (targetAbs names lvls holes body) bm
  | .forallE ty body bm =>
    .forallE (targetAbs names lvls holes ty) (targetAbs names lvls holes body) bm
  | .letE ty v body =>
    .letE (targetAbs names lvls holes ty) (targetAbs names lvls holes v)
      (targetAbs names lvls holes body)
  | .proj s i sub => .proj s i (targetAbs names lvls holes sub)

/-- The memo's invariant: every recorded answer is the real one. -/
def TargetAbsMemoInv (names : List Name) (lvls : List Level) (holes : List Expr)
    (memo : Std.HashMap Expr Expr) : Prop :=
  ∀ k v, memo[k]? = some v → v = targetAbs names lvls holes k

theorem TargetAbsMemoInv.insert {names : List Name} {lvls : List Level} {holes : List Expr}
    {memo : Std.HashMap Expr Expr}
    (hm : TargetAbsMemoInv names lvls holes memo) {e r : Expr}
    (heq : r = targetAbs names lvls holes e) :
    TargetAbsMemoInv names lvls holes (memo.insert e r) := by
  intro k v hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact heq
  · exact hm k v hk

/-- The member abstraction, memoised on the node (tower DAGs). -/
def targetAbsGo (names : List Name) (lvls : List Level) (holes : List Expr)
    (memo : Std.HashMap Expr Expr) : Expr → Expr × Std.HashMap Expr Expr
  | e@(.bvar _) => (e, memo)
  | e@(.sort _) => (e, memo)
  | e@(.lit _) => (e, memo)
  | e@(.fvar _ _) => (e, memo)
  | e@(.const n us) =>
    if us == lvls then
      match names.findIdx? (· == n) with
      | some t => (holes.getD t e, memo)
      | none => (e, memo)
    else (e, memo)
  | e =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Expr × Std.HashMap Expr Expr :=
        match e with
        | .app a b =>
          let (a', memo) := targetAbsGo names lvls holes memo a
          let (b', memo) := targetAbsGo names lvls holes memo b
          (.app a' b', memo)
        | .lam ty body bm =>
          let (t, memo) := targetAbsGo names lvls holes memo ty
          let (b, memo) := targetAbsGo names lvls holes memo body
          (.lam t b bm, memo)
        | .forallE ty body bm =>
          let (t, memo) := targetAbsGo names lvls holes memo ty
          let (b, memo) := targetAbsGo names lvls holes memo body
          (.forallE t b bm, memo)
        | .letE ty v body =>
          let (t, memo) := targetAbsGo names lvls holes memo ty
          let (v', memo) := targetAbsGo names lvls holes memo v
          let (b, memo) := targetAbsGo names lvls holes memo body
          (.letE t v' b, memo)
        | .proj s i sub =>
          let (u, memo) := targetAbsGo names lvls holes memo sub
          (.proj s i u, memo)
        | e => (e, memo)
      (r, memo.insert e r)

/-- **The memoised walk is `targetAbs`.** -/
theorem targetAbsGo_spec {names : List Name} {lvls : List Level} {holes : List Expr} :
    ∀ (e : Expr) {memo : Std.HashMap Expr Expr}, TargetAbsMemoInv names lvls holes memo →
      (targetAbsGo names lvls holes memo e).1 = targetAbs names lvls holes e ∧
        TargetAbsMemoInv names lvls holes (targetAbsGo names lvls holes memo e).2 := by
  intro e
  induction e with
  | bvar i => intro memo hm; exact ⟨rfl, hm⟩
  | sort u => intro memo hm; exact ⟨rfl, hm⟩
  | lit l => intro memo hm; exact ⟨rfl, hm⟩
  | fvar i ty _ => intro memo hm; exact ⟨rfl, hm⟩
  | const n us =>
    intro memo hm
    simp only [targetAbsGo, targetAbs]
    split
    · split <;> exact ⟨rfl, hm⟩
    · exact ⟨rfl, hm⟩
  | app a b iha ihb =>
    intro memo hm
    rw [targetAbsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iha hm
      obtain ⟨h3, h4⟩ := ihb h2
      refine ⟨by simp [targetAbs, h1, h3], ?_⟩
      exact h4.insert (by simp [targetAbs, h1, h3])
  | lam ty body m iht ihb =>
    intro memo hm
    rw [targetAbsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      obtain ⟨h3, h4⟩ := ihb h2
      refine ⟨by simp [targetAbs, h1, h3], ?_⟩
      exact h4.insert (by simp [targetAbs, h1, h3])
  | forallE ty body m iht ihb =>
    intro memo hm
    rw [targetAbsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      obtain ⟨h3, h4⟩ := ihb h2
      refine ⟨by simp [targetAbs, h1, h3], ?_⟩
      exact h4.insert (by simp [targetAbs, h1, h3])
  | letE ty v body iht ihv ihb =>
    intro memo hm
    rw [targetAbsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      obtain ⟨h3, h4⟩ := ihv h2
      obtain ⟨h5, h6⟩ := ihb h4
      refine ⟨by simp [targetAbs, h1, h3, h5], ?_⟩
      exact h6.insert (by simp [targetAbs, h1, h3, h5])
  | proj s i sub ih =>
    intro memo hm
    rw [targetAbsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := ih hm
      refine ⟨by simp [targetAbs, h1], ?_⟩
      exact h2.insert (by simp [targetAbs, h1])

/-- The executed member abstraction (one memoised DAG walk). -/
def targetAbsFast (names : List Name) (lvls : List Level) (holes : List Expr) (e : Expr) : Expr :=
  (targetAbsGo names lvls holes {} e).1

@[csimp] theorem targetAbs_eq_targetAbsFast : @targetAbs = @targetAbsFast := by
  funext names lvls holes e
  exact (targetAbsGo_spec e (fun k v h => by simp at h)).1.symm

/-- The holes of a rule frame of width `base`: member `t` is
`.fvar (base + t)` at its former's type. -/
def targetHoles (formerTys : List Expr) (base : Nat) : List Expr :=
  (List.range formerTys.length).map fun t => .fvar (base + t) (formerTys.getD t default)

/-! ## The major -/

/-- **A recursor's major, resolved.**  `ind.{lvls} ds ı⃗` with `ds`
the inductive's parameters at the recursor's own binders (fvars
`0 … nP-1`), `nPc` its parameter count, `nIdx` its index count at that
instantiation, `ctors` its constructors in declaration order with their
field counts, and `member` the block member it is (`none`: an outside
inductive — a nested block's container). -/
structure TargetMajor where
  ind : Name
  lvls : List Level
  ds : List Expr
  nPc : Nat
  nIdx : Nat
  ctors : List (ConstantVal × Nat)
  member : Option Nat
  /-- the positivity walk's recorded normal forms of this class's
  constructors (`targetMajorNfs`, K.53′) -/
  nfs : List NestCtorNf := []
  /-- the recursor's prefix openers (fvars `0 … rP-1`, the parameters
  first), the context the class is compared in (`targetClassMatch`) -/
  pfvs : List Expr := []
  deriving Inhabited

/-- A term with every free variable's ANNOTATION erased (the variable
kept): the comparison K.53′ runs up to, which is exactly what the model's
interpretation never reads (`Expr.ErasedEq`). -/
def Expr.eraseFVarTys (e : Expr) : Expr :=
  e.replaceFVars fun i => some (.fvar i (.sort .zero))

/-! ### Matching a class against a node, per component

A recursor class `I.{us} D⃗` and an instantiation the positivity check
recorded (a node's key, or a constructor entry's `(lvls, ds)`, read back:
holes as their constants, the parameters at the walk's canonical
variables) MATCH when they agree PER COMPONENT (ruling 2026-09-27): the
levels by `Level.isEquivList`, every parameter by the kernel's defeq —
the block's members abstracted to their holes on both sides
(`targetAbs`, the holes after the class's recursor prefix), every
parameter variable moved to the class's own opener of that index
(`targetCanonParams`, so both sides live over one context whatever
annotations their variables carry), both sides inferred first.  The head is
compared by the caller.  Whole-application defeq would not do: at `Prop`
two instances read alike (`P Nat`, `P Bool`: both `{pt}`) without
sharing a frame; per component, the frames agree at every value of the
holes.  The two comparisons of the recursor check against the
positivity check — the class's recorded normal forms, a call's callee
against its field (K.53′) — both run this one function, so a match
found at one is a match at the other.  (A class is a node of the walk by
construction — its seed, `checkBlockSeeds` — and matches that node's key
syntactically, up to the free variables' annotations.) -/

/-- A term over the walk's canonical parameter variables, moved to the
class's openers `pfvs` (variables `0 … |pfvs|-1`, the rest kept). -/
def targetCanonParams (pfvs : List Expr) (e : Expr) : Expr :=
  e.replaceFVars fun i => pfvs[i]?

/-- **Per-component parameter defeq** at depth `d`, each side moved to
the openers and member-abstracted by `absM`: syntactically equal, or
inferred and defeq; both sides must be closed over the parameters (no loose bound
variable, no free variable past the openers — anything else is no
parameter of an instantiation and matches nothing). -/
def targetParamsDefEq (ops : CheckerOps m) (env : Env) (d : Nat) (absM : Expr → Expr)
    (pfvs : List Expr) : List Expr → List Expr → m Bool
  | [], [] => pure true
  | a :: as, b :: bs => do
    if a.bvarB == 0 && b.bvarB == 0 && a.fvarB ≤ pfvs.length && b.fvarB ≤ pfvs.length then
      let a' := absM (targetCanonParams pfvs a)
      let b' := absM (targetCanonParams pfvs b)
      if a' == b' then targetParamsDefEq ops env d absM pfvs as bs
      else
        let _ ← ops.inferType env d a'
        let _ ← ops.inferType env d b'
        if ← ops.isDefEq env d a' b' then targetParamsDefEq ops env d absM pfvs as bs
        else pure false
    else pure false
  | _, _ => pure false

/-- **A class matches a recorded instantiation `(lvls, ds)`** (see the
section header): levels up to `Level.isEquivList`, parameters pairwise
defeq with the members abstracted — over the class's recursor prefix
`pfvs` with the holes on top (depth `|pfvs| + k`). -/
def targetClassMatch (ops : CheckerOps m) (env : Env) (p : BlockShape) (formerTys : List Expr)
    (pfvs : List Expr) (us : List Level) (ds : List Expr) (lvls : List Level) (eds : List Expr) :
    m Bool := do
  unless Level.isEquivList us lvls == some true do return false
  targetParamsDefEq ops env (pfvs.length + formerTys.length)
    (targetAbs p.memberNames (p.lps.map .param) (targetHoles formerTys pfvs.length)) pfvs ds eds

/-- **The walk's recorded constructor normal forms of a class** (K.53′):
the entries (the table `checkBlockSeeds` returns) of the class's constructors `ctors`
whose instantiation the class matches (`targetClassMatch`). -/
def targetMajorNfs (ops : CheckerOps m) (env : Env) (p : BlockShape) (formerTys : List Expr)
    (pfvs : List Expr) (us : List Level) (ds : List Expr) (ctors : List (ConstantVal × Nat)) :
    List NestCtorNf → m (List NestCtorNf)
  | [] => pure []
  | e :: es => do
    let rest ← targetMajorNfs ops env p formerTys pfvs us ds ctors es
    if ctors.any (·.1.name == e.ctor) then
      if ← targetClassMatch ops env p formerTys pfvs us ds e.lvls e.ds then pure (e :: rest)
      else pure rest
    else pure rest

/-- The constructors of a stored inductive `I` and its parameter count,
read off the environment (`nestContainer`'s reading: a constructor
belongs to the type its result names). -/
def targetCtorsOf (fe : FEnv) (I : Name) : Option (Nat × List (ConstantVal × Nat)) :=
  nestContainer ⟨[], [], 0, [], [], .zero, fe.find?, fe.env.consts⟩ I

/-- The instantiated type former of an OUTSIDE major `I.{us} ds`: its
index count and its result sort (a syntactic telescope, as
`nestInstType` reads it). -/
def targetOutsideInst (fe : FEnv) (I : Name) (us : List Level) (ds : List Expr) :
    m (Nat × Level) := do
  let some (.indInfo cvI _) := fe.find? I
    | throw (.invalid "target rec: the recursor's major is not a stored inductive")
  let some ty := instPisWith ds (cvI.type.instantiateLevelParams cvI.levelParams us)
    | throw (.invalid "target rec: the major's type former does not bind its parameters \
        (official: ill-formed inductive type)")
  let (ibs, s) := ty.piBinders
  let .sort s := s
    | throw (.invalid "target rec: the major's type former is not a telescope ending in a \
        sort (official: type expected)")
  pure (ibs.length, s)

/-! ## A recursor's class, resolved -/

/-- **A recursor's major, resolved** from its opened type `mty`
(`fvs` the recursor type's openers): a MEMBER of the block at the
block's levels and parameters, or — a nested block's container — any
other stored inductive at one of the block's auxiliary types. -/
def targetMajorOf (fe : FEnv) (p : BlockShape)
    (ctorsAs : List (List (ConstantVal × Nat))) (pfvs fvs : List Expr)
    (mty : Expr) : m TargetMajor := do
  let args := mty.getAppArgs
  match mty.getAppFn with
  | .const I us =>
    match p.memberNames.findIdx? (· == I) with
    | some t => do
      -- a MEMBER: at the block's levels and parameters
      let ms ← unwrapOr p.members[t]? (.internal "target rec: member")
      let ctorsA ← unwrapOr ctorsAs[t]? (.internal "target rec: member constructors")
      unless us == p.lps.map .param && args.take p.nP == fvs.take p.nP do
        throw (.invalid "target rec: the recursor's major premise is not the member at its \
          parameters and its index binders")
      pure { ind := I, lvls := us, ds := fvs.take p.nP, nPc := p.nP, nIdx := ms.nIdx,
             ctors := ctorsA, member := some t, pfvs := pfvs : TargetMajor }
    | none => do
      -- an OUTSIDE inductive (a nested block's container)
      if I == quotName then
        throw (.invalid "target rec: the recursor's major is Quot, which is no inductive")
      let some (nPc, ctors) := targetCtorsOf fe I
        | throw (.invalid "target rec: the recursor's major is not a stored inductive")
      let ds := args.take nPc
      unless ds.length == nPc &&
          ds.all (fun x => x.bvarB == 0 && x.fvarB ≤ p.nP) do
        throw (.invalid "target rec: the major's parameters mention more than the \
          recursor's parameters")
      -- **An auxiliary type of the block**, official's `is_nested`: some
      -- parameter `Dᵢ` names a member of the block (`inductive.cpp` v4.34.0
      -- :1033–1049: `find` over each of the `nparams` arguments for a
      -- constant of `m_new_types`; every auxiliary type is such an
      -- application, restored verbatim by `restore_nested`, and official
      -- accepts an auxiliary recursor exactly at an auxiliary type).  The
      -- calls' proof reads it: a call on a field whose walked type names no
      -- member and no hole targets no class.  Read without whnf and without
      -- entering a free variable's annotation (`nestOcc` at an empty hole
      -- range).  Every class resolved here SEEDS the positivity walk
      -- (`checkBlockSeeds`, after stage (b)), so it is a node of the walk by
      -- construction: nothing ties it to a node here.
      unless ds.any (fun x => x.nestOcc p.memberNames 0 0) do
        throw (.invalid "target rec: the recursor's major is an outside inductive at an \
          instantiation that is no auxiliary type of the block (official generates no such \
          auxiliary recursor: `elim_nested_inductive`, `is_nested`)")
      let (nIdx, sI) ← targetOutsideInst fe I us ds
      -- **Q1**: an outside major in ANOTHER
      -- universe than the block (a Type block's family eliminating a
      -- Prop inductive, or the converse) is refused here: the
      -- elimination guard is the BLOCK's (`blockLargeElimAllowed`),
      -- and it says nothing about another universe's inductive
      unless ← liftFueled "level comparison" (Level.isEquiv sI p.resSort) do
        throw (.invalid "target rec: the recursor's major lives in another universe than \
          the block (Q1)")
      pure { ind := I, lvls := us, ds := ds, nPc := nPc, nIdx := nIdx, ctors := ctors,
             member := none, pfvs := pfvs }
  | _ => throw (.invalid "target rec: the recursor's major premise is not an inductive's \
      application")

/-- **An outside major's parameters, typed at the rule prefix**:
each `D_i` of the major
`I.{us} D⃗ ı⃗`, at the depth of the rule prefix `rP` (the `D⃗` mention only
the parameter binders).  The recursor type's own check types them only
under the index binders, which may be uninhabited; the rule law of an
auxiliary recursor's `.nested` rules (`RecRuleLaw`, `EnvWF`'s pins) reads
the pins graded at the prefix itself.  It refuses nothing the recursor
type's check (`checkConstantValF`) accepted: the `D⃗` are closed over
binders below `rP`, so their typing does not depend on the index
binders.  Official types the same terms as the auxiliary constructors'
parameters (`check_constructors`, `tc().check`, `inductive.cpp`
v4.33.0 :426, after `elim_nested_inductive` instantiates the container's
constructors at them). -/
def targetPinTys (ops : CheckerOps m) (env : Env) (d : Nat) : List Expr → m Unit
  | [] => pure ()
  | x :: xs => do
    let _ ← ops.inferType env d x
    targetPinTys ops env d xs

/-- The check at a resolved major: an outside major's parameters typed
at the rule prefix (`targetPinTys`), and — for the model's rows
`hdec`/`hrule` — the instantiation `I.{us} D⃗` itself
typed there, so the `D⃗` SATISFY the container's parameter telescope at
the instantiation (the application's typing checks each `D_i` against
the telescope's domain instantiated at the earlier ones).  Official checks
exactly this term: `tc.check(nested, …)` on every replaced nested
application `I Ds` in the parameters' context (`inductive.cpp` v4.33.0
:1223–1231, "the parametric arguments `Ds` do not appear in the auxiliary
declaration, so they would otherwise escape type checking"); the `D⃗`
mention only the parameter binders, below `rP`.  Nothing at a member. -/
def targetMajorPins (ops : CheckerOps m) (env : Env) (rP : Nat) (M : TargetMajor) : m Unit :=
  if M.member.isNone then do
    targetPinTys ops env rP M.ds
    let _ ← ops.inferType env rP (Expr.mkAppN (.const M.ind M.lvls) M.ds)
    pure ()
  else pure ()

/-! ## The recursor records' pins -/

/-- **The recursor records' pins** (at any major).
The level parameters and the reserved names; the NAMES: the
recursors whose major is a member carry the set `{T_m.rec}`; the others (a
nested block's auxiliaries) carry pairwise
distinct names `T_0.rec_1 … T_0.rec_n` (official's naming, as a set).
The block's constructors in the stream's order are the members' in
block order (the grouping).  The rule pins need
the majors' constructors and are `targetRulePins`. -/
def targetRecPins (p : BlockShape) (block : List ConstantInfo) : m Unit := do
  unless blockRecLpsOk p do
    throw (.invalid "target rec: the recursor's level parameters are not the generated ones")
  unless blockRecNamesUnreserved p do
    throw (.invalid "target rec: a recursor is named for a pinned basis constant, a literal \
      guard's slot or a certified Nat operation")
  let own := p.recs.filter fun rc => rc.tgt < p.k
  let aux := p.recs.filter fun rc => !(rc.tgt < p.k)
  unless blockRecNameSetOk { p with recs := own } do
    throw (.invalid "target rec: the block's recursor names are not the generated ones \
      (one T.rec per member)")
  let n0 := (p.memberNames.head?).getD .anonymous
  let wantAux := (List.range aux.length).map fun i => n0.str s!"rec_{i + 1}"
  let gotAux := aux.map (·.cvR.name)
  unless gotAux.length == wantAux.length && wantAux.all (gotAux.contains ·) &&
      gotAux.all (wantAux.contains ·) do
    throw (.invalid "target rec: the block's auxiliary recursor names are not the generated \
      ones (T.rec_1 … T.rec_n)")
  -- the family's names are distinct (official: a duplicate declaration).
  -- Implied by the two name sets above (the generated names are
  -- distinct); stated here because the install conses the family one
  -- name at a time
  unless (p.recs.map (·.cvR.name)).Nodup do
    throw (.invalid "target rec: two recursors of the block share a name")
  match blockSplit block with
  | some (cvTs, cs, rs) =>
    unless cvTs.length == p.k && rs.length == p.recs.length &&
        p.allCtors.map (·.1.name) == cs.map (·.1.name) do
      throw (.invalid "target rec: the recursor record is not the generated recursor \
        (constructor grouping)")
  | none => throw (.invalid "target rec: the block does not split")

/-! ## A class's constructors, and node agreement (K.53′) -/

/-- A constructor's type at the major's LEVELS: a member's is stored at
the block's own level parameters, which the recursor shares; an outside
inductive's is instantiated at the major's. -/
def targetCtorAt (M : TargetMajor) (c : ConstantVal) : Expr :=
  match M.member with
  | some _ => c.type
  | none => c.type.instantiateLevelParams c.levelParams M.lvls

/-- **K.53′ at one recorded field** `f` (a walked normal form of the
called field, read back and opened at the rule's fields): its telescope is
the call's `tele` and its leaf the callee's major `majDom`, the telescope
and the major's head and indices up to the free variables' annotations,
the major's CLASS per component (`targetClassMatch` against the callee's
class `Mc`: levels up to equivalence, parameters defeq with the members
abstracted), and the leaf names a member (official's `is_nested`: the
callee's class does, and so does official's auxiliary type). -/
def targetK53 (ops : CheckerOps m) (env : Env) (p : BlockShape) (formerTys : List Expr)
    (Mc : TargetMajor) (tele : List (Expr × BinderMeta)) (majDom f : Expr) : m Bool :=
  match f.stripPis tele.length with
  | none => pure false
  | some (teleW, leafW) =>
    if teleW.map (fun b => (b.1.eraseFVarTys, b.2)) != tele.map (fun b => (b.1.eraseFVarTys, b.2))
    then pure false
    else
      match leafW.getAppFn, majDom.getAppFn with
      | .const I' us', .const I _ =>
        if I' == I && leafW.getAppArgs.length == majDom.getAppArgs.length &&
            (leafW.getAppArgs.drop Mc.nPc).map Expr.eraseFVarTys
              == (majDom.getAppArgs.drop Mc.nPc).map Expr.eraseFVarTys &&
            (Expr.mkAppN (.const I' us') (leafW.getAppArgs.take Mc.nPc)).nestOcc
              p.memberNames 0 0 then
          targetClassMatch ops env p formerTys Mc.pfvs Mc.lvls Mc.ds us'
            (leafW.getAppArgs.take Mc.nPc)
        else pure false
      | _, _ => pure false

/-- The domains of the first `|xs|` `∀` binders, each instantiated at the
earlier `xs` (a telescope's field types at given field variables). -/
def targetPiDomsWith : List Expr → Expr → Option (List Expr)
  | [], _ => some []
  | x :: xs, .forallE d b _ => (d :: ·) <$> targetPiDomsWith xs (b.instantiate1 x)
  | _ :: _, _ => none

/-! ## The stored family -/

/-- **The stored family, in the install's recursor-list format**: each
checked recursor, its annotated rules, its major's index count and its
major's constructors (`consBlockRecs` conses them). -/
def tgtRs (out : List (ConstantVal × TargetMajor × List Expr)) :
    List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)) :=
  out.map fun t => (t.1, t.2.2, t.2.1.nIdx, t.2.1.ctors)

/-- **The firing mode of a rule at an OUTSIDE major**: the
syntactic reading of the recursor type's major domain
(`Expr.nestedRuleSyn`, the major's parameter count `nPc`, constants
resolving by `resolves`) — `.nested lvls pins`, with `pins` the major's
parameters lowered into the rule-prefix context, whose guards are
`EnvWF`'s `.nested` clause (`nestedRuleSyn_inv`); `.inert` when the
reading fails (a matched major then declines at fire time; measured
never to happen at a checked outside major). -/
def auxRuleFireR (resolves : Expr → Bool) (cv : ConstantVal) (mI rP nPc : Nat) : RecRuleFire :=
  match Expr.nestedRuleSyn resolves cv.levelParams cv.type mI rP nPc with
  | some (lvls, pins) => .nested lvls pins
  | none => .inert

/-- **One checked recursor's stored rules, at its major**: `sumRules` at the
MAJOR's parameter count and constructors;
at an OUTSIDE major (a nested block's auxiliary recursor) every rule
fires as `auxRuleFireR` reads it (`.nested` at the major's
instantiation), at a member major as `sumRules` builds it. -/
def tgtStoredRules (find? : Name → Option ConstantInfo) (resolves : Expr → Bool)
    (cv : ConstantVal) (mI rP : Nat) (M : TargetMajor) (rhss : List Expr) : List RecRule :=
  let rules := sumRules find? cv.name M.nPc mI rP cv.type M.ctors rhss
  match M.member with
  | none => rules.map fun rl => { rl with fire := auxRuleFireR resolves cv mI rP M.nPc }
  | some _ => rules

/-- **The block's container bit** (official's `m_nested`):
some field kind is not flat (the positivity function reached a
container instantiation) or some recursor's major is not a member (the
family carries an auxiliary recursor).  It feeds the elimination guard
(`blockLargeElimAllowed`). -/
def blockNestedBit (p : BlockShape) (kinds : List (List (List NestFieldKind))) : Bool :=
  !nestKindsFlat kinds || p.recs.any (fun rc => !(rc.tgt < p.k))

/-- **The checked family consed through the index, at its majors**:
`consBlockRecsF` with each recursor's rules at ITS major
(`tgtStoredRules`) — the uniform route's recursor cons, which at member
majors is `consBlockRecsF` itself. -/
def consBlockRecsTF (find? : Name → Option ConstantInfo) (resolves : Expr → Bool)
    (p : BlockShape) : Nat → List (ConstantVal × TargetMajor × List Expr) → FEnv → FEnv
  | _, [], fe => fe
  | m, (cv, M, rhss) :: rest, fe =>
    consBlockRecsTF find? resolves p (m + 1) rest
      (fe.push (.recInfo cv (p.majorIdxAt m) (p.rulePrefixAt m)
        (tgtStoredRules find? resolves cv (p.majorIdxAt m) (p.rulePrefixAt m) M rhss)))

end ConLeche

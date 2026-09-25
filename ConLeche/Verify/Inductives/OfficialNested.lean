module

public import ConLeche.Kernel.Inductives.Positivity

@[expose] public section

/-!
# Official's nested elimination and positivity check, as a Lean SPEC (lane COMPLETE-2)

A faithful, small transcription of the two pieces of `inductive.cpp`
(Lean v4.34.0; line numbers below are that tag's file,
`git show v4.34.0:src/kernel/inductive.cpp`) that decide whether official
accepts a NESTED inductive's positivity:

* `elim_nested_inductive_fn` (:985–1180) — the SYNTACTIC replacement of
  every nested occurrence `I Ds is` by an auxiliary type `auxI As is`,
  whole-group copying, and the queue of new types run to a fixpoint
  (`elimNested`);
* the positivity slice of `add_inductive_fn::check_constructors`
  (:456–497) — `check_positivity` (:436–453) with `is_valid_ind_app`
  (:381–401) and `has_ind_occ` (:420), run on the AUXILIARY declaration
  (`checkCtorPos`, `OfficialPosAccepts`).

It is written over OUR `Expr`, with OUR kernel's `whnf` as the reduction
oracle (`PosOracle.whnf`: official's `tc().whnf` in the environment where
the declaration's types — members and auxiliary types — are opaque
inductive constants without constructors, `declare_inductive_types`
:360–375 having run before `check_constructors`).  A faithful
re-implementation of official's C++ whnf is out of scope; the relation
between this oracle and the walk's `ops.whnf` is the named hypothesis of
the completeness theorem (`PosDerivComplete.lean`).

## Deliberate simplifications (each verdict-neutral, argued)

* **Parameters.**  Official re-creates the parameters as fresh locals `As`
  per constructor (:1168, to keep binder infos) and maps them back to the
  shared `m_params` before comparing keys (`replace_params`, :1081).  Here
  every constructor is instantiated at the ONE list `ps` (the canonical
  parameter variables), so `replace_params` is the identity.  Binder infos
  are not observable by positivity.
* **Fresh names.**  `mk_unique_name` (:1001) avoids names in the
  environment; here the auxiliary names are `auxName i` for an abstract
  generator (freshness is a hypothesis of whoever instantiates the spec).
* **Constructor lists.**  Official reads `J_info.get_cnstrs()` (:1117);
  here the environment's constructors of `J` as the walk reads them
  (`nestContainer`: stored `.ctorInfo`s whose result is headed by `J`).
  On a well-formed environment these are the same set; the order only
  permutes the auxiliary constructors, which positivity checks one by one.
* **Index counts.**  Official counts the indices of each type by whnf-ing
  its type between binders (`check_inductive_types` :254); here the count
  is the syntactic `Π` count after the parameters (`piBinders`), as the
  walk's `nestInstType`/`nestArity` count.  Stored inductive types are
  syntactic telescopes; a member former behind δ is a separate, known
  gap (COMPLETE D-S), outside positivity.
* **Fuel.**  The queue loop and `check_positivity`'s recursion carry an
  explicit fuel (official has none); the spec ACCEPTS when it accepts at
  some fuel.
* **Locals.**  Official's fresh locals (`mk_local_decl_for` :444, :488)
  are free variables `.fvar i dom` numbered from a base `base` (any base
  above the parameters: official's verdict does not depend on the choice
  of fresh names).
* **Only positivity.**  `check_constructors`' typing (`tc().check`), the
  parameter defeq, the universe check and `check_inductive_types` are
  not transcribed: they are NOT positivity, and the completeness theorem
  carries the walk's corresponding checks (typing, N2, N3, U4) as a named
  side-condition hypothesis.  `check_uniform_ind_occs` (:134) IS
  transcribed (`uniformOcc`, lane COMPLETE-4): the containers passed it
  when official added them, which gives the walk its shape at a frame.
-/

namespace ConLeche

namespace Official

/-- One type of the declaration official checks (`inductive_type`): its
name, its former's type and its constructors' types, each with the
declaration's parameters ALREADY instantiated at the canonical `ps` (the
spec's `get_params`, :1155/:1168). -/
structure AuxType where
  name : Name
  type : Expr
  ctors : List Expr
  deriving Inhabited

/-- The environment official reads while eliminating: `m_env`'s lookups
(`find`, `get_all`, `get_cnstrs`) and the declaration's data. -/
structure ElimCtx where
  /-- `m_env.find` -/
  find? : Name → Option ConstantInfo
  /-- the constructors of an inductive (`get_cnstrs`, see the module doc) -/
  ctorsOf : Name → List (ConstantVal × Nat)
  /-- `m_lvls`: the declaration's level parameters as levels -/
  lvls : List Level
  /-- `m_params`: the canonical parameter variables -/
  ps : List Expr
  /-- `mk_unique_name`'s supply of fresh names -/
  auxName : Nat → Name

/-- The elimination's state: `m_nested_aux` (:991), `m_new_types` (:993),
`m_next_idx` (:994). -/
structure ElimSt where
  aux : List (Expr × Name) := []
  types : Array AuxType := #[]
  next : Nat := 1
  deriving Inhabited

/-- The elimination monad. -/
abbrev ElimM := StateT ElimSt (Except CheckError)

/-- "ill-formed declaration" (`throw_ill_formed` :1009). -/
def illFormed : CheckError := .invalid "official: invalid nested inductive datatype, ill-formed declaration"

/-- **`is_nested_inductive_app`** (:1023–1055): `e` is `I Ds is` with `I`
a previously declared inductive (not `Quot`: official's `is_inductive()`
is false on a quotient), at least `I`'s parameters as arguments, some
parameter mentioning a type of the declaration (`newNames`, the current
`m_new_types`); a parameter with a loose bound variable then THROWS.
Returns `(I, us, nparams, args)`. -/
def isNestedApp (c : ElimCtx) (newNames : List Name) (e : Expr) :
    Except CheckError (Option (Name × List Level × Nat × List Expr)) :=
  match e with
  | .app .. =>
    match e.getAppFn with
    | .const I us =>
      match c.find? I with
      | some (.indInfo _ caps) =>
        if I == quotName then pure none else
        let args := e.getAppArgs
        if args.length < caps.nparams then pure none else
        let ds := args.take caps.nparams
        -- :1039–1047 `is_nested`: a parameter mentions a new type (a constant
        -- of `m_new_types`; `find` does not look into locals' types)
        if !(ds.any (·.nestOcc newNames 0 0)) then pure none
        -- :1036–1038, :1051–1052: loose bound variables in a parameter throw
        else if ds.any (·.bvarB != 0) then
          throw (.invalid "official: nested inductive datatypes parameters cannot contain \
            local variables")
        else pure (some (I, us, caps.nparams, args))
      | _ => pure none
    | _ => pure none
  | _ => pure none

/-- `instantiate_pi_params` (:1057–1064): strip `n` binders, instantiate
them with `args` (no β).  The spec's `instPisWith`. -/
def instPiParams (e : Expr) (args : List Expr) : Except CheckError Expr :=
  match instPisWith args e with
  | some r => pure r
  | none => throw illFormed

/-- **Copy one container block** (:1100–1127): for every `J` of `I`'s
recorded block (`get_all()`), in order, a fresh auxiliary type whose
former is `J`'s at `us` and `Ds`, whose constructors are `J`'s at `us`
and `Ds` (still mentioning the containers: "fixed later when we process
it", :1120), recorded under the key `J Ds` (:1109). -/
def copyBlock (c : ElimCtx) (us : List Level) (ds : List Expr) : List Name → ElimM Unit
  | [] => pure ()
  | J :: Js => do
    let cvJ ← match c.find? J with
      | some (.indInfo cv _) => pure cv
      | _ => throw illFormed
    let st ← get
    let a := c.auxName st.next
    let ty ← instPiParams (cvJ.type.instantiateLevelParams cvJ.levelParams us) ds
    let ctors ← (c.ctorsOf J).mapM fun (cv, _) =>
      instPiParams (cv.type.instantiateLevelParams cv.levelParams us) ds
    set { st with
      aux := st.aux ++ [(Expr.mkAppN (.const J us) ds, a)]
      types := st.types.push ⟨a, ty, ctors⟩
      next := st.next + 1 }
    copyBlock c us ds Js

/-- The recorded block of `I` (`get_all()`). -/
def blockOf (c : ElimCtx) (I : Name) : List Name :=
  match c.find? I with
  | some (.indInfo _ caps) => caps.all
  | _ => []

/-- **`replace_if_nested`** (:1066–1132): a nested occurrence becomes
`auxI ps is` — the existing auxiliary type for the key `I Ds` (structural
equality, :1082–1093), or, the first time, after copying `I`'s whole block
(:1094–1128). -/
def replaceIfNested (c : ElimCtx) (e : Expr) : ElimM (Option Expr) := do
  let st ← get
  match ← (isNestedApp c (st.types.toList.map (·.name)) e : Except CheckError _) with
  | none => pure none
  | some (I, us, np, args) =>
    let key := Expr.mkAppN (.const I us) (args.take np)
    let mk (a : Name) : Expr := Expr.mkAppN (Expr.mkAppN (.const a c.lvls) c.ps) (args.drop np)
    match st.aux.lookup key with
    | some a => pure (some (mk a))
    | none =>
      copyBlock c us (args.take np) (blockOf c I)
      match (← get).aux.lookup key with
      | some a => pure (some (mk a))
      | none => throw illFormed  -- `lean_assert(result)` (:1128)

/-- **`replace_all_nested`** (:1134–1136): official's `replace`, top-down —
at an application, a nested occurrence is replaced WHOLE and not descended
into; otherwise every child is visited (a local's type lives in the local
context and is not). -/
def replaceAll (c : ElimCtx) : Expr → ElimM Expr
  | .app f a => do
    match ← replaceIfNested c (.app f a) with
    | some r => pure r
    | none => return .app (← replaceAll c f) (← replaceAll c a)
  | .lam t b m => return .lam (← replaceAll c t) (← replaceAll c b) m
  | .forallE t b m => return .forallE (← replaceAll c t) (← replaceAll c b) m
  | .letE t v b => return .letE (← replaceAll c t) (← replaceAll c v) (← replaceAll c b)
  | .proj s i x => return .proj s i (← replaceAll c x)
  | e => pure e

/-- **The main elimination loop** (:1148–1176): process the queue of
types from `q` on, replacing every constructor's nested occurrences; the
queue grows while it is processed; stops when every type is processed. -/
def elimLoop (c : ElimCtx) : Nat → Nat → ElimM Unit
  | 0, _ => throw (.notImplemented "official spec: elimination fuel")
  | fuel + 1, q => do
    let st ← get
    match st.types[q]? with
    | none => pure ()
    | some t =>
      let cs ← t.ctors.mapM (replaceAll c)
      modify fun st => { st with types := st.types.set! q { t with ctors := cs } }
      elimLoop c fuel (q + 1)

/-- A member of the declaration as the spec receives it: its name, its
former's type and its constructors' types (closed; the parameters their
leading binders). -/
structure MemberDecl where
  name : Name
  type : Expr
  ctors : List Expr

/-- **`elim_nested_inductive_fn::operator()`** (:1148–1180): the
declaration's own types first (their parameters instantiated at `ps`;
`get_params` throws on too few binders, :1141), then the loop. -/
def elimNested (c : ElimCtx) (decl : List MemberDecl) (fuel : Nat) : Except CheckError ElimSt := do
  let types ← decl.mapM fun d => do
    let ty ← instPiParams d.type c.ps
    let cs ← d.ctors.mapM fun t => instPiParams t c.ps
    pure (⟨d.name, ty, cs⟩ : AuxType)
  let ((), st) ← elimLoop c fuel 0 |>.run { types := types.toArray }
  pure st

/-! ## `check_uniform_ind_occs` -/

/-- **`check_uniform_ind_occs`** (:134–166): every occurrence of a type of
the declaration `names` in a constructor type, at binder depth `off`
(official's `offset`), is applied to the declaration's levels `lvls` and
to exactly its parameters — the bound variables `#(off-1) … #(off-np)`;
an over-applied occurrence is descended into (its parameter application
is visited as a subterm), and an application whose head is not one of
`names` is descended into.  `for_each` visits every subterm (a local's
type lives in the local context and is not visited). -/
def uniformOcc (names : List Name) (lvls : List Level) (np : Nat) : Nat → Expr → Bool
  | off, .app f a =>
    match (Expr.app f a).getAppFn with
    | .const n us =>
      if names.contains n then
        if np < (Expr.app f a).getAppArgs.length then
          uniformOcc names lvls np off f && uniformOcc names lvls np off a
        else
          (Expr.app f a).getAppArgs.length == np && decide (np ≤ off) && us == lvls &&
            (Expr.app f a).getAppArgs == (List.range np).map fun i => Expr.bvar (off - 1 - i)
      else uniformOcc names lvls np off f && uniformOcc names lvls np off a
    | _ => uniformOcc names lvls np off f && uniformOcc names lvls np off a
  | _, .const n us => !names.contains n || (np == 0 && us == lvls)
  | off, .lam t b _ | off, .forallE t b _ =>
    uniformOcc names lvls np off t && uniformOcc names lvls np (off + 1) b
  | off, .letE t v b =>
    uniformOcc names lvls np off t && uniformOcc names lvls np off v &&
      uniformOcc names lvls np (off + 1) b
  | off, .proj _ _ x => uniformOcc names lvls np off x
  | _, _ => true

/-! ## `check_positivity` on the auxiliary declaration -/

/-- What `check_constructors`' positivity slice reads: official's
`tc().whnf` in the auxiliary environment (the declaration's types opaque
constants), the declaration's types' names (`m_ind_types`), levels
(`m_lvls`), parameters (`m_params`) and index counts (`m_nindices`). -/
structure PosOracle where
  whnf : Nat → Expr → Except CheckError Expr
  names : List Name
  lvls : List Level
  ps : List Expr
  nIdx : Name → Nat

/-- `has_ind_occ` (:420–423): a constant of the declaration occurs (not
looking into locals' types). -/
def PosOracle.occ (o : PosOracle) (e : Expr) : Bool := e.nestOcc o.names 0 0

/-- **`is_valid_ind_app(t, i)`** (:381–401) for the type named `n`: `t` is
`n.{m_lvls} ps is` with exactly `nparams + nindices` arguments, the
parameters `m_params`, the indices free of the declaration's types. -/
def PosOracle.validAt (o : PosOracle) (n : Name) (t : Expr) : Bool :=
  t.getAppFn == .const n o.lvls &&
  t.getAppArgs.length == o.ps.length + o.nIdx n &&
  t.getAppArgs.take o.ps.length == o.ps &&
  (t.getAppArgs.drop o.ps.length).all (!o.occ ·)

/-- `is_valid_ind_app(t)` (:403–410): valid at some type of the declaration. -/
def PosOracle.valid (o : PosOracle) (t : Expr) : Bool :=
  o.names.any (o.validAt · t)

/-- **`check_positivity`** (:436–453), `t` at depth `dep` (the next fresh
local's index). -/
def checkPositivity (o : PosOracle) : Nat → Nat → Expr → Except CheckError Unit
  | 0, _, _ => throw (.notImplemented "official spec: positivity fuel")
  | fuel + 1, dep, t => do
    let t ← o.whnf dep t
    if !o.occ t then pure ()                                   -- :438 nonrecursive
    else match t with
      | .forallE a b _ =>                                      -- :440
        if o.occ a then                                        -- :441
          throw (.invalid "official: non positive occurrence of the datatypes being declared")
        else checkPositivity o fuel (dep + 1) (b.instantiate1 (.fvar dep a))   -- :444–445
      | _ =>
        if o.valid t then pure ()                              -- :446 recursive
        else throw (.invalid "official: non valid occurrence of the datatypes being declared")

/-- **One constructor's positivity** (`check_constructors` :472–494, the
fields' loop after the parameters): every field's domain through
`check_positivity`, each opened at a fresh local, and the result
`is_valid_ind_app` at the constructor's own type (:493). -/
def checkCtorPos (o : PosOracle) (self : Name) (fuel : Nat) : Nat → Nat → Expr → Except CheckError Unit
  | 0, _, _ => throw (.notImplemented "official spec: telescope fuel")
  | nb + 1, dep, t =>
    match t with
    | .forallE a b _ => do
      checkPositivity o fuel dep a
      checkCtorPos o self fuel nb (dep + 1) (b.instantiate1 (.fvar dep a))
    | _ =>
      if o.validAt self t then pure ()
      else throw (.invalid "official: invalid return type")

/-- The oracle official's positivity check runs with on the eliminated
declaration `st`: its types' names and index counts (syntactic, see the
module doc). -/
def ElimSt.oracle (st : ElimSt) (c : ElimCtx) (whnf : Nat → Expr → Except CheckError Expr) :
    PosOracle where
  whnf := whnf
  names := st.types.toList.map (·.name)
  lvls := c.lvls
  ps := c.ps
  nIdx n := match st.types.toList.find? (·.name == n) with
    | some t => t.type.piBinders.1.length
    | none => 0

/-- **Official accepts the declaration's positivity, ending its
elimination with `st`**: the elimination reaches its fixpoint `st`, and
every constructor of every type of the auxiliary declaration passes
`checkCtorPos` at EVERY fresh-local base from `base0` on (official's
fresh locals are arbitrary names: its verdict cannot depend on them). -/
def OfficialPosAcceptsAt (c : ElimCtx) (decl : List MemberDecl)
    (whnf : Nat → Expr → Except CheckError Expr) (base0 : Nat) (st : ElimSt) : Prop :=
  (∃ fuelE, elimNested c decl fuelE = .ok st) ∧
    ∀ t ∈ st.types.toList, ∀ ct ∈ t.ctors, ∀ base, base0 ≤ base → ∃ fuel nb,
      checkCtorPos (st.oracle c whnf) t.name fuel nb base ct = .ok ()

/-- **Official accepts the declaration's positivity** (fresh locals from
`base0` on). -/
def OfficialPosAccepts (c : ElimCtx) (decl : List MemberDecl)
    (whnf : Nat → Expr → Except CheckError Expr) (base0 : Nat) : Prop :=
  ∃ st, OfficialPosAcceptsAt c decl whnf base0 st

end Official

end ConLeche

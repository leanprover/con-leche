module

public import ConLeche.Kernel.Inductives.NestedParts
public import ConLeche.Kernel.Inductives.MutualInstall

@[expose] public section

/-!
# `elim_nested_inductive_fn`, mirrored (task #279)

The pure half of the nested route: the block's constructor types are
rewritten so that no container application with a block-mentioning
parameter remains, and every occurrence that was rewritten is recorded
with its PIN — the container application `J Ds` it stood for — for the
restore.

The algorithm is official's (`src/kernel/inductive.cpp`,
`elim_nested_inductive_fn::operator()`), step for step:

* the block's parameters `p⃗` are read off the FIRST type's telescope
  ("incorrect number of parameters" otherwise) and opened at the free
  variables `0 … nP-1`; every constructor's own parameter prefix is
  opened at the SAME variables, which is official's `replace_params`
  (it re-creates the parameters per constructor to keep the binder
  data, and maps them back to the block's before every comparison);
* a WORKLIST over the types — initially the block's, growing with the
  copies — rewrites each constructor's residual by a TOP-DOWN
  `replace`: at every subterm `replaceIfNested` is tried first, and
  only when it declines are the children visited (`app`: function then
  argument; a binder: domain then body).  That order is what fixes the
  mimics' creation order, hence the `rec_k` numbering;
* `replaceIfNested`: the head is a constant that is a STORED INDUCTIVE
  (a definition unfolding to a container is NOT nested — official's
  "non valid occurrence" then follows from positivity), with at least
  its own parameter count of arguments, and some parameter argument
  mentioning a type of the growing list.  A parameter argument with a
  loose bound variable then REJECTS with official's message;
* the pin `J Ds` is compared by STRUCTURAL equality against the pins
  minted so far (official's `p.first == Iparams`); on a miss the WHOLE
  `all`-group of the container is copied — for each member `J` a fresh
  `_nested.J_k` (`k` a running counter over the whole elimination), its
  type and its constructors at the container's level instantiation with
  the container's parameters replaced by `Ds` and the block's parameter
  telescope prefixed.  The copies' own nested occurrences are handled
  when the worklist reaches them, which is how chains (`Array (List
  T)`), self-nested containers and mutual containers are taken.

**One divergence from official, recorded**: official reads the
container's parameter count and `all`-group off its `inductive_val`;
our environment stores neither, so both are recovered from the stored
recursor (`containerInfo?`, `NestedParts.lean`).  When the recovery
fails at an application that COULD be a nested occurrence the block is
DECLINED — never treated as non-nested, which would be an accept the
recovery does not license.
-/

namespace ConLeche

/-! ## The state -/

/-- One type of the auxiliary mutual declaration under construction:
its name, its (closed) type and its (closed) constructor types. -/
structure AuxType where
  name : Name
  type : Expr
  /-- the constructors: name, type, field count -/
  ctors : List (Name × Expr × Nat)
  deriving Repr, Inhabited

/-- A mimic: the auxiliary type's name, the container member it copies,
and the PIN `J Ds` it stands for — in the block's parameter context,
i.e. with the block's parameters as the free variables `0 … nP-1`. -/
structure NestedPin where
  aux : Name
  container : Name
  pin : Expr
  deriving Repr, Inhabited

/-- The elimination's state: the growing type list, the pins in
creation order, and official's running name counter. -/
structure ElimState where
  types : List AuxType
  pins : List NestedPin
  nextIdx : Nat
  deriving Repr, Inhabited

/-- The names the occurrence test looks for: every type of the growing
list (the block's members and the copies minted so far — official's
`m_new_types`, so `List (List T)` inside a copy is found again). -/
def ElimState.newNames (st : ElimState) : List Name := st.types.map (·.name)

/-! ## One occurrence -/

/-- Official's `is_nested_inductive_app`, on an application whose head
is the stored inductive `I` with `nPI` parameters: is some parameter
argument mentioning a type of the growing list?  A parameter argument
with a loose bound variable then REJECTS (official's message
verbatim). -/
def nestedOccOk (I : Name) (newNames : List Name) (nPI : Nat) (args : List Expr) :
    Except CheckError Bool :=
  let ps := args.take nPI
  let isNested := ps.any fun a => newNames.any fun T => a.mentionsConst T
  let loose := ps.any fun a => !a.looseBVarsBounded 0
  if isNested && loose then
    .error (.invalid s!"invalid nested inductive datatype '{I}', nested inductive \
      datatypes parameters cannot contain local variables.")
  else .ok isNested

/-- The copy of one container member at the pins: its name, its type
and its constructor types, all prefixed by the block's parameter
telescope (official's `lctx.mk_pi(As, …)`).  `pbs` are the CURRENT
constructor's parameter binders, whose domains and binder data the
prefix keeps. -/
def mkCopy (pbs : List (Expr × BinderMeta)) (lvls : List Level)
    (Ds : List Expr) (auxName : Name) (J : ContainerMember) :
    Except CheckError AuxType := do
  unless lvls.length == J.lps.length do
    .error (.invalid s!"invalid nested inductive datatype, the level instantiation of \
      '{J.name}' has the wrong length")
  let some tyI := Expr.instPis (Expr.instantiateLevelParams J.lps lvls J.type) Ds
    | .error (.invalid "invalid nested inductive datatype, ill-formed declaration")
  let cs ← J.ctors.mapM fun c => do
    let some cI := Expr.instPis (Expr.instantiateLevelParams J.lps lvls c.type) Ds
      | .error (.invalid "invalid nested inductive datatype, ill-formed declaration")
    pure (Name.replacePrefix J.name auxName c.name, closeTelescope pbs 0 cI, c.nFields)
  pure ⟨auxName, closeTelescope pbs 0 tyI, cs⟩

/-- The copies of a container's whole `all`-group, in block order, with
the pin of the member `I` the occurrence names returned. -/
def mkCopies (pbs : List (Expr × BinderMeta)) (lvls : List Level) (Ds : List Expr)
    (I : Name) : List ContainerMember → ElimState →
    Except CheckError (ElimState × Option Name)
  | [], st => pure (st, none)
  | J :: rest, st => do
    let auxName := Name.appendIndexAfter
      (Name.appendName nestedPrefixName J.name) st.nextIdx
    let copy ← mkCopy pbs lvls Ds auxName J
    let st' : ElimState :=
      { types := st.types ++ [copy]
        pins := st.pins ++ [⟨auxName, J.name, Expr.mkAppN (.const J.name lvls) Ds⟩]
        nextIdx := st.nextIdx + 1 }
    let (st'', got) ← mkCopies pbs lvls Ds I rest st'
    pure (st'', if J.name == I then some auxName else got)

/-- Official's `replace_if_nested`: `I Ds is ↦ Iaux p⃗ is`, minting the
whole `all`-group of `I` on a pin miss.  `none` — the subterm is not a
nested occurrence, and its children are visited. -/
def replaceIfNested (env : Env) (blvls : List Level) (params : List Expr)
    (pbs : List (Expr × BinderMeta)) (st : ElimState) (e : Expr) :
    Except CheckError (Option (Expr × ElimState)) := do
  match e with
  | .app _ _ =>
    match e.getAppFn with
    | .const I lvls =>
      match env.find? I with
      | some (.indInfo _ _) =>
        if I == quotName then pure none else
        match containerInfo? env I with
        | none =>
          -- the environment does not record `I`'s block; only an
          -- application that COULD be a nested occurrence is refused
          -- (a positive decline, never a silent accept)
          if e.getAppArgs.any (fun a => st.newNames.any fun T => a.mentionsConst T) then
            .error (.notImplemented s!"nested: the block of the container '{I}' is not \
              recorded in the environment (its group is read off '{I}.rec')")
          else pure none
        | some ci =>
          let args := e.getAppArgs
          if args.length < ci.nP then pure none else
          let nested ← nestedOccOk I st.newNames ci.nP args
          if !nested then pure none else
            let Ds := args.take ci.nP
            let idxs := args.drop ci.nP
            let pin := Expr.mkAppN (.const I lvls) Ds
            match st.pins.find? (fun q => q.pin == pin) with
            | some q =>
              pure (some (Expr.mkAppN (Expr.mkAppN (.const q.aux blvls) params) idxs, st))
            | none => do
              let (st', got) ← mkCopies pbs lvls Ds I ci.members st
              match got with
              | none =>
                .error (.internal "nested: the container is not a member of its own group")
              | some auxI =>
                pure (some (Expr.mkAppN (Expr.mkAppN (.const auxI blvls) params) idxs, st'))
      | _ => pure none
    | _ => pure none
  | _ => pure none

/-! ## The top-down replace -/

/-- Official's `replace_all_nested`: a TOP-DOWN replace — at every
subterm `replaceIfNested` first, and the children only when it
declines. -/
def replaceAllNested (env : Env) (blvls : List Level) (params : List Expr)
    (pbs : List (Expr × BinderMeta)) (st : ElimState) (e : Expr) :
    Except CheckError (Expr × ElimState) :=
  match replaceIfNested env blvls params pbs st e with
  | .error err => .error err
  | .ok (some r) => .ok r
  | .ok none =>
    match e with
    | .app f a =>
      match replaceAllNested env blvls params pbs st f with
      | .error err => .error err
      | .ok (f', st₁) =>
        match replaceAllNested env blvls params pbs st₁ a with
        | .error err => .error err
        | .ok (a', st₂) => .ok (.app f' a', st₂)
    | .lam ty b bm =>
      match replaceAllNested env blvls params pbs st ty with
      | .error err => .error err
      | .ok (ty', st₁) =>
        match replaceAllNested env blvls params pbs st₁ b with
        | .error err => .error err
        | .ok (b', st₂) => .ok (.lam ty' b' bm, st₂)
    | .forallE ty b bm =>
      match replaceAllNested env blvls params pbs st ty with
      | .error err => .error err
      | .ok (ty', st₁) =>
        match replaceAllNested env blvls params pbs st₁ b with
        | .error err => .error err
        | .ok (b', st₂) => .ok (.forallE ty' b' bm, st₂)
    | .letE ty v b =>
      match replaceAllNested env blvls params pbs st ty with
      | .error err => .error err
      | .ok (ty', st₁) =>
        match replaceAllNested env blvls params pbs st₁ v with
        | .error err => .error err
        | .ok (v', st₂) =>
          match replaceAllNested env blvls params pbs st₂ b with
          | .error err => .error err
          | .ok (b', st₃) => .ok (.letE ty' v' b', st₃)
    | .proj s i x =>
      match replaceAllNested env blvls params pbs st x with
      | .error err => .error err
      | .ok (x', st₁) => .ok (.proj s i x', st₁)
    | _ => .ok (e, st)

/-! ## The worklist -/

/-- One type's constructors rewritten: each constructor's parameter
prefix is opened at the block's variables, the residual replaced, and
the prefix put back with the constructor's OWN binder data. -/
def elimCtors (env : Env) (blvls : List Level) (nP : Nat) (params : List Expr) :
    List (Name × Expr × Nat) → ElimState →
      Except CheckError (List (Name × Expr × Nat) × ElimState)
  | [], st' => pure ([], st')
  | (c, cty, nF) :: rest, st' => do
    let some (pbs, _) := cty.stripPis nP
      | .error (.invalid "invalid nested inductive datatype, ill-formed declaration")
    let some cbody := Expr.instPis cty params
      | .error (.invalid "invalid nested inductive datatype, ill-formed declaration")
    let (cbody', st₁) ← replaceAllNested env blvls params pbs st' cbody
    let (rest', st₂) ← elimCtors env blvls nP params rest st₁
    pure ((c, closeTelescope pbs 0 cbody', nF) :: rest', st₂)

/-- The worklist: every type of the growing list has its constructors
rewritten, in order, the copies created on the way processed in turn.
The fuel bounds the number of worklist steps; exhausting it is a
positive DECLINE (official's loop has no bound — a stream reaching this
one is beyond anything the corpus contains). -/
def elimLoop (env : Env) (blvls : List Level) (nP : Nat) (params : List Expr) :
    Nat → Nat → ElimState → Except CheckError ElimState
  | 0, _, _ => .error (.notImplemented "nested: the elimination worklist did not finish")
  | fuel + 1, qhead, st =>
    match st.types[qhead]? with
    | none => .ok st
    | some t =>
      match elimCtors env blvls nP params t.ctors st with
      | .error err => .error err
      | .ok (cs', st₁) =>
        elimLoop env blvls nP params fuel (qhead + 1)
          { st₁ with types := st₁.types.set qhead { t with ctors := cs' } }

/-- The worklist's fuel: official's loop is unbounded; a block that
needs more mimics than this is beyond any stream the corpus contains,
and exhausting the fuel is a positive decline. -/
def nestedElimFuel : Nat := 4096

/-- **The nested elimination** (official's `elim_nested_inductive_fn`):
the auxiliary mutual declaration's types — the block's, with rewritten
constructors, followed by the copies in creation order — and the pins,
in creation order, in the block's parameter context (the parameters as
the free variables `0 … nP-1`). -/
def elimNested (env : Env) (nP : Nat) (lps : List Name)
    (types : List AuxType) : Except CheckError ElimState := do
  let some t₀ := types.head?
    | .error (.invalid "invalid empty (mutual) inductive datatype declaration, it must \
        contain at least one inductive type.")
  let some (params, _) := openPisAtFvars nP t₀.type 0
    | .error (.invalid "invalid inductive datatype declaration, incorrect number of \
        parameters")
  elimLoop env (lps.map Level.param) nP params nestedElimFuel 0 ⟨types, [], 1⟩

end ConLeche

module

public import ConLeche.Kernel.Inductives.NestedParts
public import ConLeche.Kernel.Inductives.SumInstall

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
  /-- **The mint group's base and size in the pin list** (DESIGN §M.22's
  `grp`): a container's whole `all`-group is copied at once, and the
  reference relation has to know which pins were minted together — it
  is not recoverable from the pin list afterwards, so the mint records
  it. -/
  grpBase : Nat
  grpSize : Nat
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

/-- **Official's `mk_unique_name`**: `base` with the running counter
appended, the counter advanced until the name is free in the PRE-BLOCK
environment.  The counter is shared by the whole elimination, so the
copies are pairwise distinct whatever the environment holds.  A stream
CAN put a `_nested`-prefixed constant in the environment — the
reserved-prefix guard rejects a block whose declared types MENTION one,
not a declaration NAMED one — and official skips such a name rather
than failing, so this loop is what keeps the accept set official's.
The fuel is the loop's termination measure; exhausting it leaves the
last candidate, which `copiesFresh` then rejects. -/
def mkUniqueName (env : Env) (base : Name) : Nat → Nat → Name × Nat
  | 0, idx => (Name.appendIndexAfter base idx, idx + 1)
  | fuel + 1, idx =>
    let r := Name.appendIndexAfter base idx
    if (env.find? r).isNone then (r, idx + 1)
    else mkUniqueName env base fuel (idx + 1)

/-- The copies of a container's whole `all`-group, in block order, with
the pin of the member `I` the occurrence names returned. -/
def mkCopies (env : Env) (pbs : List (Expr × BinderMeta)) (lvls : List Level)
    (Ds : List Expr) (I : Name) (base size : Nat) : List ContainerMember → ElimState →
    Except CheckError (ElimState × Option Name)
  | [], st => pure (st, none)
  | J :: rest, st => do
    let (auxName, nextIdx) :=
      mkUniqueName env (Name.appendName nestedPrefixName J.name) 1024 st.nextIdx
    let copy ← mkCopy pbs lvls Ds auxName J
    let st' : ElimState :=
      { types := st.types ++ [copy]
        pins := st.pins ++
          [⟨auxName, J.name, Expr.mkAppN (.const J.name lvls) Ds, base, size⟩]
        nextIdx := nextIdx }
    let (st'', got) ← mkCopies env pbs lvls Ds I base size rest st'
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
              let (st', got) ← mkCopies env pbs lvls Ds I st.pins.length
                ci.members.length ci.members st
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
  -- **The prune** (the task #215 discipline, as a THEOREM about this
  -- walk rather than a memo): `replaceIfNested` fires only where a
  -- container's PARAMETER argument mentions a type of the growing list,
  -- so a subterm mentioning none of those names is returned unchanged
  -- and the state is untouched.  `mentionsConst` is the memoized walk,
  -- so a DAG-shared field domain (`tests/e2e/tower_nested.ndjson`: a
  -- depth-60 doubling tower in a constructor's `Eq` field) is dismissed
  -- in one pass instead of being descended as a tree.
  if !st.newNames.any (fun T => e.mentionsConst T) then .ok (e, st) else
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


/-! ## The copies' reference relation and its order (DESIGN §M.22, K.6)

The model's forward fold is one term per copy, each built from the
terms of the copies it REFERS to, and DESIGN §M.22 records that the
relation has no syntactic well-founded measure — on the raw terms it is
not even acyclic, kinding is what excludes the cycles.  The maintainer's
decision: the KERNEL computes the relation and emits a topological
order, and a cyclic block is a positive DECLINE.  The definitions here
are the model lane's, ported to `Bool`
(`agent/nested-279m:ConLeche/Verify/Inductives/NestedOrder.lean`,
`def CopyRef` / `structure TopoOrder`).
-/

/-- `Expr.Sub pat e` as a decision: the positions the replace walk
visits — the term itself, both sides of an application, a binder's
domain and body, a `let`'s three parts, a projection's subject — and
NOT an `fvar`'s annotation. -/
def Expr.subB (pat : Expr) : Expr → Bool
  | .app f a => (pat == Expr.app f a) || subB pat f || subB pat a
  | .lam ty b m => (pat == Expr.lam ty b m) || subB pat ty || subB pat b
  | .forallE ty b m => (pat == Expr.forallE ty b m) || subB pat ty || subB pat b
  | .letE ty v b => (pat == Expr.letE ty v b) || subB pat ty || subB pat v || subB pat b
  | .proj sn i x => (pat == Expr.proj sn i x) || subB pat x
  | e => pat == e

/-! ### `subB`, memoized (the task #215 discipline)

The relation is asked of PINS, and a pin component can be a DAG-shared
term, on which a tree walk does not finish.  Same arrangement as
`mentionsConst`: the memo is keyed by the node and dropped after each
call (the answer depends on `pat`), and `@[csimp]` swaps it in. -/

/-- The memo's invariant: every recorded answer is the real one. -/
def SubMemoInv (pat : Expr) (memo : Std.HashMap Expr Bool) : Prop :=
  ∀ (k : Expr) (r : Bool), memo[k]? = some r → r = Expr.subB pat k

theorem SubMemoInv.empty {pat : Expr} : SubMemoInv pat {} := by
  intro k r h; simp at h

theorem SubMemoInv.insert {pat : Expr} {memo : Std.HashMap Expr Bool}
    (hm : SubMemoInv pat memo) {e : Expr} {r : Bool} (heq : r = Expr.subB pat e) :
    SubMemoInv pat (memo.insert e r) := by
  intro k r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact heq
  · exact hm k r' hk

/-- Memoized `subB`. -/
def Expr.subBGo (pat : Expr) (memo : Std.HashMap Expr Bool) :
    Expr → Bool × Std.HashMap Expr Bool
  | .bvar i => (pat == Expr.bvar i, memo)
  | .sort u => (pat == Expr.sort u, memo)
  | .lit l => (pat == Expr.lit l, memo)
  | .const n us => (pat == Expr.const n us, memo)
  | .fvar i ty => (pat == Expr.fvar i ty, memo)
  | e =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Bool × Std.HashMap Expr Bool :=
        match e with
        | .app f a =>
          let (b₁, memo) := subBGo pat memo f
          let (b₂, memo) := subBGo pat memo a
          ((pat == Expr.app f a) || b₁ || b₂, memo)
        | .lam ty b m =>
          let (b₁, memo) := subBGo pat memo ty
          let (b₂, memo) := subBGo pat memo b
          ((pat == Expr.lam ty b m) || b₁ || b₂, memo)
        | .forallE ty b m =>
          let (b₁, memo) := subBGo pat memo ty
          let (b₂, memo) := subBGo pat memo b
          ((pat == Expr.forallE ty b m) || b₁ || b₂, memo)
        | .letE ty v b =>
          let (b₁, memo) := subBGo pat memo ty
          let (b₂, memo) := subBGo pat memo v
          let (b₃, memo) := subBGo pat memo b
          ((pat == Expr.letE ty v b) || b₁ || b₂ || b₃, memo)
        | .proj sn i x =>
          let (b, memo) := subBGo pat memo x
          ((pat == Expr.proj sn i x) || b, memo)
        | e => (Expr.subB pat e, memo)
      (r, memo.insert e r)

/-- **The memoized walk is `subB`.** -/
theorem Expr.subBGo_spec {pat : Expr} :
    ∀ (e : Expr) (memo : Std.HashMap Expr Bool), SubMemoInv pat memo →
      (subBGo pat memo e).1 = Expr.subB pat e ∧ SubMemoInv pat (subBGo pat memo e).2 := by
  intro e
  induction e with
  | bvar i => intro memo hm; exact ⟨rfl, hm⟩
  | sort u => intro memo hm; exact ⟨rfl, hm⟩
  | const n us => intro memo hm; exact ⟨rfl, hm⟩
  | lit l => intro memo hm; exact ⟨rfl, hm⟩
  | fvar i ty _ => intro memo hm; exact ⟨rfl, hm⟩
  | app a b iha ihb =>
    intro memo hm
    rw [subBGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iha memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      refine ⟨by simp [subB, h1, h3], ?_⟩
      exact h4.insert (by simp [subB, h1, h3])
  | lam ty body bi iht ihb =>
    intro memo hm
    rw [subBGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      refine ⟨by simp [subB, h1, h3], ?_⟩
      exact h4.insert (by simp [subB, h1, h3])
  | forallE ty body bi iht ihb =>
    intro memo hm
    rw [subBGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      refine ⟨by simp [subB, h1, h3], ?_⟩
      exact h4.insert (by simp [subB, h1, h3])
  | letE ty val body iht ihv ihb =>
    intro memo hm
    rw [subBGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihv _ h2
      obtain ⟨h5, h6⟩ := ihb _ h4
      refine ⟨by simp [subB, h1, h3, h5], ?_⟩
      exact h6.insert (by simp [subB, h1, h3, h5])
  | proj sn i sub ih =>
    intro memo hm
    rw [subBGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := ih memo hm
      refine ⟨by simp [subB, h1], ?_⟩
      exact h2.insert (by simp [subB, h1])

/-- The executed `subB` (one memoized DAG walk). -/
def Expr.subBFast (pat e : Expr) : Bool := (subBGo pat {} e).1

@[csimp] theorem Expr.subB_eq_subBFast : @Expr.subB = @Expr.subBFast := by
  funext pat e
  exact (subBGo_spec e {} SubMemoInv.empty).1.symm

/-- The mint-group assignment of the pin list: `grp j` is pin `j`'s
group base and size (`(0, 0)` off the list). -/
def ElimState.grp (st : ElimState) (j : Nat) : Nat × Nat :=
  match st.pins[j]? with
  | some q => (q.grpBase, q.grpSize)
  | none => (0, 0)

/-- **`CopyRef grp k st j j'`, as a decision** (the model lane's
`CopyRef`, clause for clause): a processed constructor of copy `j`
mentions copy `j'`'s name; `j'` is OUTSIDE `j`'s mint group; and no pin
of `j`'s group is a subterm of `j'`'s pin — the exclusion that keeps a
container's references through its OWN mimics out of the relation, since
a mimic's pin contains a group pin. -/
def copyRefB (grp : Nat → Nat × Nat) (k : Nat) (st : ElimState) (j j' : Nat) : Bool :=
  match st.types[k + j]?, st.types[k + j']?, st.pins[j']? with
  | some t, some t', some q' =>
    t.ctors.any (fun c => c.2.1.mentionsConst t'.name) &&
    !((grp j).1 ≤ j' && j' < (grp j).1 + (grp j).2) &&
    (List.range (grp j).2).all (fun i =>
      match st.pins[(grp j).1 + i]? with
      | some g => !Expr.subB g.pin q'.pin
      | none => true)
  | _, _, _ => false

/-- The targets of copy `j` among the `n` copies. -/
def copyRefsOf (grp : Nat → Nat × Nat) (k : Nat) (st : ElimState) (n j : Nat) : List Nat :=
  (List.range n).filter (fun j' => copyRefB grp k st j j')

/-- **`TopoOrder`'s four fields, as one decision**: a duplicate-free
list of copy indices that covers them all and in which every reference
points to an EARLIER entry. -/
def topoOrderOk (refs : Nat → List Nat) (n : Nat) (order : List Nat) : Bool :=
  decide order.Nodup &&
    (List.range n).all (fun j => order.contains j) &&
    order.all (fun j => j < n) &&
    order.all (fun j => (refs j).all
      (fun j' => order.contains j' && order.idxOf j' < order.idxOf j))

/-- The sort: repeatedly emit a copy all of whose references are out
already.  `.error (j, j')` when no copy can be emitted — `j` is one of
the copies left and `j'` one of its references that is also left, i.e.
an edge ON a cycle. -/
def topoGo (refs : Nat → List Nat) (n : Nat) : Nat → List Nat →
    Except (Nat × Nat) (List Nat)
  | 0, acc => .ok acc
  | fuel + 1, acc =>
    match (List.range n).find?
        (fun j => !acc.contains j && (refs j).all (fun j' => acc.contains j')) with
    | some j => topoGo refs n fuel (acc ++ [j])
    | none =>
      match (List.range n).find? (fun j => !acc.contains j) with
      | none => .ok acc
      | some j =>
        match (refs j).find? (fun j' => !acc.contains j') with
        | some j' => .error (j, j')
        | none => .error (j, j)

/-- **The copies' topological order**, or an edge on a cycle.  The
result is checked against `topoOrderOk`, so the four `TopoOrder` fields
are facts about it and not about the algorithm. -/
def nestedTopoOrder (grp : Nat → Nat × Nat) (k : Nat) (st : ElimState) :
    Except (Nat × Nat) (List Nat) :=
  let n := st.pins.length
  let refs := copyRefsOf grp k st n
  match topoGo refs n n [] with
  | .error e => .error e
  | .ok order => if topoOrderOk refs n order then .ok order else .error (0, 0)

/-- The worklist's fuel: official's loop is unbounded; a block that
needs more mimics than this is beyond any stream the corpus contains,
and exhausting the fuel is a positive decline. -/
def nestedElimFuel : Nat := 4096

/-- **Every name the elimination MINTS**: each copy's type, its
recursor and its constructors.  The copies' types and constructors are
consed into the SCRATCH environment by the mutual installer, which does
not check freshness, and the copies' recursors are generated there
too — so this is the list `copiesFresh` asks about. -/
def nestedCopyNames (k : Nat) (st : ElimState) : List Name :=
  (st.types.drop k).flatMap fun t =>
    t.name :: t.name.str "rec" :: t.ctors.map (·.1)

/-- **The minted names are free in the PRE-BLOCK environment.**  A
`false` is a REJECT, and it is official's: the copies' types and
constructors go into the environment through `declare_inductive_types`,
whose `check_name` throws "already declared" on a collision, and their
recursors through the same door.  The copies' TYPE names cannot collide
at all — `mkUniqueName` is official's `mk_unique_name` and skips a
taken one — so what can fire here is a constructor or a recursor name,
which official refuses in exactly the same way.  Without the check a
crafted stream could declare `_nested.List_1.cons` and then a block
nesting through `List`, and the scratch environment's cons would
SHADOW it: nothing else in the route looks at the generated names, the
reserved-prefix guard rejects a block whose declared types MENTION a
`_nested` constant but not a declaration NAMED one, and the restore
never puts a copy's name back. -/
def copiesFresh (env : Env) (k : Nat) (st : ElimState) : Bool :=
  (nestedCopyNames k st).all fun n => (env.find? n).isNone

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

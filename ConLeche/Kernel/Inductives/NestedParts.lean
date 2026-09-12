module

public import ConLeche.Kernel.Inductives.MutualParts

@[expose] public section

/-!
# Nested inductive blocks: the names, the container's block, the
recogniser and `check_uniform_ind_occs` (task #279)

A **nested block** is an inductive declaration one of whose
constructor fields mentions the block inside a *parameter* of an
already-declared inductive type (`mk : List (T α) → T α`).  The
official kernel does not give such a block its own construction: it
*eliminates* the nesting (`elim_nested_inductive_fn`,
`src/kernel/inductive.cpp`), replacing every nested occurrence `I Ds is`
by an auxiliary mimic `Iaux p⃗ is` — a fresh member of a MUTUAL block
that copies the whole `all`-group of `I` at the pins `Ds` — checks that
mutual block, and then *restores* the nesting in the constructor types,
the recursor types and the rule right-hand sides
(`restore_nested`).  What is stored is the restored block, with one
recursor per member under its own name and one per mimic under
`<first member>.rec_1`, `.rec_2`, ….

This file carries the pieces the elimination needs before it can run:

* the reserved `_nested` prefix and the `Name` arithmetic official
  uses to mint the copies' names (`mk_unique_name`,
  `Name.replacePrefix`);
* **the container's block, read off the stored recursor**
  (`containerInfo?`).  Official reads `I`'s parameter count, its
  `all`-group and its constructors straight off the `inductive_val`;
  our `Env` stores an inductive as `indInfo cv caps` and records
  neither the group nor the parameter count, so both are RECOVERED:
  the parameter count from a constructor record (`ctorInfo`'s
  `numParams`), the group from the *motive binders of `I.rec`* — the
  recursor of a block with `k` members and `n` mimics carries `k + n`
  motives in `all` order, and the first `k` are exactly those whose
  major premise is a member applied to the block's parameters and its
  own index variables (a mimic's major is the container at the pins,
  which mention a member and so are never the bare parameters).  A
  block the reading cannot recover is a positive DECLINE at the use
  site, never a silent "not nested" (see `NestedElim.lean`);
* `uniformIndOccsOk` — v4.34.0-rc2's `check_uniform_ind_occs`, the
  syntactic walk asking that every occurrence of a datatype being
  declared be applied to the declaration's own parameters and universe
  levels (the arena's `nested-nonuniform-param`);
* `nestedParts?`, the recogniser: several recursor records for one
  block is what a nested block looks like in the stream.
-/

namespace ConLeche

/-! ## The reserved prefix and the copies' names -/

/-- Official's `g_nested`: the prefix the auxiliary mimic types are
minted under.  They exist only in the scratch environment, so a stream
naming one is rejected (`check_no_nested_aux`, leanprover/lean4#14616). -/
def nestedPrefixName : Name := .str .anonymous "_nested"

/-- `pre ++ n` — official's `name::operator+`. -/
def Name.appendName (pre : Name) : Name → Name
  | .anonymous => pre
  | .str p s => .str (Name.appendName pre p) s
  | .num p k => .num (Name.appendName pre p) k

/-- Official's `Name.appendIndexAfter`: the index appended to the last
string component (`_nested.List` ↦ `_nested.List_1`). -/
def Name.appendIndexAfter : Name → Nat → Name
  | .str p s, i => .str p (s ++ "_" ++ toString i)
  | n, i => .str n ("_" ++ toString i)

/-- Is `pre` a prefix of `n` (`n` itself included)? -/
def Name.hasPrefixOf (pre : Name) : Name → Bool
  | .anonymous => (Name.anonymous == pre)
  | .str p s => (Name.str p s == pre) || Name.hasPrefixOf pre p
  | .num p k => (Name.num p k == pre) || Name.hasPrefixOf pre p

/-- Official's `name::replace_prefix`: `old` replaced by `new` where it
is a prefix, the name itself otherwise. -/
def Name.replacePrefix (old new : Name) : Name → Name
  | .anonymous => if (Name.anonymous == old) then new else .anonymous
  | .str p s =>
    if (Name.str p s == old) then new else .str (Name.replacePrefix old new p) s
  | .num p k =>
    if (Name.num p k == old) then new else .num (Name.replacePrefix old new p) k

/-- Does the expression mention a `_nested`-prefixed constant, or
project through a `_nested`-prefixed structure?  Official's
`check_no_nested_aux` (the `proj` clause is official's: the kernel
rewrites a nested occurrence in the constructor to the auxiliary type,
so a projection naming that type matches without the declaration ever
mentioning it as a constant). -/
def Expr.mentionsNestedAux : Expr → Bool
  | .bvar _ | .sort _ | .lit _ => false
  | .const n _ => Name.hasPrefixOf nestedPrefixName n
  | .fvar _ ty => Expr.mentionsNestedAux ty
  | .app f a => Expr.mentionsNestedAux f || Expr.mentionsNestedAux a
  | .lam ty b _ | .forallE ty b _ =>
    Expr.mentionsNestedAux ty || Expr.mentionsNestedAux b
  | .letE ty v b =>
    Expr.mentionsNestedAux ty || Expr.mentionsNestedAux v || Expr.mentionsNestedAux b
  | .proj s _ e => Name.hasPrefixOf nestedPrefixName s || Expr.mentionsNestedAux e

/-! ### `mentionsNestedAux`, memoized (the task #215 discipline)

The guard runs over every declared type of the block, and a stream may
put a DAG-shared tower in one (`tests/e2e/tower_nested.ndjson`), on
which a tree walk does not finish.  The memoized walk is swapped in by
`@[csimp]`, as `mentionsConst` above: kernel-checked, no trust point,
the pure definition stays what every proof consumes. -/

/-- The memo's invariant: every recorded answer is the real one. -/
def NestedAuxMemoInv (memo : Std.HashMap Expr Bool) : Prop :=
  ∀ (k : Expr) (r : Bool), memo[k]? = some r → r = k.mentionsNestedAux

theorem NestedAuxMemoInv.empty : NestedAuxMemoInv {} := by
  intro k r h; simp at h

theorem NestedAuxMemoInv.insert {memo : Std.HashMap Expr Bool}
    (hm : NestedAuxMemoInv memo) {e : Expr} {r : Bool} (heq : r = e.mentionsNestedAux) :
    NestedAuxMemoInv (memo.insert e r) := by
  intro k r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact heq
  · exact hm k r' hk

/-- Memoized `mentionsNestedAux`. -/
def Expr.mentionsNestedAuxGo (memo : Std.HashMap Expr Bool) :
    Expr → Bool × Std.HashMap Expr Bool
  | .bvar _ => (false, memo)
  | .sort _ => (false, memo)
  | .lit _ => (false, memo)
  | .const n _ => (Name.hasPrefixOf nestedPrefixName n, memo)
  | e =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Bool × Std.HashMap Expr Bool :=
        match e with
        | .fvar _ ty => mentionsNestedAuxGo memo ty
        | .app f a =>
          let (b₁, memo) := mentionsNestedAuxGo memo f
          let (b₂, memo) := mentionsNestedAuxGo memo a
          (b₁ || b₂, memo)
        | .lam ty body _ =>
          let (b₁, memo) := mentionsNestedAuxGo memo ty
          let (b₂, memo) := mentionsNestedAuxGo memo body
          (b₁ || b₂, memo)
        | .forallE ty body _ =>
          let (b₁, memo) := mentionsNestedAuxGo memo ty
          let (b₂, memo) := mentionsNestedAuxGo memo body
          (b₁ || b₂, memo)
        | .letE ty val body =>
          let (b₁, memo) := mentionsNestedAuxGo memo ty
          let (b₂, memo) := mentionsNestedAuxGo memo val
          let (b₃, memo) := mentionsNestedAuxGo memo body
          (b₁ || b₂ || b₃, memo)
        | .proj s _ sub =>
          let (b, memo) := mentionsNestedAuxGo memo sub
          (Name.hasPrefixOf nestedPrefixName s || b, memo)
        | e => (e.mentionsNestedAux, memo)
      (r, memo.insert e r)

/-- **The memoized walk is `mentionsNestedAux`.** -/
theorem Expr.mentionsNestedAuxGo_spec :
    ∀ (e : Expr) (memo : Std.HashMap Expr Bool), NestedAuxMemoInv memo →
      (mentionsNestedAuxGo memo e).1 = e.mentionsNestedAux ∧
        NestedAuxMemoInv (mentionsNestedAuxGo memo e).2 := by
  intro e
  induction e with
  | bvar i => intro memo hm; exact ⟨rfl, hm⟩
  | sort u => intro memo hm; exact ⟨rfl, hm⟩
  | const n us => intro memo hm; exact ⟨rfl, hm⟩
  | lit l => intro memo hm; exact ⟨rfl, hm⟩
  | fvar i ty ih =>
    intro memo hm
    rw [mentionsNestedAuxGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := ih memo hm
      refine ⟨by simp [mentionsNestedAux, h1], ?_⟩
      exact h2.insert (by simp [mentionsNestedAux, h1])
  | app a b iha ihb =>
    intro memo hm
    rw [mentionsNestedAuxGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iha memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      refine ⟨by simp [mentionsNestedAux, h1, h3], ?_⟩
      exact h4.insert (by simp [mentionsNestedAux, h1, h3])
  | lam ty body bi iht ihb =>
    intro memo hm
    rw [mentionsNestedAuxGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      refine ⟨by simp [mentionsNestedAux, h1, h3], ?_⟩
      exact h4.insert (by simp [mentionsNestedAux, h1, h3])
  | forallE ty body bi iht ihb =>
    intro memo hm
    rw [mentionsNestedAuxGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      refine ⟨by simp [mentionsNestedAux, h1, h3], ?_⟩
      exact h4.insert (by simp [mentionsNestedAux, h1, h3])
  | letE ty val body iht ihv ihb =>
    intro memo hm
    rw [mentionsNestedAuxGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihv _ h2
      obtain ⟨h5, h6⟩ := ihb _ h4
      refine ⟨by simp [mentionsNestedAux, h1, h3, h5], ?_⟩
      exact h6.insert (by simp [mentionsNestedAux, h1, h3, h5])
  | proj s i sub ih =>
    intro memo hm
    rw [mentionsNestedAuxGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := ih memo hm
      refine ⟨by simp [mentionsNestedAux, h1], ?_⟩
      exact h2.insert (by simp [mentionsNestedAux, h1])

/-- The executed `mentionsNestedAux` (one memoized DAG walk). -/
def Expr.mentionsNestedAuxFast (e : Expr) : Bool :=
  (mentionsNestedAuxGo {} e).1

@[csimp] theorem Expr.mentionsNestedAux_eq_mentionsNestedAuxFast :
    @Expr.mentionsNestedAux = @Expr.mentionsNestedAuxFast := by
  funext e
  exact (mentionsNestedAuxGo_spec e {} NestedAuxMemoInv.empty).1.symm

/-! ## The container's block, read off its stored recursor -/

/-- One constructor of a container: its name, its stored type and its
field count. -/
structure ContainerCtor where
  name : Name
  type : Expr
  nFields : Nat
  deriving Repr, Inhabited

/-- One member of a container's `all`-group. -/
structure ContainerMember where
  name : Name
  lps : List Name
  type : Expr
  ctors : List ContainerCtor
  deriving Repr, Inhabited

/-- A stored inductive's block, as the nested elimination needs it:
the parameter count and the `all`-group in block order. -/
structure ContainerInfo where
  nP : Nat
  members : List ContainerMember
  deriving Repr, Inhabited

/-- Is this motive binder's domain a REAL member's motive — `Π ı⃗ (t :
C p⃗ ı⃗), Sort ℓ` with `C` a stored inductive applied to the block's
parameters (the bound variables at the right offsets) and its own index
variables in order?  `dom` sits at binder depth `nP + i` (the
parameters and the `i` earlier motives).  A MIMIC's motive fails it:
its major is the container at the pins, and a pin mentions a member, so
it is never the bare parameter spine. -/
def containerMotiveMember? (env : Env) (nP i : Nat) (dom : Expr) : Option Name :=
  let (bs, res) := dom.piBinders
  match res with
  | .sort _ =>
    match bs.getLast? with
    | some (major, _) =>
      let nIdx := bs.length - 1
      match major.getAppFn with
      | .const C _ =>
        let args := major.getAppArgs
        if args.length == nP + nIdx &&
            (List.range nP).all
              (fun j => args[j]? == some (Expr.bvar (nIdx + i + nP - 1 - j))) &&
            (List.range nIdx).all
              (fun l => args[nP + l]? == some (Expr.bvar (nIdx - 1 - l))) &&
            (match env.find? C with | some (.indInfo _ _) => true | _ => false) then
          some C
        else none
      | _ => none
    | none => none
  | _ => none

/-- The maximal prefix of motive binders that are real members'
(`containerMotiveMember?`), in `all` order.  `fuel` bounds the walk by
the recursor's own motive-plus-minor count. -/
def containerMembersGo (env : Env) (nP : Nat) : Nat → Nat → Expr → List Name
  | 0, _, _ => []
  | fuel + 1, i, .forallE dom body _ =>
    match containerMotiveMember? env nP i dom with
    | some C => C :: containerMembersGo env nP fuel (i + 1) body
    | none => []
  | _ + 1, _, _ => []

/-- **The container's block** (official's `inductive_val`): `none` when
the environment does not record enough to reconstruct it — no stored
former, no `I.rec`, an unreadable parameter count, a group whose
members disagree on the rule prefix or the level parameters, a
constructor record missing.  `Quot` is excluded deliberately: official
stores it as a `quotInfo`, not an inductive, so `is_nested_inductive_app`
never fires on it and an occurrence of the block inside a `Quot`
parameter is official's non-positive occurrence. -/
def containerInfo? (env : Env) (I : Name) : Option ContainerInfo := do
  if I == quotName then none else
  let .indInfo cvT _ := (← env.find? I) | none
  let .recInfo cvR mI rP rules := (← env.find? (I.str "rec")) | none
  if rP ≤ mI then
    -- the parameter count: official reads it off the `inductive_val`;
    -- here off a constructor record (`ctorInfo`'s `numParams`), or —
    -- at a zero-constructor container — off the former's telescope
    -- minus the recursor's index count
    let nP : Nat ← (match rules.head? with
      | some r =>
        match env.find? r.ctor with
        | some (.ctorInfo _ n _) => some n
        | _ => none
      | none =>
        if mI - rP ≤ cvT.type.piArity then some (cvT.type.piArity - (mI - rP))
        else none)
    let (_, recBody) ← cvR.type.stripPis nP
    let names := containerMembersGo env nP (rP + 1) 0 recBody
    if names.contains I && names.Nodup then
      let members ← names.mapM fun C => do
        let .indInfo cvC _ := (← env.find? C) | none
        let .recInfo _ _ rPc rulesC := (← env.find? (C.str "rec")) | none
        if rPc == rP && cvC.levelParams == cvT.levelParams then
          let ctors ← rulesC.mapM fun r =>
            match env.find? r.ctor with
            | some (.ctorInfo cvc nPc nF) =>
              if nPc == nP then some ⟨r.ctor, cvc.type, nF⟩ else none
            | _ => none
          some ⟨C, cvC.levelParams, cvC.type, ctors⟩
        else none
      some ⟨nP, members⟩
    else none
  else none

/-! ## `check_uniform_ind_occs` (v4.34.0-rc2) -/

/-- One node of `check_uniform_ind_occs`' walk: `some true` — the node
is an occurrence of a datatype being declared, applied exactly to the
parameters and the universe levels (do not descend); `some false` —
descend into the children; `none` — a non-uniform occurrence, official's
reject.  An OVER-applied occurrence descends, so that the indices are
checked too; the parameter application itself is visited as a subterm. -/
def uniformOccNode (indNames : List Name) (lvls : List Level) (nP offset : Nat)
    (t : Expr) : Option Bool :=
  match t.getAppFn with
  | .const n us =>
    if indNames.contains n then
      let args := t.getAppArgs
      if args.length > nP then some false
      else if args.length == nP && offset ≥ nP && us == lvls &&
          (List.range nP).all (fun i => args[i]? == some (Expr.bvar (offset - 1 - i))) then
        some true
      else none
    else some false
  | _ => some false

/-- `check_uniform_ind_occs` over one constructor type. -/
def uniformIndOccsE (indNames : List Name) (lvls : List Level) (nP : Nat) :
    Nat → Expr → Bool
  | offset, e =>
    -- **The prune** (the task #215 discipline, and a THEOREM about this
    -- walk rather than a memo): a subterm mentioning no datatype being
    -- declared has no occurrence to check, so every node under it
    -- answers `true`.  `mentionsConst` is the memoized walk, so a
    -- DAG-shared field (`tests/e2e/tower_nested.ndjson`) is dismissed in
    -- one pass instead of being descended as a tree.
    if !indNames.any (fun T => e.mentionsConst T) then true else
    match uniformOccNode indNames lvls nP offset e with
    | none => false
    | some true => true
    | some false =>
      match e with
      | .bvar _ | .sort _ | .lit _ | .const .. => true
      | .fvar _ ty => uniformIndOccsE indNames lvls nP offset ty
      | .app f a =>
        uniformIndOccsE indNames lvls nP offset f &&
          uniformIndOccsE indNames lvls nP offset a
      | .lam ty b _ | .forallE ty b _ =>
        uniformIndOccsE indNames lvls nP offset ty &&
          uniformIndOccsE indNames lvls nP (offset + 1) b
      | .letE ty v b =>
        uniformIndOccsE indNames lvls nP offset ty &&
          uniformIndOccsE indNames lvls nP offset v &&
          uniformIndOccsE indNames lvls nP (offset + 1) b
      | .proj _ _ x => uniformIndOccsE indNames lvls nP offset x

/-- **Every occurrence of a datatype being declared is applied to the
declaration's parameters and universe levels** — the walk official
runs first, over every constructor type of the block
(`environment::add_inductive`, v4.34.0-rc2).  Later phases inspect the
constructor types modulo `whnf`, which can erase an occurrence, and the
parametric arguments of a nested occurrence are dropped from the
auxiliary declaration altogether, so a non-uniform occurrence would
otherwise escape checking; reduction never creates an occurrence of a
datatype being declared, so the syntactic occurrences are all of
them. -/
def uniformIndOccsOk (indNames : List Name) (lvls : List Level) (nP : Nat)
    (ctorTypes : List Expr) : Bool :=
  ctorTypes.all (uniformIndOccsE indNames lvls nP 0)

/-! ## The recogniser -/

/-- The pieces of a recognised NESTED block: the block's own members
(as the mutual route reads them) plus the stream's mimic recursors.
The block's own recursors and the mimics are compared with the
generated ones AFTER the restore (`checkNested`), never as a condition
of recognition — official's replay compares the exported recursor with
the generated one and rejects a mismatch, it does not decline. -/
structure NestedParts where
  /-- the formers in block order, with their index counts -/
  formers : List (ConstantVal × Nat)
  /-- the constructors in block order, member by member -/
  ctors : List MutualCtor
  /-- the declared parameter count -/
  nP : Nat
  /-- the block's level parameters -/
  lps : List Name
  /-- the recursors' level-parameter shape -/
  large : Bool
  /-- the elimination level parameter (`.anonymous` at the small one) -/
  elim : Name
  /-- the block's own recursors, in member order (`T_m.rec`) -/
  memberRecs : List (ConstantVal × List RecRule)
  /-- the mimic recursors `T₁.rec_1, T₁.rec_2, …`, in order -/
  mimicRecs : List (ConstantVal × List RecRule)
  deriving Repr, Inhabited

def NestedParts.k (p : NestedParts) : Nat := p.formers.length
def NestedParts.numNested (p : NestedParts) : Nat := p.mimicRecs.length
def NestedParts.memberNames (p : NestedParts) : List Name := p.formers.map (·.1.name)
/-- The mimic recursors' names, official's `mk_aux_rec_name_map`:
`<first member>.rec_1`, `.rec_2`, … in `all` order. -/
def NestedParts.mimicRecName (p : NestedParts) (j : Nat) : Name :=
  Name.appendIndexAfter ((p.formers.headD default).1.name.str "rec") (j + 1)

/-- **Recognise a nested block**: at least one type former and MORE
recursor records than formers — the kernel's nested→mutual
specialisation mints one recursor per mimic, so a block with `k`
formers and `k + n` recursors (`n ≥ 1`) claims `n` nested occurrences.
The first `k` recursors are the members' own (`T_m.rec`), the rest the
mimics' under `T₁.rec_j` in order.  Index counts are read off the
formers' own syntactic telescopes (a nested block's recursor records
carry the AUXILIARY block's argument sums, so `mI - rP` is not this
block's index count and a former declared at a definition is not
recognised here). -/
def nestedParts? (nPd : Nat) (block : List ConstantInfo) : Option NestedParts :=
  match mutualSplit block with
  | some (formers, cs, recs) =>
    let k := formers.length
    if k == 0 || recs.length ≤ k then none
    else if formers.any (fun cvT => reservedBasisNames.contains cvT.name) ||
        cs.any (fun c => reservedBasisNames.contains c.1.name) ||
        recs.any (fun r => reservedBasisNames.contains r.1.name) then none
    else
      let lps := (formers.headD default).levelParams
      let memberNames := formers.map (·.name)
      let recOf : Name → Option (ConstantVal × Nat × Nat × List RecRule) := fun T =>
        recs.find? fun r => r.1.name == T.str "rec"
      let members? : Option (List (ConstantVal × Nat)) := formers.mapM fun cvT => do
        let _ ← recOf cvT.name
        match cvT.type.piBinders with
        | (bs, .sort _) => if nPd ≤ bs.length then some (cvT, bs.length - nPd) else none
        | _ => none
      match members? with
      | none => none
      | some fs =>
        let n := recs.length - k
        let recName : Name → Option (ConstantVal × List RecRule) := fun nm =>
          (recs.find? fun r => r.1.name == nm).map fun r => (r.1, r.2.2.2)
        let memberRecs? := (formers.map (·.name.str "rec")).mapM recName
        let mimicName : Nat → Name := fun j =>
          Name.appendIndexAfter ((formers.headD default).name.str "rec") (j + 1)
        let mimicRecs? := ((List.range n).map mimicName).mapM recName
        match memberRecs?, mimicRecs? with
        | some mrs, some nrs =>
          -- every record accounted for: the members' and the mimics'
          -- names are distinct and exhaust the block's recursors
          if (mrs.map (·.1.name) ++ nrs.map (·.1.name)).Nodup &&
              mrs.length + nrs.length == recs.length then
            let ctors := cs.map fun (cvC, _, nF) =>
              (⟨cvC, nF, mutualCtorMember memberNames cvC.type⟩ : MutualCtor)
            let cvR₀ := (mrs.headD default).1
            match cvR₀.levelParams with
            | elim :: relps =>
              if relps == lps && !lps.contains elim then
                some ⟨fs, ctors, nPd, lps, true, elim, mrs, nrs⟩
              else some ⟨fs, ctors, nPd, lps, false, .anonymous, mrs, nrs⟩
            | [] => some ⟨fs, ctors, nPd, lps, false, .anonymous, mrs, nrs⟩
          else none
        | _, _ => none
  | none => none

end ConLeche

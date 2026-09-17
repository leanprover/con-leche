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

/-- `pre ++ n` — official's `name::operator+`. -/
def Name.appendName (pre : Name) : Name → Name
  | .anonymous => pre
  | .str p s => .str (Name.appendName pre p) s
  | .num p k => .num (Name.appendName pre p) k

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

/-! ## The containers' facts (task #279 K.14)

Three syntactic facts about the CONTAINERS a nested block nests
through.  The model tier's ψ needs them and no `IndRep`/`EnvWF` clause
exposes them (the model lane's DESIGN §M.28); they are facts of every
container the checker itself installed, so the route RE-ASKS them of the
stored constants and records the answer — the K.1–K.13 pattern, a
kernel-recorded fact rather than a new datum field.  A failure is
`.internal`: it cannot happen on an environment this checker built.  -/

/-- The motive's sort of a stored recursor: strip the `nP` parameter
binders, take the first motive binder's domain, and read the sort its
own telescope ends in (`Π ı⃗ (t : C p⃗ ı⃗), Sort w`). -/
def containerMotiveSort? (nP : Nat) (recTy : Expr) : Option Level :=
  match recTy.stripPis nP with
  | some (_, .forallE dom _ _) =>
    match dom.piBinders with
    | (_, .sort w) => some w
    | _ => none
  | _ => none

/-- **The two recursor facts** the model lane's `ContainersRep` states
of every container member (§M.28), read off the stored recursor's level
parameters and type:

* LARGE (the recursor carries one level parameter more than the block —
  the elimination universe, `u :: lps`): that universe is NOT among the
  block's own (`large → elim ∉ lps`), so a substitution at the pin's
  levels leaves it free for the carrier's rank;
* SMALL (the recursor's level parameters ARE the block's): the motive's
  sort is `Prop` (`large = false → w = 0`).

Both hold of every recursor the checker generates — the mutual route
mints the elimination universe with `mkUniqueName`-style freshness and
sets the motive's sort to `.zero` at a small-eliminating block — and
neither is exposed by any stored record, which is why they are asked
here. -/
def containerRecOk (env : Env) (nP : Nat) (J : ContainerMember) : Bool :=
  match env.find? (J.name.str "rec") with
  | some (.recInfo cvR _ _ _) =>
    if cvR.levelParams == J.lps then
      match containerMotiveSort? nP cvR.type with
      | some w => Level.isEquiv w .zero == some true
      | none => false
    else
      match cvR.levelParams with
      | u :: rest => rest == J.lps && !J.lps.contains u
      | [] => false
  | _ => false

/-- The head constant of a field domain, its OWN `Π` binders peeled (a
reflexive field's `a⃗ : A⃗` prefix), with the peel depth. -/
def fieldHeadAt (dom : Expr) : Option (Name × List Expr × Nat) :=
  let (fbs, res) := dom.piBinders
  match res.getAppFn with
  | .const C _ => some (C, res.getAppArgs, fbs.length)
  | _ => none

/-- **A field domain that MENTIONS the group is NOT ORDINARY**
(task #279 K.15 (3)) — it is one of the two shapes the positivity walk
leaves: the field's own binders peeled, the residual is an application
of a GROUP MEMBER whose first `nP` arguments are the block's parameters
(a recursive or reflexive field, the bound variables at the field's
frame: `nP` parameters, `i` earlier fields, the peeled binders), or of a
STORED INDUCTIVE (a NESTED field — the member sits inside that
container's parameters).  A field that mentions no member is ORDINARY
and passes.  This is the statement the model lane's `BridgeSyntax`
sub-term clause needs: a field the container classifies as ordinary
mentions no member, so a group pin cannot sit inside a pin minted there.

**The nested arm is not slack**, it is the shape a NESTED container
has: `P4C`'s own stored constructor carries `Array (P4C α)`, which
mentions the group member `P4C` without being headed by it
(`tests/e2e/nested_p04.ndjson`, measured — DESIGN K.15). -/
def containerFieldOk (env : Env) (names : List Name) (nP i : Nat) (dom : Expr) : Bool :=
  if !names.any (fun T => dom.mentionsConst T) then true else
  match fieldHeadAt dom with
  | some (C, args, d) =>
    (names.contains C && args.length ≥ nP &&
      (List.range nP).all (fun j => args[j]? == some (Expr.bvar (nP + i - 1 - j + d)))) ||
    (match env.find? C with | some (.indInfo _ _) => true | _ => false)
  | none => false

/-- The fields of one stored constructor. -/
def containerCtorFieldsOk (env : Env) (names : List Name) (nP : Nat) (c : ContainerCtor) :
    Bool :=
  match c.type.stripPis (nP + c.nFields) with
  | some (bs, _) =>
    (List.range c.nFields).all fun i =>
      match bs[nP + i]? with
      | some (dom, _) => containerFieldOk env names nP i dom
      | none => false
  | none => false

/-- **A group's members recover the same group** (K.15 (2)): every
member's own `containerInfo?` reads the same `all`-order and the same
parameter count — a fact of any environment this checker built (the
motive prefix of every member's recursor lists the block in block
order), and one the model tier needs to instantiate a group-mate's
reads at the group's one datum. -/
def containerGroupOk (env : Env) (ci : ContainerInfo) : Bool :=
  ci.members.all fun J =>
    match containerInfo? env J.name with
    | some ci' =>
      ci'.nP == ci.nP && ci'.members.map (·.name) == ci.members.map (·.name)
    | none => false

/-- **The four facts at one container**: its stored constructors'
occurrences of the group are UNIFORM — every occurrence of a member is
applied to the group's parameters and universe levels, which is
`uniformIndOccsOk`, the very walk official runs over a block being
declared (`check_uniform_ind_occs`) and this route runs over the nested
block itself — and the two recursor facts at every member.

The uniformity is what the model lane's `BridgeSyntax` sub-term clause
rests on: a pin of a group is that group's member applied to the pin's
components, so a group pin can be a sub-term of another pin only where
the stored constructor carries the member at the parameter spine, and
uniformity is exactly the statement that every occurrence is of that
shape.

**`Name.nodup J.lps`** (task #279 K.21) is the fourth: a member's
declared LEVEL PARAMETERS are pairwise distinct.  `checkConstantVal`
asks it of every constant at its own install, so it holds of any
container this checker stored; no record exposes it, and the model
tier's forward fire needs it for the level equation (a repeated
parameter would make the substitution at the pin's levels ambiguous).
The alternative — an `EnvWF`/`ConstWF` clause — was sized at a session
and reverted, so it is recorded here like the other three. -/
def containerFactsOk (env : Env) (ci : ContainerInfo) : Bool :=
  containerGroupOk env ci &&
  ci.members.all fun J =>
    Name.nodup J.lps &&
    uniformIndOccsOk (ci.members.map (·.name)) (J.lps.map Level.param) ci.nP
      (J.ctors.map (·.type)) &&
    containerRecOk env ci.nP J &&
    J.ctors.all (containerCtorFieldsOk env (ci.members.map (·.name)) ci.nP)

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

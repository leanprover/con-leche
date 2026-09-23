module

public import ConLeche.Kernel.CheckerBase
public import ConLeche.Kernel.Inductives.NativeParts

@[expose] public section

/-!
# Positivity: the one interface (lane NESTPOS, ARCH R2)

Everything the uniform route decides about WHERE the block occurs in a
constructor field lives here, and nothing about it anywhere else:

* **the occurrence test** at the block's whole member list
  (`Expr.mentionsAnyConst`, memoized by `@[csimp]`);
* **the normalisation** official's `check_positivity` classifies on
  (`normPosDom`/`normFieldDoms`/`normCtorVal`), at the member list;
* **the classifier** (`blockPositivity`/`blockFieldKind`/
  `blockCtorKinds`): official's walk at k names, a recursive occurrence
  carrying the member it TARGETS;
* **positivity through containers** (`nestPos`, the last section): ONE
  function, official's walk with a container case that recurses into the
  container's constructors at the CONCRETE instantiation (the charter,
  items 3–4) — GATED: the recogniser still routes a nested block to the
  modelled path, and only the `--nested-shadow` run and the tests call it.

**The walk has no proof consumer.**  Its verdict reaches the proofs
only through the syntactic re-check the install runs on the stored
constructors (`blockOpenedOk`, `ConLeche/Kernel/Inductives/BlockInstall.lean`),
which also carries the target bound `tgt < names.length`; the
normalisation's output is re-checked from scratch (`normCtorVal`).  So
the walk may be rewritten freely: only the mechanical fuel/cache
simulations (`Verify/BridgeDecl.lean`, `Verify/Cached/BridgeCS3.lean`)
unfold it.
-/

-- the `simp only` sets below are written for robustness against the
-- normal forms of the two sides, and several entries fire on one side only
set_option linter.unusedSimpArgs false

namespace ConLeche

/-! ## `mentionsAnyConst`: the positivity walk's question at k names -/

/-- Does any of the constants `names` occur in `e`?  A syntactic walk
(`fvar` annotations included; a `.proj` node names its structure) —
`Expr.mentionsConst` at a list, so that the k-ary positivity walk does
ONE traversal per field domain and not one per member. -/
def Expr.mentionsAnyConst (names : List Name) : Expr → Bool
  | .bvar _ | .sort _ | .lit _ => false
  | .const n _ => names.contains n
  | .fvar _ ty => ty.mentionsAnyConst names
  | .app f a => f.mentionsAnyConst names || a.mentionsAnyConst names
  | .lam ty b _ | .forallE ty b _ => ty.mentionsAnyConst names || b.mentionsAnyConst names
  | .letE ty v b =>
    ty.mentionsAnyConst names || v.mentionsAnyConst names || b.mentionsAnyConst names
  | .proj s _ e => names.contains s || e.mentionsAnyConst names

/-- Membership in a one-element name list. -/
theorem List.contains_singleton (T n : Name) : ([T] : List Name).contains n = (n == T) := by
  cases h : (n == T) <;> simp [List.contains, List.elem, h]

/-- At ONE name the walk is `Expr.mentionsConst`. -/
theorem Expr.mentionsAnyConst_single (T : Name) :
    ∀ e : Expr, e.mentionsAnyConst [T] = e.mentionsConst T
  | .bvar _ | .sort _ | .lit _ => rfl
  | .const n _ => List.contains_singleton T n
  | .fvar _ ty => by
    simp [Expr.mentionsAnyConst, Expr.mentionsConst, Expr.mentionsAnyConst_single T ty]
  | .app f a => by
    simp [Expr.mentionsAnyConst, Expr.mentionsConst, Expr.mentionsAnyConst_single T f,
      Expr.mentionsAnyConst_single T a]
  | .lam ty b _ => by
    simp [Expr.mentionsAnyConst, Expr.mentionsConst, Expr.mentionsAnyConst_single T ty,
      Expr.mentionsAnyConst_single T b]
  | .forallE ty b _ => by
    simp [Expr.mentionsAnyConst, Expr.mentionsConst, Expr.mentionsAnyConst_single T ty,
      Expr.mentionsAnyConst_single T b]
  | .letE ty v b => by
    simp [Expr.mentionsAnyConst, Expr.mentionsConst, Expr.mentionsAnyConst_single T ty,
      Expr.mentionsAnyConst_single T v, Expr.mentionsAnyConst_single T b]
  | .proj s _ e => by
    show (([T] : List Name).contains s || e.mentionsAnyConst [T]) = ((s == T) || e.mentionsConst T)
    rw [List.contains_singleton, Expr.mentionsAnyConst_single T e]

/-! ### `mentionsAnyConst`, memoized

`Expr.mentionsConst`'s arrangement (`ConLeche/Kernel/Inductives/StructParts.lean`):
the tree walk does not finish on a DAG-shared field type, the memoized
walk is swapped in by `@[csimp]`, and the pure definition stays what
every proof consumes.  The memo is keyed by the node and dropped after
each call (the answer depends on `names`). -/

/-- The memo's invariant: every recorded answer is the real one. -/
def MentionsAnyMemoInv (names : List Name) (memo : Std.HashMap Expr Bool) : Prop :=
  ∀ (k : Expr) (r : Bool), memo[k]? = some r → r = k.mentionsAnyConst names

theorem MentionsAnyMemoInv.empty {names : List Name} : MentionsAnyMemoInv names {} := by
  intro k r h; simp at h

theorem MentionsAnyMemoInv.insert {names : List Name} {memo : Std.HashMap Expr Bool}
    (hm : MentionsAnyMemoInv names memo) {e : Expr} {r : Bool}
    (heq : r = e.mentionsAnyConst names) :
    MentionsAnyMemoInv names (memo.insert e r) := by
  intro e' r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact heq
  · exact hm e' r' hk

/-- Record one answer in the memo the walk hands back. -/
@[inline] def Expr.mentionsAnyIns (e : Expr)
    (r : Bool × Std.HashMap Expr Bool) : Bool × Std.HashMap Expr Bool :=
  (r.1, r.2.insert e r.1)

/-- Memoized `mentionsAnyConst`. -/
def Expr.mentionsAnyGo (names : List Name) (memo : Std.HashMap Expr Bool) :
    Expr → Bool × Std.HashMap Expr Bool
  | .bvar _ => (false, memo)
  | .sort _ => (false, memo)
  | .lit _ => (false, memo)
  | .const n _ => (names.contains n, memo)
  | e =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Bool × Std.HashMap Expr Bool :=
        match e with
        | .fvar _ ty => mentionsAnyGo names memo ty
        | .app f a =>
          let (b₁, memo) := mentionsAnyGo names memo f
          let (b₂, memo) := mentionsAnyGo names memo a
          (b₁ || b₂, memo)
        | .lam ty body _ =>
          let (b₁, memo) := mentionsAnyGo names memo ty
          let (b₂, memo) := mentionsAnyGo names memo body
          (b₁ || b₂, memo)
        | .forallE ty body _ =>
          let (b₁, memo) := mentionsAnyGo names memo ty
          let (b₂, memo) := mentionsAnyGo names memo body
          (b₁ || b₂, memo)
        | .letE ty val body =>
          let (b₁, memo) := mentionsAnyGo names memo ty
          let (b₂, memo) := mentionsAnyGo names memo val
          let (b₃, memo) := mentionsAnyGo names memo body
          (b₁ || b₂ || b₃, memo)
        | .proj s _ sub =>
          let (b, memo) := mentionsAnyGo names memo sub
          (names.contains s || b, memo)
        | e => (e.mentionsAnyConst names, memo)
      (r, memo.insert e r)

/-- **The memoized walk is `mentionsAnyConst`.** -/
theorem Expr.mentionsAnyGo_spec {names : List Name} :
    ∀ (e : Expr) (memo : Std.HashMap Expr Bool), MentionsAnyMemoInv names memo →
      (mentionsAnyGo names memo e).1 = e.mentionsAnyConst names ∧
        MentionsAnyMemoInv names (mentionsAnyGo names memo e).2 := by
  intro e
  induction e with
  | bvar i => intro memo hm; exact ⟨rfl, hm⟩
  | sort u => intro memo hm; exact ⟨rfl, hm⟩
  | const n us => intro memo hm; exact ⟨rfl, hm⟩
  | lit l => intro memo hm; exact ⟨rfl, hm⟩
  | fvar i ty ih =>
    intro memo hm
    rw [mentionsAnyGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := ih memo hm
      refine ⟨by simp [mentionsAnyConst, h1], ?_⟩
      exact h2.insert (by simp [mentionsAnyConst, h1])
  | app a b iha ihb =>
    intro memo hm
    rw [mentionsAnyGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iha memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      refine ⟨by simp [mentionsAnyConst, h1, h3], ?_⟩
      exact h4.insert (by simp [mentionsAnyConst, h1, h3])
  | lam ty body bi iht ihb =>
    intro memo hm
    rw [mentionsAnyGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      refine ⟨by simp [mentionsAnyConst, h1, h3], ?_⟩
      exact h4.insert (by simp [mentionsAnyConst, h1, h3])
  | forallE ty body bi iht ihb =>
    intro memo hm
    rw [mentionsAnyGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      refine ⟨by simp [mentionsAnyConst, h1, h3], ?_⟩
      exact h4.insert (by simp [mentionsAnyConst, h1, h3])
  | letE ty val body iht ihv ihb =>
    intro memo hm
    rw [mentionsAnyGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihv _ h2
      obtain ⟨h5, h6⟩ := ihb _ h4
      refine ⟨by simp [mentionsAnyConst, h1, h3, h5], ?_⟩
      exact h6.insert (by simp [mentionsAnyConst, h1, h3, h5])
  | proj s i sub ih =>
    intro memo hm
    rw [mentionsAnyGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := ih memo hm
      refine ⟨by simp [mentionsAnyConst, h1], ?_⟩
      exact h2.insert (by simp [mentionsAnyConst, h1])

/-- The executed `mentionsAnyConst` (one memoized DAG walk). -/
def Expr.mentionsAnyConstFast (names : List Name) (e : Expr) : Bool :=
  (mentionsAnyGo names {} e).1

@[csimp] theorem Expr.mentionsAnyConst_eq_mentionsAnyConstFast :
    @Expr.mentionsAnyConst = @Expr.mentionsAnyConstFast := by
  funext names e
  exact (mentionsAnyGo_spec e {} MentionsAnyMemoInv.empty).1.symm

/-! ## Positivity across the block's k names

Official's `check_positivity` (`inductive.cpp`) with `m_ind_cnsts` the
whole member list: a field domain is classified against EVERY member of
the block, and a recursive occurrence carries the member it names.  At
one member this is `recPositivity`'s reading with the target `0`
(`ConLeche/Kernel/Inductives/NativeParts.lean`), which is why
`BlockFieldKind.toRec` forgets exactly the target. -/

/-- The kind of a constructor field of a block, with the TARGET member
a recursive or reflexive occurrence names (decision D7: the target
lives in the kind, not in a parallel list). -/
inductive BlockFieldKind where
  /-- the domain mentions no member of the block -/
  | ordinary
  /-- the domain is exactly `T_tgt p⃗ e⃗`: a finitary recursive field -/
  | recursive (tgt : Nat)
  /-- the domain is `Π a⃗ : A⃗, T_tgt p⃗ e⃗(a⃗)` with `A⃗` free of the
  block: a REFLEXIVE (function-space) recursive field (task #202) -/
  | reflexive (tgt : Nat)
  /-- a non-positive (or non-valid) occurrence: the official kernel
  rejects the block -/
  | negative
  /-- an occurrence the official kernel accepts (nested, under a redex)
  that this route does not model yet -/
  | unsupported
  deriving Repr, DecidableEq, Inhabited

/-- The one-member reading: the kind without its target. -/
def BlockFieldKind.toRec : BlockFieldKind → RecFieldKind
  | .ordinary => .ordinary
  | .recursive _ => .recursive
  | .reflexive _ => .reflexive
  | .negative => .negative
  | .unsupported => .unsupported

/-- Which member of the block a head expression names, at the block's
own level parameters (official's `m_ind_cnsts` lookup): `none` at any
other head, INCLUDING a member's constant at other levels — which
`blockPositivity` then classifies as the official "non valid
occurrence". -/
def memberIdxAt? (names : List Name) (lvls : List Level) : Expr → Option Nat
  | .const n us => if us == lvls then names.findIdx? (· == n) else none
  | _ => none

/-- The member a head expression names, `0` at any other head (which
`blockFamOk`'s own head test then refuses): the TARGET, read
positionally so that the walk's shape is the one-name walk's. -/
def memberTgt (names : List Name) (lps : List Name) (e : Expr) : Nat :=
  (memberIdxAt? names (lps.map .param) e.getAppFn).getD 0

/-- Is `e` the block's member `memberTgt e` at the parameter variables
(sitting `o` binders up) followed by that member's index expressions,
none of which mentions any member?  Official's `is_valid_ind_app` at k
names: the head, the arity, the parameters (structurally) and
`has_ind_occ` on every index argument. -/
def blockFamOk (names : List Name) (lps : List Name) (nP : Nat) (nIdxs : List Nat)
    (o : Nat) (e : Expr) : Bool :=
  e.getAppFn == Expr.const (names.getD (memberTgt names lps e) default) (lps.map .param) &&
  e.getAppArgs.length == nP + nIdxs.getD (memberTgt names lps e) 0 &&
  e.getAppArgs.take nP == structPsAt o nP &&
  (e.getAppArgs.drop nP).all fun a => !a.mentionsAnyConst names

/-- Official `check_positivity`'s telescope walk on a field domain that
mentions the block, at k names: `k` binders of the field's own
telescope have been peeled (the parameters sit `o + k` binders up).  A
member application at the head whose parameters are not the block's,
with the wrong number of arguments, or whose INDEX expressions mention
a member is the official "non valid occurrence" (`.negative`); an
application of another constant is a nested occurrence
(`.unsupported`: the modeled path).  The kind carries the target
member (decision D7). -/
def blockPositivity (names : List Name) (lps : List Name) (nP : Nat) (nIdxs : List Nat)
    (o : Nat) : Expr → Nat → BlockFieldKind
  | .forallE dom body _, k =>
    if dom.mentionsAnyConst names then .negative
    else blockPositivity names lps nP nIdxs o body (k + 1)
  | e, k =>
    if !e.mentionsAnyConst names then .ordinary
    else if e.getAppFn ==
        Expr.const (names.getD (memberTgt names lps e) default) (lps.map .param) then
      (if e.getAppArgs.length == nP + nIdxs.getD (memberTgt names lps e) 0 &&
          e.getAppArgs.take nP == structPsAt (o + k) nP then
        (if blockFamOk names lps nP nIdxs (o + k) e then
          (if k == 0 then .recursive (memberTgt names lps e)
           else .reflexive (memberTgt names lps e))
         else .negative)
       else .negative)
    else
      match e.getAppFn with
      | .const T' _ => if names.contains T' then .negative else .unsupported
      | _ => .unsupported

/-- The kind of a field whose domain is `dom`, `o` fields into the
constructor's telescope. -/
def blockFieldKind (names : List Name) (lps : List Name) (nP : Nat) (nIdxs : List Nat)
    (o : Nat) (dom : Expr) : BlockFieldKind :=
  if dom.mentionsAnyConst names then blockPositivity names lps nP nIdxs o dom 0
  else .ordinary

/-- The kinds of one constructor's fields, off its (raw or annotated)
type — `recCtorKinds` at the member list (its docstring's argument for
the `structUsedLater` guard is unchanged: the guard is the model's own
invariant, never a verdict of its own). -/
def blockCtorKinds (names : List Name) (lps : List Name) (nP : Nat) (nIdxs : List Nat)
    (c : ConstantVal × Nat) : Option (List BlockFieldKind) :=
  match c.1.type.stripPis (nP + c.2) with
  | some (cbs, cbody) =>
    let ks := (List.range c.2).map fun i =>
      match blockFieldKind names lps nP nIdxs i (cbs.getD (nP + i) default).1 with
      | .recursive t => if structUsedLater c.1.type nP i then .unsupported else .recursive t
      | .reflexive t => if structUsedLater c.1.type nP i then .unsupported else .reflexive t
      | k => k
    if (cbody.getAppArgs.drop nP).all (fun a => !a.mentionsAnyConst names) then some ks
    else some (ks.map fun _ => .negative)
  | none => none

/-! ## The normalisation official classifies on -/

section Norm

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]

/-- Close a telescope opened at the free variables `i ..< i + bs.length`
back into a syntactic Π-telescope over `body`: innermost binder first,
each abstraction turning the binder's own free variable into the bound
one (`abstract1`; the domains of the inner binders are closed by the
outer abstractions, which descend into binder domains). -/
def closeTelescope : List (Expr × BinderMeta) → Nat → Expr → Expr
  | [], _, body => body
  | (dom, bm) :: bs, i, body =>
    .forallE dom ((closeTelescope bs (i + 1) body).abstract1 i 0) bm

/-- **Official's positivity walk, as a normalisation** (task #210 Part
D, audit #206-A5): `check_positivity` (`inductive.cpp`) reduces a
constructor field's type to weak head normal form before classifying
it, and again under every Π binder of a reflexive field.  A field whose
type only whnf's to an occurrence of the block (`Id' T`, `Nat → Id' T`)
is recursive for official and invisible to a syntactic reading.  So the
field's domain is REPLACED by the form official classifies: whnf'd at
its own depth, and — while the block occurs — walked under its Π
binders (a Π domain mentioning the block is official's "non positive
occurrence", INVALID), each body whnf'd in turn.  A domain the block
does not occur in is kept as declared, unreduced (official whnf's it
too, and discards the result: reduction cannot introduce the block);
one it occurs in only before whnf (`idf (T → Type) (fun _ => N) t`,
which official classifies as an ordinary field) is REPLACED by the
whnf'd form, so that the field no longer mentions the block nor, with
it, any earlier recursive field (`structUsedLater`).  The result is
definitionally equal to the declared domain; the constructor is
re-checked from scratch on the rebuilt type (`normCtorVal`), so
nothing about the reduction is trusted — task #195's arrangement at
the type former, now at the fields.  `fuel` bounds the Π walk (a
reflexive field's own telescope); exhaustion is a positive decline.

**The block is its WHOLE member list** (lane NESTPOS, ARCH R2(c)):
"mentions the block" is `mentionsAnyConst names`, official's
`has_ind_occ` over `m_ind_cnsts`.  With the member's own name alone, a
field of `A` that reaches ANOTHER member `B` only through a redex
(`Id' B`, `Fn B`, `Const' Unit B`) was kept as declared, and the
classifier then read the redex's head as a nested occurrence and
declined a block official accepts (the four
`tests/e2e/corner_mutual_redex_other*` fixtures). -/
def normPosDom (ops : CheckerOps m) (env : Env) (names : List Name) :
    Nat → Nat → Expr → m Expr
  | _, 0, _ => throw (.notImplemented "direct sum: positivity walk fuel")
  | d, fuel + 1, e => do
    if !e.mentionsAnyConst names then pure e else
    let w ← ops.whnf env d e
    if !w.mentionsAnyConst names then pure w else
    match w with
    | .forallE dom body bm =>
      if dom.mentionsAnyConst names then
        throw (.invalid "direct sum: non positive occurrence of the inductive type")
      else do
        let body' ← normPosDom ops env names (d + 1) fuel (body.instantiate1 (.fvar d dom))
        pure (.forallE dom (body'.abstract1 d) bm)
    | _ => pure w

/-- The constructor's field binders with their domains normalised
(`normPosDom`), opened at the free variables `i ..< i + n` as
`whnfTelescope` opens the former's; the residual returned scoped at
those variables. -/
def normFieldDoms (ops : CheckerOps m) (env : Env) (names : List Name) :
    Nat → Nat → Expr → m (List (Expr × BinderMeta) × Expr)
  | _, 0, e => pure ([], e)
  | i, n + 1, .forallE dom body bm => do
    let dom' ← normPosDom ops env names i 1024 dom
    let (bs, r) ← normFieldDoms ops env names (i + 1) n (body.instantiate1 (.fvar i dom))
    pure ((dom', bm) :: bs, r)
  | _, _ + 1, _ => throw (.notImplemented "direct sum: constructor field telescope")

/-- The checked constructor with its field domains normalised: the
parameter binders as declared, the field binders through
`normFieldDoms`, closed back into a telescope (`closeTelescope`) and
— when anything changed — checked as the constructor's type in its
place, from scratch. -/
def normCtorVal (ops : CheckerOps m) (env : Env) (names : List Name) (nP nF : Nat)
    (cvC cvCa : ConstantVal) : m ConstantVal := do
  let (cbs, _) ← unwrapOr (cvCa.type.stripPis nP)
    (.notImplemented "direct sum: constructor telescope")
  let (fvsP, crest) ← unwrapOr (openPisAtFvars nP cvCa.type 0)
    (.notImplemented "direct sum: constructor telescope")
  let pbs := List.zipWith (fun (x : Expr) (b : Expr × BinderMeta) => (x.fvarTypeD, b.2)) fvsP cbs
  let (fbs, resid) ← normFieldDoms ops env names nP nF crest
  let ty' := closeTelescope (pbs ++ fbs) 0 resid
  if ty' == cvCa.type then pure cvCa
  else checkConstantVal ops env { cvC with type := ty' }

end Norm

/-! ## Positivity through containers — ONE function, GATED

The charter (DESIGN.md, "THE CHARTER", items 3–4): there is ONE
positivity function in the kernel; it reduces with the kernel's own
verified whnf (`ops.whnf`, β, δ, ι, …); the theorem to come is
"returns ⇒ the operator is monotone", by inversion of its run.  It
looks through a container at the CONCRETE instantiation `C (t[X])`:
the arguments `t[X]` — λ or not — are substituted into `C`'s
constructors and positivity is checked there, jointly in the member
holes `X` and in the instantiation's own recursive occurrences `Y`.
Nothing is stated or cached about a container in the abstract: the
only cache is keyed by the instantiation.  Official's nested→mutual
encoding is never mirrored: no auxiliary type, constructor or name.

**`nestPos`, the function**, by structural recursion on its fuel; its
cases are the monotonicity induction's:

* the whnf of the domain mentions no member — hole-free (`const`);
* a `Π` whose domain mentions no member — recurse on the body (`pi`);
* a member at the block's levels and parameters with member-free
  indices — a hole (`holeApp`, official's `is_valid_ind_app` :338);
* a stored inductive `C` (not a member) applied to parameters `Ds`
  (some mentioning a member, none a field or binder variable — official
  :962) and member-free indices (`contApp`): an instantiation IN
  PROGRESS is a `Y` hole; one already accepted is a cache hit; else its
  checks — (N2) the instantiated index telescope names no member
  (official checks the auxiliary type former before the block exists,
  :219), (N3) its sort `Level.isEquiv` the block's (:250) — and then
  `nestPos` on every field of every constructor of `C` AT the
  instantiation, the instantiation pushed onto the in-progress list,
  and the constructor's result indices member-free;
* anything else — official's "non valid occurrence".

**No basis special-casing** but one: `Quot`, stored as an `.indInfo`
yet no inductive for official, is a "non valid occurrence" as a
container head.  The pinned `Eq`/`Nat`/`PUnit`/`Empty`/`False` (and the
stream's `And`) are read from the environment like any stored inductive
— their constructors are `.ctorInfo` records with parameter counts.
The parameter-free ones never reach the container case; `Eq` (two
parameters, `α` and `a`, as official) always ends in official's
verdicts: a field in `a` is a local variable, `@Eq Prop (T p) True`
fails the instantiated `refl`'s result index ("invalid return type"),
`@Eq Prop T T` has a member in an index (probes, lane NESTPOS).

**Fuel**: `nestPos` recurses on an explicit fuel (1024 per member field,
one unit per `Π` body and per container field descent) and the cache
holds at most 4096 instantiations; running out of either THROWS
`.notImplemented` — a decline (exit 2), never an accept.  A
non-uniformly growing instantiation (`C α | mk : C (List α) → C α`,
which official's parameters forbid) is the shape that could reach it.

**Recorded departures from official** (all accept-supersets, each with
an e2e fixture; raised with the maintainer per the charter):
* official locates nested instances SYNTACTICALLY, before any whnf
  (`replace_all_nested` :1043), so a container reached only by
  reduction (`F T`, `F α := List α`) is a "non valid occurrence" there;
  here the container case reads the whnf, so it accepts
  (`corner_nestpos_redex_bad`);
* official copies EVERY member of the container's mutual group
  (:1009), reachable or not; here only the instantiations a field
  reaches are checked (`corner_nestpos_group_bad`).
* a container with NO constructor has no recorded parameter count and
  is DECLINED (exit 2), never guessed.

**The gate.**  Nothing in the install calls this section: the
recogniser (`blockParts?`) still routes every nested block to the
modelled path.  `--nested-shadow` (`Main.lean`, `tests/nested-shadow.sh`)
runs it beside the install, and the unit tests run its pure
instantiation.
-/

section Nested

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]

/-- Does a MEMBER occur in `e`?  Official's `has_ind_occ`: constants
only — a free variable's annotation is NOT looked into (a local's type
lives in the local context, not in the term) and a `.proj` node's
structure name is no occurrence.  Memoised on the node. -/
def Expr.nestOccGo (names : List Name) (memo : Std.HashMap Expr Bool) :
    Expr → Bool × Std.HashMap Expr Bool
  | .bvar _ => (false, memo)
  | .sort _ => (false, memo)
  | .lit _ => (false, memo)
  | .fvar _ _ => (false, memo)
  | .const n _ => (names.contains n, memo)
  | e =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Bool × Std.HashMap Expr Bool :=
        match e with
        | .app f a =>
          let (b₁, memo) := nestOccGo names memo f
          if b₁ then (true, memo) else nestOccGo names memo a
        | .lam ty body _ =>
          let (b₁, memo) := nestOccGo names memo ty
          if b₁ then (true, memo) else nestOccGo names memo body
        | .forallE ty body _ =>
          let (b₁, memo) := nestOccGo names memo ty
          if b₁ then (true, memo) else nestOccGo names memo body
        | .letE ty val body =>
          let (b₁, memo) := nestOccGo names memo ty
          if b₁ then (true, memo) else
          let (b₂, memo) := nestOccGo names memo val
          if b₂ then (true, memo) else nestOccGo names memo body
        | .proj _ _ sub => nestOccGo names memo sub
        | _ => (false, memo)
      (r, memo.insert e r)

/-- `nestOccGo` from an empty memo. -/
def Expr.nestOcc (names : List Name) (e : Expr) : Bool :=
  (e.nestOccGo names {}).1

/-- Instantiate the leading `Π` binders of `e` at `args`, in order
(the parameters of a constructor or a type former). -/
def instPisWith : List Expr → Expr → Option Expr
  | [], e => some e
  | a :: as, .forallE _ body _ => instPisWith as (body.instantiate1 a)
  | _ :: _, _ => none

/-- A container INSTANTIATION `C.{lvls} Ds`, its parameters scoped at the
block's canonical parameter variables `0 ..< nP` — the key of the only
cache there is. -/
structure NestKey where
  cname : Name
  lvls : List Level
  ds : List Expr
  deriving DecidableEq, Repr, Inhabited

/-- An accepted instantiation: its key and its index count. -/
structure NestKeyInfo where
  key : NestKey
  nIdx : Nat
  deriving Repr, Inhabited

/-- The field's kind as the run found it: hole-free, a member hole
(finitary or under `Π` binders), an instantiation IN PROGRESS (a `Y`
hole — only inside a container's constructors), or an accepted
instantiation `key` (index into the table; under `Π` binders when
`refl`). -/
inductive NestFieldKind where
  | ordinary
  | recursive (tgt : Nat)
  | reflexive (tgt : Nat)
  | inProgress
  | nested (key : Nat) (refl : Bool)
  deriving DecidableEq, Repr, Inhabited

/-- The block, as the function needs it: the members, their level
parameters, the shared parameter count and the members' index counts,
the canonical parameter variables, the block's sort, and the
environment's lookup and constant list (the pure `Env`'s or the cached
index's). -/
structure NestCtx where
  names : List Name
  lps : List Name
  nP : Nat
  nIdxs : List Nat
  params : List Expr
  sort : Level
  find? : Name → Option ConstantInfo
  consts : List ConstantInfo

/-- The run's state: the accepted instantiations (the cache, keyed by the
instantiation, in completion order) and the environment lookups of
container constructor lists (`none`: no inductive) — a reading of the
environment, not a fact about the container. -/
structure NestState where
  keys : Array NestKeyInfo := #[]
  ctorsOf : List (Name × Option (Nat × List (ConstantVal × Nat))) := []
  deriving Inhabited

/-- What the run found: the accepted instantiations and every member
constructor's field kinds. -/
structure NestedPositivity where
  keys : Array NestKeyInfo
  kinds : List (List (List NestFieldKind))
  deriving Inhabited

/-- The constructors of the inductive `C` and its parameter count, read
off the environment (a constructor belongs to the type its result
names, `ctorMember?`'s reading): `none` when `C` is no inductive;
`some (0, [])` for an inductive without constructors. -/
def nestContainer (ctx : NestCtx) (C : Name) : Option (Nat × List (ConstantVal × Nat)) :=
  match ctx.find? C with
  | some (.indInfo _ _) =>
    let cs := ctx.consts.filterMap fun ci =>
      match ci with
      | .ctorInfo cv nPc nF =>
        match cv.type.stripPis (nPc + nF) with
        | some (_, body) =>
          match body.getAppFn with
          | .const n _ => if n == C then some (cv, nPc, nF) else none
          | _ => none
        | none => none
      | _ => none
    match cs with
    | [] => some (0, [])
    | (_, nPc, _) :: _ => some (nPc, (cs.map fun c => (c.1, c.2.2)).reverse)
  | _ => none

/-- `nestContainer`, looked up once per name. -/
def nestContainerC (ctx : NestCtx) (st : NestState) (C : Name) :
    Option (Nat × List (ConstantVal × Nat)) × NestState :=
  match st.ctorsOf.lookup C with
  | some r => (r, st)
  | none =>
    let r := nestContainer ctx C
    (r, { st with ctorsOf := (C, r) :: st.ctorsOf })

/-- Official's "non valid occurrence" (`check_positivity` :405). -/
def nestNonValid : CheckError :=
  .invalid "nested positivity: non valid occurrence of the datatypes being declared"

/-- The instantiation's type former, checked as official checks the
auxiliary type BEFORE the block exists: (N2) its index telescope at
`Ds` names no member (official: "unknown constant"), (N3) its sort is
`Level.isEquiv` the block's.  Returns the index count. -/
def nestInstType (ctx : NestCtx) (key : NestKey) : m Nat := do
  let some (.indInfo cvC _) := ctx.find? key.cname
    | throw (.internal "nested positivity: container vanished")
  let ty0 := cvC.type.instantiateLevelParams cvC.levelParams key.lvls
  let some ty := instPisWith key.ds ty0
    | throw (.notImplemented "nested positivity: container type telescope")
  let (ibs, s) := ty.piBinders
  let .sort s := s
    | throw (.notImplemented "nested positivity: container type is not a syntactic telescope")
  if ibs.any (fun b => b.1.mentionsAnyConst ctx.names) then
    throw (.invalid "nested positivity: a container's index telescope mentions the block \
      (official: unknown constant)")
  unless Level.isEquiv s ctx.sort == some true do
    throw (.invalid "nested positivity: mutually inductive types must live in the \
      same universe")
  pure ibs.length

/-- **The positivity function** (see the section header): the domain
`e` at depth `dep`, `kb` `Π` binders into the field, `prog` the
instantiations in progress.  Throws official's verdict on a
non-positive or non-valid occurrence; returns the field's kind and the
cache. -/
def nestPos (ops : CheckerOps m) (env : Env) (ctx : NestCtx) :
    Nat → List NestKey → Nat → Nat → Expr → NestState → m (NestFieldKind × NestState)
  | 0, _, _, _, _, _ => throw (.notImplemented "nested positivity: fuel")
  | fuel + 1, prog, dep, kb, e, st => do
    let w ← ops.whnf env dep e
    -- `const`: the reduct mentions no member
    if !w.nestOcc ctx.names then return (.ordinary, st)
    match w with
    | .forallE a b _ =>
      -- `pi`: the domain member-free, the codomain positive
      if a.nestOcc ctx.names then
        throw (.invalid "nested positivity: non positive occurrence of the datatypes \
          being declared")
      nestPos ops env ctx fuel prog (dep + 1) (kb + 1) (b.instantiate1 (.fvar dep a)) st
    | _ =>
      let args := w.getAppArgs
      let free (xs : List Expr) : Bool := xs.all fun x => !x.nestOcc ctx.names
      match w.getAppFn with
      | .const n us =>
        match ctx.names.findIdx? (· == n) with
        | some t =>
          -- `holeApp`: a member at the block's levels and parameters
          if us == ctx.lps.map .param && args.length == ctx.nP + ctx.nIdxs.getD t 0 &&
              args.take ctx.nP == ctx.params && free (args.drop ctx.nP) then
            return (if kb == 0 then .recursive t else .reflexive t, st)
          else throw nestNonValid
        | none =>
          -- `contApp`: a stored inductive at a concrete instantiation
          let (ci, st) := nestContainerC ctx st n
          let some (nPc, ctors) := ci | throw nestNonValid
          if ctors.isEmpty then
            throw (.notImplemented "nested positivity: a container without constructors \
              (its parameter count is not recorded)")
          if args.length < nPc || !free (args.drop nPc) then throw nestNonValid
          -- `Quot` is stored as an `.indInfo` but is no inductive for
          -- official (`is_nested_inductive_app` asks `is_inductive()`):
          -- the one name read here.  Every other basis type (`Eq`, `Nat`,
          -- `PUnit`, `Empty`, `False`, and `And`) is a container like any
          -- stored inductive.
          if n == quotName then throw nestNonValid
          let ds := args.take nPc
          unless ds.all (fun x => x.bvarB == 0 && x.fvarB ≤ ctx.nP) do
            throw (.invalid "nested positivity: nested inductive datatypes parameters \
              cannot contain local variables")
          let key : NestKey := ⟨n, us, ds⟩
          if prog.contains key then return (.inProgress, st)
          match st.keys.findIdx? (·.key == key) with
          | some q => return (.nested q (kb != 0), st)
          | none =>
            let nIdx ← nestInstType ctx key
            let prog' := key :: prog
            let mut st := st
            for (cv, nF) in ctors do
              let ty := cv.type.instantiateLevelParams cv.levelParams us
              let some crest := instPisWith ds ty
                | throw (.notImplemented "nested positivity: container constructor telescope")
              let mut cur := crest
              for j in List.range nF do
                match cur with
                | .forallE a b _ =>
                  let (_, st') ← nestPos ops env ctx fuel prog' (ctx.nP + j) 0 a st
                  st := st'
                  cur := b.instantiate1 (.fvar (ctx.nP + j) a)
                | _ => throw (.notImplemented "nested positivity: container constructor fields")
              -- official's "invalid return type" on the instantiated constructor
              unless free (cur.getAppArgs.drop nPc) do
                throw (.invalid "nested positivity: invalid return type of an instantiated \
                  container constructor (an index mentions the block)")
            if st.keys.size ≥ 4096 then
              throw (.notImplemented "nested positivity: instantiation fuel")
            return (.nested st.keys.size (kb != 0),
              { st with keys := st.keys.push ⟨key, nIdx⟩ })
      | _ => throw nestNonValid

/-- The fields of one member constructor (the parameters instantiated
at the canonical variables), each through `nestPos` at its depth. -/
def nestMemberCtor (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (nF : Nat) (crest : Expr)
    (st : NestState) : m (List NestFieldKind × NestState) := do
  let mut st := st
  let mut cur := crest
  let mut ks : Array NestFieldKind := #[]
  for j in List.range nF do
    match cur with
    | .forallE a b _ =>
      let (k, st') ← nestPos ops env ctx 1024 [] (ctx.nP + j) 0 a st
      st := st'
      ks := ks.push k
      cur := b.instantiate1 (.fvar (ctx.nP + j) a)
    | _ => throw (.notImplemented "nested positivity: constructor field telescope")
  pure (ks.toList, st)

/-- **Positivity through containers, for a whole block**: every member
constructor's fields through `nestPos`, sharing one cache.  `ctorss`
are the members' constructors ANNOTATED (not normalised: the function
reduces itself). -/
def nestedBlockPositivity (ops : CheckerOps m) (env : Env) (ctx : NestCtx)
    (ctorss : List (List (ConstantVal × Nat))) : m NestedPositivity := do
  let mut st : NestState := {}
  let mut kinds : Array (List (List NestFieldKind)) := #[]
  for cs in ctorss do
    let mut kss : Array (List NestFieldKind) := #[]
    for c in cs do
      let some crest := instPisWith ctx.params c.1.type
        | throw (.notImplemented "nested positivity: constructor parameter telescope")
      let (ks, st') ← nestMemberCtor ops env ctx c.2 crest st
      st := st'
      kss := kss.push ks
    kinds := kinds.push kss.toList
  pure ⟨st.keys, kinds.toList⟩

end Nested

end ConLeche

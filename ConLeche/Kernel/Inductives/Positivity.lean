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
* **positivity through containers** (`nestedBlockPositivity`, the last
  section): official's nested class (N1)–(N4) decided at the concrete
  parameter instantiation, recursively and memoised on the container
  instance — GATED: the recogniser still routes a nested block to the
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

/-! ## Positivity through containers — official's nested class, GATED

The maintainer's direction (DESIGN, the uniform charter): a field
`C a⃗ (… T …)` whose head `C` is an inductive ALREADY in the environment
is positive when, after instantiating `C`'s constructors at those
parameters, the block occurs positively in them — recursively (a
container's constructors may themselves nest), memoised on the
container INSTANCE, at the CONCRETE parameters.  Official's
nested→mutual encoding is NOT mirrored: no auxiliary type, constructor
or name is minted, nothing is stored, and the instance a field nests
through is stood for, during the walk only, by a free variable
(`y_q`, the placeholder) the way DESIGN theory v2 §2.1 "abstracts" it.

**Official's class** (`_tmp/lean4-src/src/kernel/inductive.cpp`,
`elim_nested_inductive_fn` :894–1090 then `add_inductive_fn` on the
auxiliary declaration; TWIN-O §6.2, TWIN-F §9.2), and where each
clause is decided here:

* **(N1) detection is syntactic** (`is_nested_inductive_app` :932,
  `replace_all_nested` :1043): a subterm `C Ds is` of a constructor's
  DECLARED field type, `C` an inductive of the environment, some
  parameter in `Ds` naming a member; OUTERMOST first (`replace` does not
  descend into a replaced node); a `Ds` with a loose bound variable —
  a field or a binder of the field's own telescope — is a REJECT
  ("nested inductive datatypes parameters cannot contain local
  variables").  `nestLocate`, before any `whnf`: a container reached
  only by reduction (`F T` with `F α := List α`) is not located, and
  the walk then rejects it as official does ("non valid occurrence").
* **(N2) the instance's type former is checked BEFORE the block
  exists** (:219): the container's index telescope at `Ds` may not
  mention a member (official: "unknown constant").  `nestKeyOf`.
* **(N3) one sort** (:250): the container's sort at its levels is
  `Level.isEquiv` the block's.  `nestKeyOf`.  A `Prop` block therefore
  nests only through `Prop` containers.
* **(N4) the auxiliary block passes the non-nested checks**: the walk
  (`nestWalk`, official's `check_positivity` :393 with `whnf` exactly
  where official has it — the field's domain and every `Π` body) on
  every member field AND every instantiated container constructor,
  a located instance counting as a member (`is_valid_ind_app` :338: its
  index arguments free of the block); an instantiated constructor's
  RESULT indices free of the block (`check_constructors`' "invalid
  return type").  The field-universe bound of the auxiliary
  constructors follows from (N3) and the container's own install (its
  fields are below its sort at every level instantiation).

**Two conscious deviations**, both accept-supersets and both recorded
as findings in the lane's report:
* official copies EVERY member of the container's mutual group
  (`I_val->get_all()`, :1009), reachable or not; the walk descends
  only into the instances a field reaches (the environment stores no
  mutual group: `.indInfo` has no `all` — the charter's deferred item
  N2).  A container group with an UNREACHED member that is negative in
  its parameter is rejected by official and accepted here
  (`corner_nestpos_group_bad`);
* a container with NO constructor has no recorded parameter count; it
  is DECLINED (exit 2), never guessed.

Basis containers are the maintainer's ruling (DESIGN, 2026-09-21): a
located instance headed by a reserved basis name is INVALID (`Quot` is
no inductive for official; `Eq` always fails (N1)/(N4) there).

**The gate.**  Nothing in the install calls this section: the
recogniser (`blockParts?`) still routes every nested block to the
modelled path.  It is run beside the install by `--nested-shadow`
(`Main.lean`, `tests/nested-shadow.sh`) and by the unit tests.
-/

section Nested

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]

/-- Does `e` occur the block — a member constant, or a placeholder
`fvar i` with `lo ≤ i < hi`?  Official's `has_ind_occ`: constants only
(a free variable's annotation is NOT looked into — a local constant's
type lives in the local context, not in the term), and a `.proj` node's
structure name is no occurrence.  Memoised on the node. -/
def Expr.nestOccGo (names : List Name) (lo hi : Nat) (memo : Std.HashMap Expr Bool) :
    Expr → Bool × Std.HashMap Expr Bool
  | .bvar _ => (false, memo)
  | .sort _ => (false, memo)
  | .lit _ => (false, memo)
  | .const n _ => (names.contains n, memo)
  | .fvar i _ => (decide (lo ≤ i ∧ i < hi), memo)
  | e =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Bool × Std.HashMap Expr Bool :=
        match e with
        | .app f a =>
          let (b₁, memo) := nestOccGo names lo hi memo f
          if b₁ then (true, memo) else nestOccGo names lo hi memo a
        | .lam ty body _ =>
          let (b₁, memo) := nestOccGo names lo hi memo ty
          if b₁ then (true, memo) else nestOccGo names lo hi memo body
        | .forallE ty body _ =>
          let (b₁, memo) := nestOccGo names lo hi memo ty
          if b₁ then (true, memo) else nestOccGo names lo hi memo body
        | .letE ty val body =>
          let (b₁, memo) := nestOccGo names lo hi memo ty
          if b₁ then (true, memo) else
          let (b₂, memo) := nestOccGo names lo hi memo val
          if b₂ then (true, memo) else nestOccGo names lo hi memo body
        | .proj _ _ sub => nestOccGo names lo hi memo sub
        | _ => (false, memo)
      (r, memo.insert e r)

/-- `nestOccGo` from an empty memo. -/
def Expr.nestOcc (names : List Name) (lo hi : Nat) (e : Expr) : Bool :=
  (e.nestOccGo names lo hi {}).1

/-- Instantiate the leading `Π` binders of `e` at `args`, in order
(the parameters of a constructor or a type former). -/
def instPisWith : List Expr → Expr → Option Expr
  | [], e => some e
  | a :: as, .forallE _ body _ => instPisWith as (body.instantiate1 a)
  | _ :: _, _ => none

/-- A container INSTANCE — official's `I Ds`, the key of its auxiliary
type: the container, its universe levels and its parameters, scoped at
the block's canonical parameter variables `0 ..< nP`. -/
structure NestKey where
  cname : Name
  lvls : List Level
  ds : List Expr
  deriving DecidableEq, Repr, Inhabited

/-- One located instance: its key, the container's parameter and
index counts, the instance's index telescope ending in its sort
(scoped at `nP`; the placeholder's annotation) and the container's
constructors with their field counts. -/
structure NestKeyInfo where
  key : NestKey
  nIdx : Nat
  ty : Expr
  ctors : List (ConstantVal × Nat)
  deriving Repr, Inhabited

/-- The kind of a field under positivity through containers: official's
verdict on the auxiliary block, read back without its encoding.  A
`.nested q refl` field reaches the block only through the instance
`q` (a reflexive one under `Π` binders). -/
inductive NestFieldKind where
  | ordinary
  | recursive (tgt : Nat)
  | reflexive (tgt : Nat)
  | nested (key : Nat) (refl : Bool)
  deriving DecidableEq, Repr, Inhabited

/-- The block, as the walk needs it: the members, their level
parameters, the shared parameter count and the members' index counts,
the canonical parameter variables, the block's sort, and the
environment's lookup and constant list (the pure `Env`'s or the
cached index's). -/
structure NestCtx where
  names : List Name
  lps : List Name
  nP : Nat
  nIdxs : List Nat
  params : List Expr
  sort : Level
  find? : Name → Option ConstantInfo
  consts : List ConstantInfo

/-- The walk's state: the instance table (the MEMO — insertion order,
looked up structurally, official's `m_nested_aux`) and the per-
container cache of constructor lists (`none`: no inductive). -/
structure NestState where
  keys : Array NestKeyInfo := #[]
  cache : List (Name × Option (Nat × List (ConstantVal × Nat))) := []
  deriving Inhabited

/-- Everything the check found: the instance table in completion
order and every member constructor's field kinds. -/
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

/-- `nestContainer`, cached in the state. -/
def nestContainerC (ctx : NestCtx) (st : NestState) (C : Name) :
    Option (Nat × List (ConstantVal × Nat)) × NestState :=
  match st.cache.lookup C with
  | some r => (r, st)
  | none =>
    let r := nestContainer ctx C
    (r, { st with cache := (C, r) :: st.cache })

/-- **Register an instance** (official's `replace_if_nested`, :965): the
key's index in the table — an existing entry structurally (the memo),
else a new one, checked for (N2) and (N3) on the way in. -/
def nestKeyOf (ctx : NestCtx) (st : NestState) (C : Name) (ls : List Level) (nPc : Nat)
    (ctors : List (ConstantVal × Nat)) (ds : List Expr) : m (Nat × NestState) := do
  let key : NestKey := ⟨C, ls, ds⟩
  match st.keys.findIdx? (fun ki => ki.key == key) with
  | some q => pure (q, st)
  | none =>
    if st.keys.size ≥ 4096 then
      throw (.notImplemented "nested positivity: container instance fuel")
    let some (.indInfo cvC _) := ctx.find? C
      | throw (.internal "nested positivity: container vanished")
    let ty0 := cvC.type.instantiateLevelParams cvC.levelParams ls
    let some ty := instPisWith ds ty0
      | throw (.notImplemented "nested positivity: container type telescope")
    let (ibs, s) := ty.piBinders
    let .sort s := s
      | throw (.notImplemented "nested positivity: container type is not a syntactic telescope")
    -- (N2): the instance's type former is checked before the block
    -- exists — its index telescope may not name a member
    if ibs.any (fun b => b.1.mentionsAnyConst ctx.names) then
      throw (.invalid "nested positivity: a container's index telescope mentions the block \
        (official: unknown constant)")
    -- (N3): one sort for the auxiliary block
    unless Level.isEquiv s ctx.sort == some true do
      throw (.invalid "nested positivity: mutually inductive types must live in the \
        same universe")
    let _ := nPc
    pure (st.keys.size, { st with keys := st.keys.push ⟨key, ibs.length, ty, ctors⟩ })

/-- **Locate** (N1): the field's declared domain `e` at depth `d` with
every nested instance `C Ds` replaced by its placeholder
`.fvar (d + q) ty_q` (the index arguments stay applied), outermost
first — a replaced node is not descended into, official's `replace`;
memoised on the node within one domain. -/
def nestLocate (ctx : NestCtx) (d : Nat) :
    Expr → NestState → Std.HashMap Expr Expr → m (Expr × NestState × Std.HashMap Expr Expr)
  | e, st, memo =>
    if !e.nestOcc ctx.names 0 0 then pure (e, st, memo) else
    match memo[e]? with
    | some r => pure (r, st, memo)
    | none => do
      let (r, st, memo) ← (match e with
        | .app f a => do
          let args := e.getAppArgs
          let cand : Option (Name × List Level) :=
            match e.getAppFn with
            | .const C ls => if ctx.names.contains C then none else some (C, ls)
            | _ => none
          let (inst, st) : Option (Name × List Level × Nat × List (ConstantVal × Nat)) ×
              NestState :=
            match cand with
            | some (C, ls) =>
              match nestContainerC ctx st C with
              | (some (nPc, ctors), st) => (some (C, ls, nPc, ctors), st)
              | (none, st) => (none, st)
            | none => (none, st)
          match inst with
          | some (C, ls, nPc, ctors) =>
            if ctors.isEmpty && args.any (fun x => x.nestOcc ctx.names 0 0) then
              throw (.notImplemented "nested positivity: a container without constructors \
                (its parameter count is not recorded)")
            let ds := args.take nPc
            if nPc ≤ args.length && ds.any (fun x => x.nestOcc ctx.names 0 0) then
              if reservedBasisNames.contains C then
                throw (.invalid "nested positivity: non valid occurrence of the datatypes \
                  being declared (a basis container)")
              unless ds.all (fun x => x.bvarB == 0 && x.fvarB ≤ ctx.nP) do
                throw (.invalid "nested positivity: nested inductive datatypes parameters \
                  cannot contain local variables")
              let (q, st) ← nestKeyOf ctx st C ls nPc ctors ds
              let ki := st.keys[q]!
              pure (Expr.mkAppN (.fvar (d + q) ki.ty) (args.drop nPc), st, memo)
            else do
              let (f', st, memo) ← nestLocate ctx d f st memo
              let (a', st, memo) ← nestLocate ctx d a st memo
              pure (.app f' a', st, memo)
          | none => do
            let (f', st, memo) ← nestLocate ctx d f st memo
            let (a', st, memo) ← nestLocate ctx d a st memo
            pure (.app f' a', st, memo)
        | .lam ty body bm => do
          let (ty', st, memo) ← nestLocate ctx d ty st memo
          let (body', st, memo) ← nestLocate ctx d body st memo
          pure (.lam ty' body' bm, st, memo)
        | .forallE ty body bm => do
          let (ty', st, memo) ← nestLocate ctx d ty st memo
          let (body', st, memo) ← nestLocate ctx d body st memo
          pure (.forallE ty' body' bm, st, memo)
        | .letE ty val body => do
          let (ty', st, memo) ← nestLocate ctx d ty st memo
          let (val', st, memo) ← nestLocate ctx d val st memo
          let (body', st, memo) ← nestLocate ctx d body st memo
          pure (.letE ty' val' body', st, memo)
        | .proj s i sub => do
          let (sub', st, memo) ← nestLocate ctx d sub st memo
          pure (.proj s i sub', st, memo)
        | e => pure (e, st, memo))
      pure (r, st, memo.insert e r)

/-- The official "non valid occurrence" (`check_positivity` :405). -/
def nestNonValid : CheckError :=
  .invalid "nested positivity: non valid occurrence of the datatypes being declared"

/-- **The walk** — official's `check_positivity` (:393) on the LOCATED
domain, `whnf` exactly where official has it (the domain, and every `Π`
body), the members and the placeholders `lo ..< hi` both counting as
the block (official's auxiliary block): a `Π` whose domain mentions the
block is the "non positive occurrence"; the head must be a member at
the block's levels and parameters, or a placeholder, with every index
argument free of the block (`is_valid_ind_app` :338).  `k` counts the
`Π` binders peeled (a reflexive field). -/
def nestWalk (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (keys : Array NestKeyInfo)
    (lo hi : Nat) : Nat → Nat → Nat → Expr → m NestFieldKind
  | 0, _, _, _ => throw (.notImplemented "nested positivity: walk fuel")
  | fuel + 1, dep, k, e => do
    let w ← ops.whnf env dep e
    if !w.nestOcc ctx.names lo hi then pure .ordinary else
    match w with
    | .forallE dom body _ =>
      if dom.nestOcc ctx.names lo hi then
        throw (.invalid "nested positivity: non positive occurrence of the datatypes \
          being declared")
      else nestWalk ops env ctx keys lo hi fuel (dep + 1) (k + 1) (body.instantiate1 (.fvar dep dom))
    | _ =>
      let args := w.getAppArgs
      let free (xs : List Expr) : Bool := xs.all fun a => !a.nestOcc ctx.names lo hi
      match w.getAppFn with
      | .const n us =>
        match ctx.names.findIdx? (· == n) with
        | some t =>
          if us == ctx.lps.map .param && args.length == ctx.nP + ctx.nIdxs.getD t 0 &&
              args.take ctx.nP == ctx.params && free (args.drop ctx.nP) then
            pure (if k == 0 then .recursive t else .reflexive t)
          else throw nestNonValid
        | none => throw nestNonValid
      | .fvar i _ =>
        if lo ≤ i && i < hi && args.length == (keys.getD (i - lo) default).nIdx && free args then
          pure (.nested (i - lo) (k != 0))
        else throw nestNonValid
      | _ => throw nestNonValid

/-- One field: locate at its depth `d`, then walk at `d + N` (the `N`
placeholders sit at `d ..< d + N`). -/
def nestField (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (d : Nat) (dom : Expr)
    (st : NestState) : m (NestFieldKind × NestState) := do
  let (abs, st, _) ← nestLocate ctx d dom st {}
  let n := st.keys.size
  let k ← nestWalk ops env ctx st.keys d (d + n) 1024 (d + n) 0 abs
  pure (k, st)

/-- A constructor's `n` fields, opened at `d, d + 1, …`; returns their
kinds and the residual (the constructor's result). -/
def nestFields (ops : CheckerOps m) (env : Env) (ctx : NestCtx) :
    Nat → Nat → Expr → NestState → m (List NestFieldKind × Expr × NestState)
  | 0, _, e, st => pure ([], e, st)
  | n + 1, d, .forallE dom body _, st => do
    let (k, st) ← nestField ops env ctx d dom st
    let (ks, r, st) ← nestFields ops env ctx n (d + 1) (body.instantiate1 (.fvar d dom)) st
    pure (k :: ks, r, st)
  | _ + 1, _, _, _ => throw (.notImplemented "nested positivity: constructor field telescope")

/-- A member's constructors, at the canonical parameter variables. -/
def nestMemberCtors (ops : CheckerOps m) (env : Env) (ctx : NestCtx) :
    List (ConstantVal × Nat) → NestState → m (List (List NestFieldKind) × NestState)
  | [], st => pure ([], st)
  | c :: cs, st => do
    let some crest := instPisWith ctx.params c.1.type
      | throw (.notImplemented "nested positivity: constructor parameter telescope")
    let (ks, _, st) ← nestFields ops env ctx c.2 ctx.nP crest st
    let (kss, st) ← nestMemberCtors ops env ctx cs st
    pure (ks :: kss, st)

/-- Every member's constructors. -/
def nestMembers (ops : CheckerOps m) (env : Env) (ctx : NestCtx) :
    List (List (ConstantVal × Nat)) → NestState →
      m (List (List (List NestFieldKind)) × NestState)
  | [], st => pure ([], st)
  | cs :: rest, st => do
    let (kss, st) ← nestMemberCtors ops env ctx cs st
    let (ksss, st) ← nestMembers ops env ctx rest st
    pure (kss :: ksss, st)

/-- An instance's constructors — the container's, at the instance's
levels and parameters (official's auxiliary constructors, :1027),
their fields opened after the block's parameters — through the same
locate-and-walk; the RESULT's index arguments free of the block
(official's "invalid return type" on the auxiliary constructor). -/
def nestInstCtors (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (key : NestKey) :
    List (ConstantVal × Nat) → NestState → m NestState
  | [], st => pure st
  | (cv, nF) :: cs, st => do
    let ty := cv.type.instantiateLevelParams cv.levelParams key.lvls
    let some crest := instPisWith key.ds ty
      | throw (.notImplemented "nested positivity: container constructor telescope")
    let (_, resid, st) ← nestFields ops env ctx nF ctx.nP crest st
    unless (resid.getAppArgs.drop key.ds.length).all (fun a => !a.nestOcc ctx.names 0 0) do
      throw (.invalid "nested positivity: invalid return type of an instantiated container \
        constructor (an index mentions the block)")
    nestInstCtors ops env ctx key cs st

/-- The instance table, in order, each entry's constructors once — new
entries found on the way are appended and reached (official's queue,
:1066). -/
def nestInstances (ops : CheckerOps m) (env : Env) (ctx : NestCtx) :
    Nat → Nat → NestState → m NestState
  | 0, _, _ => throw (.notImplemented "nested positivity: container instance fuel")
  | fuel + 1, q, st =>
    if h : q < st.keys.size then do
      let ki := st.keys[q]
      let st ← nestInstCtors ops env ctx ki.key ki.ctors st
      nestInstances ops env ctx fuel (q + 1) st
    else pure st

/-- **Positivity through containers, for a whole block**: every
member constructor's fields, then every located instance's
constructors, sharing one instance table (the memo).  Throws official's
verdict on a block outside the class (`.invalid`), declines what it
cannot read (`.notImplemented`), and returns the table and the members'
field kinds otherwise.  `ctorss` are the members' constructors,
ANNOTATED and NOT normalised (official locates on the declared types). -/
def nestedBlockPositivity (ops : CheckerOps m) (env : Env) (ctx : NestCtx)
    (ctorss : List (List (ConstantVal × Nat))) : m NestedPositivity := do
  let (kinds, st) ← nestMembers ops env ctx ctorss {}
  let st ← nestInstances ops env ctx 4097 0 st
  pure ⟨st.keys, kinds⟩

end Nested

end ConLeche

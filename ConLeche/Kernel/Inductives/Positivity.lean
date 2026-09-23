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

end ConLeche

module

public import ConLeche.Kernel.CheckerBase
public import ConLeche.Kernel.Inductives.FieldTele

@[expose] public section

/-!
# Positivity: the one interface (lane NESTPOS, ARCH R2)

Everything the uniform route decides about WHERE the block occurs in a
constructor field lives here, and nothing about it anywhere else:

* **the occurrence test** at the block's whole member list
  (`Expr.mentionsAnyConst`, memoized by `@[csimp]`);
* **the normalisation** official's `check_positivity` classifies on:
  the positivity function's own normal form (`nestMemberCtors`' output,
  OUTPUT only — the install stores every constructor as declared, lane
  ALPHA1);
* **positivity through containers** (`nestPos`, the last section): ONE
  function, official's walk with a container case that recurses into the
  container's constructors at the CONCRETE instantiation (the charter,
  items 3–4) — GATED: the recogniser still routes a nested block to the
  modelled path, and only the `--nested-shadow` run and the tests call it.

**The walk's run is the proofs' interface.**  The install runs it on
the stored constructors (`checkBlockPositivity`,
`ConLeche/Kernel/Inductives/BlockInstall.lean`), and the model inverts
that run (`checkBlockPositivity_inv`, `StoredFieldShapes`); the field
kinds it returns are the capability record's `is_rec` (`nestIsRec`).
There is no second classifier: the reject-only recursor conformance
check computes its own (`ConLeche/Conformance/RecGen.lean`).
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

/-- Which member of the block a head expression names, at the block's
own level parameters (official's `m_ind_cnsts` lookup): `none` at any
other head, INCLUDING a member's constant at other levels.  The
recogniser's constructor grouping reads it (`ctorMember?`). -/
def memberIdxAt? (names : List Name) (lvls : List Level) : Expr → Option Nat
  | .const n us => if us == lvls then names.findIdx? (· == n) else none
  | _ => none

/-! ## Closing a telescope -/

/-- Close a telescope opened at the free variables `i ..< i + bs.length`
back into a syntactic Π-telescope over `body`: innermost binder first,
each abstraction turning the binder's own free variable into the bound
one (`abstract1`; the domains of the inner binders are closed by the
outer abstractions, which descend into binder domains). -/
def closeTelescope : List (Expr × BinderMeta) → Nat → Expr → Expr
  | [], _, body => body
  | (dom, bm) :: bs, i, body =>
    .forallE dom ((closeTelescope bs (i + 1) body).abstract1 i 0) bm

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

**The holes are variables** (lane POSPROOF; charter item 2: "the holes
are ordinary open terms (members abstracted to fvars)").  The members
are abstracted to free variables BEFORE the walk (`nestAbstract`,
unapplied: `T_m.{lps} ↦ x_m`, typed by the former's type, at
`nP + m`), and a container's own constant is abstracted to its FRAME's
hole before its constructors are instantiated (charter item 4's `Y`
holes, keyed by the instantiation).  So every hole the monotonicity
theorem varies is a variable of the term `ops.whnf` reduces: `whnf`'s
denotation lemma is stated at one environment model, where a constant
reads one fixed leaf, and says nothing about a constant's reading at
other values.  Verdict-neutral: a member is an inductive former with
no δ and, at positivity time, no ι, so a typed variable in its place
changes no reduction; an installed container's own occurrences are at
its canonical parameters, so its frame's hole is met at the frame's
own `Ds` (anything else declines).  An instantiation in progress met as
a CONSTANT — from inside ANOTHER instantiation's constructors, i.e. a
cycle through a container's mutual group — RESTARTS that instantiation's
frame with the group-mates the cycle passed through abstracted as holes
too (`nestFrame`, bounded; running out declines), so an accepted frame
reads the joint operator of the reached group at the instantiation
(S3, coordinator's provisional ruling: the restart route, not a group
record).

**`nestPos`, the function**, by structural recursion on its fuel; its
cases are the monotonicity induction's:

* the whnf of the domain mentions no member — hole-free (`const`);
* a `Π` whose domain mentions no member — recurse on the body (`pi`);
* a member hole at the block's parameters with hole-free indices
  (`holeApp`, official's `is_valid_ind_app` :338), or a frame's hole at
  its own instantiation's parameters (in progress);
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

**Fuel** (lane FUELFIX: derived from the input, no fixed limit):
`nestPos` recurses on an explicit fuel, one unit per `Π` body and per
container field descent — per member constructor `whnfWalkFuel` of its
type (its depth plus a slack, see "The input-derived fuel" below), so a
telescope or a nesting written out in the input never exhausts it; a
frame restarts at most once per member of the container's recorded
block (`nestRestartFuel`, unreachable).  Running out THROWS
`.notImplemented` — a decline (exit 2), never an accept.  The cache of
instantiations is unbounded: every entry is a frame the walk completed.

**Accepted supersets of official** (the charter's item 8, ruled
2026-09-23; each with an e2e fixture; a reject-only check for either
would go into `ConLeche/Conformance/`, never into this function):
* official locates nested instances SYNTACTICALLY, before any whnf
  (`replace_all_nested` :1043), so a container reached only by
  reduction (`F T`, `F α := List α`) is a "non valid occurrence" there;
  here the container case reads the whnf, so it accepts
  (`corner_nestpos_redex_bad`, D1);
* official copies EVERY member of the container's mutual group
  (:1009), reachable or not; here only the instantiations a field
  reaches are checked (`corner_nestpos_group_bad`, D2).
A container with NO constructor is read at its RECORDED parameter
count (`IndCaps.nparams`); its frame walks nothing (lane RESTRICT-FIX).

**The gate.**  Nothing in the install calls this section: the
recogniser (`blockParts?`) still routes every nested block to the
modelled path.  `--nested-shadow` (`Main.lean`, `tests/nested-shadow.sh`)
runs it beside the install, and the unit tests run its pure
instantiation.
-/

section Nested

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]

/-- Does a MEMBER or a HOLE occur in `e`?  Official's `has_ind_occ`:
member constants, and here also the hole variables `lo ..< hi` — a free
variable's annotation is NOT looked into (a local's type lives in the
local context, not in the term) and a `.proj` node's structure name is
no occurrence.  The pure definition; the executed walk is memoised
(`nestOccGo`, swapped in by `@[csimp]`). -/
def Expr.nestOcc (names : List Name) (lo hi : Nat) : Expr → Bool
  | .bvar _ => false
  | .sort _ => false
  | .lit _ => false
  | .fvar i _ => decide (lo ≤ i ∧ i < hi)
  | .const n _ => names.contains n
  | .app f a => nestOcc names lo hi f || nestOcc names lo hi a
  | .lam ty body _ => nestOcc names lo hi ty || nestOcc names lo hi body
  | .forallE ty body _ => nestOcc names lo hi ty || nestOcc names lo hi body
  | .letE ty val body =>
    nestOcc names lo hi ty || nestOcc names lo hi val || nestOcc names lo hi body
  | .proj _ _ sub => nestOcc names lo hi sub

/-- The occurrence walk, memoised on the node. -/
def Expr.nestOccGo (names : List Name) (lo hi : Nat) (memo : Std.HashMap Expr Bool) :
    Expr → Bool × Std.HashMap Expr Bool
  | .bvar _ => (false, memo)
  | .sort _ => (false, memo)
  | .lit _ => (false, memo)
  | .fvar i _ => (decide (lo ≤ i ∧ i < hi), memo)
  | .const n _ => (names.contains n, memo)
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

/-- The memo's invariant: every recorded answer is the real one. -/
def NestOccMemoInv (names : List Name) (lo hi : Nat) (memo : Std.HashMap Expr Bool) : Prop :=
  ∀ (k : Expr) (v : Bool), memo[k]? = some v → v = Expr.nestOcc names lo hi k

theorem NestOccMemoInv.insert {names : List Name} {lo hi : Nat} {memo : Std.HashMap Expr Bool}
    (hm : NestOccMemoInv names lo hi memo) {e : Expr} {r : Bool}
    (heq : r = e.nestOcc names lo hi) : NestOccMemoInv names lo hi (memo.insert e r) := by
  intro k v hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact heq
  · exact hm k v hk

/-- **The memoised walk is `nestOcc`.** -/
theorem Expr.nestOccGo_spec {names : List Name} {lo hi : Nat} :
    ∀ (e : Expr) {memo : Std.HashMap Expr Bool}, NestOccMemoInv names lo hi memo →
      (e.nestOccGo names lo hi memo).1 = e.nestOcc names lo hi ∧
        NestOccMemoInv names lo hi (e.nestOccGo names lo hi memo).2 := by
  intro e
  induction e with
  | bvar i => intro memo hm; exact ⟨rfl, hm⟩
  | sort u => intro memo hm; exact ⟨rfl, hm⟩
  | lit l => intro memo hm; exact ⟨rfl, hm⟩
  | const n us => intro memo hm; exact ⟨rfl, hm⟩
  | fvar i ty _ => intro memo hm; exact ⟨rfl, hm⟩
  | app a b iha ihb =>
    intro memo hm
    rw [Expr.nestOccGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit), hm⟩
    · obtain ⟨h1, h2⟩ := iha hm
      obtain ⟨h3, h4⟩ := ihb h2
      dsimp only
      by_cases hb : (a.nestOccGo names lo hi memo).1 = true
      · rw [if_pos hb]
        have : Expr.nestOcc names lo hi (.app a b) = true := by
          simp [Expr.nestOcc, ← h1, hb]
        exact ⟨this.symm, h2.insert this.symm⟩
      · rw [if_neg hb]
        have ha : a.nestOcc names lo hi = false := by rw [← h1]; simpa using hb
        have : Expr.nestOcc names lo hi (.app a b) = (b.nestOccGo names lo hi (a.nestOccGo names lo hi memo).2).1 := by
          simp [Expr.nestOcc, ha, h3]
        exact ⟨this.symm, h4.insert this.symm⟩
  | lam ty body mm iht ihb =>
    intro memo hm
    rw [Expr.nestOccGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit), hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      obtain ⟨h3, h4⟩ := ihb h2
      dsimp only
      by_cases hb : (ty.nestOccGo names lo hi memo).1 = true
      · rw [if_pos hb]
        have : Expr.nestOcc names lo hi (.lam ty body mm) = true := by
          simp [Expr.nestOcc, ← h1, hb]
        exact ⟨this.symm, h2.insert this.symm⟩
      · rw [if_neg hb]
        have ha : ty.nestOcc names lo hi = false := by rw [← h1]; simpa using hb
        have : Expr.nestOcc names lo hi (.lam ty body mm) = (body.nestOccGo names lo hi (ty.nestOccGo names lo hi memo).2).1 := by
          simp [Expr.nestOcc, ha, h3]
        exact ⟨this.symm, h4.insert this.symm⟩
  | forallE ty body mm iht ihb =>
    intro memo hm
    rw [Expr.nestOccGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit), hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      obtain ⟨h3, h4⟩ := ihb h2
      dsimp only
      by_cases hb : (ty.nestOccGo names lo hi memo).1 = true
      · rw [if_pos hb]
        have : Expr.nestOcc names lo hi (.forallE ty body mm) = true := by
          simp [Expr.nestOcc, ← h1, hb]
        exact ⟨this.symm, h2.insert this.symm⟩
      · rw [if_neg hb]
        have ha : ty.nestOcc names lo hi = false := by rw [← h1]; simpa using hb
        have : Expr.nestOcc names lo hi (.forallE ty body mm)
            = (body.nestOccGo names lo hi (ty.nestOccGo names lo hi memo).2).1 := by
          simp [Expr.nestOcc, ha, h3]
        exact ⟨this.symm, h4.insert this.symm⟩
  | letE ty v body iht ihv ihb =>
    intro memo hm
    rw [Expr.nestOccGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit), hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      dsimp only
      by_cases hb : (ty.nestOccGo names lo hi memo).1 = true
      · rw [if_pos hb]
        have : Expr.nestOcc names lo hi (.letE ty v body) = true := by
          simp [Expr.nestOcc, ← h1, hb]
        exact ⟨this.symm, h2.insert this.symm⟩
      · rw [if_neg hb]
        have ha : ty.nestOcc names lo hi = false := by rw [← h1]; simpa using hb
        obtain ⟨h3, h4⟩ := ihv h2
        by_cases hb2 : (v.nestOccGo names lo hi (ty.nestOccGo names lo hi memo).2).1 = true
        · rw [if_pos hb2]
          have : Expr.nestOcc names lo hi (.letE ty v body) = true := by
            simp [Expr.nestOcc, ha, ← h3, hb2]
          exact ⟨this.symm, h4.insert this.symm⟩
        · rw [if_neg hb2]
          have hv : v.nestOcc names lo hi = false := by rw [← h3]; simpa using hb2
          obtain ⟨h5, h6⟩ := ihb h4
          have : Expr.nestOcc names lo hi (.letE ty v body)
              = (body.nestOccGo names lo hi
                (v.nestOccGo names lo hi (ty.nestOccGo names lo hi memo).2).2).1 := by
            simp [Expr.nestOcc, ha, hv, h5]
          exact ⟨this.symm, h6.insert this.symm⟩
  | proj s i sub ih =>
    intro memo hm
    rw [Expr.nestOccGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit), hm⟩
    · obtain ⟨h1, h2⟩ := ih hm
      dsimp only
      have : Expr.nestOcc names lo hi (.proj s i sub) = (sub.nestOccGo names lo hi memo).1 := by
        simp [Expr.nestOcc, h1]
      exact ⟨this.symm, h2.insert this.symm⟩

/-- `nestOccGo` from an empty memo: the executed `nestOcc`. -/
def Expr.nestOccFast (names : List Name) (lo hi : Nat) (e : Expr) : Bool :=
  (e.nestOccGo names lo hi {}).1

@[csimp] theorem Expr.nestOcc_eq_nestOccFast : @Expr.nestOcc = @Expr.nestOccFast := by
  funext names lo hi e
  exact (Expr.nestOccGo_spec e (fun k v h => by simp at h)).1.symm

/-- `e` is a hole `lo ≤ h < hi` applied to EXACTLY the parameter
variables `fvar 0, …, fvar (n - 1)`. -/
def Expr.holeParamsApp (lo hi : Nat) : Expr → Nat → Bool
  | .fvar i _, 0 => decide (lo ≤ i ∧ i < hi)
  | .app f (.fvar j _), n + 1 => j == n && holeParamsApp lo hi f n
  | _, _ => false

/-- **M3 and M2′ on the walk's normal form** (lane NESTKERN, session 2):
every member hole `nP ≤ h < hi` occurs applied to the parameter
variables (the head of a spine whose first `nP` arguments are
`fvar 0, …, fvar (nP - 1)`), and no member constant occurs.  A `letE`,
`proj` or literal node must be free of both.  The pure definition; the
executed walk is memoised (`holesAppliedGo`, swapped in by `@[csimp]`).

Official v4.33.1+ imposes a superset (`check_uniform_ind_occs`,
`inductive.cpp` :134: every member occurrence of the DECLARED type
applied to exactly the parameters at the declaration's levels): whnf
keeps a hole applied (a substitution replaces bound variables, never
the hole's head or the parameter variables), and introduces no member
constant (the members are fresh below the block).  At flat kinds the
walk's own arms already establish it; at a container field it is new:
a member unapplied in a PHANTOM container parameter
(`restrict_a29_m3_phantom_unapplied`: official 0 up to v4.33.0, 1 from
v4.33.1) is never read by the walk. -/
def Expr.holesApplied (names : List Name) (nP hi : Nat) : Expr → Bool
  | .fvar i ty => (Expr.fvar i ty).holeParamsApp nP hi nP || !decide (nP ≤ i ∧ i < hi)
  | .app f a => (Expr.app f a).holeParamsApp nP hi nP ||
      (holesApplied names nP hi f && holesApplied names nP hi a)
  | .const n _ => !names.contains n
  | .forallE t b _ => holesApplied names nP hi t && holesApplied names nP hi b
  | .lam t b _ => holesApplied names nP hi t && holesApplied names nP hi b
  | .bvar _ => true
  | .sort _ => true
  | .letE t v b => !(Expr.letE t v b).nestOcc names nP hi
  | .lit l => !(Expr.lit l).nestOcc names nP hi
  | .proj s i e => !(Expr.proj s i e).nestOcc names nP hi

/-- The memoised walk of `holesApplied`. -/
def Expr.holesAppliedGo (names : List Name) (nP hi : Nat) (memo : Std.HashMap Expr Bool) :
    Expr → Bool × Std.HashMap Expr Bool
  | .bvar _ => (true, memo)
  | .sort _ => (true, memo)
  | .fvar i ty => ((Expr.fvar i ty).holesApplied names nP hi, memo)
  | .const n _ => (!names.contains n, memo)
  | .lit l => ((Expr.lit l).holesApplied names nP hi, memo)
  | e =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Bool × Std.HashMap Expr Bool :=
        match e with
        | .app f a =>
          if (Expr.app f a).holeParamsApp nP hi nP then (true, memo) else
          let (b₁, memo) := holesAppliedGo names nP hi memo f
          let (b₂, memo) := holesAppliedGo names nP hi memo a
          (b₁ && b₂, memo)
        | .lam t b _ =>
          let (b₁, memo) := holesAppliedGo names nP hi memo t
          let (b₂, memo) := holesAppliedGo names nP hi memo b
          (b₁ && b₂, memo)
        | .forallE t b _ =>
          let (b₁, memo) := holesAppliedGo names nP hi memo t
          let (b₂, memo) := holesAppliedGo names nP hi memo b
          (b₁ && b₂, memo)
        | .letE t v b => (!(Expr.letE t v b).nestOcc names nP hi, memo)
        | .proj s i e => (!(Expr.proj s i e).nestOcc names nP hi, memo)
        | _ => (true, memo)
      (r, memo.insert e r)

/-- The memo's invariant: every recorded answer is the real one. -/
def HolesAppliedMemoInv (names : List Name) (nP hi : Nat) (memo : Std.HashMap Expr Bool) :
    Prop :=
  ∀ (k : Expr) (v : Bool), memo[k]? = some v → v = Expr.holesApplied names nP hi k

theorem HolesAppliedMemoInv.insert {names : List Name} {nP hi : Nat}
    {memo : Std.HashMap Expr Bool} (hm : HolesAppliedMemoInv names nP hi memo) {e : Expr}
    {r : Bool} (heq : r = e.holesApplied names nP hi) :
    HolesAppliedMemoInv names nP hi (memo.insert e r) := by
  intro k v hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact heq
  · exact hm k v hk

/-- **The memoised walk is `holesApplied`.** -/
theorem Expr.holesAppliedGo_spec {names : List Name} {nP hi : Nat} :
    ∀ (e : Expr) {memo : Std.HashMap Expr Bool}, HolesAppliedMemoInv names nP hi memo →
      (e.holesAppliedGo names nP hi memo).1 = e.holesApplied names nP hi ∧
        HolesAppliedMemoInv names nP hi (e.holesAppliedGo names nP hi memo).2 := by
  intro e
  induction e with
  | bvar i => intro memo hm; exact ⟨rfl, hm⟩
  | sort u => intro memo hm; exact ⟨rfl, hm⟩
  | const n us => intro memo hm; exact ⟨rfl, hm⟩
  | fvar i ty _ => intro memo hm; exact ⟨rfl, hm⟩
  | app a b iha ihb =>
    intro memo hm
    rw [Expr.holesAppliedGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit), hm⟩
    · dsimp only
      by_cases hp : (Expr.app a b).holeParamsApp nP hi nP = true
      · rw [if_pos hp]
        have : Expr.holesApplied names nP hi (.app a b) = true := by
          simp [Expr.holesApplied, hp]
        exact ⟨this.symm, hm.insert this.symm⟩
      · rw [if_neg hp]
        obtain ⟨h1, h2⟩ := iha hm
        obtain ⟨h3, h4⟩ := ihb h2
        have : Expr.holesApplied names nP hi (.app a b)
            = ((a.holesAppliedGo names nP hi memo).1 &&
              (b.holesAppliedGo names nP hi (a.holesAppliedGo names nP hi memo).2).1) := by
          simp [Expr.holesApplied, hp, h1, h3]
        exact ⟨this.symm, h4.insert this.symm⟩
  | lam t b mm iht ihb =>
    intro memo hm
    rw [Expr.holesAppliedGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit), hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      obtain ⟨h3, h4⟩ := ihb h2
      dsimp only
      have : Expr.holesApplied names nP hi (.lam t b mm)
          = ((t.holesAppliedGo names nP hi memo).1 &&
            (b.holesAppliedGo names nP hi (t.holesAppliedGo names nP hi memo).2).1) := by
        simp [Expr.holesApplied, h1, h3]
      exact ⟨this.symm, h4.insert this.symm⟩
  | forallE t b mm iht ihb =>
    intro memo hm
    rw [Expr.holesAppliedGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit), hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      obtain ⟨h3, h4⟩ := ihb h2
      dsimp only
      have : Expr.holesApplied names nP hi (.forallE t b mm)
          = ((t.holesAppliedGo names nP hi memo).1 &&
            (b.holesAppliedGo names nP hi (t.holesAppliedGo names nP hi memo).2).1) := by
        simp [Expr.holesApplied, h1, h3]
      exact ⟨this.symm, h4.insert this.symm⟩
  | letE t v b _ _ _ =>
    intro memo hm
    rw [Expr.holesAppliedGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit), hm⟩
    · dsimp only
      exact ⟨rfl, hm.insert rfl⟩
  | lit l => intro memo hm; exact ⟨rfl, hm⟩
  | proj s i sub _ =>
    intro memo hm
    rw [Expr.holesAppliedGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit), hm⟩
    · dsimp only
      exact ⟨rfl, hm.insert rfl⟩

/-- `holesAppliedGo` from an empty memo: the executed `holesApplied`. -/
def Expr.holesAppliedFast (names : List Name) (nP hi : Nat) (e : Expr) : Bool :=
  (e.holesAppliedGo names nP hi {}).1

@[csimp] theorem Expr.holesApplied_eq_holesAppliedFast :
    @Expr.holesApplied = @Expr.holesAppliedFast := by
  funext names nP hi e
  exact (Expr.holesAppliedGo_spec e (fun k v h => by simp at h)).1.symm

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

/-- A HOLE of the walk: the instantiation it stands for, and the first
hole index of its frame (a frame has one hole per member of the
container's group it has reached). -/
structure NestHole where
  key : NestKey
  base : Nat
  deriving DecidableEq, Repr, Inhabited

/-! ### The input-derived fuel (lane FUELFIX)

The walks that read a telescope THROUGH whnf (`nestPos`, and the
recursor stage's `targetWhnfPis`) recurse on an explicit fuel, one unit
per `Π` body and per container descent.  The fuel is derived from the
term the walk starts on: its DEPTH (the longest root-to-leaf path,
`fvar` annotations not descended) bounds every `Π` and every container
argument the term carries syntactically, so a telescope or a nesting
written out in the input never exhausts it; `fuelSlack` on top covers
what the syntax does not show — a container constructor's own fields
walked in a frame, a redex that reduces to a `Π` — and keeps the fuel
at or above the fixed 1024 it replaces, so no verdict that ran within
the old fuel changes.  Running out still DECLINES (it takes a
telescope that reduction manufactures beyond both).  No proof reads
the value: the functions' theorems hold at every fuel. -/

/-- The fuel's slack above the term's depth (see the section header). -/
def fuelSlack : Nat := 1024

/-- `Expr.depth`'s memoised walk: every node is visited once (the memo
is keyed by the node), so a DAG costs its distinct nodes, never its
unfolding. -/
def Expr.depthGo (memo : Std.HashMap Expr Nat) : Expr → Nat × Std.HashMap Expr Nat
  | .bvar _ => (1, memo)
  | .fvar .. => (1, memo)
  | .sort _ => (1, memo)
  | .const .. => (1, memo)
  | .lit _ => (1, memo)
  | e =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Nat × Std.HashMap Expr Nat :=
        match e with
        | .app f a =>
          let (d₁, memo) := depthGo memo f
          let (d₂, memo) := depthGo memo a
          (max d₁ d₂ + 1, memo)
        | .lam ty body _ | .forallE ty body _ =>
          let (d₁, memo) := depthGo memo ty
          let (d₂, memo) := depthGo memo body
          (max d₁ d₂ + 1, memo)
        | .letE ty v body =>
          let (d₁, memo) := depthGo memo ty
          let (d₂, memo) := depthGo memo v
          let (d₃, memo) := depthGo memo body
          (max (max d₁ d₂) d₃ + 1, memo)
        | .proj _ _ x =>
          let (d, memo) := depthGo memo x
          (d + 1, memo)
        | _ => (1, memo)
      (r, memo.insert e r)

/-- A term's depth (the longest root-to-leaf path; `fvar` annotations
not descended), memoised. -/
def Expr.depth (e : Expr) : Nat := (e.depthGo {}).1

/-- **The fuel of a walk through whnf** starting at `e`: its depth plus
the slack (see the section header). -/
def whnfWalkFuel (e : Expr) : Nat := e.depth + fuelSlack

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
  deriving DecidableEq, Inhabited

/-- A field kind the uniform route installs: no container instantiation. -/
def NestFieldKind.flat : NestFieldKind → Bool
  | .ordinary | .recursive _ | .reflexive _ => true
  | _ => false

/-- **Every field of every constructor of every member is flat** (no
container instantiation): the uniform route's install gate while nested
blocks stay on the modelled route (`checkBlockPositivity`), and the
reject-only conformance check's switch (`checkBlockTail`: it has no
container arm). -/
def nestKindsFlat (ks : List (List (List NestFieldKind))) : Bool :=
  ks.all (·.all (·.all NestFieldKind.flat))

/-- Official's `is_rec` off the walk's kinds, BLOCK-wide: some field of
some constructor of some member is not ordinary (on the auxiliary block
official builds, a container occurrence counts).  The capability
record's `is_rec` (`checkBlockPass`). -/
def nestIsRec (ks : List (List (List NestFieldKind))) : Bool :=
  ks.any fun kss => kss.any fun fs => fs.any (· != .ordinary)

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
  /-- a RESTART request (S3): the frame whose holes start at the first
  component must be walked again with the named group-mates abstracted
  too; every step unwinds while it is set -/
  restart : Option (Nat × List Name) := none
  deriving Inhabited

/-- What the run found: the accepted instantiations and every member
constructor's field kinds. -/
structure NestedPositivity where
  keys : Array NestKeyInfo
  kinds : List (List (List NestFieldKind))
  /-- every member constructor's normalised type (the positivity function's
  output; the install stores the declared type) -/
  normals : List (List Expr) := []
  deriving Inhabited

/-- The constructors of the inductive `C` and its parameter count, read
off the environment (a constructor belongs to the type its result
names, `ctorMember?`'s reading): `none` when `C` is no inductive; for
an inductive without constructors, its RECORDED parameter count
(`IndCaps.nparams`, official's `inductive_val.nparams`; lane
RESTRICT-FIX, finding C1: official nests through such a container, its
auxiliary type simply has no constructor). -/
def nestContainer (ctx : NestCtx) (C : Name) : Option (Nat × List (ConstantVal × Nat)) :=
  match ctx.find? C with
  | some (.indInfo _ caps) =>
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
    | [] => some (caps.nparams, [])
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

/-- The first hole-free variable index of a walk under `nf` frames:
the parameters are `0 ..< nP`, the member holes `nP ..< nP + k`, and
frame `i`'s hole `nP + k + i`. -/
def NestCtx.hiAt (ctx : NestCtx) (nf : Nat) : Nat := ctx.nP + ctx.names.length + nf

/-- The instantiation's type former, checked as official checks the
auxiliary type BEFORE the block exists: (N2) its index telescope at
`Ds` names no member and no hole below `hi` (official: "unknown
constant"), (N3) its sort is `Level.isEquiv` the block's.  Returns the
index count and the container's type at the key's levels (the type of
the frame's hole). -/
def nestInstType (ctx : NestCtx) (hi : Nat) (key : NestKey) : m (Nat × Expr) := do
  let cvC ← unwrapOr (match ctx.find? key.cname with
      | some (.indInfo cv _) => some cv
      | _ => none)
    (.internal "nested positivity: container vanished")
  -- the container's parameters are a SYNTACTIC telescope (lane CONTSEM:
  -- its canonical instantiation exists, so the N2 check below reads
  -- against the container's recorded index telescope; every stored
  -- inductive's parameters are binders of its type, as official checks)
  unless (cvC.type.stripPis key.ds.length).isSome do
    throw (.invalid "nested positivity: invalid nested inductive datatype, its type does \
      not bind its parameters (official: ill-formed inductive type)")
  let ty ← unwrapOr (instPisWith key.ds
      (cvC.type.instantiateLevelParams cvC.levelParams key.lvls))
    (.invalid "nested positivity: invalid nested inductive datatype, its type does not bind \
      its parameters (official: ill-formed inductive type)")
  let s ← unwrapOr (match ty.piBinders.2 with
      | .sort s => some s
      | _ => none)
    (.invalid "nested positivity: invalid nested inductive datatype, its type is not a \
      telescope ending in a sort (official: type expected)")
  if ty.piBinders.1.any (fun b => b.1.nestOcc ctx.names ctx.nP hi) then
    throw (.invalid "nested positivity: a container's index telescope mentions the block \
      (official: unknown constant)")
  unless ← liftFueled "level comparison" (Level.isEquiv s ctx.sort) do
    throw (.invalid "nested positivity: mutually inductive types must live in the \
      same universe")
  pure (ty.piBinders.1.length, cvC.type.instantiateLevelParams cvC.levelParams key.lvls)

/-- A constructor's result is headed by a variable (its member's hole,
once the members are abstracted) — `checkSumCtor` already checked the
result is the member applied, so this never fires on a checked block;
the monotonicity proof reads the result's spine off it. -/
def nestResHead (e : Expr) : Bool :=
  match e.getAppFn with
  | .fvar .. => true
  | _ => false

/-- A constructor's field telescope `cur` (`nF` fields from field `j`),
each field through `rec` at its depth `base + j`, the field opened at the
variable `base + j`: the fields' kinds, the result (all fields opened)
and the state.  `err` is thrown at a telescope that is too short.  A
pending restart (`NestState.restart`) unwinds at once. -/
def nestFields
    (rec : List NestHole → Nat → Nat → Expr → NestState → m (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (base : Nat) (err : CheckError) :
    Nat → Nat → Expr → NestState →
      m (List NestFieldKind × List (Expr × BinderMeta) × Expr × NestState)
  | 0, _, cur, st => pure ([], [], cur, st)
  | nF + 1, j, cur, st =>
    match cur with
    | .forallE a b bm => do
      let (k, nd, st) ← rec prog (base + j) 0 a st
      if st.restart.isSome then return ([k], [(nd, bm)], cur, st)
      let (ks, nds, res, st) ← nestFields rec prog base err nF (j + 1)
        (b.instantiate1 (.fvar (base + j) a)) st
      pure (k :: ks, (nd, bm) :: nds, res, st)
    | _ => throw err

/-- A frame's constructors: each with the frame's group abstracted
(`sub`), instantiated at `ds`, TYPED at the frame's context (the holes
typed by the container's former at the instantiation — official types
its auxiliary constructors; NESTPLAN L3 (ii), lane CONTSEM: the frame's
walk is read at a graded term), its fields through `rec` above `hi`, U4
on the walked telescope (no later field and not the result reads a
non-ordinary field — lane NESTKERN), and its result indices hole-free
below `hi`.  A pending restart unwinds. -/
def nestCtors (ctx : NestCtx) (ops : CheckerOps m) (env : Env)
    (rec : List NestHole → Nat → Nat → Expr → NestState → m (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (hi : Nat) (us : List Level) (ds : List Expr) (nPc : Nat)
    (sub : Name → List Level → Option Expr) :
    List (ConstantVal × Nat) → NestState → m NestState
  | [], st => pure st
  | (cv, nF) :: cs, st => do
    -- the constructor's level parameters are distinct (lane CONTSEM: the
    -- substitution law instantiates them as the recorded reading does;
    -- every stored constant passed `checkConstantVal`'s own check)
    unless Name.nodup cv.levelParams do
      throw (.invalid "nested positivity: invalid nested inductive datatype, its constructor \
        has a duplicate universe level parameter (official: duplicate universe level \
        parameter)")
    let crest ← unwrapOr
      (instPisWith ds ((cv.type.instantiateLevelParams cv.levelParams us).replaceConsts sub))
      (.invalid "nested positivity: invalid nested inductive datatype, its constructor type \
        does not bind the parameters (official: ill-formed constructor)")
    let ty ← ops.inferType env hi crest
    let _ ← ops.ensureSort env hi ty
    let (ks, nds, cur, st) ← nestFields rec prog hi
      (.invalid "nested positivity: invalid nested inductive datatype, its constructor type \
        does not bind its fields (official: ill-formed constructor)") nF 0 crest st
    if st.restart.isSome then return st
    -- U4 on the instantiated constructor (lane NESTKERN, finding F-W1 of
    -- lane NESTW): no later field and not the result reads a field that is
    -- not ordinary (recursive, reflexive, nested or in progress) — on the
    -- walked (whnf'd) telescope.  Official rejects every instance
    -- (charter item 9; DESIGN "LANDED (lane NESTKERN, U4 …)")
    if (List.range nF).any (fun i => ks.getD i .ordinary != .ordinary &&
        structUsedLater (closeTelescope nds hi cur) 0 i) then
      throw (.invalid "nested positivity: non valid occurrence of the datatypes being \
        declared (a later field or the result of an instantiated container constructor \
        depends on a recursive or nested field)")
    -- official's "invalid return type" on the instantiated constructor; its
    -- result is headed by its hole (lane CONTSEM: the frame's result reads
    -- as the hole applied — never fires, a stored constructor's result is
    -- its inductive at its own levels, which `sub` abstracts)
    unless nestResHead cur && (cur.getAppArgs.drop nPc).all
        (fun x => !x.nestOcc ctx.names ctx.nP hi) do
      throw (.invalid "nested positivity: invalid return type of an instantiated \
        container constructor (an index mentions the block)")
    nestCtors ctx ops env rec prog hi us ds nPc sub cs st

/-- The constructors of every container in `cs` (at one parameter
count), read off the environment. -/
def nestGroupCtors (ctx : NestCtx) (nPc : Nat) :
    List Name → NestState → m (List (ConstantVal × Nat) × NestState)
  | [], st => pure ([], st)
  | c :: cs, st => do
    let q ← unwrapOr (nestContainerC ctx st c).1 nestNonValid
    let st := (nestContainerC ctx st c).2
    let (nPc', ctors) := q
    unless nPc' == nPc || ctors.isEmpty do
      throw (.invalid "nested positivity: number of parameters mismatch in inductive \
        datatype declaration (a container's group)")
    let (rest, st) ← nestGroupCtors ctx nPc cs st
    pure (ctors ++ rest, st)

/-- The recorded block of the inductive `C` (`IndCaps.all`, official's
`all`): `[]` when none is recorded. -/
def nestBlockOf (ctx : NestCtx) (C : Name) : List Name :=
  match ctx.find? C with
  | some (.indInfo _ caps) => caps.all
  | _ => []

/-- **A frame hole's full arity**: its container member's recorded type's
binder count (parameters and indices; a stored inductive's type is a
syntactic telescope ending in a sort).  Official applies every
occurrence of a block member — the container's copied members among
them — to exactly its parameters and indices (`is_valid_ind_app`,
`inductive.cpp` v4.33.0 :341); a well-typed field's frame hole is
fully applied anyway (a type former's partial or over-application is
no type).  The accessibility proof (lane ACCMODEL) reads a frame hole's
value only at its full arity: a partial application is a λ-graph of
the container's family, which no support over the family's elements
carries to another family. -/
def nestArity (ctx : NestCtx) (C : Name) : Nat :=
  match ctx.find? C with
  | some (.indInfo cv _) => cv.type.piBinders.1.length
  | _ => 0

/-- A frame's group grown by the named containers, each at the frame's
instantiation, its hole typed by its instantiated former. -/
def nestGrowGroup (ctx : NestCtx) (hi : Nat) (us : List Level) (ds : List Expr) :
    List Name → List (Name × Expr) → m (List (Name × Expr))
  | [], grp => pure grp
  | c :: cs, grp => do
    let (_, cty) ← nestInstType ctx hi ⟨c, us, ds⟩
    nestGrowGroup ctx hi us ds cs (grp ++ [(c, cty)])

/-- The reached group-mates accepted with a frame's instantiation (those
not yet cached). -/
def nestAcceptGroup (ctx : NestCtx) (hi : Nat) (us : List Level) (ds : List Expr) :
    List (Name × Expr) → NestState → m NestState
  | [], st => pure st
  | (c, _) :: rest, st => do
    let k' : NestKey := ⟨c, us, ds⟩
    if !(st.keys.any (·.key == k')) then
      let (ni, _) ← nestInstType ctx hi k'
      nestAcceptGroup ctx hi us ds rest { st with keys := st.keys.push ⟨k', ni⟩ }
    else nestAcceptGroup ctx hi us ds rest st

/-- **A container frame** at the instantiation `(us, ds)`, its holes
the reached part of the container's group `grp` (at `hi, hi + 1, …`,
typed by `tys`), every one of their constructors walked with all of
them abstracted.  When the walk meets one of its instantiations as a
CONSTANT (a cycle, S3), the frame is walked again from its entry state
with the group-mates the cycle passed through abstracted as well —
bounded by `r`, running out DECLINES.  So an accepted frame's readings
are the joint operator of the reached group at the instantiation. -/
def nestFrame (ctx : NestCtx) (ops : CheckerOps m) (env : Env)
    (rec : List NestHole → Nat → Nat → Expr → NestState → m (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (hi : Nat) (us : List Level) (ds : List Expr) (nPc : Nat) :
    Nat → List (Name × Expr) → NestState → m (List (Name × Expr) × NestState)
  | 0, _, _ => throw (.notImplemented "nested positivity: restart fuel")
  | r + 1, grp, st₀ => do
    let holes := grp.mapIdx fun i (c, ty) => (c, Expr.fvar (hi + i) ty)
    let prog' := (grp.mapIdx fun _ (c, _) =>
      ({ key := ⟨c, us, ds⟩, base := hi } : NestHole)).reverse ++ prog
    let sub (c : Name) (us' : List Level) : Option Expr :=
      if us' == us then (holes.lookup c) else none
    let (ctors, st) ← nestGroupCtors ctx nPc (grp.map (·.1)) st₀
    let st ← nestCtors ctx ops env rec prog' (hi + grp.length) us ds nPc sub ctors st
    match st.restart with
    | some (b, adds) =>
      if b == hi then
        let new := adds.eraseDups.filter fun c => !(grp.map (·.1)).contains c
        if new.isEmpty then
          throw (.invalid "nested positivity: non valid occurrence of the datatypes being \
            declared (a container cycle this frame cannot absorb)")
        -- G1 (lane CONTSEM): the frame's holes stay inside ONE recorded
        -- block — the container's (`IndCaps.all`).  Never fires on a
        -- checked environment (a cycle between stored inductives is a
        -- mutual block, by install order); a reject if it does.
        unless new.all (fun c => (nestBlockOf ctx ((grp.headD default).1)).contains c) do
          throw (.invalid "nested positivity: non valid occurrence of the datatypes being \
            declared (a container cycle through two blocks)")
        let grp' ← nestGrowGroup ctx hi us ds new grp
        nestFrame ctx ops env rec prog hi us ds nPc r grp' { st₀ with ctorsOf := st.ctorsOf }
      else pure (grp, st)
    | none => pure (grp, st)

/-- **The restart fuel** of the frame at the container `C` (lane
FUELFIX): one walk more than `C`'s recorded block has members.  Every
restart grows the frame's group by a group-mate not yet in it, all of
them in that block (G1) — else the frame rejects — so the frame is
walked at most once per member plus once more, and the "restart fuel"
decline is unreachable. -/
def nestRestartFuel (ctx : NestCtx) (C : Name) : Nat := (nestBlockOf ctx C).length + 1

/-- An instantiation's frame (`nestCont`'s last cases): its former's
checks (`nestInstType`), the frame (`nestFrame`), and — unless a restart
is pending — the reached group-mates accepted with it and the
instantiation cached.  `old`: the instantiation's table index when it is
already cached (a key mentioning a frame hole, walked again — see
`nestContKey`); it keeps that index and is not pushed again. -/
def nestContNew (ctx : NestCtx) (ops : CheckerOps m) (env : Env)
    (rec : List NestHole → Nat → Nat → Expr → NestState → m (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level) (ds : List Expr) (nPc : Nat)
    (old : Option Nat) (st : NestState) : m (NestFieldKind × NestState) := do
  let ni ← nestInstType ctx (ctx.hiAt prog.length) ⟨n, us, ds⟩
  let gs ← nestFrame ctx ops env rec prog (ctx.hiAt prog.length) us ds nPc
    (nestRestartFuel ctx n) [(n, ni.2)] st
  if gs.2.restart.isSome then return (.inProgress, gs.2)
  -- the reached group-mates are accepted with it
  let st ← nestAcceptGroup ctx (ctx.hiAt prog.length) us ds (gs.1.drop 1) gs.2
  match old with
  | some q => return (.nested q (kb != 0), st)
  | none =>
    return (.nested st.keys.size (kb != 0),
      { st with keys := st.keys.push ⟨⟨n, us, ds⟩, ni.1⟩ })

/-- The instantiation `(n, us, ds)` met (`nestCont` after its checks): IN
PROGRESS — a cycle through a container's mutual group, a restart request
to its frame naming the group-mates of the frames above it at the same
instantiation (S3); cached — a hit, but only when its parameters mention
no FRAME hole (NESTPLAN L3 (iii), lane CONTSEM: a frame hole's variable
is reused by a later frame, with other parameters, so such a key is
walked again, keeping its table index); else a new frame. -/
def nestContKey (ctx : NestCtx) (ops : CheckerOps m) (env : Env)
    (rec : List NestHole → Nat → Nat → Expr → NestState → m (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level) (ds : List Expr) (nPc : Nat)
    (st : NestState) : m (NestFieldKind × NestState) :=
  match prog.find? (·.key == ⟨n, us, ds⟩) with
  | some h =>
    -- a cycle: restart `h`'s frame with the frames above it at the same
    -- instantiation abstracted too
    if ((prog.filter fun e => h.base < e.base && e.key.lvls == us && e.key.ds == ds).map
        (·.key.cname)).isEmpty then
      throw (.invalid "nested positivity: non valid occurrence of the datatypes being \
        declared (a container cycle at two instantiations)")
    else
      pure (.inProgress, { st with restart := some (h.base,
        (prog.filter fun e => h.base < e.base && e.key.lvls == us && e.key.ds == ds).map
          (·.key.cname)) })
  | none =>
    match st.keys.findIdx? (·.key == ⟨n, us, ds⟩) with
    | some q =>
      if ds.all (fun x => x.fvarB ≤ ctx.hiAt 0) then pure (.nested q (kb != 0), st)
      else nestContNew ctx ops env rec prog kb n us ds nPc (some q) st
    | none => nestContNew ctx ops env rec prog kb n us ds nPc none st

/-- **The container case** of `nestPos`: the reduct `w` is the stored
inductive `n.{us}` applied to `args` (`contApp`), `rec` the function
itself one fuel lower (at a frame's fields).  The container's
constructors are read off the environment; its checks (constructors
exist, enough arguments and hole-free indices, not `Quot`, parameters
without local variables); then the instantiation (`nestContKey`).  Split
off so that the monotonicity theorem can take the container case as its
own lemma. -/
def nestCont (ctx : NestCtx) (ops : CheckerOps m) (env : Env)
    (rec : List NestHole → Nat → Nat → Expr → NestState → m (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level) (args : List Expr)
    (st : NestState) : m (NestFieldKind × NestState) := do
  let q ← unwrapOr (nestContainerC ctx st n).1 nestNonValid
  if args.length < q.1 ||
      !(args.drop q.1).all (fun x => !x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length)) then
    throw nestNonValid
  -- `Quot` is stored as an `.indInfo` but is no inductive for
  -- official (`is_nested_inductive_app` asks `is_inductive()`):
  -- the one name read here.  Every other basis type (`Eq`, `Nat`,
  -- `PUnit`, `Empty`, `False`, and `And`) is a container like any
  -- stored inductive.
  if n == quotName then throw nestNonValid
  unless (args.take q.1).all (fun x => x.bvarB == 0 && x.fvarB ≤ ctx.hiAt prog.length) do
    throw (.invalid "nested positivity: nested inductive datatypes parameters \
      cannot contain local variables")
  -- the instance is FULLY applied (lane CONTSEM): the container case
  -- compares the container's family at the index tuple, and a partial
  -- application is a function, whose graph does not grow with its values.
  -- A field's domain is a type, so a checked constructor never has one.
  let ni ← nestInstType ctx (ctx.hiAt prog.length) ⟨n, us, args.take q.1⟩
  unless args.length == q.1 + ni.1 do
    throw (.invalid "nested positivity: type expected (a container instance that is not \
      fully applied)")
  nestContKey ctx ops env rec prog kb n us (args.take q.1) q.1 (nestContainerC ctx st n).2

/-- **The positivity function** (see the section header): the domain
`e` at depth `dep`, `kb` `Π` binders into the field, `prog` the
instantiations in progress (innermost first; frame `i` from the
outside has its hole at `ctx.hiAt i`).  The block's members are HOLES
(the free variables `nP ..< nP + k`, abstracted by
`nestedBlockPositivity`), and so is each instantiation in progress (its
container abstracted to its frame's hole before its constructors are
instantiated) — so every hole the monotonicity induction varies is a
variable of the term `ops.whnf` reduces.  Throws official's verdict on
a non-positive or non-valid occurrence; returns the field's kind and
the cache. -/
def nestPos (ops : CheckerOps m) (env : Env) (ctx : NestCtx) :
    Nat → List NestHole → Nat → Nat → Expr → NestState → m (NestFieldKind × Expr × NestState)
  | 0, _, _, _, _, _ => throw (.notImplemented "nested positivity: fuel")
  | fuel + 1, prog, dep, kb, e, st => do
    let hi := ctx.hiAt prog.length
    let w ← ops.whnf env dep e
    -- `const`: the reduct mentions no member and no hole; the normal
    -- form is the input when it mentions none either, else the reduct
    if !w.nestOcc ctx.names ctx.nP hi then
      return (.ordinary, (if e.nestOcc ctx.names ctx.nP hi then w else e), st)
    match w with
    | .forallE a b bm =>
      -- `pi`: the domain hole-free, the codomain positive
      if a.nestOcc ctx.names ctx.nP hi then
        throw (.invalid "nested positivity: non positive occurrence of the datatypes \
          being declared")
      let (k, nb, st) ←
        nestPos ops env ctx fuel prog (dep + 1) (kb + 1) (b.instantiate1 (.fvar dep a)) st
      pure (k, .forallE a (nb.abstract1 dep) bm, st)
    | _ =>
      let args := w.getAppArgs
      match w.getAppFn with
      | .fvar i _ =>
        if ctx.nP ≤ i && i < ctx.hiAt 0 then
          -- `holeApp`: a member hole at the block's parameters
          let t := i - ctx.nP
          if args.length == ctx.nP + ctx.nIdxs.getD t 0 &&
              args.take ctx.nP == ctx.params &&
              args.all (fun x => !x.nestOcc ctx.names ctx.nP hi) then
            return (if kb == 0 then .recursive t else .reflexive t, w, st)
          else throw nestNonValid
        else if ctx.hiAt 0 ≤ i && i < hi then
          -- a frame's hole: the instantiation in progress at that frame,
          -- at its own parameters, with hole-free indices
          match prog.reverse[i - ctx.hiAt 0]? with
          | none => throw (.internal "nested positivity: frame hole without a frame")
          | some h =>
            if h.key.ds.length ≤ args.length && args.take h.key.ds.length == h.key.ds then
              if (args.drop h.key.ds.length).all (fun x => !x.nestOcc ctx.names ctx.nP hi) then
                -- at its full arity (official `is_valid_ind_app`, :341)
                if args.length == nestArity ctx h.key.cname then
                  return (.inProgress, w, st)
                else throw nestNonValid
              else throw nestNonValid
            else
              throw (.invalid "nested positivity: non valid occurrence of the datatypes \
                being declared (a container's own occurrence at other parameters)")
        else throw nestNonValid
      | .const n us =>
        -- a member constant left after the abstraction (other levels)
        if ctx.names.contains n then throw nestNonValid
        -- `contApp`: a stored inductive at a concrete instantiation
        let (k, st) ← nestCont ctx ops env (nestPos ops env ctx fuel) prog kb n us args st
        pure (k, w, st)
      | _ => throw nestNonValid

/-- The fields of one member constructor (the parameters instantiated
at the canonical variables, the members abstracted to their holes),
each through `nestPos` at its depth, the fields above the holes; then
the checks on the NORMALISED telescope — the fields' normal forms,
closed back over the fields (`closeTelescope`), official's
`check_positivity` form: U4, no
later field and no result index uses a recursive, reflexive or nested
field (nested since lane NESTKERN: official's auxiliary type makes every
such read ill-typed)
(the closure witness's class condition, today's `structUsedLater`
guard; a reject — lane RESTRICT-FIX: official rejects every instance), and the result's indices mention no member
(official's "invalid return type").  Returns the kinds and the
normalised telescope. -/
def nestMemberCtor (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (nF : Nat) (crest : Expr)
    (st : NestState) : m (List NestFieldKind × Expr × NestState) := do
  let base := ctx.hiAt 0
  let (ks, nds, cur, st) ← nestFields (nestPos ops env ctx (whnfWalkFuel crest)) [] base
    (.invalid "nested positivity: a constructor type does not bind its fields (official: \
      ill-formed constructor)") nF 0 crest st
  if st.restart.isSome then
    throw (.internal "nested positivity: a restart request without its frame")
  let tyN := closeTelescope nds base cur
  if (List.range nF).any (fun i =>
      (match ks.getD i .ordinary with
        | .recursive _ | .reflexive _ | .nested _ _ => true
        | _ => false) && structUsedLater tyN 0 i) then
    throw (.invalid "nested positivity: non valid occurrence of the datatypes being \
      declared (a later field or the result depends on a recursive or nested field)")
  unless nestResHead cur && (cur.getAppArgs.drop ctx.nP).all
      (fun a => !a.nestOcc ctx.names ctx.nP base) do
    throw (.invalid "nested positivity: invalid return type — a constructor's result \
      index mentions the block")
  -- M3 and M2′ on the normal form (`Expr.holesApplied`, lane NESTKERN)
  unless tyN.holesApplied ctx.names ctx.nP base do
    throw (.invalid "nested positivity: invalid occurrence of a datatype being declared: it \
      must be applied to the parameters and universe levels of the mutual declaration (a \
      member not applied to the parameters, in a container's parameter)")
  pure (ks, tyN, st)

/-- The member holes back to the members (`nP + m ↦ T_m.{lps}`), on a
term with no loose bound variable. -/
def nestConcrete (ctx : NestCtx) (e : Expr) : Expr :=
  (List.range ctx.names.length).foldl (fun e mm =>
    (e.abstract1 (ctx.nP + mm) 0).instantiate1
      (.const (ctx.names.getD mm .anonymous) (ctx.lps.map .param))) e

/-- The member holes: member `m` is the free variable `nP + m`, typed by
its former's type (closed, so the hole is well-scoped anywhere above
the parameters).  `none` when a member is not a stored former. -/
def nestHoles (ctx : NestCtx) : Option (List Expr) :=
  (List.range ctx.names.length).mapM fun mm =>
    match ctx.find? (ctx.names.getD mm .anonymous) with
    | some (.indInfo cv _) => some (.fvar (ctx.nP + mm) cv.type)
    | _ => none

/-- **The member abstraction** (charter item 2: "the holes are ordinary
open terms (members abstracted to fvars)"): every member constant at
the block's own levels becomes its hole, UNAPPLIED — so a redex that
produces `T_m p⃗` only after whnf still reduces to the hole. -/
def nestAbstract (ctx : NestCtx) (holes : List Expr) (e : Expr) : Expr :=
  e.replaceConsts fun c us =>
    if us == ctx.lps.map .param then
      match ctx.names.findIdx? (· == c) with
      | some mm => holes[mm]?
      | none => none
    else none

/-- M2′: a member-abstracted constructor type mentions no member
CONSTANT (every member occurrence was at the block's own levels) — a
REJECT with official's wording (lane L9FIX).  Official imposes it since
v4.33.1: `check_uniform_ind_occs` (`inductive.cpp`, run by
`add_inductive` before the nested elimination) walks every constructor
type SYNTACTICALLY and throws at every occurrence of a member whose
levels are not structurally the declaration's (`const_levels(fn) ==
lvls`) — a superset of this check (it also wants the member applied to
exactly the parameter variables, which the walk's own arms check where
it reads the occurrence).  Official ≤ v4.33.0 accepts where the walk
never reads the occurrence (a redex whnf drops, a phantom container
parameter): charter item 9 follows the newer kernel.  Needed by CONTSEM
s2's frame reading. -/
def nestNoMemberConst (ctx : NestCtx) (e : Expr) : m Unit :=
  if e.nestOcc ctx.names 0 0 then
    throw (.invalid "nested positivity: invalid occurrence of a datatype being declared: it \
      must be applied to the parameters and universe levels of the mutual declaration (a \
      member at other universe levels in a constructor type)")
  else pure ()

/-- One member's constructors through `nestMemberCtor`, sharing the
cache: their kinds and the walk's NORMAL FORMS, member-abstracted at the
walk's context (the parameters at `ctx.params`, member `m` at `nP + m`).
The normal forms are OUTPUT only (lane ALPHA1): the install stores the
constructors as declared; the model reads its fields with holes off the
normal forms, and ties them to the declared types semantically. -/
def nestMemberCtors (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (holes : List Expr) :
    List (ConstantVal × Nat) → NestState → m (List (List NestFieldKind) × List Expr × NestState)
  | [], st => pure ([], [], st)
  | c :: cs, st => do
    let crest ← unwrapOr (instPisWith ctx.params (nestAbstract ctx holes c.1.type))
      (.invalid "nested positivity: a constructor type does not bind the parameters \
        (official: ill-formed constructor)")
    let (ks, tyN, st) ← nestMemberCtor ops env ctx c.2 crest st
    -- M2′ (lane CONTSEM): every member occurrence is at the block's own
    -- levels — the abstracted type mentions no member constant — so the
    -- walk's holes are exactly the recorded reading's, at every later
    -- instantiation of the block as a container.  AFTER the walk (lane
    -- RESTRICT-FIX): a member at other levels in a position the walk
    -- reads is the walk's own "non valid occurrence" (fixture
    -- `restrict_b02_m2prime_direct_bad`); this check catches the rest —
    -- a redex whnf drops, a phantom container parameter
    -- (`restrict_a27_m2prime_redex`, `restrict_a28_m2prime_phantom`).
    -- A REJECT (lane L9FIX): official ≥ v4.33.1 rejects every such
    -- occurrence (`check_uniform_ind_occs`; DESIGN, charter item 9)
    nestNoMemberConst ctx (nestAbstract ctx holes c.1.type)
    let (kss, nss, st) ← nestMemberCtors ops env ctx holes cs st
    pure (ks :: kss, tyN :: nss, st)

/-- Every member's constructors, in block order, sharing the cache. -/
def nestBlockCtors (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (holes : List Expr) :
    List (List (ConstantVal × Nat)) → NestState →
      m (List (List (List NestFieldKind)) × List (List Expr) × NestState)
  | [], st => pure ([], [], st)
  | cs :: css, st => do
    let (kss, nss, st) ← nestMemberCtors ops env ctx holes cs st
    let (ksss, nsss, st) ← nestBlockCtors ops env ctx holes css st
    pure (kss :: ksss, nss :: nsss, st)

/-- A constructor's normal form made concrete again: the members
restored (`nestConcrete`) and the parameters closed back over the
declared type's own parameter binders (reads only `ctx`'s names, levels
and parameter count). -/
def nestConcreteCtor (ctx : NestCtx) (cty tyN : Expr) : Option Expr :=
  (cty.stripPis ctx.nP).map fun cq => closeTelescope cq.1 0 (nestConcrete ctx tyN)

/-- **Positivity through containers, for a whole block**: every member
constructor's fields through `nestPos`, sharing one cache.  `ctorss`
are the members' constructors ANNOTATED (not normalised: the function
reduces itself); their member constants are abstracted here.  Returns
the accepted instantiations, the kinds and every constructor's
NORMALISED type (official's `check_positivity` form, the members
restored and the parameters closed back as declared).  The
loops are explicit recursions (`nestBlockCtors`, `nestMemberCtors`) so
that the run inverts constructor by constructor. -/
def nestedBlockPositivity (ops : CheckerOps m) (env : Env) (ctx : NestCtx)
    (ctorss : List (List (ConstantVal × Nat))) : m NestedPositivity := do
  let holes ← unwrapOr (nestHoles ctx)
    (.internal "nested positivity: a member is not a stored former")
  let (kinds, nfs, st) ← nestBlockCtors ops env ctx holes ctorss {}
  pure ⟨st.keys, kinds, (ctorss.zip nfs).map fun (cs, ns) =>
    (cs.zip ns).map fun (c, n) => (nestConcreteCtor ctx c.1.type n).getD n⟩

/-- The constructors with their types replaced by `normals` (the
positivity function's concrete normal forms, `NestedPositivity.normals`):
the telescope the reject-only recursor conformance check reads. -/
def withNormals (ctorsAs : List (List (ConstantVal × Nat))) (normals : List (List Expr)) :
    List (List (ConstantVal × Nat)) :=
  (ctorsAs.zip normals).map fun (cs, ns) => (cs.zip ns).map fun (c, n) => ({ c.1 with type := n }, c.2)

end Nested

end ConLeche

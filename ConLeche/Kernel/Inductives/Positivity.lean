module

public import ConLeche.Kernel.CheckerBase
public import ConLeche.Kernel.Inductives.FieldTele

@[expose] public section

/-!
# Positivity: the one interface

Everything the uniform route decides about WHERE the block occurs in a
constructor field lives here, and nothing about it anywhere else:

* **the occurrence test** at the block's whole member list
  (`Expr.mentionsAnyConst`, memoized by `@[csimp]`);
* **the normalisation** official's `check_positivity` classifies on:
  the positivity function's own normal form (the root frame's output,
  `nestRoot`; OUTPUT only — the install stores every constructor as
  declared);
* **positivity through containers** (`nestPos`, the last section): ONE
  function, official's walk with a container case that recurses into the
  container's constructors at the CONCRETE instantiation (the charter,
  items 3–4), whose ROOT frame is the block itself (`nestRoot`): the
  install's walk, and the unit tests' entry `nestedBlockPositivity`.

**The walk's run is the proofs' interface.**  The install runs it on
the stored constructors (`checkBlockPositivity`,
`ConLeche/Kernel/Inductives/BlockInstall.lean`), and the model inverts
that run (`checkBlockPositivity_inv_gen`, `StoredFieldShapes`).  The
capability record's `is_rec` is NOT read off its kinds: official's is
syntactic (`blockRawRec`).  There is no second classifier.
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

**The holes are variables** (charter item 2: "the holes
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
own `Ds` (anything else declines).  A frame abstracts the container's
WHOLE recorded block (`IndCaps.all`) at the instantiation and walks all
their constructors in one pass (N2-eager), as official copies the whole
group; so an
accepted frame reads the joint operator of the container's block at the
instantiation, and an instantiation in progress is only ever met as its
hole — met as a constant (reduction only) it is official's "non valid
occurrence".

**`nestPos`, the function**, by structural recursion on its fuel; its
cases are the monotonicity induction's:

* the whnf of the domain mentions no member — hole-free (`const`);
* a `Π` whose domain mentions no member — recurse on the body (`pi`);
* a hole at its frame's own parameters with hole-free indices, at its
  full arity (`holeApp`, official's `is_valid_ind_app` :338): a member
  hole — the ROOT frame's, at the block's parameters — or a container
  frame's (its instantiation in progress);
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
`@Eq Prop T T` has a member in an index.

**Fuel** (derived from the input, no fixed limit):
`nestPos` recurses on an explicit fuel, one unit per `Π` body and per
container field descent — per root constructor `whnfWalkFuel` of its
instantiated type (its depth plus a slack, see "The input-derived fuel"
below), so a
telescope or a nesting written out in the input never exhausts it.
Running out THROWS
`.notImplemented` — a decline (exit 2), never an accept.  The cache of
instantiations is unbounded: every entry is a frame the walk completed.

**The seeds**: the stream's recursor family names official's
auxiliary types as its outside majors (the recursor check's classes);
the recursor check walks every class it resolved at the root like a
container instance met there (`nestSeeds`, "The seeds" below), so every
class is a node BY CONSTRUCTION — an occurrence whnf erases among
them.

**Accepted superset of official** (the charter's item 8; with an e2e
fixture; a reject-only check would go into a separate unverified
stage, never into this function): official locates
nested instances SYNTACTICALLY, before any whnf (`replace_all_nested`
:1043), so a container reached only by reduction (`F T`,
`F α := List α`) is a "non valid occurrence" there; here the container
case reads the whnf, so it accepts (`corner_nestpos_redex_bad`, D1).
A container with NO constructor is read at its RECORDED parameter
count (`IndCaps.nparams`); its frame walks nothing.

**Who calls it.**  The install's positivity stage runs the walk
(`checkBlockPositivity`, `nestRoot`); `nestedBlockPositivity` is
the unit tests' entry, on a hand-built context.
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

/-- **M3 and M2′ on the walk's normal form**: every member hole
`nP ≤ h < hi` occurs applied to the
parameter variables (the head of a spine whose first `nP` arguments are
`fvar 0, …, fvar (nP - 1)`), and no member constant occurs.  The walk
descends into EVERY subterm — binders, `letE` (type, value, body),
`proj` (the struct argument) — exactly as official's traversal does.
The pure definition; the executed walk is memoised (`holesAppliedGo`,
swapped in by `@[csimp]`).

Official v4.33.1+ (`check_uniform_ind_occs`, v4.34.0 `inductive.cpp`
:134) runs `for_each` over each constructor type — every subterm,
`let`s and projections included — and at an application spine
`get_app_args(t)` whose head is a member constant: over-applied
(`args.size() > nparams`) it descends into the arguments; otherwise it
demands exactly `nparams` arguments, the i-th the bound variable
`#(offset-1-i)` (the parameters), at the declaration's levels, and does
not descend.  Here the members are holes (`fvar`s), the parameters
`fvar 0 …`, so `holeParamsApp` is that exactly-applied test, the `.app`
arm's descent covers the over-applied case (its spine head is reached
exactly applied), and the `.fvar` arm rejects a bare hole unless
`nP = 0`.  The `letE`/`proj` arms descend too: demanding the subterm
be free of holes there is an accept-subset (`complete_m3_proj_param`,
`List ((T, Nat).1)`, official 0).

whnf keeps a hole applied (a substitution replaces bound variables,
never the hole's head or the parameter variables), and introduces no
member constant (the members are fresh below the block).  At flat kinds
the walk's own arms already establish it; at a container field it is
new: a member unapplied in a PHANTOM container parameter
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
  | .letE t v b => holesApplied names nP hi t && holesApplied names nP hi v &&
      holesApplied names nP hi b
  | .lit _ => true
  | .proj _ _ e => holesApplied names nP hi e

/-- The memoised walk of `holesApplied`. -/
def Expr.holesAppliedGo (names : List Name) (nP hi : Nat) (memo : Std.HashMap Expr Bool) :
    Expr → Bool × Std.HashMap Expr Bool
  | .bvar _ => (true, memo)
  | .sort _ => (true, memo)
  | .fvar i ty => ((Expr.fvar i ty).holesApplied names nP hi, memo)
  | .const n _ => (!names.contains n, memo)
  | .lit _ => (true, memo)
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
        | .letE t v b =>
          let (b₁, memo) := holesAppliedGo names nP hi memo t
          let (b₂, memo) := holesAppliedGo names nP hi memo v
          let (b₃, memo) := holesAppliedGo names nP hi memo b
          (b₁ && b₂ && b₃, memo)
        | .proj _ _ e => holesAppliedGo names nP hi memo e
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
  | letE t v b iht ihv ihb =>
    intro memo hm
    rw [Expr.holesAppliedGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit), hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      obtain ⟨h3, h4⟩ := ihv h2
      obtain ⟨h5, h6⟩ := ihb h4
      dsimp only
      have : Expr.holesApplied names nP hi (.letE t v b)
          = ((t.holesAppliedGo names nP hi memo).1 &&
            (v.holesAppliedGo names nP hi (t.holesAppliedGo names nP hi memo).2).1 &&
            (b.holesAppliedGo names nP hi
              (v.holesAppliedGo names nP hi (t.holesAppliedGo names nP hi memo).2).2).1) := by
        simp [Expr.holesApplied, h1, h3, h5]
      exact ⟨this.symm, h6.insert this.symm⟩
  | lit l => intro memo hm; exact ⟨rfl, hm⟩
  | proj s i sub ih =>
    intro memo hm
    rw [Expr.holesAppliedGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit), hm⟩
    · obtain ⟨h1, h2⟩ := ih hm
      dsimp only
      have : Expr.holesApplied names nP hi (.proj s i sub)
          = (sub.holesAppliedGo names nP hi memo).1 := by
        simp [Expr.holesApplied, h1]
      exact ⟨this.symm, h2.insert this.symm⟩

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

/-! ### The input-derived fuel

The walks that read a telescope THROUGH whnf (`nestPos`, and the
recursor stage's `targetWhnfPis`) recurse on an explicit fuel, one unit
per `Π` body and per container descent.  The fuel is derived from the
term the walk starts on: its DEPTH (the longest root-to-leaf path,
`fvar` annotations not descended) bounds every `Π` and every container
argument the term carries syntactically, so a telescope or a nesting
written out in the input never exhausts it; `fuelSlack` on top covers
what the syntax does not show — a container constructor's own fields
walked in a frame, a redex that reduces to a `Π` — and keeps the fuel
at or above 1024.  Running out DECLINES (it takes a
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

/-- The field's kind as the run found it: hole-free, a member hole
(finitary or under `Π` binders), an instantiation IN PROGRESS (a `Y`
hole — only inside a container's constructors), or an accepted
instantiation (under `Π` binders when `refl`). -/
inductive NestFieldKind where
  | ordinary
  | recursive (tgt : Nat)
  | reflexive (tgt : Nat)
  | inProgress
  | nested (refl : Bool)
  deriving DecidableEq, Inhabited

/-- A field kind the uniform route installs: no container instantiation. -/
def NestFieldKind.flat : NestFieldKind → Bool
  | .ordinary | .recursive _ | .reflexive _ => true
  | _ => false

/-- **Every field of every constructor of every member is flat** (no
container instantiation): the reject-only conformance check's switch
(`checkBlockTail`: it has no container arm). -/
def nestKindsFlat (ks : List (List (List NestFieldKind))) : Bool :=
  ks.all (·.all (·.all NestFieldKind.flat))

/-- **A constructor's walked normal form, recorded** (K.53′): the
constructor `ctor` of the class it builds at the
levels `lvls` and the parameters `ds`, and its field telescope as the
walk normalised it (`nestFields`' normal forms, closed over the fields,
`closeTelescope`), both READ BACK — every hole replaced by the constant it
stands for (`nestHoleConst`: a member hole by the member, a frame hole by
its group member at the frame's levels), so only the block's parameter
variables stay free.  Recorded at every node the walk derives: the
members' constructors at the block's own levels and parameters, and every
frame's constructors at the frame's key.  The recursor stage reads a
recursive call's callee off it: the called field's normal form, at the
rule's field variables, IS the callee's major type (official: the
auxiliary type replacing that very occurrence, `replace_all_nested`;
`mk_rec_rules`' `whnf(infer_type(u_i))`). -/
structure NestCtorNf where
  ctor : Name
  lvls : List Level
  ds : List Expr
  ty : Expr
  deriving Inhabited

/-- The block, as the function needs it: the members, their level
parameters, the shared parameter count and the members' index counts,
the canonical parameter variables, the block's sort, and the
environment's lookup (the pure `Env`'s or the cached index's). -/
structure NestCtx where
  names : List Name
  lps : List Name
  nP : Nat
  nIdxs : List Nat
  params : List Expr
  sort : Level
  find? : Name → Option ConstantInfo

/-- The run's state: the accepted instantiations (the cache, keyed by the
instantiation) and the environment lookups of
container constructor lists (`none`: no inductive) — a reading of the
environment, not a fact about the container. -/
structure NestState where
  keys : Array NestKey := #[]
  ctorsOf : List (Name × Option (Nat × List (ConstantVal × Nat))) := []
  /-- the instantiations whose frames are being walked (every group
  member at the key), outermost last: an instantiation walked at the
  EMPTY stack (`nestWalkStack`) is still in progress for the cycle check
  (`nestContKey`) -/
  active : List NestKey := []
  /-- every derived node's constructors, normalised and read back
  (`NestCtorNf`, K.53′), in walk order -/
  ctorNfs : Array NestCtorNf := #[]
  deriving Inhabited

/-- What the run found: the accepted instantiations and every member
constructor's field kinds. -/
structure NestedPositivity where
  keys : Array NestKey
  kinds : List (List (List NestFieldKind))
  /-- every member constructor's normalised type, member-abstracted at the
  walk's context (the positivity function's output; the install stores
  the declared type) -/
  normals : List (List Expr) := []
  /-- every derived node's constructors, normalised and read back
  (`NestState.ctorNfs`, K.53′) -/
  ctorNfs : Array NestCtorNf := #[]
  deriving Inhabited

/-- A stored constant's entry as a constructor of `C`: a constructor
record whose result, past its parameters and fields, is headed by `C`
(its parameter and field counts); `none` for anything else. -/
def nestCtorEntry (C : Name) : ConstantInfo → Option (ConstantVal × Nat × Nat)
  | .ctorInfo cv nPc nF =>
    match cv.type.stripPis (nPc + nF) with
    | some (_, body) =>
      match body.getAppFn with
      | .const n _ => if n == C then some (cv, nPc, nF) else none
      | _ => none
    | none => none
  | _ => none

/-- The constructors of the inductive `C` and its parameter count: the
constructor names `C`'s stored record lists (`IndCaps.ctors`, official's
`inductive_val.cnstrs`), each looked up and kept when it is a stored
constructor whose result names `C` (`nestCtorEntry`) — no scan of the
environment.  `none` when `C` is no inductive; for an inductive without
constructors, its RECORDED parameter count (`IndCaps.nparams`,
official's `inductive_val.nparams`: official nests through such a
container, its auxiliary type simply has no constructor). -/
def nestContainer (ctx : NestCtx) (C : Name) : Option (Nat × List (ConstantVal × Nat)) :=
  match ctx.find? C with
  | some (.indInfo _ caps) =>
    let cs := caps.ctors.filterMap fun n => (ctx.find? n).bind (nestCtorEntry C)
    match cs with
    | [] => some (caps.nparams, [])
    | (_, nPc, _) :: _ => some (nPc, cs.map fun c => (c.1, c.2.2))
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

/-- **The ROOT frame's entries**: the block itself is the walk's root
frame — its key each member at the block's own levels and canonical
parameters, its holes the member holes `nP + t` (base `nP`). -/
def NestCtx.rootHoles (ctx : NestCtx) : List NestHole :=
  ctx.names.map fun n => ⟨⟨n, ctx.lps.map .param, ctx.params⟩, ctx.nP⟩

/-- **The hole `i`'s entry** under the frames `prog`: the walk's stack
read root first — the root frame's entries (`NestCtx.rootHoles`), then
`prog` from the outside — hole `i` its entry `i - nP`; `none` off the
holes. -/
def nestHoleAt (ctx : NestCtx) (prog : List NestHole) (i : Nat) : Option NestHole :=
  if ctx.nP ≤ i then (ctx.rootHoles ++ prog.reverse)[i - ctx.nP]? else none

/-! ### Reading a walked term back

A walked constructor's normal form is recorded for the recursor check
(K.53′, `NestCtorNf`) in the recursor's representation: the members and
every frame's group back to their constants (`nestHoleConst`) — the
auxiliary constructor's type exactly as `restore_nested` writes it into
official's auxiliary recursor. -/

/-- Replace the free variables `f` maps (their annotations are not
descended into: a mapped variable is replaced whole, an unmapped one is
kept as it is). -/
def Expr.replaceFVars (f : Nat → Option Expr) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar i ty => (f i).getD (.fvar i ty)
  | .sort u => .sort u
  | .const n us => .const n us
  | .app a b => .app (replaceFVars f a) (replaceFVars f b)
  | .lam ty body m => .lam (replaceFVars f ty) (replaceFVars f body) m
  | .forallE ty body m => .forallE (replaceFVars f ty) (replaceFVars f body) m
  | .letE ty v body => .letE (replaceFVars f ty) (replaceFVars f v) (replaceFVars f body)
  | .lit l => .lit l
  | .proj s i e => .proj s i (replaceFVars f e)

/-- The memo's invariant: every recorded answer is the real one. -/
def ReplaceFVarsMemoInv (f : Nat → Option Expr) (memo : Std.HashMap Expr Expr) : Prop :=
  ∀ k v, memo[k]? = some v → v = Expr.replaceFVars f k

theorem ReplaceFVarsMemoInv.insert {f : Nat → Option Expr} {memo : Std.HashMap Expr Expr}
    (hm : ReplaceFVarsMemoInv f memo) {e r : Expr} (heq : r = Expr.replaceFVars f e) :
    ReplaceFVarsMemoInv f (memo.insert e r) := by
  intro k v hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact heq
  · exact hm k v hk

/-- Memoized `replaceFVars`. -/
def Expr.replaceFVarsGo (f : Nat → Option Expr) (memo : Std.HashMap Expr Expr) :
    Expr → Expr × Std.HashMap Expr Expr
  | e@(.bvar _) => (e, memo)
  | e@(.sort _) => (e, memo)
  | e@(.lit _) => (e, memo)
  | e@(.const ..) => (e, memo)
  | .fvar i ty => ((f i).getD (.fvar i ty), memo)
  | e =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Expr × Std.HashMap Expr Expr :=
        match e with
        | .app a b =>
          let (a', memo) := replaceFVarsGo f memo a
          let (b', memo) := replaceFVarsGo f memo b
          (.app a' b', memo)
        | .lam ty body m =>
          let (t, memo) := replaceFVarsGo f memo ty
          let (b, memo) := replaceFVarsGo f memo body
          (.lam t b m, memo)
        | .forallE ty body m =>
          let (t, memo) := replaceFVarsGo f memo ty
          let (b, memo) := replaceFVarsGo f memo body
          (.forallE t b m, memo)
        | .letE ty v body =>
          let (t, memo) := replaceFVarsGo f memo ty
          let (v', memo) := replaceFVarsGo f memo v
          let (b, memo) := replaceFVarsGo f memo body
          (.letE t v' b, memo)
        | .proj s i sub =>
          let (u, memo) := replaceFVarsGo f memo sub
          (.proj s i u, memo)
        | e => (e, memo)
      (r, memo.insert e r)

/-- **The memoized walk is `replaceFVars`.** -/
theorem Expr.replaceFVarsGo_spec {f : Nat → Option Expr} :
    ∀ (e : Expr) {memo : Std.HashMap Expr Expr}, ReplaceFVarsMemoInv f memo →
      (Expr.replaceFVarsGo f memo e).1 = Expr.replaceFVars f e ∧
        ReplaceFVarsMemoInv f (Expr.replaceFVarsGo f memo e).2 := by
  intro e
  induction e with
  | bvar i => intro memo hm; exact ⟨rfl, hm⟩
  | sort u => intro memo hm; exact ⟨rfl, hm⟩
  | lit l => intro memo hm; exact ⟨rfl, hm⟩
  | const n us => intro memo hm; exact ⟨rfl, hm⟩
  | fvar i ty _ => intro memo hm; exact ⟨rfl, hm⟩
  | app a b iha ihb =>
    intro memo hm
    rw [Expr.replaceFVarsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iha hm
      obtain ⟨h3, h4⟩ := ihb h2
      refine ⟨by simp [Expr.replaceFVars, h1, h3], ?_⟩
      exact h4.insert (by simp [Expr.replaceFVars, h1, h3])
  | lam ty body m iht ihb =>
    intro memo hm
    rw [Expr.replaceFVarsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      obtain ⟨h3, h4⟩ := ihb h2
      refine ⟨by simp [Expr.replaceFVars, h1, h3], ?_⟩
      exact h4.insert (by simp [Expr.replaceFVars, h1, h3])
  | forallE ty body m iht ihb =>
    intro memo hm
    rw [Expr.replaceFVarsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      obtain ⟨h3, h4⟩ := ihb h2
      refine ⟨by simp [Expr.replaceFVars, h1, h3], ?_⟩
      exact h4.insert (by simp [Expr.replaceFVars, h1, h3])
  | letE ty v body iht ihv ihb =>
    intro memo hm
    rw [Expr.replaceFVarsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      obtain ⟨h3, h4⟩ := ihv h2
      obtain ⟨h5, h6⟩ := ihb h4
      refine ⟨by simp [Expr.replaceFVars, h1, h3, h5], ?_⟩
      exact h6.insert (by simp [Expr.replaceFVars, h1, h3, h5])
  | proj s i sub ih =>
    intro memo hm
    rw [Expr.replaceFVarsGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := ih hm
      refine ⟨by simp [Expr.replaceFVars, h1], ?_⟩
      exact h2.insert (by simp [Expr.replaceFVars, h1])

/-- The executed `replaceFVars` (one memoized DAG walk). -/
def Expr.replaceFVarsFast (f : Nat → Option Expr) (e : Expr) : Expr :=
  (Expr.replaceFVarsGo f {} e).1

@[csimp] theorem Expr.replaceFVars_eq_replaceFVarsFast :
    @Expr.replaceFVars = @Expr.replaceFVarsFast := by
  funext f e
  exact (Expr.replaceFVarsGo_spec e (fun k v h => by simp at h)).1.symm

/-- The holes' constants under the frames `prog`: every hole is its
entry's (`nestHoleAt`) group member at the entry's levels — member `t`'s
hole `nP + t` the member `T_t.{lps}`, a frame's hole its container. -/
def nestHoleConst (ctx : NestCtx) (prog : List NestHole) (i : Nat) : Option Expr :=
  (nestHoleAt ctx prog i).map fun h => .const h.key.cname h.key.lvls

/-- `nestHoleConst` by the hole's kind: a member hole's constant is the
member at the block's levels, a frame hole's its frame's. -/
theorem nestHoleConst_eq (ctx : NestCtx) (prog : List NestHole) (i : Nat) :
    nestHoleConst ctx prog i =
      if ctx.nP ≤ i ∧ i < ctx.hiAt 0 then
        some (.const (ctx.names.getD (i - ctx.nP) .anonymous) (ctx.lps.map .param))
      else if ctx.hiAt 0 ≤ i ∧ i < ctx.hiAt prog.length then
        (prog.reverse[i - ctx.hiAt 0]?).map fun h => .const h.key.cname h.key.lvls
      else none := by
  unfold nestHoleConst nestHoleAt NestCtx.rootHoles NestCtx.hiAt
  by_cases h1 : ctx.nP ≤ i
  · rw [if_pos h1]
    by_cases h2 : i < ctx.nP + ctx.names.length + 0
    · rw [if_pos ⟨h1, h2⟩, List.getElem?_append_left (by simp; omega)]
      simp [List.getElem?_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
        (show i - ctx.nP < ctx.names.length by omega)]
    · rw [if_neg (fun h => h2 h.2), List.getElem?_append_right (by simp; omega)]
      simp only [List.length_map]
      by_cases h3 : i < ctx.nP + ctx.names.length + prog.length
      · rw [if_pos ⟨by omega, h3⟩, show i - ctx.nP - ctx.names.length =
          i - (ctx.nP + ctx.names.length + 0) by omega]
      · rw [if_neg (fun h => h3 h.2), List.getElem?_eq_none (by simp; omega)]
        rfl
  · rw [if_neg h1, if_neg (fun h => h1 h.1), if_neg (fun h => by omega)]
    rfl

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
  -- the container is applied at its own level count (official:
  -- `infer_constant`'s "incorrect number of universe levels", which every
  -- constant of a checked constructor type — and of every
  -- reduct of it — passed; the model reads the key's constants at it)
  unless key.lvls.length = cvC.levelParams.length do
    throw (.invalid "nested positivity: incorrect number of universe levels for a nested \
      inductive datatype (official: incorrect number of universe levels)")
  -- the container's parameters are a SYNTACTIC telescope (its canonical
  -- instantiation exists, so the N2 check below reads
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
and the state.  `err` is thrown at a telescope that is too short. -/
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
      let (ks, nds, res, st) ← nestFields rec prog base err nF (j + 1)
        (b.instantiate1 (.fvar (base + j) a)) st
      pure (k :: ks, (nd, bm) :: nds, res, st)
    | _ => throw err

/-- **A frame constructor's record** (K.53′): the constructor `cv` of
the frame's key `(us, ds)` under the frames `prog`, its walked field
telescope `nds` (opened at `hi, hi + 1, …`) onto `cur` closed back, all
read back (`nestHoleConst`). -/
def nestCtorNf (ctx : NestCtx) (prog : List NestHole) (hi : Nat) (us : List Level)
    (ds : List Expr) (cv : ConstantVal) (nds : List (Expr × BinderMeta)) (cur : Expr) :
    NestCtorNf :=
  ⟨cv.name, us, ds.map (·.replaceFVars (nestHoleConst ctx prog)),
    (closeTelescope nds hi cur).replaceFVars (nestHoleConst ctx prog)⟩

/-- **A frame's constructors** — the ROOT frame's (the block's own,
`nestRoot`) and every container frame's (`nestFrame`) alike: each with
the frame's group abstracted
(`sub`), instantiated at `ds`, TYPED at the frame's context (the holes
typed by their formers — official types its auxiliary constructors; at
the root this is the typing of the member-abstracted constructor the
monotonicity proof reads; the frame's walk is read at a graded term),
its fields through `rec` at its instantiated type (the walk, fueled: a
container frame's is its enclosing walk one fuel lower, the root's is
fueled by the constructor, `nestRoot`)
above `hi`, U4 on the walked telescope (no later field and not the
result reads a non-ordinary field), its result
indices hole-free below `hi`, and its walked normal form recorded
(K.53′).  Returns every constructor's field kinds and walked normal form
(closed over its fields, holes kept) — the root's are the install's. -/
def nestCtors (ctx : NestCtx) (ops : CheckerOps m) (env : Env)
    (rec : Expr → List NestHole → Nat → Nat → Expr → NestState →
      m (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (hi : Nat) (us : List Level) (ds : List Expr) (nPc : Nat)
    (sub : Name → List Level → Option Expr) :
    List (ConstantVal × Nat) → NestState → m (List (List NestFieldKind × Expr) × NestState)
  | [], st => pure ([], st)
  | (cv, nF) :: cs, st => do
    -- the constructor's level parameters are distinct (the substitution law
    -- instantiates them as the recorded reading does;
    -- every stored constant passed `checkConstantVal`'s own check)
    unless Name.nodup cv.levelParams do
      throw (.invalid "nested positivity: invalid nested inductive datatype, its constructor \
        has a duplicate universe level parameter (official: duplicate universe level \
        parameter)")
    -- the container's constructor instantiated at the key WITHOUT a
    -- β-step (official's `instantiate_pi_params`, `inductive.cpp` v4.34.0)
    let crest ← unwrapOr
      (instPisWith ds ((cv.type.instantiateLevelParams cv.levelParams us).replaceConsts sub))
      (.invalid "nested positivity: invalid nested inductive datatype, its constructor type \
        does not bind the parameters (official: ill-formed constructor)")
    let ty ← ops.inferType env hi crest
    let _ ← ops.ensureSort env hi ty
    let (ks, nds, cur, st) ← nestFields (rec crest) prog hi
      (.invalid "nested positivity: invalid nested inductive datatype, its constructor type \
        does not bind its fields (official: ill-formed constructor)") nF 0 crest st
    -- U4 on the instantiated constructor: no later field and not the result
    -- reads a field that is
    -- not ordinary (recursive, reflexive, nested or in progress) — on the
    -- walked (whnf'd) telescope.  Official rejects every instance
    -- (charter item 9)
    if (List.range nF).any (fun i => ks.getD i .ordinary != .ordinary &&
        structUsedLater (closeTelescope nds hi cur) 0 i) then
      throw (.invalid "nested positivity: non valid occurrence of the datatypes being \
        declared (a later field or the result depends on a recursive or nested field)")
    -- official's "invalid return type" on the instantiated constructor; its
    -- result is headed by its hole (the frame's result reads
    -- as the hole applied — never fires, a stored constructor's result is
    -- its inductive at its own levels, which `sub` abstracts)
    unless nestResHead cur && (cur.getAppArgs.drop nPc).all
        (fun x => !x.nestOcc ctx.names ctx.nP hi) do
      throw (.invalid "nested positivity: invalid return type — a constructor's result \
        index mentions the block")
    -- K.53′: the constructor's walked normal form at the
    -- frame's key, read back (`NestCtorNf`)
    let st := { st with ctorNfs := st.ctorNfs.push (nestCtorNf ctx prog hi us ds cv nds cur) }
    let (os, st) ← nestCtors ctx ops env rec prog hi us ds nPc sub cs st
    pure ((ks, closeTelescope nds hi cur) :: os, st)

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

/-- **A frame's group-mates** (N2-eager): every
OTHER member of the container `C`'s recorded block (`IndCaps.all`), each
once.  Official copies the whole block of every container it finds
(`for J_name : I_val->get_all()`, `inductive.cpp` v4.34.0), reachable or
not; so does the frame. -/
def nestFrameMates (ctx : NestCtx) (C : Name) : List Name :=
  (nestBlockOf ctx C).eraseDups.filter (· != C)

/-- **A frame hole's full arity**: its container member's recorded type's
binder count (parameters and indices; a stored inductive's type is a
syntactic telescope ending in a sort).  Official applies every
occurrence of a block member — the container's copied members among
them — to exactly its parameters and indices (`is_valid_ind_app`,
`inductive.cpp` v4.33.0 :341); a well-typed field's frame hole is
fully applied anyway (a type former's partial or over-application is
no type).  The accessibility proof reads a frame hole's
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

/-- A frame's group accepted with its instantiation: every member at the
instantiation `(us, ds)` cached, those not cached yet. -/
def nestAcceptGroup (us : List Level) (ds : List Expr) :
    List (Name × Expr) → Array NestKey → Array NestKey
  | [], keys => keys
  | (c, _) :: rest, keys =>
    nestAcceptGroup us ds rest
      (if keys.contains ⟨c, us, ds⟩ then keys else keys.push ⟨c, us, ds⟩)

/-- **A container frame** at the instantiation `(us, ds)`, its holes the
container's WHOLE recorded group `grp` (at `hi, hi + 1, …`, typed by
their instantiated formers), every one of their constructors walked with
all of them abstracted, in one pass (N2-eager).  So an accepted frame's
readings are the joint operator of the container's block at the
instantiation. -/
def nestFrame (ctx : NestCtx) (ops : CheckerOps m) (env : Env)
    (rec : List NestHole → Nat → Nat → Expr → NestState → m (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (hi : Nat) (us : List Level) (ds : List Expr) (nPc : Nat)
    (grp : List (Name × Expr)) (st : NestState) : m NestState := do
  -- K.52: the instantiation `C.{us} ds` is TYPED at the
  -- frame's own depth (its holes typed by their containers' formers, as
  -- the constants they stand for).  Official imposes it: after the nested
  -- elimination, `add_inductive` type-checks every replaced nested
  -- application `I Ds` (`tc.check(nested, …)` over `m_aux2nested`,
  -- `inductive.cpp` v4.32.2 :1186–1189, v4.34.0 :1320–1323), and a reduct
  -- of a typed term is typed.  The model grades the key's parameters in
  -- the frame's stack context by it.
  let _ ← ops.inferType env hi (Expr.mkAppN (.const (grp.headD default).1 us) ds)
  let holes := grp.mapIdx fun i (c, ty) => (c, Expr.fvar (hi + i) ty)
  let prog' := (grp.mapIdx fun _ (c, _) =>
    ({ key := ⟨c, us, ds⟩, base := hi } : NestHole)).reverse ++ prog
  let sub (c : Name) (us' : List Level) : Option Expr :=
    if us' == us then (holes.lookup c) else none
  let (ctors, st) ← nestGroupCtors ctx nPc (grp.map (·.1)) st
  let (_, st) ← nestCtors ctx ops env (fun _ => rec) prog' (hi + grp.length) us ds nPc sub ctors st
  pure st

/-- **The frame stack an instantiation is walked under**: the EMPTY one
when its parameters mention no frame hole (they then read only the
parameters and the members), else the frames it was met under. -/
def nestWalkStack (ctx : NestCtx) (prog : List NestHole) (ds : List Expr) : List NestHole :=
  if ds.all (fun x => x.fvarB ≤ ctx.hiAt 0) then [] else prog

/-- An instantiation's frame (`nestCont`'s last cases): the group-mates'
former checks (`nestGrowGroup`; the instantiation's own, `nestInstType`,
ran at the occurrence and gave `cty`, the type of its hole), the frame
(`nestFrame`), and the whole group cached — when its parameters mention
no frame hole, the only keys that can hit (`nestContKey`). -/
def nestContNew (ctx : NestCtx) (ops : CheckerOps m) (env : Env)
    (rec : List NestHole → Nat → Nat → Expr → NestState → m (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level) (ds : List Expr) (nPc : Nat)
    (cty : Expr) (st : NestState) : m (NestFieldKind × NestState) := do
  -- an instantiation whose parameters mention no frame hole is walked at
  -- the EMPTY frame stack: its frame
  -- reads nothing of the frames it was met under, so every cached frame
  -- is derived at the root and a hit's subtree owns all its holes
  let wp := nestWalkStack ctx prog ds
  let grp ← nestGrowGroup ctx (ctx.hiAt wp.length) us ds (nestFrameMates ctx n) [(n, cty)]
  let act := st.active
  let st := { st with active := grp.map (fun p => ({ cname := p.1, lvls := us, ds := ds } : NestKey)) ++ act }
  let st ← nestFrame ctx ops env rec wp (ctx.hiAt wp.length) us ds nPc grp st
  -- the group is accepted with it — cached only when its parameters
  -- mention no frame hole: only such a key can ever hit (`nestContKey`)
  return (.nested (kb != 0),
    { st with active := act,
              keys := if ds.all (fun x => x.fvarB ≤ ctx.hiAt 0) then
                nestAcceptGroup us ds grp st.keys else st.keys })

/-- The instantiation `(n, us, ds)` met (`nestCont` after its checks): IN
PROGRESS (`active`: every frame being walked, the enclosing frames among
them — `Complete/ProgActive.lean`) — met as a CONSTANT, which only
reduction can produce (the frame abstracts its whole group, so a
syntactic occurrence of a group-mate at the key is its hole): official's
"non valid occurrence" (its `check_positivity` reads the reduct, where a
copied type's constant is no member of the auxiliary block); cached — a hit, but only
when its parameters mention no FRAME hole (a frame hole's variable is reused
by a later frame, with other
parameters, so such a key is walked again); else a new frame.  `cty`:
the type of its hole (`nestInstType`, run by the caller). -/
def nestContKey (ctx : NestCtx) (ops : CheckerOps m) (env : Env)
    (rec : List NestHole → Nat → Nat → Expr → NestState → m (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level) (ds : List Expr) (nPc : Nat)
    (cty : Expr) (st : NestState) : m (NestFieldKind × NestState) :=
  if st.active.contains ⟨n, us, ds⟩ then
    throw (.invalid "nested positivity: non valid occurrence of the datatypes being \
      declared (an instantiation in progress, reached through reduction)")
  else if ds.all (fun x => x.fvarB ≤ ctx.hiAt 0) && st.keys.contains ⟨n, us, ds⟩ then
    pure (.nested (kb != 0), st)
  else nestContNew ctx ops env rec prog kb n us ds nPc cty st

/-- **The container case** of `nestPos`: the reduct `w` is the stored
inductive `n.{us}` applied to `args` (`contApp`), `rec` the walk
itself one fuel lower (at a frame's fields).  The container's
constructors are looked up by the names its record lists
(`nestContainer`); its checks (constructors
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
  -- the instance is FULLY applied: the container case
  -- compares the container's family at the index tuple, and a partial
  -- application is a function, whose graph does not grow with its values.
  -- A field's domain is a type, so a checked constructor never has one.
  let ni ← nestInstType ctx (ctx.hiAt prog.length) ⟨n, us, args.take q.1⟩
  unless args.length == q.1 + ni.1 do
    throw (.invalid "nested positivity: type expected (a container instance that is not \
      fully applied)")
  nestContKey ctx ops env rec prog kb n us (args.take q.1) q.1 ni.2 (nestContainerC ctx st n).2

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
        -- `holeApp`: a hole (`nestHoleAt`) — a member's, the ROOT frame's,
        -- or a container frame's, its instantiation in progress — applied
        -- to its frame's own parameters (the root's: the block's canonical
        -- ones) and hole-free indices, at its full arity (official
        -- `is_valid_ind_app`, :338–341)
        match nestHoleAt ctx prog i with
        | some h =>
          if h.key.ds.length ≤ args.length && args.take h.key.ds.length == h.key.ds &&
              (args.drop h.key.ds.length).all (fun x => !x.nestOcc ctx.names ctx.nP hi) &&
              args.length == nestArity ctx h.key.cname then
            return (if i < ctx.hiAt 0 then
                (if kb == 0 then .recursive (i - ctx.nP) else .reflexive (i - ctx.nP))
              else .inProgress, w, st)
          else throw nestNonValid
        | none => throw nestNonValid
      | .const n us =>
        -- a member constant left after the abstraction (other levels)
        if ctx.names.contains n then throw nestNonValid
        -- `contApp`: a stored inductive at a concrete instantiation
        let (k, st) ← nestCont ctx ops env (nestPos ops env ctx fuel) prog kb n us args st
        pure (k, w, st)
      | _ => throw nestNonValid

/-- The member holes: member `m` is the free variable `nP + m`, typed by
its former's type (closed, so the hole is well-scoped anywhere above
the parameters).  `none` when a member is not a stored former. -/
def nestHoles (ctx : NestCtx) : Option (List Expr) :=
  (List.range ctx.names.length).mapM fun mm =>
    match ctx.find? (ctx.names.getD mm .anonymous) with
    | some (.indInfo cv _) => some (.fvar (ctx.nP + mm) cv.type)
    | _ => none

/-- **The ROOT frame's substitution** (charter item 2: "the holes are
ordinary open terms (members abstracted to fvars)"): every member
constant at the block's own levels to its hole, UNAPPLIED — so a redex
that produces `T_m p⃗` only after whnf still reduces to the hole.  A
container frame's is its group's (`nestFrame`'s `sub`). -/
def nestRootSub (ctx : NestCtx) (holes : List Expr) : Name → List Level → Option Expr :=
  fun c us =>
    if us == ctx.lps.map .param then
      match ctx.names.findIdx? (· == c) with
      | some mm => holes[mm]?
      | none => none
    else none

/-- **The member abstraction**: the root frame's substitution
(`nestRootSub`) applied (`nestAbstract_eq`). -/
def nestAbstract (ctx : NestCtx) (holes : List Expr) (e : Expr) : Expr :=
  e.replaceConsts fun c us =>
    if us == ctx.lps.map .param then
      match ctx.names.findIdx? (· == c) with
      | some mm => holes[mm]?
      | none => none
    else none

theorem nestAbstract_eq (ctx : NestCtx) (holes : List Expr) (e : Expr) :
    nestAbstract ctx holes e = e.replaceConsts (nestRootSub ctx holes) := rfl

/-- M2′: a member-abstracted constructor type mentions no member
CONSTANT (every member occurrence was at the block's own levels) — a
REJECT with official's wording.  Official imposes it since
v4.33.1: `check_uniform_ind_occs` (`inductive.cpp`, run by
`add_inductive` before the nested elimination) walks every constructor
type SYNTACTICALLY and throws at every occurrence of a member whose
levels are not structurally the declaration's (`const_levels(fn) ==
lvls`) — a superset of this check (it also wants the member applied to
exactly the parameter variables, which the walk's own arms check where
it reads the occurrence).  Official ≤ v4.33.0 accepts where the walk
never reads the occurrence (a redex whnf drops, a phantom container
parameter): charter item 9 follows the newer kernel.  The frame reading
needs it. -/
def nestNoMemberConst (ctx : NestCtx) (e : Expr) : m Unit :=
  if e.nestOcc ctx.names 0 0 then
    throw (.invalid "nested positivity: invalid occurrence of a datatype being declared: it \
      must be applied to the parameters and universe levels of the mutual declaration (a \
      member at other universe levels in a constructor type)")
  else pure ()

/-! ### The root frame

The block itself is the walk's ROOT frame: its key each member at the
block's own levels and canonical parameters (`NestCtx.rootHoles`), its
holes the member holes, its constructors the block's own — walked by the
one constructor loop (`nestCtors`), exactly as a container frame's are:
instantiated at the key (the members abstracted by `nestRootSub`), typed
at the holes' context, every field through `nestPos`, U4, the result,
the normal form recorded (K.53′).  What only the root has is its own
lines (`nestRootLines`): the members' uniform occurrences (M3, M2′), and
— at the install — the fields' universes at the holes
(`checkAbsCtorSorts`, `BlockInstall.lean`). -/

/-- **The root frame**: every member's constructors through `nestCtors`
at the root key (the block's levels `lps`, the canonical parameters, the
holes `nP + t` above them, `nestRootSub`), member by member, sharing the
walk's state; each constructor walked at the input-derived fuel of its
instantiated type (`whnfWalkFuel`: the root has no enclosing walk).
Returns every constructor's kinds and walked normal form
(member-abstracted, at the walk's context), per member. -/
def nestRoot (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (holes : List Expr) :
    List (List (ConstantVal × Nat)) → NestState →
      m (List (List (List NestFieldKind × Expr)) × NestState)
  | [], st => pure ([], st)
  | cs :: css, st => do
    let (o, st) ← nestCtors ctx ops env (fun crest => nestPos ops env ctx (whnfWalkFuel crest)) []
      (ctx.hiAt 0) (ctx.lps.map .param) ctx.params ctx.nP (nestRootSub ctx holes) cs st
    let (os, st) ← nestRoot ops env ctx holes css st
    pure (o :: os, st)

/-- **The root's own lines**, per constructor, on its walked normal form
`tyN` (the root frame's output): M3 and M2′ (`Expr.holesApplied`) —
official's `check_uniform_ind_occs` reads the members' occurrences —
and M2′ on the member-abstracted DECLARED type (`nestNoMemberConst`): a
member at other levels where the walk never reads it (a redex whnf
drops, a phantom container parameter, `restrict_a27_m2prime_redex`,
`restrict_a28_m2prime_phantom`; one it reads is the walk's own "non
valid occurrence", `restrict_b02_m2prime_direct_bad`).  Rejects, as
official ≥ v4.33.1. -/
def nestRootLines (ctx : NestCtx) (holes : List Expr) :
    List (ConstantVal × Nat) → List (List NestFieldKind × Expr) → m Unit
  | c :: cs, o :: os => do
    unless o.2.holesApplied ctx.names ctx.nP (ctx.hiAt 0) do
      throw (.invalid "nested positivity: invalid occurrence of a datatype being declared: it \
        must be applied to the parameters and universe levels of the mutual declaration (a \
        member not applied to the parameters, in a container's parameter)")
    nestNoMemberConst ctx (nestAbstract ctx holes c.1.type)
    nestRootLines ctx holes cs os
  | _, _ => pure ()

/-- `nestRootLines` at every member. -/
def nestRootLinesAll (ctx : NestCtx) (holes : List Expr) :
    List (List (ConstantVal × Nat)) → List (List (List NestFieldKind × Expr)) → m Unit
  | cs :: css, os :: oss => do
    nestRootLines ctx holes cs os
    nestRootLinesAll ctx holes css oss
  | _, _ => pure ()

/-! ### The seeds

The stream's recursor family names the classes it eliminates: every
recursor's major `I.{us} D⃗ ı⃗`.  An outside one — `I` a stored inductive
that is no member and not `Quot` — is official's auxiliary type.  The
recursor check RESOLVES every major first (`targetMajorOf`: the head,
the levels, the parameters `D⃗` over the recursor's parameter binders),
and every outside class it resolved SEEDS the walk (`nestSeedOf`): it is
walked at the root like a container instance met there (`nestContKey`
at the empty frame stack: a cache hit, or its frame walked), after the
members' constructors, sharing the cache.  So every class of the
family is a node by construction — an occurrence whnf erases
(`K (List T)` with `K _ := Nat`) among them — and the walk reads no
syntactic occurrence.

A class is moved to the walk's representation (`nestSeedOf`): its
parameters' members abstracted to their holes (`nestAbstract`) and
every free variable — a recursor parameter binder — replaced WHOLE by
the canonical parameter variable of its index (`ctx.params`), so the
key's leaves are the canonical variables' and the holes'.  Nothing
here trusts the stream: every seed is walked as the positivity check
walks any container instance, and the proofs read a seed's key only
through its frame's derivation and its leaves. -/

/-- **A resolved class as a seed**: the outside class `I.{us} ds`
(`ds` over the recursor's parameter binders `0 ..< nP`) in the walk's
representation, with its parameter count (see "The seeds"). -/
def nestSeedOf (ctx : NestCtx) (holes : List Expr) (I : Name) (us : List Level)
    (ds : List Expr) (nPc : Nat) : NestKey × Nat :=
  (⟨I, us, ds.map fun x => (nestAbstract ctx holes x).replaceFVars fun i => ctx.params[i]?⟩,
    nPc)

/-- **The seeds walked**, in order, at the root (see "The seeds"): each
class a container instance met at the empty frame stack
(`nestContKey`).  A seed's parameters are closed and below the frame
holes by construction (`nestSeedOf` of a class whose parameters mention
only the recursor's parameter binders, `targetMajorOf`), so nothing about
them is checked here. -/
def nestSeeds (ops : CheckerOps m) (env : Env) (ctx : NestCtx) :
    List (NestKey × Nat) → NestState → m NestState
  | [], st => pure st
  | (key, nPc) :: ks, st => do
    let F := key.ds.foldl (fun a d => max a (whnfWalkFuel d)) fuelSlack
    let (_, cty) ← nestInstType ctx (ctx.hiAt 0) key
    let (_, st) ← nestContKey ctx ops env (nestPos ops env ctx F) [] 0 key.cname key.lvls
      key.ds nPc cty st
    nestSeeds ops env ctx ks st

/-- **Positivity through containers, for a whole block** (the unit
tests' entry): the root frame (`nestRoot`) and its own lines
(`nestRootLinesAll`), from the empty state.  `ctorss` are the members'
constructors ANNOTATED (not normalised: the function reduces itself).
Returns the accepted instantiations, the kinds, every constructor's
NORMALISED type and the recorded normal forms. -/
def nestedBlockPositivity (ops : CheckerOps m) (env : Env) (ctx : NestCtx)
    (ctorss : List (List (ConstantVal × Nat))) : m NestedPositivity := do
  let holes ← unwrapOr (nestHoles ctx)
    (.internal "nested positivity: a member is not a stored former")
  let (outs, st) ← nestRoot ops env ctx holes ctorss {}
  nestRootLinesAll ctx holes ctorss outs
  pure ⟨st.keys, outs.map (·.map (·.1)), outs.map (·.map (·.2)), st.ctorNfs⟩

end Nested

end ConLeche

module

public import ConLeche.Kernel.Inductives.NativeParts

@[expose] public section

/-!
# The k-ary block: the record, the recogniser, the positivity walk
(the uniform inductive route, milestone M1)

`BlockParts` is the shape a block on the fixpoint route is read into,
at ANY number `k` of mutually recursive members: the members with
their own index counts, constructors and recursors, the shared
parameter count, the shared elimination level and result sort.  The
`k = 1` instance is the record the one-member route has always used
(`NativeParts`, `ConLeche/Kernel/Inductives/NativeParts.lean`);
`BlockParts.toNative` is that reading, and the install's stages agree
with the one-member stages through it
(`ConLeche/Verify/Inductives/BlockOne.lean`).

**The route is gated at `k = 1`** (`blockRouteK1Only`): `blockParts?`
returns `none` for a block with two or more type formers, so a mutual
block is still the in-process modeller's and every tree between here
and the flip is a complete, proved checker.  The gate is ONE named
constant, deleted at the flip.

The three pieces:

* **the record** (`MemberShape`/`BlockShape`/`BlockParts`) with the
  `complete`/`withKinds`/`withSort` projections the proofs' `generalize`
  dance needs (the pattern of `NativeParts.complete_*`);
* **the recogniser** (`blockSplit`, `blockCounts?`, `blockShape?`,
  `blockParts?`) — official's `add_inductive` reads the type formers,
  the constructors and the parameter count and GENERATES the recursors,
  so nothing the recursor records claim is a condition of recognition:
  their structural pin travels with the record (`blockRecPinOk`,
  `blockRecLpsOk`) and the install throws on it (task #220's
  arrangement, at k members);
* **positivity across k names** (`blockFieldKind`, `blockCtorKinds`):
  official's `check_positivity` with `m_ind_cnsts` the whole member
  list, so a recursive field carries the TARGET member it names
  (`BlockFieldKind.recursive (tgt : Nat)`).

The constructors are assigned to members by their result head
(`ctorMember?`), official's own reading: a constructor belongs to the
type its result names.  A head that is no member of the block leaves
the constructor in member 0's group, where the install rejects it with
official's message ("invalid return type", `structCtorResidOk`); a
grouping that is not monotone in block order contradicts the generated
recursors' minor order and is rejected by the recursor pin
(`blockRecPinOk`'s last conjunct).
-/

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

/-- The positions of the recursive fields (the ones with an inductive
hypothesis), `recIdxOf` at the target-carrying kinds. -/
def blockRecIdxOf (ks : List BlockFieldKind) : List Nat :=
  (List.range ks.length).filter fun i =>
    match ks.getD i .ordinary with
    | .recursive _ => true
    | .reflexive _ => true
    | _ => false

/-- The targets of the fields, one per field (`0` at a field with no
inductive hypothesis, where nothing reads it). -/
def blockTgtsOf (ks : List BlockFieldKind) : List Nat :=
  ks.map fun k =>
    match k with
    | .recursive t => t
    | .reflexive t => t
    | _ => 0

/-! ## The record -/

/-- One member of a block: its type former, its own index count, its
constructors (member-local, in block order), its recursor and that
recursor's rules as exported. -/
structure MemberShape where
  /-- the member's type former -/
  cvT : ConstantVal
  /-- the member's index count -/
  nIdx : Nat
  /-- the member's constructors in block order, each with its field count -/
  ctors : List (ConstantVal × Nat)
  /-- the member's recursor -/
  cvR : ConstantVal
  /-- the member's rules' right-hand sides as exported -/
  rhss : List Expr
  deriving Repr, Inhabited

/-- The pieces of a recognised block at any number of members: the
members, the SHARED parameter count, elimination level parameter and
result sort (official requires the parameters to agree definitionally
and the result sorts to be equivalent — `check_inductive_types`, and
one elimination level for all k recursors). -/
structure BlockShape where
  /-- the members in block order -/
  members : List MemberShape
  /-- the shared parameter count -/
  nP : Nat
  /-- the recursors' fresh elimination level parameter (`large` only;
  `.anonymous` for a small eliminator) -/
  elim : Name
  /-- the result sort (member 0's; the others are `Level.isEquiv` to it) -/
  resSort : Level
  /-- large eliminator (a fresh elimination level parameter in front) -/
  large : Bool
  /-- the result sort is provably `Prop` -/
  isProp : Bool
  deriving Repr, Inhabited

/-- The constructors of a list of members, counted (a recursion, not a
`foldl`, so that ONE member's count is `n + 0` and reduces). -/
def numCtorsOf : List MemberShape → Nat
  | [] => 0
  | ms :: rest => ms.ctors.length + numCtorsOf rest

namespace BlockShape

/-- The number of members. -/
def k (p : BlockShape) : Nat := p.members.length
/-- The number of constructors of the whole block. -/
def numCtors (p : BlockShape) : Nat := numCtorsOf p.members
/-- The constructors of the members before `m`. -/
def offs (p : BlockShape) (m : Nat) : Nat := numCtorsOf (p.members.take m)
/-- The members' names, in block order (the positivity walk's `names`). -/
def memberNames (p : BlockShape) : List Name := p.members.map (·.cvT.name)
/-- The members' index counts, in block order. -/
def nIdxs (p : BlockShape) : List Nat := p.members.map (·.nIdx)
/-- The block's level parameters (member 0's; every member carries
them — the recogniser checks it). -/
def lps (p : BlockShape) : List Name :=
  (p.members.head?.map (·.cvT.levelParams)).getD []
/-- The constructors of the whole block, in block order. -/
def allCtors (p : BlockShape) : List (ConstantVal × Nat) :=
  (p.members.map (·.ctors)).flatten
/-- Every recursor's rule prefix: the parameters, the k motives and the
block's minors (official's `nparams + ntypes + nminors`). -/
def rulePrefix (p : BlockShape) : Nat := p.nP + p.k + p.numCtors
/-- Member `m`'s recursor's major-premise index. -/
def majorIdx (p : BlockShape) (m : Nat) : Nat :=
  p.rulePrefix + (p.members.getD m default).nIdx

/-- The record completed with the former stage's result sort (task
#195 at k members: the sort is read off member 0's checked telescope,
the other members' being `Level.isEquiv` to it). -/
def withSort (p : BlockShape) (s : Level) : BlockShape :=
  { p with resSort := s, isProp := Level.isEquiv s .zero == some true }

@[simp] theorem withSort_members (p : BlockShape) (s : Level) :
    (p.withSort s).members = p.members := rfl
@[simp] theorem withSort_nP (p : BlockShape) (s : Level) : (p.withSort s).nP = p.nP := rfl
@[simp] theorem withSort_elim (p : BlockShape) (s : Level) : (p.withSort s).elim = p.elim := rfl
@[simp] theorem withSort_resSort (p : BlockShape) (s : Level) :
    (p.withSort s).resSort = s := rfl
@[simp] theorem withSort_large (p : BlockShape) (s : Level) :
    (p.withSort s).large = p.large := rfl
@[simp] theorem withSort_isProp (p : BlockShape) (s : Level) :
    (p.withSort s).isProp = (Level.isEquiv s .zero == some true) := rfl
@[simp] theorem withSort_k (p : BlockShape) (s : Level) : (p.withSort s).k = p.k := rfl
@[simp] theorem withSort_numCtors (p : BlockShape) (s : Level) :
    (p.withSort s).numCtors = p.numCtors := rfl
@[simp] theorem withSort_memberNames (p : BlockShape) (s : Level) :
    (p.withSort s).memberNames = p.memberNames := rfl
@[simp] theorem withSort_nIdxs (p : BlockShape) (s : Level) :
    (p.withSort s).nIdxs = p.nIdxs := rfl
@[simp] theorem withSort_lps (p : BlockShape) (s : Level) : (p.withSort s).lps = p.lps := rfl
@[simp] theorem withSort_allCtors (p : BlockShape) (s : Level) :
    (p.withSort s).allCtors = p.allCtors := rfl
@[simp] theorem withSort_rulePrefix (p : BlockShape) (s : Level) :
    (p.withSort s).rulePrefix = p.rulePrefix := rfl
@[simp] theorem withSort_majorIdx (p : BlockShape) (s : Level) (m : Nat) :
    (p.withSort s).majorIdx m = p.majorIdx m := rfl

/-- Completing a record that already carries its own sort (with the
`isProp` flag the recogniser pinned) changes nothing. -/
theorem withSort_self (p : BlockShape)
    (h : p.isProp = (Level.isEquiv p.resSort .zero == some true)) :
    p.withSort p.resSort = p := by
  cases p with
  | mk members nP elim resSort large isProp =>
    simp only [BlockShape.withSort]
    simp only at h
    rw [← h]

end BlockShape

/-- The pieces of a recognised block: its shape, the fields' kinds
(per member, per constructor, per field — a PLACEHOLDER at recognition,
filled by the install) and the recursor records' structural pin. -/
structure BlockParts extends BlockShape where
  /-- per member, per constructor, per field: its kind -/
  kinds : List (List (List BlockFieldKind))
  /-- **the stream's recursor records passed the structural pin**
  (task #220 at k members): each recursor's two argument sums, its rule
  count, each rule's constructor and field count, and the constructors'
  grouping being monotone in block order (the generated minors are in
  block order, so a permuted export cannot match them).  The recogniser
  records the verdict; the recursor stage THROWS on `false`. -/
  recPinned : Bool
  deriving Repr, Inhabited

/-- **The record completed by the formers' stage**: the shape the
formers' run returned (its result sort read through `whnf`) with the
recogniser's field kinds. -/
def BlockParts.complete (p₀ : BlockParts) (p₁ : BlockShape) : BlockParts :=
  ⟨p₁, p₀.kinds, p₀.recPinned⟩

@[simp] theorem BlockParts.complete_toBlockShape (p₀ : BlockParts) (p₁ : BlockShape) :
    (p₀.complete p₁).toBlockShape = p₁ := rfl
@[simp] theorem BlockParts.complete_kinds (p₀ : BlockParts) (p₁ : BlockShape) :
    (p₀.complete p₁).kinds = p₀.kinds := rfl
@[simp] theorem BlockParts.complete_recPinned (p₀ : BlockParts) (p₁ : BlockShape) :
    (p₀.complete p₁).recPinned = p₀.recPinned := rfl
@[simp] theorem BlockParts.complete_members (p₀ : BlockParts) (p₁ : BlockShape) :
    (p₀.complete p₁).members = p₁.members := rfl
@[simp] theorem BlockParts.complete_nP (p₀ : BlockParts) (p₁ : BlockShape) :
    (p₀.complete p₁).nP = p₁.nP := rfl
@[simp] theorem BlockParts.complete_elim (p₀ : BlockParts) (p₁ : BlockShape) :
    (p₀.complete p₁).elim = p₁.elim := rfl
@[simp] theorem BlockParts.complete_resSort (p₀ : BlockParts) (p₁ : BlockShape) :
    (p₀.complete p₁).resSort = p₁.resSort := rfl
@[simp] theorem BlockParts.complete_large (p₀ : BlockParts) (p₁ : BlockShape) :
    (p₀.complete p₁).large = p₁.large := rfl
@[simp] theorem BlockParts.complete_isProp (p₀ : BlockParts) (p₁ : BlockShape) :
    (p₀.complete p₁).isProp = p₁.isProp := rfl

/-- The record completed with the fields' kinds: the install
classifies them on the constructors it stored (their field domains
normalised by official's positivity walk) and every later stage runs on
this record. -/
def BlockParts.withKinds (p : BlockParts) (ks : List (List (List BlockFieldKind))) :
    BlockParts :=
  { p with kinds := ks }

@[simp] theorem BlockParts.withKinds_kinds (p : BlockParts)
    (ks : List (List (List BlockFieldKind))) : (p.withKinds ks).kinds = ks := rfl
@[simp] theorem BlockParts.withKinds_recPinned (p : BlockParts)
    (ks : List (List (List BlockFieldKind))) : (p.withKinds ks).recPinned = p.recPinned := rfl
@[simp] theorem BlockParts.withKinds_toBlockShape (p : BlockParts)
    (ks : List (List (List BlockFieldKind))) :
    (p.withKinds ks).toBlockShape = p.toBlockShape := rfl

/-- **The one-member reading of the shape** (the M1 bridge): at
`k = 1` a `BlockShape` IS an `InductiveShape`.  At `k ≠ 1` it reads
member 0 and is junk — nothing consumes it there, because the route is
gated (`blockRouteK1Only`). -/
def BlockShape.toInductive (p : BlockShape) : InductiveShape :=
  let ms := p.members.headD default
  ⟨ms.cvT, ms.ctors, p.nP, ms.nIdx, ms.cvR, p.elim, p.resSort, ms.rhss, p.large, p.isProp⟩

/-- **The one-member reading of the record**: the shape's, with the
kinds' targets forgotten.  The install's stages agree with the
one-member stages through this map
(`ConLeche/Verify/Inductives/BlockOne.lean`). -/
def BlockParts.toNative (p : BlockParts) : NativeParts :=
  ⟨p.toBlockShape.toInductive,
    (p.kinds.headD []).map (List.map BlockFieldKind.toRec), p.recPinned⟩

@[simp] theorem BlockShape.toInductive_withSort (p : BlockShape) (s : Level) :
    (p.withSort s).toInductive = p.toInductive.withSort s := rfl

/-! ## Recognition

The block's members after the type formers: the constructors, then the
closing recursors — `sumSplit` (`ConLeche/Kernel/Inductives/SumParts.lean`)
at k formers and k recursors.  Nothing is refused by COUNT here: a
block with two formers splits, and `blockParts?`'s gate is what keeps
it off the route until the flip. -/

/-- The closing recursors. -/
def blockSplitRecs : List ConstantInfo →
    Option (List (ConstantVal × Nat × Nat × List RecRule))
  | [] => some []
  | .recInfo cvR mI rP rules :: rest =>
    (blockSplitRecs rest).map fun rs => (cvR, mI, rP, rules) :: rs
  | _ => none

/-- The constructors, then the recursors. -/
def blockSplitCtors : List ConstantInfo →
    Option (List (ConstantVal × Nat × Nat) × List (ConstantVal × Nat × Nat × List RecRule))
  | .ctorInfo cvC nP nF :: rest =>
    (blockSplitCtors rest).map fun q => ((cvC, nP, nF) :: q.1, q.2)
  | rest => (blockSplitRecs rest).map fun rs => ([], rs)

/-- The type formers, the constructors and the recursors. -/
def blockSplit : List ConstantInfo →
    Option (List ConstantVal × List (ConstantVal × Nat × Nat) ×
      List (ConstantVal × Nat × Nat × List RecRule))
  | .indInfo cvT _ :: rest =>
    (blockSplit rest).map fun q => (cvT :: q.1, q.2)
  | rest => (blockSplitCtors rest).map fun q => ([], q.1, q.2)

/-- **One member's parameter and index counts**, read as official
reads them (`nativeCounts?` at k members): `nP` is the count the
DECLARATION carries and `nIdx` is what is left of the member's
Π-telescope once those binders are peeled.  At a former declared AT A
DEFINITION (task #195) the syntactic telescope is not the one official
walks and the member's own recursor record's argument sums are the only
reading available — with `nP + k + N` the rule prefix at k members. -/
def blockCounts? (nPd k nC : Nat) (cvT : ConstantVal) (mI rP : Nat) : Option (Nat × Nat) :=
  match cvT.type.piBinders with
  | (bs, .sort _) => if nPd ≤ bs.length then some (nPd, bs.length - nPd) else none
  | _ =>
    if rP < nC + k || mI < rP then none
    else if rP - (nC + k) == nPd then some (nPd, mI - rP) else none

/-- The member a constructor belongs to: the one its RESULT names
(official's own reading — `check_constructors` checks each constructor
against the type its result heads). -/
def ctorMember? (names : List Name) (lps : List Name) (nP : Nat)
    (c : ConstantVal × Nat) : Option Nat :=
  match c.1.type.stripPis (nP + c.2) with
  | some (_, cbody) => memberIdxAt? names (lps.map .param) cbody.getAppFn
  | none => none

/-- **The constructors grouped by member**, in block order.

At ONE member the assignment is forced and nothing is read: the
constructor's result head is official's "invalid return type" check,
thrown by the constructor stage (`structCtorResidOk`,
`ConLeche/Kernel/Inductives/SumInstall.lean`) exactly as it always has
been.  At two or more members the group is read off the result head; a
constructor whose head is no member of the block stays in NO group and
is caught by the recursor pin's grouping conjunct
(`blockRecPinOk`) — a `.invalid`, as official's is. -/
def blockGroups (names : List Name) (lps : List Name) (nP k : Nat)
    (cs : List (ConstantVal × Nat)) : List (List (ConstantVal × Nat)) :=
  if k == 1 then [cs]
  else (List.range k).map fun m => cs.filter fun c => ctorMember? names lps nP c == some m

/-- **The recursor records' structural pin** (task #220 at k members),
thrown at the recursor stage: every recursor's two argument sums, one
rule per constructor of ITS member in block order, each rule naming its
constructor with its field count — and the grouping itself, which must
exhaust the block's constructors in block order (the generated minors
are the block's constructors in block order, so a grouping that is not
monotone cannot match any generated recursor). -/
def blockRecPinOk (p : BlockShape) (block : List ConstantInfo) : Bool :=
  match blockSplit block with
  | some (cvTs, cs, rs) =>
    cvTs.length == p.k && rs.length == p.k &&
    (p.allCtors.map (·.1.name) == cs.map (·.1.name)) &&
    (List.range p.k).all fun m =>
      match rs[m]?, p.members[m]? with
      | some (_, mI, rP, rules), some ms =>
        rP == p.rulePrefix && mI == p.rulePrefix + ms.nIdx &&
        rules.length == ms.ctors.length &&
        (List.range ms.ctors.length).all fun j =>
          match rules[j]?, cs[p.offs m + j]? with
          | some rule, some (cvC, _, nF) => rule.ctor == cvC.name && rule.nfields == nF
          | _, _ => false
      | _, _ => false
  | none => false

/-- **The recursor records' level-parameter pin** (task #220 at k
members): official generates ONE elimination level parameter for the
whole block, so every recursor carries the block's own level parameters
with that one in front at the large eliminator. -/
def blockRecLpsOk (p : BlockShape) : Bool :=
  p.members.all fun ms =>
    if p.large then ms.cvR.levelParams == p.elim :: p.lps
    else ms.cvR.levelParams == p.lps

/-- **The members' index counts**, one `blockCounts?` per member
against its own recursor record: `none` unless there are as many
recursors as formers (the count agreement official's replay makes when
it compares every generated recursor with an exported one). -/
def blockMemberCounts? (nPd k nC : Nat) : List ConstantVal →
    List (ConstantVal × Nat × Nat × List RecRule) → Option (List Nat)
  | [], [] => some []
  | cvT :: ts, r :: rs =>
    match blockCounts? nPd k nC cvT r.2.1 r.2.2.1 with
    | some c => (blockMemberCounts? nPd k nC ts rs).map fun ns => c.2 :: ns
    | none => none
  | _, _ => none

/-- The block's shape: the members with their counts, the shared
parameter count, the result sort read off member 0 (or the placeholder
the install replaces, task #195) and which eliminator the recursor
records claim.  Nothing of the recursor records is pinned here
(`blockRecPinOk`/`blockRecLpsOk` travel with the record and the install
throws on them) — the arrangement of task #220, so that a block whose
recursor record is a stub is REJECTED by its own type and constructors
rather than declined. -/
def blockShape? (nPd : Nat) (block : List ConstantInfo) : Option BlockShape :=
  match blockSplit block with
  | some (cvTs, cs, rs) =>
    match cvTs, rs with
    | cvT0 :: _, (cvR0, _, _, _) :: _ =>
      let lps := cvT0.levelParams
      let names := cvTs.map (·.name)
      let k := cvTs.length
      match blockMemberCounts? nPd k cs.length cvTs rs with
      | none => none
      | some nIdxs =>
        let nP := nPd
        if (cvTs.all fun c => reservedBasisNames.contains c.name == false) &&
            (rs.all fun r => reservedBasisNames.contains r.1.name == false) &&
            (cvTs.all fun c => c.levelParams == lps) &&
            cs.all (fun c => c.2.1 == nP && c.1.levelParams == lps &&
              reservedBasisNames.contains c.1.name == false) then
          -- the result sort: member 0's, read off its declared type when
          -- that is a syntactic telescope ending in a sort; otherwise
          -- (task #195) a PLACEHOLDER the install's whnf loop replaces
          let s : Level := match cvT0.type.stripPis (nP + nIdxs.headD 0) with
            | some (_, .sort s) => s
            | _ => .zero
          let isProp := Level.isEquiv s .zero == some true
          let ctors : List (ConstantVal × Nat) :=
            cs.map fun (c : ConstantVal × Nat × Nat) => (c.1, c.2.2)
          let groups := blockGroups names lps nP k ctors
          let members := ((cvTs.zip nIdxs).zip (groups.zip rs)).map
            fun (a : (ConstantVal × Nat) ×
                (List (ConstantVal × Nat) × ConstantVal × Nat × Nat × List RecRule)) =>
              (⟨a.1.1, a.1.2, a.2.1, a.2.2.1, a.2.2.2.2.2.map RecRule.rhs⟩ : MemberShape)
          -- WHICH ELIMINATOR the recursors are: the LARGE one carries a
          -- fresh elimination level parameter in front of the block's.
          -- Read off member 0's; the others are `blockRecLpsOk`'s, thrown
          -- at the recursor stage
          let large? : Option Name :=
            match cvR0.levelParams with
            | elim :: relps => if relps == lps && !lps.contains elim then some elim else none
            | [] => none
          match large? with
          | some elim => some ⟨members, nP, elim, s, true, isProp⟩
          | none => some ⟨members, nP, .anonymous, s, false, isProp⟩
        else none
    | _, _ => none
  | none => none

/-- **THE ROUTE'S GATE** (decision D6, milestone M1): the uniform
installer is written at any number of members, but the route takes only
ONE-MEMBER blocks until the flip (milestone M6), so that the in-process
modeller keeps serving mutual blocks and every tree in between is a
complete, proved checker.  Deleting this constant — and the guard in
`blockParts?` it names — is the flip. -/
def blockRouteK1Only : Bool := true

/-- Recognise a block for the uniform fixpoint route: its SHAPE
(`blockShape?`), with the fields' kinds a PLACEHOLDER the install fills
(`BlockParts.withKinds`) after normalising every field domain by
official's positivity walk, and the recursor records' structural pin
(`blockRecPinOk`), which the recursor stage throws on.  A block with
two or more members is refused HERE, by the gate alone. -/
def blockParts? (nPd : Nat) (block : List ConstantInfo) : Option BlockParts :=
  match blockSplit block with
  | some (cvTs, _, _) =>
    if blockRouteK1Only && cvTs.length != 1 then none
    else (blockShape? nPd block).map fun p => ⟨p, [], blockRecPinOk p block⟩
  | none => none

end ConLeche

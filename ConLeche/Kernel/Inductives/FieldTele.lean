module

public import ConLeche.Kernel.ExprOps

@[expose] public section

/-!
# Constructor fields: their kinds and their telescopes

The field-level vocabulary the uniform installer (`BlockParts`,
`BlockRec`, `BlockInstall`), the model and the recursor conformance
check (`ConLeche/Conformance/`) share:

* `RecFieldKind` — a field's kind: `.ordinary` (the domain does not
  mention the block), `.recursive` (`T p⃗ e⃗`), `.reflexive`
  (`Π a⃗ : A⃗, T p⃗ e⃗(a⃗)`), `.negative` (a non-positive or non-valid
  occurrence; the block is rejected) and `.unsupported`;
* a field's own telescope and index expressions off the constructor's
  type (`structFieldTeleOf`, `structFieldIdxOf`), the positions with an
  inductive hypothesis (`recIdxOf`), and those telescopes and indices
  moved to a rule's frame (`structIdxAt`, `structTeleAt`,
  `structTeleVars`, `Expr.mkPisOf`);
* the memoised variable-occurrence test `Expr.mentionsFvar`.

(These lived in the one-member route's `NativeParts`/`NativeInstall`
until lane CONFDIR moved that route's recursor generator to
`ConLeche/Conformance/`.)
-/

namespace ConLeche

/-- The kind of a constructor field of a block (see the module
docstring). -/
inductive RecFieldKind where
  /-- the domain does not mention the block -/
  | ordinary
  /-- the domain is exactly `T p⃗ e⃗`: a finitary recursive field -/
  | recursive
  /-- the domain is `Π a⃗ : A⃗, T p⃗ e⃗(a⃗)` with `A⃗` free of the block: a
  REFLEXIVE (function-space) recursive field (task #202) -/
  | reflexive
  /-- a non-positive (or non-valid) occurrence: the official kernel
  rejects the block -/
  | negative
  /-- an occurrence the official kernel accepts (reflexive, nested,
  under a redex) that this route does not model yet -/
  | unsupported
  deriving Repr, DecidableEq, Inhabited

/-- All leading `∀` binders of an expression (outermost first) and
the body — a recursive field's own telescope (`[]` at a finitary
field, the `a⃗ : A⃗` of a reflexive one, task #202). -/
def Expr.piBinders : Expr → List (Expr × BinderMeta) × Expr
  | .forallE ty b m =>
    let (bs, e) := piBinders b
    ((ty, m) :: bs, e)
  | e => ([], e)

/-- Field `i`'s own telescope `a⃗ : A⃗` (at the field's frame: the
parameters and the earlier fields), off the constructor's type. -/
def structFieldTeleOf (cty : Expr) (nP nF i : Nat) : List (Expr × BinderMeta) :=
  match cty.stripPis (nP + nF) with
  | some (cbs, _) => ((cbs.getD (nP + i) default).1.piBinders).1
  | none => []

/-- The index expressions of field `i`'s domain `Π a⃗, T p⃗ e⃗` (under
the field's own telescope, at the field's frame), off the
constructor's type; `[]` when the field is not of that shape. -/
def structFieldIdxOf (cty : Expr) (nP nF i : Nat) : List Expr :=
  match cty.stripPis (nP + nF) with
  | some (cbs, _) => ((cbs.getD (nP + i) default).1.piBinders).2.getAppArgs.drop nP
  | none => []

/-- The positions of the recursive fields (finitary or reflexive: the
ones with an inductive hypothesis). -/
def recIdxOf (ks : List RecFieldKind) : List Nat :=
  (List.range ks.length).filter fun i =>
    ks.getD i .ordinary == .recursive || ks.getD i .ordinary == .reflexive

/-- An expression of recursive field `i`'s domain sitting under `m`
binders of the field's own telescope, spelled at the field's frame
(the parameters, the `i` earlier fields), moved under all `nF` fields,
`l` further binders below them and `o` extras between the parameters
and the fields: the earlier fields move by `nF - i + l`, the
parameters by `o` more; the `m` telescope binders stay. -/
def structIdxAt (nF o i l m : Nat) (e : Expr) : Expr :=
  (e.liftLooseBVars (nF - i + l) m).liftLooseBVars o (nF + l + m)

/-- Field `i`'s own telescope moved as `structIdxAt` moves its
expressions (binder `k` sits under `k` earlier telescope binders). -/
def structTeleAt (nF o i l : Nat) (pw : PropWhen) (tele : List (Expr × BinderMeta)) :
    List (Expr × BinderMeta) :=
  (List.range tele.length).map fun k =>
    let b := tele.getD k default
    (structIdxAt nF o i l k b.1, ⟨pw⟩)

/-- The variables of an `m`-binder telescope, innermost last. -/
def structTeleVars (m : Nat) : List Expr := (List.range m).map fun k => Expr.bvar (m - 1 - k)

/-- `∀ tele, body` over a binder list (outermost first). -/
def Expr.mkPisOf : List (Expr × BinderMeta) → Expr → Expr
  | [], body => body
  | (ty, mt) :: bs, body => .forallE ty (mkPisOf bs body) mt

/-- `λ tele, body` over a binder list (outermost first). -/
def Expr.mkLamsOf : List (Expr × BinderMeta) → Expr → Expr
  | [], body => body
  | (ty, mt) :: bs, body => .lam ty (mkLamsOf bs body) mt
/-- Does the variable `q` occur as a leaf of `e` (annotations
included, as `fvarLeaves` walks them)? -/
def Expr.mentionsFvar (q : Nat) (e : Expr) : Bool := e.fvarLeaves.any fun l => l.1 == q

/-! ### `mentionsFvar` memoizes

`Expr.fvarLeaves` returns a list that IS tree-sized by construction,
so it cannot be memoized where it stands; the fix belongs to its
consumer.  `mentionsFvar` asks a `Bool` question of it, and that
question memoizes: the answer at a node is a function of the node and
`q` alone, so one hash map keyed by the node — `q` is fixed for the
whole walk, unlike `hasLooseBVarB`'s index — shares the answer across
every path that reaches a shared node.

**There is no cutoff to put in front of it.**  The packed `fvarB`
field is the fvar range of a node's *own* spine and stops at an
`fvar` leaf (`fvarRange (.fvar idx _) = idx + 1`), while `fvarLeaves`
descends hereditarily into the leaf's TYPE ANNOTATION, so
`e.fvarB ≤ q` does not license "`q` does not occur in `e`" — the
range field cannot answer this question at all, and the memo is the
whole remedy.

`tests/e2e/tower_recfield.ndjson` — a recursive structure whose field
after the recursive one is a depth-60 tower over the FIRST field's
variable — is what walks it: `nativeOpenedOk` asks whether the
recursive field's variable occurs in any later field's domain, the
answer is `false`, and nothing short-circuits. -/

/-- `mentionsFvar` at an `fvar` leaf: the index, or its annotation. -/
theorem Expr.mentionsFvar_fvar (q idx : Nat) (ty : Expr) :
    (Expr.fvar idx ty).mentionsFvar q = ((idx == q) || ty.mentionsFvar q) := by
  simp [Expr.mentionsFvar, Expr.fvarLeaves]

theorem Expr.mentionsFvar_app (q : Nat) (f a : Expr) :
    (Expr.app f a).mentionsFvar q = (f.mentionsFvar q || a.mentionsFvar q) := by
  simp [Expr.mentionsFvar, Expr.fvarLeaves]

theorem Expr.mentionsFvar_lam (q : Nat) (ty b : Expr) (m : BinderMeta) :
    (Expr.lam ty b m).mentionsFvar q = (ty.mentionsFvar q || b.mentionsFvar q) := by
  simp [Expr.mentionsFvar, Expr.fvarLeaves]

theorem Expr.mentionsFvar_forallE (q : Nat) (ty b : Expr) (m : BinderMeta) :
    (Expr.forallE ty b m).mentionsFvar q
      = (ty.mentionsFvar q || b.mentionsFvar q) := by
  simp [Expr.mentionsFvar, Expr.fvarLeaves]

theorem Expr.mentionsFvar_letE (q : Nat) (t v b : Expr) :
    (Expr.letE t v b).mentionsFvar q
      = (t.mentionsFvar q || v.mentionsFvar q || b.mentionsFvar q) := by
  simp [Expr.mentionsFvar, Expr.fvarLeaves, Bool.or_assoc]

theorem Expr.mentionsFvar_proj (q : Nat) (s : Name) (i : Nat) (e : Expr) :
    (Expr.proj s i e).mentionsFvar q = e.mentionsFvar q := by
  simp [Expr.mentionsFvar, Expr.fvarLeaves]

/-- The memo's invariant: every recorded answer is the real one. -/
def MentionsFvarMemoInv (q : Nat) (memo : Std.HashMap Expr Bool) : Prop :=
  ∀ (e : Expr) (r : Bool), memo[e]? = some r → r = e.mentionsFvar q

theorem MentionsFvarMemoInv.empty {q : Nat} : MentionsFvarMemoInv q {} := by
  intro e r h; simp at h

theorem MentionsFvarMemoInv.insert {q : Nat} {memo : Std.HashMap Expr Bool}
    (hm : MentionsFvarMemoInv q memo) {e : Expr} {r : Bool}
    (heq : r = e.mentionsFvar q) :
    MentionsFvarMemoInv q (memo.insert e r) := by
  intro e' r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact heq
  · exact hm e' r' hk

/-- Record one answer for `e` in the memo the walk hands back.
Written with projections rather than a destructuring `let` so that the
correctness proof can `split` the walk's own matches. -/
@[inline] def Expr.mentionsFvarIns (e : Expr)
    (r : Bool × Std.HashMap Expr Bool) : Bool × Std.HashMap Expr Bool :=
  (r.1, r.2.insert e r.1)

/-- Memoized `mentionsFvar`. -/
def Expr.mentionsFvarGo (q : Nat) (memo : Std.HashMap Expr Bool) (e : Expr) :
    Bool × Std.HashMap Expr Bool :=
  match e with
  | .bvar _ => (false, memo)
  | .sort _ => (false, memo)
  | .const .. => (false, memo)
  | .lit _ => (false, memo)
  | e =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      Expr.mentionsFvarIns e <|
        match e with
        | .fvar idx ty =>
          if idx == q then (true, memo) else mentionsFvarGo q memo ty
        | .app f a =>
          match mentionsFvarGo q memo f with
          | (true, memo) => (true, memo)
          | (false, memo) => mentionsFvarGo q memo a
        | .lam ty b _ =>
          match mentionsFvarGo q memo ty with
          | (true, memo) => (true, memo)
          | (false, memo) => mentionsFvarGo q memo b
        | .forallE ty b _ =>
          match mentionsFvarGo q memo ty with
          | (true, memo) => (true, memo)
          | (false, memo) => mentionsFvarGo q memo b
        | .letE t v b =>
          match mentionsFvarGo q memo t with
          | (true, memo) => (true, memo)
          | (false, memo) =>
            match mentionsFvarGo q memo v with
            | (true, memo) => (true, memo)
            | (false, memo) => mentionsFvarGo q memo b
        | .proj _ _ sub => mentionsFvarGo q memo sub
        | _ => (false, memo)

/-- **The memoized walk is `mentionsFvar`.** -/
theorem Expr.mentionsFvarGo_spec (q : Nat) :
    ∀ (e : Expr) (memo : Std.HashMap Expr Bool), MentionsFvarMemoInv q memo →
      (mentionsFvarGo q memo e).1 = e.mentionsFvar q ∧
        MentionsFvarMemoInv q (mentionsFvarGo q memo e).2 := by
  intro e
  induction e with
  | bvar j =>
    intro memo hm
    exact ⟨by simp [mentionsFvarGo, Expr.mentionsFvar, Expr.fvarLeaves], hm⟩
  | sort u =>
    intro memo hm
    exact ⟨by simp [mentionsFvarGo, Expr.mentionsFvar, Expr.fvarLeaves], hm⟩
  | const n us =>
    intro memo hm
    exact ⟨by simp [mentionsFvarGo, Expr.mentionsFvar, Expr.fvarLeaves], hm⟩
  | lit l =>
    intro memo hm
    exact ⟨by simp [mentionsFvarGo, Expr.mentionsFvar, Expr.fvarLeaves], hm⟩
  | fvar idx ty ih =>
    intro memo hm
    rw [mentionsFvarGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · simp only [mentionsFvarIns]
      split
      · rename_i hq
        refine ⟨by simp [mentionsFvar_fvar, hq], hm.insert (by simp [mentionsFvar_fvar, hq])⟩
      · rename_i hq
        obtain ⟨h1, h2⟩ := ih memo hm
        exact ⟨by simp [mentionsFvar_fvar, hq, h1], h2.insert (by simp [mentionsFvar_fvar, hq, h1])⟩
  | app f a ihf iha =>
    intro memo hm
    rw [mentionsFvarGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := ihf memo hm
      simp only [mentionsFvarIns]
      split
      · rename_i memo₁ heq
        rw [heq] at h1 h2
        exact ⟨by simp [mentionsFvar_app, ← h1], h2.insert (by simp [mentionsFvar_app, ← h1])⟩
      · rename_i memo₁ heq
        rw [heq] at h1 h2
        obtain ⟨h3, h4⟩ := iha memo₁ h2
        exact ⟨by simp [mentionsFvar_app, ← h1, h3],
          h4.insert (by simp [mentionsFvar_app, ← h1, h3])⟩
  | lam ty b m iht ihb =>
    intro memo hm
    rw [mentionsFvarGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      simp only [mentionsFvarIns]
      split
      · rename_i memo₁ heq
        rw [heq] at h1 h2
        exact ⟨by simp [mentionsFvar_lam, ← h1], h2.insert (by simp [mentionsFvar_lam, ← h1])⟩
      · rename_i memo₁ heq
        rw [heq] at h1 h2
        obtain ⟨h3, h4⟩ := ihb memo₁ h2
        exact ⟨by simp [mentionsFvar_lam, ← h1, h3],
          h4.insert (by simp [mentionsFvar_lam, ← h1, h3])⟩
  | forallE ty b m iht ihb =>
    intro memo hm
    rw [mentionsFvarGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      simp only [mentionsFvarIns]
      split
      · rename_i memo₁ heq
        rw [heq] at h1 h2
        exact ⟨by simp [mentionsFvar_forallE, ← h1],
          h2.insert (by simp [mentionsFvar_forallE, ← h1])⟩
      · rename_i memo₁ heq
        rw [heq] at h1 h2
        obtain ⟨h3, h4⟩ := ihb memo₁ h2
        exact ⟨by simp [mentionsFvar_forallE, ← h1, h3],
          h4.insert (by simp [mentionsFvar_forallE, ← h1, h3])⟩
  | letE t v b iht ihv ihb =>
    intro memo hm
    rw [mentionsFvarGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      simp only [mentionsFvarIns]
      split
      · rename_i memo₁ heq
        rw [heq] at h1 h2
        exact ⟨by simp [mentionsFvar_letE, ← h1],
          h2.insert (by simp [mentionsFvar_letE, ← h1])⟩
      · rename_i memo₁ heq
        rw [heq] at h1 h2
        obtain ⟨h3, h4⟩ := ihv memo₁ h2
        split
        · rename_i memo₂ heq₂
          rw [heq₂] at h3 h4
          exact ⟨by simp [mentionsFvar_letE, ← h1, ← h3],
            h4.insert (by simp [mentionsFvar_letE, ← h1, ← h3])⟩
        · rename_i memo₂ heq₂
          rw [heq₂] at h3 h4
          obtain ⟨h5, h6⟩ := ihb memo₂ h4
          exact ⟨by simp [mentionsFvar_letE, ← h1, ← h3, h5],
            h6.insert (by simp [mentionsFvar_letE, ← h1, ← h3, h5])⟩
  | proj s j sub ih =>
    intro memo hm
    rw [mentionsFvarGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := ih memo hm
      simp only [mentionsFvarIns]
      exact ⟨by simp [mentionsFvar_proj, h1], h2.insert (by simp [mentionsFvar_proj, h1])⟩

/-- The executed `mentionsFvar` (one memoized DAG walk). -/
def Expr.mentionsFvarFast (q : Nat) (e : Expr) : Bool :=
  (Expr.mentionsFvarGo q {} e).1

@[csimp] theorem Expr.mentionsFvar_eq_mentionsFvarFast :
    @Expr.mentionsFvar = @Expr.mentionsFvarFast := by
  funext q e
  exact (mentionsFvarGo_spec q e {} MentionsFvarMemoInv.empty).1.symm

end ConLeche

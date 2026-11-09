module

public import ConLeche.Kernel.Core

@[expose] public section

/-!
# Shared syntactic generators of the inductive install

The syntactic pieces the block install reads and compares against the
stream: the family and constructor spines and the Π-rewrites of the
generated recursor shape (read by the recursor stage,
`ConLeche/Kernel/Inductives/GenRec.lean`), the projection table's
bodies (`structProjBodies`, stored by `checkStructProjTable` at a
structure-like member), and the memoized occurrence walk
(`mentionsAnyConst`).

Line numbers cite lean4lean `Lean4Lean/Inductive/Add.lean`, a
line-by-line port of the official `src/kernel/inductive/inductive.cpp`.
-/

namespace ConLeche

/-! ## The generated recursor's pieces

The reference kernels *generate* the recursor from the block
(lean4lean `Inductive/Add.lean:326-483`, official
`inductive.cpp`'s `mk_rec_infos`); the pieces below spell that shape
syntactically, over the stored type former and constructor types, one
minor premise and one rule per constructor.

**Binders** carry no name, info or other datum (`Expr` has no slot for
them), so the generated telescope is compared against an exported
shape (the standard-axiom pins, `stdAxiomOk`, against the stored
`Iff.rec`/`Nonempty.rec`) by plain equality.  The domains are
re-emitted verbatim. -/

/-- The parameter variables as seen from under `o` extra binders:
`p_k = bvar (o + nP - 1 - k)` — `structFamI`'s argument spine. -/
def structPsAt (o nP : Nat) : List Expr :=
  (List.range nP).map fun k => Expr.bvar (o + nP - 1 - k)

/-- The recursor's elimination level: the fresh parameter at the large
eliminator, `zero` at the small one. -/
def structElimLevel (elim : Name) (large : Bool) : Level :=
  if large then .param elim else .zero

/-! ## The generated recursor at an indexed family (task #175 indexed)

A non-recursive family `T : ∀ p⃗ ı⃗, Sort w` with constructors
`C_k : ∀ p⃗ f⃗, T p⃗ e⃗_k` (the index expressions `e⃗_k` arbitrary terms
over the parameters and the fields) has the recursor

    ∀ p⃗ {motive : ∀ ı⃗ (t : T p⃗ ı⃗), Sort ℓ}
      (minor_k : ∀ f⃗, motive e⃗_k (C_k p⃗ f⃗))…
      ı⃗ (t : T p⃗ ı⃗), motive ı⃗ t

(lean4lean `Inductive/Add.lean:326-483`, official `mk_rec_infos`):
the index binders are the type former's own telescope past the
parameters, re-emitted twice — at the motive (over the parameters
alone) and after the minors (lifted under the motive and the `n`
minors); the minor's conclusion applies the motive to the
constructor's residual index expressions (lifted under the extras)
before the constructor spine.  A rule binds no index
(`rulePrefix = nP + 1 + n`). -/

/-- A constructor residual's shape at an indexed family: the family
at exactly the parameter variables (`o` binders below the parameter
frame) followed by `nIdx` index expressions. -/
def structCtorResidOk (T : Name) (lps : List Name) (nP o nIdx : Nat) (cbody : Expr) : Bool :=
  cbody.getAppFn == .const T (lps.map .param) &&
  cbody.getAppArgs.length == nP + nIdx &&
  cbody.getAppArgs.take nP == structPsAt o nP

/-- The parameter spine of the generated projection bodies, spelled at
the frame of the final `∀ p⃗ (t : T p⃗), _` telescope: `p_k = bvar
(nP - k)`, below the subject `bvar 0`. -/
def structProjPs (nP : Nat) : List Expr :=
  (List.range nP).map fun k => Expr.bvar (nP - k)

/-- The `j`-th earlier-field substitute in a **tower entry's**
generated type (task #175 wiring): the first-class node `t.j`
(`.proj T j` of the subject), at the frame of the subject
`t = bvar 0`.  Each field's entry stands alone, which is what makes
O4's per-field entry branch real. -/
def structProjArgP (T : Name) (j : Nat) : Expr :=
  Expr.proj T j (Expr.bvar 0)

/-- **The projection bodies of a recognised block** (task #175 S1),
one walk of the constructor telescope: the parameter binders are
skipped, and field `i`'s raw domain is instantiated once
(`Expr.instantiateLift`) at the values of the binders before it,
innermost first — the subject's earlier projections `.proj T j (bvar
0)` (`structProjArgP`), then the parameters as the loose variables
`structProjPs nP` (parameter `k` at `bvar (nP - k)`, the subject
reserved at `bvar 0`).  So `bodies[i] = F_i[p⃗ ↦ bvars, f_j ↦ .proj T
j (bvar 0)]`, scoped at `nP + 1`: what a `.proj T i e` use
instantiates in one `instantiateList` along the subject type's
arguments and the subject (`ProjEntry.typeAt`).  The values are
threaded down the telescope (`vs`, one cons per field), the rest of
the telescope is never rewritten.  The table holds every field (the
official `infer_proj` restriction at a `Prop`-declared structure is
checked at the use, `projGuardRows`); no entry is inferred or
pinned. -/
def structProjBodiesGo (T : Name) (vs : List Expr) : Nat → Nat → Expr → Option (List Expr)
  | 0, _, _ => some []
  | k + 1, i, .forallE fdom body =>
    (structProjBodiesGo T (structProjArgP T i :: vs) k (i + 1) body).map
      (fdom.instantiateLift vs :: ·)
  | _ + 1, _, _ => none

def structProjBodies (T : Name) (nP nF : Nat) (cty : Expr) : Option (Array Expr) :=
  match cty.stripPis nP with
  | some (_, r) => (structProjBodiesGo T (structProjPs nP).reverse nF 0 r).map List.toArray
  | none => none

/-! ## `mentionsAnyConst`: the positivity walk's question at k names -/

/-- Does any of the constants `names` occur in `e`?  A syntactic walk
(`fvar` annotations included; a `.proj` node names its structure), at a
list of names, so that the k-ary positivity walk does ONE traversal per
field domain and not one per member; the fold's `sorryAx` test
(`unresolvedConstsError`, `ConLeche/Kernel/CheckerBase.lean`) asks it
at one name. -/
def Expr.mentionsAnyConst (names : List Name) : Expr → Bool
  | .bvar _ | .sort _ | .lit _ => false
  | .const n _ => names.contains n
  | .fvar _ ty => ty.mentionsAnyConst names
  | .app f a => f.mentionsAnyConst names || a.mentionsAnyConst names
  | .lam ty b | .forallE ty b => ty.mentionsAnyConst names || b.mentionsAnyConst names
  | .letE ty v b =>
    ty.mentionsAnyConst names || v.mentionsAnyConst names || b.mentionsAnyConst names
  | .proj s _ e => names.contains s || e.mentionsAnyConst names

/-! ### `mentionsAnyConst`, memoized

The tree walk does not finish on a DAG-shared field type (task #215's
`tower_struct`: a depth-60 doubling tower in a structure field), so the
memoized walk is swapped in by `@[csimp]` (task #210 Part B), and the
pure definition stays what every proof consumes.  The memo is keyed by the node and dropped after
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
        | .lam ty body =>
          let (b₁, memo) := mentionsAnyGo names memo ty
          let (b₂, memo) := mentionsAnyGo names memo body
          (b₁ || b₂, memo)
        | .forallE ty body =>
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
  | lam ty body iht ihb =>
    intro memo hm
    rw [mentionsAnyGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      refine ⟨by simp [mentionsAnyConst, h1, h3], ?_⟩
      exact h4.insert (by simp [mentionsAnyConst, h1, h3])
  | forallE ty body iht ihb =>
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

end ConLeche

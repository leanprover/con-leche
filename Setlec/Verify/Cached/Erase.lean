import Setlec.Cached.ExprC
import Setlec.Kernel.ArenaWF
import Setlec.Verify.IExpr

/-!
# The cached-representation seam floor (task #163)

The erasure `eraseC : ExprC → Expr`, the field invariant `WFc`, and
the facts that replace the arena's `EStore.WF` + `denote_inj` for the
cached checker variant (see DESIGN.md, "Task #163 CACHED-LIVE P1"):

* `WFc e := ofExpr (eraseC e) = e` — every field of every node equals
  the smart constructor's recurrence on the erased term;
* `eraseC` is **injective on `WFc`** (`eraseC_inj`): the fields are
  functions of the structure, so a well-formed `ExprC` is uniquely
  determined by its erasure — `denote_inj` without a table;
* field exactness: on `WFc` nodes the `O(1)` readers `bvarB`/`fvarB`/
  `hasLP`/`hash` read exactly the spec functions `Expr.bvarBound`/
  `Expr.fvarRange`/`Expr.hasLevelParam`/`hashSpec` of the erasure, so
  every cutoff the cached operations take is the cutoff the spec takes;
* equality: `beqSpec` (the hash-checking descent) decides equality of
  the *equality normal form* `zeroC` exactly (`beqSpec_iff_zeroC`),
  whence soundness on all terms, the `EquivBEq`/`LawfulHashable`
  instances the `Std.HashMap` lemmas need, and completeness on the
  invariant (`beq_iff`);
* `toExpr_eq`: the memoized readback *is* the erasure — proved, so
  `toExpr` is not a trust point.

Everything here consumes only the *pure* definitions (`ofExpr` =
`ofExprSpec`, `beq` = `beqSpec`); the two `unsafe` accelerations in
`Setlec/Cached/ExprC.lean` are named trust points the proofs never
touch.
-/

namespace Setlec.Cached

open Setlec

namespace ExprC

/-! ## The field invariant is a theorem — and a trivial one

Before task #172 B3a the four derived data were *constructor
arguments*, so `WFc e := ofExpr (eraseC e) = e` was a real invariant:
a node could carry a field disagreeing with its recurrence, and the
whole tier's job was to show the checker never builds one.  Under
`@[computed_field]` there is no field to disagree — the fields are
functions of the node — so `WFc` holds of everything (`WFc_all`), the
erasure is the identity (`eraseC_id`), and the inversion lemmas below
are `rfl` plus that fact.

The names and signatures are kept so the tier reads unchanged; the
`WFc` arguments they still take are vestigial and are removed by the
batch's next stage. -/

/-- The erasure is the identity: there is one expression type.  (NOT a
`simp` lemma while the erasure still stands: the tier's statements are
written on `eraseC` and normalizing it away mid-proof desynchronizes
hypotheses from goals.  The erasure's deletion is its own stage.) -/
theorem eraseC_id : ∀ e : ExprC, eraseC e = e := by
  intro e
  induction e <;> simp_all [eraseC]

/-- …and so is the conversion. -/
theorem ofExpr_id : ∀ e : Expr, ofExpr e = e := by
  intro e
  induction e <;>
    simp_all [ofExpr, ofExprSpec, mkBVar, mkFVar, mkSort, mkConst, mkApp,
      mkLam, mkForallE, mkLetE, mkLit, mkProj]

/-- **The field invariant holds of every term.**  This is the whole
content of the computed-field migration on the proof side. -/
theorem WFc_all (e : ExprC) : WFc e := by
  show ofExpr (eraseC e) = e
  rw [eraseC_id, ofExpr_id]

theorem WFc.fvar_inv {idx : Nat} {n : Name} {ty : ExprC}
    (_hw : WFc (.fvar idx n ty)) :
    WFc ty ∧ Expr.fvar idx n ty = mkFVar idx n ty :=
  ⟨WFc_all ty, rfl⟩

theorem WFc.app_inv {f a : ExprC} (_hw : WFc (.app f a)) :
    WFc f ∧ WFc a ∧ Expr.app f a = mkApp f a :=
  ⟨WFc_all f, WFc_all a, rfl⟩

theorem WFc.lam_inv {n : Name} {ty b : ExprC} {m : BinderMeta}
    (_hw : WFc (.lam n ty b m)) :
    WFc ty ∧ WFc b ∧ Expr.lam n ty b m = mkLam n ty b m :=
  ⟨WFc_all ty, WFc_all b, rfl⟩

theorem WFc.forallE_inv {n : Name} {ty b : ExprC} {m : BinderMeta}
    (_hw : WFc (.forallE n ty b m)) :
    WFc ty ∧ WFc b ∧ Expr.forallE n ty b m = mkForallE n ty b m :=
  ⟨WFc_all ty, WFc_all b, rfl⟩

theorem WFc.letE_inv {n : Name} {ty v b : ExprC}
    (_hw : WFc (.letE n ty v b)) :
    WFc ty ∧ WFc v ∧ WFc b ∧ Expr.letE n ty v b = mkLetE n ty v b :=
  ⟨WFc_all ty, WFc_all v, WFc_all b, rfl⟩

theorem WFc.proj_inv {s : Name} {i : Nat} {e : ExprC}
    (_hw : WFc (.proj s i e)) :
    WFc e ∧ Expr.proj s i e = mkProj s i e :=
  ⟨WFc_all e, rfl⟩

/-! ## Field exactness (the reader form)

On `WFc` nodes the `O(1)` readers are exactly the spec functions of
the erasure — the same exactness the arena's `TWF.bvarBoundD_exact2` /
`fvarRangeD_exact2` / `ehasParamD_exact2` provide for the parallel
arrays, so the cutoff-consequence lemmas transpose verbatim. -/

/-- The `bvarB` field is `Expr.bvarBound` — the same recurrence, one
written as a computed field and one as an ordinary function. -/
theorem bvarB_eq : ∀ e : ExprC, e.bvarB = e.bvarBound := by
  intro e
  induction e <;> simp_all [Expr.bvarB, Expr.bvarBound]

/-- `bvarB` reads `Expr.bvarBound` of the erasure. -/
theorem bvarB_exact {e : ExprC} (_hw : WFc e) :
    e.bvarB = (eraseC e).bvarBound := by
  rw [eraseC_id]; exact bvarB_eq e

/-- Cutoff consequence: a bound at or below the cursor certifies
`looseBVarsBounded` of the erasure (the transposition of
`TWF.bvarBoundD_le2`). -/
theorem bvarB_le {e : ExprC} {d : Nat} (hw : WFc e) (hle : e.bvarB ≤ d) :
    (eraseC e).looseBVarsBounded d = true :=
  EStore.looseBVarsBounded_iff.mpr (bvarB_exact hw ▸ hle)

/-- The `fvarB` field is `Expr.fvarRange`. -/
theorem fvarB_eq : ∀ e : ExprC, e.fvarB = e.fvarRange := by
  intro e
  induction e <;> simp_all [Expr.fvarB, Expr.fvarRange]

/-- `fvarB` reads `Expr.fvarRange` of the erasure. -/
theorem fvarB_exact {e : ExprC} (_hw : WFc e) :
    e.fvarB = (eraseC e).fvarRange := by
  rw [eraseC_id]; exact fvarB_eq e

/-- Cutoff consequence: a range at or below the base certifies
`Expr.fvarsBelow` of the erasure — the predicate the abstraction
traversals consume (`abstractRange_eq_self`); the transposition of
`TWF.fvarRangeD_le`. -/
theorem fvarB_le {e : ExprC} {d : Nat} (hw : WFc e) (hle : e.fvarB ≤ d) :
    (eraseC e).fvarsBelow d :=
  EStore.fvarsBelow_iff.mpr (fvarB_exact hw ▸ hle)

/-! ### Has-level-param -/

/-- The node-level walk is the kernel's `Level.hasParam`. -/
theorem levelHasParam_eq : ∀ u : Level, levelHasParam u = u.hasParam := by
  intro u
  induction u <;> simp_all [levelHasParam, Level.hasParam]

/-- …and its list fold is `List.any`. -/
theorem levelsHaveParam_eq : ∀ us : List Level,
    levelsHaveParam us = us.any Level.hasParam := by
  intro us
  induction us with
  | nil => rfl
  | cons u us ih => simp [levelsHaveParam, List.any_cons, levelHasParam_eq, ih]

/-- The `hasLP` field is `Expr.hasLevelParam`. -/
theorem hasLP_eq : ∀ e : ExprC, e.hasLP = e.hasLevelParam := by
  intro e
  induction e <;>
    simp_all [Expr.hasLP, Expr.hasLevelParam, levelHasParam_eq,
      levelsHaveParam_eq]

/-- `hasLP` reads `Expr.hasLevelParam` of the erasure. -/
theorem hasLP_exact {e : ExprC} (_hw : WFc e) :
    e.hasLP = (eraseC e).hasLevelParam := by
  rw [eraseC_id]; exact hasLP_eq e

/-- Invisibility consequence: level instantiation is the identity on a
node whose flag is off (the `O(1)` shortcut every `instLevelParams`
traversal takes). -/
theorem hasLP_false {e : ExprC} {ks : List Name} {us : List Level}
    (hw : WFc e) (h : e.hasLP = false) :
    (eraseC e).instantiateLevelParams ks us = eraseC e :=
  Expr.instantiateLevelParams_eq_self (by rw [← hasLP_exact hw, h])

/-! ## Equality

The executed equality's specification is decidable equality (task #172
B3a): with the hash a *function* of the node there is nothing for the
old `beqSpec`/`zeroC` normal-form apparatus to say — it existed only to
characterize a descent that compared *stored* hashes, which could
disagree with the term.  `beq` is `decide (· = ·)`, so the `EquivBEq`
and `LawfulHashable` premises the `Std.HashMap` lemmas want are the
standard ones. -/

/-- Soundness of a decided equality, in the erasure form the memo
proofs consume. -/
theorem beq_sound {a b : ExprC} (h : (a == b) = true) :
    eraseC a = eraseC b :=
  congrArg eraseC (eq_of_beq h)

/-- `beq` in its unfolded form decides equality. -/
theorem beq_eq {a b : ExprC} (h : Expr.beq a b = true) : a = b :=
  of_decide_eq_true h

/-- …and is reflexive there. -/
@[simp] theorem beq_self (a : ExprC) : Expr.beq a a = true := by
  simp [Expr.beq]

/-- Equality is an equivalence — the `Std.HashMap` lemmas' first
premise (an instance, so every memo-preservation proof gets it for
free). -/
instance : EquivBEq ExprC where
  symm h := by rw [eq_of_beq h]; exact beq_self_eq_true _
  trans hab hbc := by rw [eq_of_beq hab]; exact hbc
  rfl := beq_self_eq_true _

/-- The `O(1)` `Hashable` instance (the computed field) is lawful for
it — the `Std.HashMap` lemmas' second premise. -/
instance : LawfulHashable ExprC where
  hash_eq _ _ h := by rw [eq_of_beq h]

/-- Decided equality **is** equality of the erasures.  (Before B3a the
`←` direction needed `WFc` on both sides — `eraseC_inj` — because
distinct field blocks could erase alike; the arguments are vestigial.) -/
theorem beq_iff {a b : ExprC} (_ha : WFc a) (_hb : WFc b) :
    (a == b) = true ↔ eraseC a = eraseC b := by
  rw [eraseC_id, eraseC_id, beq_iff_eq]

/-! ## The readback is the erasure

`toExprGo` is memoized on `ExprC` keys, so it is *not* a trust point:
the memo invariant "every value the map yields is the erasure of the
key it was looked up at" survives insertion because a hit's key is
`beq`-equal to the query and `beq`-equal terms have equal erasures
(`beq_sound`) — no `WFc` anywhere. -/

/-- The `toExpr` memo invariant. -/
def MemoErase (memo : Std.HashMap ExprC Expr) : Prop :=
  ∀ (k : ExprC) (v : Expr), memo[k]? = some v → v = eraseC k

theorem MemoErase.empty : MemoErase {} := by
  intro k v h
  simp at h

theorem MemoErase.insert {memo : Std.HashMap ExprC Expr} (hm : MemoErase memo)
    (e : ExprC) : MemoErase (memo.insert e (eraseC e)) := by
  intro k v hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    exact beq_sound hbeq
  · exact hm k v hk

/-- The memoized readback returns the erasure and preserves the memo
invariant. -/
theorem toExprGo_spec : ∀ (e : ExprC) {memo : Std.HashMap ExprC Expr},
    MemoErase memo →
    (toExprGo memo e).1 = eraseC e ∧ MemoErase (toExprGo memo e).2 := by
  intro e
  induction e with
  | bvar i =>
    intro memo hm
    rw [toExprGo.eq_def]
    split
    · rename_i x hx
      exact ⟨hm _ _ hx, hm⟩
    · exact ⟨rfl, hm.insert _⟩
  | sort u =>
    intro memo hm
    rw [toExprGo.eq_def]
    split
    · rename_i x hx
      exact ⟨hm _ _ hx, hm⟩
    · exact ⟨rfl, hm.insert _⟩
  | const n us =>
    intro memo hm
    rw [toExprGo.eq_def]
    split
    · rename_i x hx
      exact ⟨hm _ _ hx, hm⟩
    · exact ⟨rfl, hm.insert _⟩
  | lit l =>
    intro memo hm
    rw [toExprGo.eq_def]
    split
    · rename_i x hx
      exact ⟨hm _ _ hx, hm⟩
    · exact ⟨rfl, hm.insert _⟩
  | fvar idx n ty iht =>
    intro memo hm
    rw [toExprGo.eq_def]
    split
    · rename_i x hx
      exact ⟨hm _ _ hx, hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      rcases hp : toExprGo memo ty with ⟨t, mt⟩
      rw [hp] at h1 h2
      simp only [hp]
      subst h1
      exact ⟨rfl, h2.insert _⟩
  | proj s i sub ihe =>
    intro memo hm
    rw [toExprGo.eq_def]
    split
    · rename_i x hx
      exact ⟨hm _ _ hx, hm⟩
    · obtain ⟨h1, h2⟩ := ihe hm
      rcases hp : toExprGo memo sub with ⟨t, mt⟩
      rw [hp] at h1 h2
      simp only [hp]
      subst h1
      exact ⟨rfl, h2.insert _⟩
  | app f a ihf iha =>
    intro memo hm
    rw [toExprGo.eq_def]
    split
    · rename_i x hx
      exact ⟨hm _ _ hx, hm⟩
    · obtain ⟨hf1, hf2⟩ := ihf hm
      rcases hpf : toExprGo memo f with ⟨f', mf⟩
      rw [hpf] at hf1 hf2
      obtain ⟨ha1, ha2⟩ := iha hf2
      rcases hpa : toExprGo mf a with ⟨a', ma⟩
      rw [hpa] at ha1 ha2
      simp only [hpf, hpa]
      subst hf1
      subst ha1
      exact ⟨rfl, ha2.insert _⟩
  | lam n ty bd m iht ihb =>
    intro memo hm
    rw [toExprGo.eq_def]
    split
    · rename_i x hx
      exact ⟨hm _ _ hx, hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      rcases hp : toExprGo memo ty with ⟨t, mt⟩
      rw [hp] at h1 h2
      obtain ⟨h3, h4⟩ := ihb h2
      rcases hq : toExprGo mt bd with ⟨b', mb⟩
      rw [hq] at h3 h4
      simp only [hp, hq]
      subst h1
      subst h3
      exact ⟨rfl, h4.insert _⟩
  | forallE n ty bd m iht ihb =>
    intro memo hm
    rw [toExprGo.eq_def]
    split
    · rename_i x hx
      exact ⟨hm _ _ hx, hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      rcases hp : toExprGo memo ty with ⟨t, mt⟩
      rw [hp] at h1 h2
      obtain ⟨h3, h4⟩ := ihb h2
      rcases hq : toExprGo mt bd with ⟨b', mb⟩
      rw [hq] at h3 h4
      simp only [hp, hq]
      subst h1
      subst h3
      exact ⟨rfl, h4.insert _⟩
  | letE n ty v bd iht ihv ihb =>
    intro memo hm
    rw [toExprGo.eq_def]
    split
    · rename_i x hx
      exact ⟨hm _ _ hx, hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      rcases hp : toExprGo memo ty with ⟨t, mt⟩
      rw [hp] at h1 h2
      obtain ⟨h3, h4⟩ := ihv h2
      rcases hq : toExprGo mt v with ⟨v', mv⟩
      rw [hq] at h3 h4
      obtain ⟨h5, h6⟩ := ihb h4
      rcases hr : toExprGo mv bd with ⟨b', mb⟩
      rw [hr] at h5 h6
      simp only [hp, hq, hr]
      subst h1
      subst h3
      subst h5
      exact ⟨rfl, h6.insert _⟩

/-- **The readback is the erasure** — proved outright, so `toExpr` is
not a trust point. -/
theorem toExpr_eq (e : ExprC) : ExprC.toExpr e = eraseC e :=
  (toExprGo_spec e MemoErase.empty).1

end ExprC

end Setlec.Cached

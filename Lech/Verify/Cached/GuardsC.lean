import Lech.Cached.ParsedC
import Lech.Verify.Cached.OpsC
import Lech.Verify.EnvBound

/-!
# The cached representation's guard walks and the conversion boundary

Task #163, batch 4.  The pieces of the cached clone that sit *between*
the parse arena and the core:

* the fabrication leaf guard (`fvarLeaves`/`leafMem`/`leavesSubGo`/
  `leafGuard`) — the transposition of `leafGuard_spec'`
  (`Lech/Verify/IExprOps.lean`);
* the level-parameter definedness walk
  (`ExprC.allLevelParamsDefined`) — the transposition of
  `allLevelParamsDefinedI_spec`;
* the constant-resolution walk (`constsResolveFC`) — the transposition
  of `constsResolveFI_spec`;
* the arena→`ExprC` conversion (`ofStoreGo`/`ofStore`), the clone's
  counterpart of `EStore.readbackGo`: on a well-formed parse arena the
  conversion of a denoting index succeeds and yields a term whose
  erasure *is* the denotation.

Two structural differences from the arena twins are paid for here.

1. The clone's `fvarLeaves` walk carries a **`seen` set** (the arena's
   is a result memo), so the leaf *list* it returns is deduplicated and
   is **not** `Expr.fvarLeaves` of the erasure — only its *set of
   elements* is.  Since the only consumer (`leafMem`) is a membership
   test, a membership characterization is exactly what is needed, and
   `leafGuard_spec` still lands on `leafGuard_spec'`'s `Expr`-side
   right-hand side verbatim.

   Marking a node *before* descending into it is what makes the `seen`
   invariant ("a marked node's leaves are already in the accumulator")
   momentarily false for the node being processed and for its
   ancestors.  The proof closes that gap the way a DFS on an acyclic
   graph does: the invariant is relaxed by a *gray* predicate `G` on
   erasures ("…*or* the marked node is gray"), the call at `e` requires
   every gray erasure to be strictly bigger than `e` — which is
   what rules a hit at `e` itself out — and the call's post-condition
   pops `e` off `G` again, because by then `e`'s leaves *are* in
   the accumulator.  Acyclicity is free here: `ExprC` is an inductive
   *tree*, so the size side-condition is discharged by each
   constructor's own `sizeF` recurrence.

2. `ofStoreGo` has `emlt` guards on every child (they make the
   traversal's `(etier, epos)` measure decrease without an arena
   hypothesis).  On a `TWF` store the children of a denoting node are
   `emlt`-below it (`denoteT_some_inv`), so no guard ever fires — the
   same discharge `readbackGo_spec` performs.
-/

namespace Lech.Cached

open Lech

namespace ExprC

/-! ## Level-parameter definedness

`ExprC.allLevelParamsDefinedGo` is a plain `ExprC`-keyed memoized walk
with the `hasLP` cutoff; the memo invariant is the
erasure-function-of-key form, and the cutoff arm is discharged by
`hasLP_eq _` plus `Expr.allLevelParamsDefined_of_not_hasLevelParam`. -/

/-- The definedness walk's memo invariant. -/
def MemoLPDInv (ps : List Name) (memo : Std.HashMap ExprC Bool) : Prop :=
  ∀ (e : ExprC) (r : Bool), memo[e]? = some r →
    r = (Expr.allLevelParamsDefined ps e)

theorem MemoLPDInv.empty {ps : List Name} : MemoLPDInv ps {} := by
  intro e r h
  simp at h

theorem MemoLPDInv.insert {ps : List Name} {memo : Std.HashMap ExprC Bool}
    (hm : MemoLPDInv ps memo) {e : ExprC} {r : Bool}
    (heq : r = (Expr.allLevelParamsDefined ps e)) :
    MemoLPDInv ps (memo.insert e r) := by
  intro e' r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← beq_sound hbeq]
    exact heq
  · exact hm e' r' hk

/-- **The definedness walk agrees with `Expr.allLevelParamsDefined` on
the erasure.** -/
theorem allLevelParamsDefinedGo_spec {ps : List Name} :
    ∀ {e : ExprC},
    ∀ {memo : Std.HashMap ExprC Bool}, MemoLPDInv ps memo →
      (allLevelParamsDefinedGo ps memo e).1
          = (Expr.allLevelParamsDefined ps e) ∧
        MemoLPDInv ps (allLevelParamsDefinedGo ps memo e).2 := by
  intro e
  induction e with
  | bvar i =>
    intro memo hm
    rw [allLevelParamsDefinedGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(Expr.allLevelParamsDefined_of_not_hasLevelParam (params := ps)
        (by rw [← hasLP_eq _]; simp)).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · exact ⟨rfl, hm.insert rfl⟩
  | lit l =>
    intro memo hm
    rw [allLevelParamsDefinedGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(Expr.allLevelParamsDefined_of_not_hasLevelParam (params := ps)
        (by rw [← hasLP_eq _]; simp)).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · exact ⟨rfl, hm.insert rfl⟩
  | sort u =>
    intro memo hm
    rw [allLevelParamsDefinedGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(Expr.allLevelParamsDefined_of_not_hasLevelParam (params := ps)
        (by rw [← hasLP_eq _]; simpa using hcut)).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · exact ⟨rfl, hm.insert rfl⟩
  | const n us =>
    intro memo hm
    rw [allLevelParamsDefinedGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(Expr.allLevelParamsDefined_of_not_hasLevelParam (params := ps)
        (by rw [← hasLP_eq _]; simpa using hcut)).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · exact ⟨rfl, hm.insert rfl⟩
  | fvar idx n ty iht =>
    intro memo hm
    rw [allLevelParamsDefinedGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(Expr.allLevelParamsDefined_of_not_hasLevelParam (params := ps)
        (by rw [← hasLP_eq _]; simpa using hcut)).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · obtain ⟨h1, h2⟩ := iht hm
        rcases hp : allLevelParamsDefinedGo ps memo ty with ⟨rt, mt⟩
        rw [hp] at h1 h2
        simp only [hp]
        exact ⟨h1, h2.insert h1⟩
  | app f a ihf iha =>
    intro memo hm
    rw [allLevelParamsDefinedGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(Expr.allLevelParamsDefined_of_not_hasLevelParam (params := ps)
        (by rw [← hasLP_eq _]; simpa using hcut)).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · obtain ⟨h1, h2⟩ := ihf hm
        rcases hp : allLevelParamsDefinedGo ps memo f with ⟨rf, mf⟩
        rw [hp] at h1 h2
        simp only [hp]
        cases rf with
        | true =>
          obtain ⟨h3, h4⟩ := iha h2
          rcases hq : allLevelParamsDefinedGo ps mf a with ⟨ra, ma⟩
          rw [hq] at h3 h4
          have hres : ra
              = (Expr.allLevelParamsDefined ps (.app f a)) := by
            show ra = (Expr.app f a).allLevelParamsDefined ps
            rw [Expr.allLevelParamsDefined, ← h1, ← h3, Bool.true_and]
          exact ⟨hres, h4.insert hres⟩
        | false =>
          have hres : false
              = (Expr.allLevelParamsDefined ps (.app f a)) := by
            show false
              = (Expr.app f a).allLevelParamsDefined ps
            rw [Expr.allLevelParamsDefined, ← h1, Bool.false_and]
          exact ⟨hres, h2.insert hres⟩
  | lam n ty bd m iht ihb =>
    intro memo hm
    rw [allLevelParamsDefinedGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(Expr.allLevelParamsDefined_of_not_hasLevelParam (params := ps)
        (by rw [← hasLP_eq _]; simpa using hcut)).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · obtain ⟨h1, h2⟩ := iht hm
        rcases hp : allLevelParamsDefinedGo ps memo ty with ⟨rt, mt⟩
        rw [hp] at h1 h2
        simp only [hp]
        cases rt with
        | true =>
          obtain ⟨h3, h4⟩ := ihb h2
          rcases hq : allLevelParamsDefinedGo ps mt bd with ⟨rb, mb⟩
          rw [hq] at h3 h4
          have hres : (rb && m.pw.paramsDefined ps)
              = (Expr.allLevelParamsDefined ps (.lam n ty bd m)) := by
            show _ = (Expr.lam n ty bd m
              ).allLevelParamsDefined ps
            rw [Expr.allLevelParamsDefined, ← h1, ← h3, Bool.true_and]
          exact ⟨hres, h4.insert hres⟩
        | false =>
          have hres : false
              = (Expr.allLevelParamsDefined ps (.lam n ty bd m)) := by
            show false = (Expr.lam n ty bd m
              ).allLevelParamsDefined ps
            rw [Expr.allLevelParamsDefined, ← h1]
            simp
          exact ⟨hres, h2.insert hres⟩
  | forallE n ty bd m iht ihb =>
    intro memo hm
    rw [allLevelParamsDefinedGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(Expr.allLevelParamsDefined_of_not_hasLevelParam (params := ps)
        (by rw [← hasLP_eq _]; simpa using hcut)).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · obtain ⟨h1, h2⟩ := iht hm
        rcases hp : allLevelParamsDefinedGo ps memo ty with ⟨rt, mt⟩
        rw [hp] at h1 h2
        simp only [hp]
        cases rt with
        | true =>
          obtain ⟨h3, h4⟩ := ihb h2
          rcases hq : allLevelParamsDefinedGo ps mt bd with ⟨rb, mb⟩
          rw [hq] at h3 h4
          have hres : (rb && m.pw.paramsDefined ps)
              = (Expr.allLevelParamsDefined ps (.forallE n ty bd m)) := by
            show _ = (Expr.forallE n ty bd m
              ).allLevelParamsDefined ps
            rw [Expr.allLevelParamsDefined, ← h1, ← h3, Bool.true_and]
          exact ⟨hres, h4.insert hres⟩
        | false =>
          have hres : false
              = (Expr.allLevelParamsDefined ps (.forallE n ty bd m)) := by
            show false = (Expr.forallE n ty bd m
              ).allLevelParamsDefined ps
            rw [Expr.allLevelParamsDefined, ← h1]
            simp
          exact ⟨hres, h2.insert hres⟩
  | letE n ty val bd iht ihv ihb =>
    intro memo hm
    rw [allLevelParamsDefinedGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(Expr.allLevelParamsDefined_of_not_hasLevelParam (params := ps)
        (by rw [← hasLP_eq _]; simpa using hcut)).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · have herase : (Expr.letE n ty val bd)
            = Expr.letE n ty val bd := rfl
        obtain ⟨h1, h2⟩ := iht hm
        rcases hp : allLevelParamsDefinedGo ps memo ty with ⟨rt, mt⟩
        rw [hp] at h1 h2
        simp only [hp]
        cases rt with
        | false =>
          have hres : false
              = (Expr.allLevelParamsDefined ps (.letE n ty val bd)) := by
            rw [herase, Expr.allLevelParamsDefined, ← h1]
            simp
          exact ⟨hres, h2.insert hres⟩
        | true =>
          obtain ⟨h3, h4⟩ := ihv h2
          rcases hq : allLevelParamsDefinedGo ps mt val with ⟨rv, mv⟩
          rw [hq] at h3 h4
          cases rv with
          | false =>
            have hres : false
                = (Expr.allLevelParamsDefined ps (.letE n ty val bd)) := by
              rw [herase, Expr.allLevelParamsDefined, ← h1, ← h3]
              simp
            exact ⟨hres, h4.insert hres⟩
          | true =>
            obtain ⟨h5, h6⟩ := ihb h4
            rcases hr : allLevelParamsDefinedGo ps mv bd with ⟨rb, mb⟩
            rw [hr] at h5 h6
            have hres : rb
                = (Expr.allLevelParamsDefined ps (.letE n ty val bd)) := by
              rw [herase, Expr.allLevelParamsDefined, ← h1, ← h3, ← h5]
              simp
            exact ⟨hres, h6.insert hres⟩
  | proj s i sub ihe =>
    intro memo hm
    rw [allLevelParamsDefinedGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(Expr.allLevelParamsDefined_of_not_hasLevelParam (params := ps)
        (by rw [← hasLP_eq _]; simpa using hcut)).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · obtain ⟨h1, h2⟩ := ihe hm
        rcases hp : allLevelParamsDefinedGo ps memo sub with ⟨rs, ms⟩
        rw [hp] at h1 h2
        simp only [hp]
        exact ⟨h1, h2.insert h1⟩

/-- **`ExprC.allLevelParamsDefined` is `Expr.allLevelParamsDefined` of
the erasure.** -/
theorem allLevelParamsDefined_spec {ps : List Name} {e : ExprC} :
    ExprC.allLevelParamsDefined ps e = (Expr.allLevelParamsDefined ps e) :=
  (allLevelParamsDefinedGo_spec MemoLPDInv.empty).1

/-! ## The fabrication leaf guard

`Expr.fvarLeaves` recurses into `fvar` annotations, so it is
well-founded on `sizeF` rather than structural: its per-constructor
equations have to be named before anything can rewrite with them. -/

private theorem fvarLeaves_bvar (i : Nat) :
    (Expr.bvar i).fvarLeaves = [] := by simp [Expr.fvarLeaves]

private theorem fvarLeaves_sort (u : Level) :
    (Expr.sort u).fvarLeaves = [] := by simp [Expr.fvarLeaves]

private theorem fvarLeaves_const (n : Name) (us : List Level) :
    (Expr.const n us).fvarLeaves = [] := by simp [Expr.fvarLeaves]

private theorem fvarLeaves_lit (l : Literal) :
    (Expr.lit l).fvarLeaves = [] := by simp [Expr.fvarLeaves]

private theorem fvarLeaves_fvar (idx : Nat) (n : Name) (ty : Expr) :
    (Expr.fvar idx n ty).fvarLeaves = (idx, n, ty) :: ty.fvarLeaves := by
  rw [Expr.fvarLeaves]

private theorem fvarLeaves_app (f a : Expr) :
    (Expr.app f a).fvarLeaves = f.fvarLeaves ++ a.fvarLeaves := by
  rw [Expr.fvarLeaves]

private theorem fvarLeaves_lam (n : Name) (ty b : Expr) (m : BinderMeta) :
    (Expr.lam n ty b m).fvarLeaves = ty.fvarLeaves ++ b.fvarLeaves := by
  rw [Expr.fvarLeaves]

private theorem fvarLeaves_forallE (n : Name) (ty b : Expr) (m : BinderMeta) :
    (Expr.forallE n ty b m).fvarLeaves = ty.fvarLeaves ++ b.fvarLeaves := by
  rw [Expr.fvarLeaves]

private theorem fvarLeaves_letE (n : Name) (ty v b : Expr) :
    (Expr.letE n ty v b).fvarLeaves
      = ty.fvarLeaves ++ v.fvarLeaves ++ b.fvarLeaves := by
  rw [Expr.fvarLeaves]

private theorem fvarLeaves_proj (s : Name) (i : Nat) (e : Expr) :
    (Expr.proj s i e).fvarLeaves = e.fvarLeaves := by rw [Expr.fvarLeaves]

/-- The clone's `fvarB == 0` shortcut on the leaf walks: a node whose
cached fvar range is zero has no `fvar` node outside annotations at
all, hence no reachable leaf (the counterpart of
`fvarLeaves_eq_nil_of_not_hasFvar` at the *range* cutoff). -/
private theorem fvarLeaves_nil_of_fvarsBelow_zero : ∀ (e : Expr),
    Expr.fvarsBelow 0 e → e.fvarLeaves = [] := by
  intro e
  induction e <;> intro hb <;>
    simp_all [Expr.fvarsBelow, fvarLeaves_bvar, fvarLeaves_sort,
      fvarLeaves_const, fvarLeaves_lit, fvarLeaves_app,
      fvarLeaves_lam, fvarLeaves_forallE, fvarLeaves_letE, fvarLeaves_proj]

/-- Erasure of a cached leaf list (the counterpart of the arena's
`leavesDen`; the annotation component goes through `eraseC`). -/
def leavesEr (xs : List (Nat × Name × ExprC)) : List (Nat × Name × Expr) :=
  xs.map fun l => (l.1, l.2.1, l.2.2)

@[simp] theorem leavesEr_nil : leavesEr [] = [] := rfl

@[simp] theorem leavesEr_cons (idx : Nat) (n : Name) (ty : ExprC)
    (xs : List (Nat × Name × ExprC)) :
    leavesEr ((idx, n, ty) :: xs) = (idx, n, ty) :: leavesEr xs := rfl

/-! ### The `seen`-set walk

`fvarLeavesGo` marks a node **before** descending into it, so the
obvious invariant ("a marked node's leaves are already in the
accumulator") is false for the node currently being processed and for
its ancestors.  The invariant is therefore relaxed by a *gray*
predicate `G` on erasures, and the call at `e` requires every gray
erasure to be strictly bigger than `e` — which is what rules a
hit at `e` itself out.  Descending pushes `e` into `G`; the
call's post-condition pops it again, because by then `e`'s leaves *are*
in the accumulator.  `ExprC` is an inductive tree, so the size
condition is discharged by the constructor's own `sizeF`
recurrence. -/

/-- The leaf walk's `seen`-set invariant at a gray predicate `G`. -/
def SeenInv (G : Expr → Prop) (acc : List (Nat × Name × ExprC))
    (seen : Std.HashMap ExprC Unit) : Prop :=
  ∀ (k : ExprC) (u : Unit), seen[k]? = some u →
    (∀ l ∈ (Expr.fvarLeaves k), l ∈ leavesEr acc) ∨ G k

theorem SeenInv.empty {G : Expr → Prop}
    {acc : List (Nat × Name × ExprC)} : SeenInv G acc {} := by
  intro k u h
  simp at h

/-- Weakening: a bigger accumulator and a bigger gray predicate keep
the invariant. -/
theorem SeenInv.mono {G G' : Expr → Prop} {acc acc' : List (Nat × Name × ExprC)}
    {seen : Std.HashMap ExprC Unit} (h : SeenInv G acc seen)
    (hacc : ∀ l, l ∈ leavesEr acc → l ∈ leavesEr acc')
    (hG : ∀ y, G y → G' y) : SeenInv G' acc' seen := by
  intro k u hk
  rcases h k u hk with hsub | hgray
  · exact Or.inl fun l hl => hacc l (hsub l hl)
  · exact Or.inr (hG _ hgray)

/-- Marking the node about to be descended into: it joins the gray
predicate. -/
theorem SeenInv.insertGray {G : Expr → Prop}
    {acc : List (Nat × Name × ExprC)} {seen : Std.HashMap ExprC Unit}
    (h : SeenInv G acc seen) (e : ExprC) :
    SeenInv (fun y => G y ∨ y = e) acc (seen.insert e ()) := by
  intro k u hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    exact Or.inr (Or.inr (beq_sound hbeq).symm)
  · rcases h k u hk with hsub | hgray
    · exact Or.inl hsub
    · exact Or.inr (Or.inl hgray)

/-- …and, once the descent is finished and the node's leaves are in the
accumulator, it leaves it again. -/
theorem SeenInv.dropGray {G : Expr → Prop}
    {acc : List (Nat × Name × ExprC)} {seen : Std.HashMap ExprC Unit}
    {e : ExprC} (h : SeenInv (fun y => G y ∨ y = e) acc seen)
    (he : ∀ l ∈ (Expr.fvarLeaves e), l ∈ leavesEr acc) :
    SeenInv G acc seen := by
  intro k u hk
  rcases h k u hk with hsub | hgray
  · exact Or.inl hsub
  · rcases hgray with hg | heq
    · exact Or.inr hg
    · exact Or.inl (by rw [heq]; exact he)

/-- **The leaf walk accumulates exactly the erasure's leaves** (as a
*set*: the `seen` dedup makes the list itself smaller than
`Expr.fvarLeaves`), keeps every annotation field-correct, and restores
the `seen` invariant at the caller's gray predicate. -/
theorem fvarLeavesGo_spec : ∀ {e : ExprC},
    ∀ {G : Expr → Prop} {acc : List (Nat × Name × ExprC)}
      {seen : Std.HashMap ExprC Unit},
      SeenInv G acc seen →
      (∀ y, G y → e.sizeF < y.sizeF) →
      (∀ l, l ∈ leavesEr (fvarLeavesGo acc seen e).1 ↔
          l ∈ leavesEr acc ∨ l ∈ (Expr.fvarLeaves e)) ∧
        SeenInv G (fvarLeavesGo acc seen e).1 (fvarLeavesGo acc seen e).2 := by
  intro e
  induction e with
  | bvar i =>
    intro G acc seen hseen hG
    rw [fvarLeavesGo.eq_def]
    have hnil : (Expr.fvarLeaves (Expr.bvar i)) = [] :=
      fvarLeaves_bvar i
    split
    · exact ⟨by simp [hnil], hseen⟩
    · split
      · rename_i u hhit
        exact ⟨by simp [hnil], hseen⟩
      · exact ⟨by simp [hnil],
          (hseen.insertGray _).dropGray (by simp [hnil])⟩
  | sort u =>
    intro G acc seen hseen hG
    rw [fvarLeavesGo.eq_def]
    have hnil : (Expr.fvarLeaves (Expr.sort u)) = [] :=
      fvarLeaves_sort u
    split
    · exact ⟨by simp [hnil], hseen⟩
    · split
      · rename_i v hhit
        exact ⟨by simp [hnil], hseen⟩
      · exact ⟨by simp [hnil],
          (hseen.insertGray _).dropGray (by simp [hnil])⟩
  | const n us =>
    intro G acc seen hseen hG
    rw [fvarLeavesGo.eq_def]
    have hnil : (Expr.fvarLeaves (Expr.const n us)) = [] :=
      fvarLeaves_const n us
    split
    · exact ⟨by simp [hnil], hseen⟩
    · split
      · rename_i v hhit
        exact ⟨by simp [hnil], hseen⟩
      · exact ⟨by simp [hnil],
          (hseen.insertGray _).dropGray (by simp [hnil])⟩
  | lit l =>
    intro G acc seen hseen hG
    rw [fvarLeavesGo.eq_def]
    have hnil : (Expr.fvarLeaves (Expr.lit l)) = [] :=
      fvarLeaves_lit l
    split
    · exact ⟨by simp [hnil], hseen⟩
    · split
      · rename_i v hhit
        exact ⟨by simp [hnil], hseen⟩
      · exact ⟨by simp [hnil],
          (hseen.insertGray _).dropGray (by simp [hnil])⟩
  | fvar idx n ty iht =>
    intro G acc seen hseen hG
    have herase : (Expr.fvar idx n ty)
        = Expr.fvar idx n ty := rfl
    have hlv : (Expr.fvarLeaves (Expr.fvar idx n ty))
        = (idx, n, ty) :: (Expr.fvarLeaves ty) := by
      rw [herase, fvarLeaves_fvar]
    rw [fvarLeavesGo.eq_def]
    split
    · rename_i hcut
      have : (Expr.fvarLeaves (Expr.fvar idx n ty)) = [] :=
        fvarLeaves_nil_of_fvarsBelow_zero _
          (fvarB_le (Nat.le_of_eq (by simpa using hcut)))
      exact ⟨by simp [this], hseen⟩
    · split
      · rename_i v hhit
        rcases hseen _ _ hhit with hsub | hgray
        · exact ⟨fun l => ⟨Or.inl, fun h => h.elim id (hsub l)⟩, hseen⟩
        · exact absurd (hG _ hgray) (Nat.lt_irrefl _)
      · dsimp only
        have hGty : ∀ y, (G y ∨ y = (Expr.fvar idx n ty)) →
            ty.sizeF < y.sizeF := by
          intro y hy
          have hs : (Expr.fvar idx n ty).sizeF
              = ty.sizeF + 1 := by rw [herase]; rfl
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h2, h3⟩ := iht
          ((hseen.insertGray _).mono
            (fun l h => by rw [leavesEr_cons]; exact List.mem_cons_of_mem _ h)
            (fun _ h => h))
          hGty
        rcases hp : fvarLeavesGo ((idx, n, ty) :: acc) (seen.insert _ ()) ty
          with ⟨acc1, seen1⟩
        rw [hp] at h2 h3
        have hmem : ∀ l, l ∈ leavesEr acc1 ↔
            l ∈ leavesEr acc ∨
              l ∈ (Expr.fvarLeaves (Expr.fvar idx n ty)) := by
          intro l
          rw [h2, hlv]
          simp only [leavesEr_cons, List.mem_cons]
          grind
        exact ⟨hmem, h3.dropGray (fun l hl => (hmem l).mpr (Or.inr hl))⟩
  | app f a ihf iha =>
    intro G acc seen hseen hG
    have herase : (Expr.app f a)
        = Expr.app f a := rfl
    have hlv : (Expr.fvarLeaves (Expr.app f a))
        = (Expr.fvarLeaves f) ++ (Expr.fvarLeaves a) := by
      rw [herase, fvarLeaves_app]
    have hsz : (Expr.app f a).sizeF
        = f.sizeF + a.sizeF + 1 := by rw [herase]; rfl
    rw [fvarLeavesGo.eq_def]
    split
    · rename_i hcut
      have : (Expr.fvarLeaves (Expr.app f a)) = [] :=
        fvarLeaves_nil_of_fvarsBelow_zero _
          (fvarB_le (Nat.le_of_eq (by simpa using hcut)))
      exact ⟨by simp [this], hseen⟩
    · split
      · rename_i v hhit
        rcases hseen _ _ hhit with hsub | hgray
        · exact ⟨fun l => ⟨Or.inl, fun h => h.elim id (hsub l)⟩, hseen⟩
        · exact absurd (hG _ hgray) (Nat.lt_irrefl _)
      · dsimp only
        have hGf : ∀ y, (G y ∨ y = (Expr.app f a)) →
            f.sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h2, h3⟩ := ihf (hseen.insertGray _) hGf
        rcases hp : fvarLeavesGo acc (seen.insert _ ()) f with ⟨acc1, seen1⟩
        rw [hp] at h2 h3
        have hGa : ∀ y, (G y ∨ y = (Expr.app f a)) →
            a.sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h5, h6⟩ := iha h3 hGa
        rcases hq : fvarLeavesGo acc1 seen1 a with ⟨acc2, seen2⟩
        rw [hq] at h5 h6
        have hmem : ∀ l, l ∈ leavesEr acc2 ↔
            l ∈ leavesEr acc ∨
              l ∈ (Expr.fvarLeaves (Expr.app f a)) := by
          intro l
          rw [h5, h2, hlv, List.mem_append]
          grind
        exact ⟨hmem, h6.dropGray (fun l hl => (hmem l).mpr (Or.inr hl))⟩
  | lam n ty bd m iht ihb =>
    intro G acc seen hseen hG
    have herase : (Expr.lam n ty bd m)
        = Expr.lam n ty bd m := rfl
    have hlv : (Expr.fvarLeaves (Expr.lam n ty bd m))
        = (Expr.fvarLeaves ty) ++ (Expr.fvarLeaves bd) := by
      rw [herase, fvarLeaves_lam]
    have hsz : (Expr.lam n ty bd m).sizeF
        = ty.sizeF + bd.sizeF + 1 := by rw [herase]; rfl
    rw [fvarLeavesGo.eq_def]
    split
    · rename_i hcut
      have : (Expr.fvarLeaves (Expr.lam n ty bd m)) = [] :=
        fvarLeaves_nil_of_fvarsBelow_zero _
          (fvarB_le (Nat.le_of_eq (by simpa using hcut)))
      exact ⟨by simp [this], hseen⟩
    · split
      · rename_i v hhit
        rcases hseen _ _ hhit with hsub | hgray
        · exact ⟨fun l => ⟨Or.inl, fun h => h.elim id (hsub l)⟩, hseen⟩
        · exact absurd (hG _ hgray) (Nat.lt_irrefl _)
      · dsimp only
        have hGt : ∀ y, (G y ∨ y = (Expr.lam n ty bd m)) →
            ty.sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h2, h3⟩ := iht (hseen.insertGray _) hGt
        rcases hp : fvarLeavesGo acc (seen.insert _ ()) ty with ⟨acc1, seen1⟩
        rw [hp] at h2 h3
        have hGb : ∀ y, (G y ∨ y = (Expr.lam n ty bd m)) →
            bd.sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h5, h6⟩ := ihb h3 hGb
        rcases hq : fvarLeavesGo acc1 seen1 bd with ⟨acc2, seen2⟩
        rw [hq] at h5 h6
        have hmem : ∀ l, l ∈ leavesEr acc2 ↔
            l ∈ leavesEr acc ∨
              l ∈ (Expr.fvarLeaves (Expr.lam n ty bd m)) := by
          intro l
          rw [h5, h2, hlv, List.mem_append]
          grind
        exact ⟨hmem, h6.dropGray (fun l hl => (hmem l).mpr (Or.inr hl))⟩
  | forallE n ty bd m iht ihb =>
    intro G acc seen hseen hG
    have herase : (Expr.forallE n ty bd m)
        = Expr.forallE n ty bd m := rfl
    have hlv : (Expr.fvarLeaves (Expr.forallE n ty bd m))
        = (Expr.fvarLeaves ty) ++ (Expr.fvarLeaves bd) := by
      rw [herase, fvarLeaves_forallE]
    have hsz : (Expr.forallE n ty bd m).sizeF
        = ty.sizeF + bd.sizeF + 1 := by rw [herase]; rfl
    rw [fvarLeavesGo.eq_def]
    split
    · rename_i hcut
      have : (Expr.fvarLeaves (Expr.forallE n ty bd m)) = [] :=
        fvarLeaves_nil_of_fvarsBelow_zero _
          (fvarB_le (Nat.le_of_eq (by simpa using hcut)))
      exact ⟨by simp [this], hseen⟩
    · split
      · rename_i v hhit
        rcases hseen _ _ hhit with hsub | hgray
        · exact ⟨fun l => ⟨Or.inl, fun h => h.elim id (hsub l)⟩, hseen⟩
        · exact absurd (hG _ hgray) (Nat.lt_irrefl _)
      · dsimp only
        have hGt : ∀ y,
            (G y ∨ y = (Expr.forallE n ty bd m)) →
            ty.sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h2, h3⟩ := iht (hseen.insertGray _) hGt
        rcases hp : fvarLeavesGo acc (seen.insert _ ()) ty with ⟨acc1, seen1⟩
        rw [hp] at h2 h3
        have hGb : ∀ y,
            (G y ∨ y = (Expr.forallE n ty bd m)) →
            bd.sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h5, h6⟩ := ihb h3 hGb
        rcases hq : fvarLeavesGo acc1 seen1 bd with ⟨acc2, seen2⟩
        rw [hq] at h5 h6
        have hmem : ∀ l, l ∈ leavesEr acc2 ↔
            l ∈ leavesEr acc ∨
              l ∈ (Expr.fvarLeaves (Expr.forallE n ty bd m)) := by
          intro l
          rw [h5, h2, hlv, List.mem_append]
          grind
        exact ⟨hmem, h6.dropGray (fun l hl => (hmem l).mpr (Or.inr hl))⟩
  | letE n ty val bd iht ihv ihb =>
    intro G acc seen hseen hG
    have herase : (Expr.letE n ty val bd)
        = Expr.letE n ty val bd := rfl
    have hlv : (Expr.fvarLeaves (Expr.letE n ty val bd))
        = (Expr.fvarLeaves ty) ++ (Expr.fvarLeaves val)
            ++ (Expr.fvarLeaves bd) := by
      rw [herase, fvarLeaves_letE]
    have hsz : (Expr.letE n ty val bd).sizeF
        = ty.sizeF + val.sizeF + bd.sizeF + 1 := by
      rw [herase]; rfl
    rw [fvarLeavesGo.eq_def]
    split
    · rename_i hcut
      have : (Expr.fvarLeaves (Expr.letE n ty val bd)) = [] :=
        fvarLeaves_nil_of_fvarsBelow_zero _
          (fvarB_le (Nat.le_of_eq (by simpa using hcut)))
      exact ⟨by simp [this], hseen⟩
    · split
      · rename_i v hhit
        rcases hseen _ _ hhit with hsub | hgray
        · exact ⟨fun l => ⟨Or.inl, fun h => h.elim id (hsub l)⟩, hseen⟩
        · exact absurd (hG _ hgray) (Nat.lt_irrefl _)
      · dsimp only
        have hGt : ∀ y,
            (G y ∨ y = (Expr.letE n ty val bd)) →
            ty.sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h2, h3⟩ := iht (hseen.insertGray _) hGt
        rcases hp : fvarLeavesGo acc (seen.insert _ ()) ty with ⟨acc1, seen1⟩
        rw [hp] at h2 h3
        have hGv : ∀ y,
            (G y ∨ y = (Expr.letE n ty val bd)) →
            val.sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h5, h6⟩ := ihv h3 hGv
        rcases hq : fvarLeavesGo acc1 seen1 val with ⟨acc2, seen2⟩
        rw [hq] at h5 h6
        have hGb : ∀ y,
            (G y ∨ y = (Expr.letE n ty val bd)) →
            bd.sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h8, h9⟩ := ihb h6 hGb
        rcases hr : fvarLeavesGo acc2 seen2 bd with ⟨acc3, seen3⟩
        rw [hr] at h8 h9
        have hmem : ∀ l, l ∈ leavesEr acc3 ↔
            l ∈ leavesEr acc ∨
              l ∈ (Expr.fvarLeaves (Expr.letE n ty val bd)) := by
          intro l
          rw [h8, h5, h2, hlv, List.mem_append, List.mem_append]
          grind
        exact ⟨hmem, h9.dropGray (fun l hl => (hmem l).mpr (Or.inr hl))⟩
  | proj s i sub ihe =>
    intro G acc seen hseen hG
    have herase : (Expr.proj s i sub)
        = Expr.proj s i sub := rfl
    have hlv : (Expr.fvarLeaves (Expr.proj s i sub))
        = (Expr.fvarLeaves sub) := by rw [herase, fvarLeaves_proj]
    have hsz : (Expr.proj s i sub).sizeF
        = sub.sizeF + 1 := by rw [herase]; rfl
    rw [fvarLeavesGo.eq_def]
    split
    · rename_i hcut
      have : (Expr.fvarLeaves (Expr.proj s i sub)) = [] :=
        fvarLeaves_nil_of_fvarsBelow_zero _
          (fvarB_le (Nat.le_of_eq (by simpa using hcut)))
      exact ⟨by simp [this], hseen⟩
    · split
      · rename_i v hhit
        rcases hseen _ _ hhit with hsub | hgray
        · exact ⟨fun l => ⟨Or.inl, fun h => h.elim id (hsub l)⟩, hseen⟩
        · exact absurd (hG _ hgray) (Nat.lt_irrefl _)
      · dsimp only
        have hGs : ∀ y, (G y ∨ y = (Expr.proj s i sub)) →
            sub.sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h2, h3⟩ := ihe (hseen.insertGray _) hGs
        rcases hp : fvarLeavesGo acc (seen.insert _ ()) sub with ⟨acc1, seen1⟩
        rw [hp] at h2 h3
        have hmem : ∀ l, l ∈ leavesEr acc1 ↔
            l ∈ leavesEr acc ∨
              l ∈ (Expr.fvarLeaves (Expr.proj s i sub)) := by
          intro l
          rw [h2, hlv]
        exact ⟨hmem, h3.dropGray (fun l hl => (hmem l).mpr (Or.inr hl))⟩

/-! ### The base leaf list

`leafMem` compares annotations with `ExprC`'s `==`, so on a
field-correct base list it decides `Expr`-level membership.  What the
subset walk needs of the base is exactly this pair of facts. -/

/-- A cached base leaf list is a faithful stand-in for an `Expr`-side
one: field-correct annotations, and the same *set* of erased leaves. -/
def LeafBase (bl : List (Nat × Name × ExprC))
    (B' : List (Nat × Name × Expr)) : Prop :=
  ∀ l, l ∈ leavesEr bl ↔ l ∈ B'

/-- `leafMem` decides membership in the erased list. -/
theorem leafMem_iff : ∀ {bl : List (Nat × Name × ExprC)},
    ∀ {idx : Nat} {nm : Name} {ty : ExprC},
      (leafMem bl idx nm ty = true ↔ (idx, nm, ty) ∈ leavesEr bl) := by
  intro bl
  induction bl with
  | nil => intro idx nm ty; simp [leafMem]
  | cons p rest ih =>
    obtain ⟨i, n, t⟩ := p
    intro idx nm ty
    rw [show leafMem ((i, n, t) :: rest) idx nm ty
        = ((i == idx && n == nm && (t == ty)) || leafMem rest idx nm ty)
      from rfl]
    rw [leavesEr_cons, List.mem_cons, Bool.or_eq_true, ih,
      Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq,
      beq_iff (a := t)]
    simp only [Prod.mk.injEq]
    grind

/-- …hence agrees with the `Expr`-side `contains` on a `LeafBase`. -/
theorem leafMem_spec {bl : List (Nat × Name × ExprC)}
    {B' : List (Nat × Name × Expr)} (h : LeafBase bl B')
    {idx : Nat} {nm : Name} {ty : ExprC} :
    leafMem bl idx nm ty = B'.contains (idx, nm, ty) := by
  rw [Bool.eq_iff_iff, List.contains_eq_mem, decide_eq_true_iff,
    leafMem_iff, h]

/-- The base list built by the leaf walk *is* a `LeafBase` for the
erasure's leaves. -/
theorem fvarLeaves_leafBase {base : ExprC} :
    LeafBase (fvarLeaves base) (Expr.fvarLeaves base) := by
  obtain ⟨h2, -⟩ := fvarLeavesGo_spec (e := base)
    (G := fun _ => False) (acc := []) (seen := {})
    SeenInv.empty (by intro y hy; exact hy.elim)
  intro l
  simp only [ExprC.fvarLeaves, h2]
  simp

/-! ### The subset walk -/

/-- The subset walk's memo invariant. -/
def MemoSubInv (B' : List (Nat × Name × Expr))
    (memo : Std.HashMap ExprC Bool) : Prop :=
  ∀ (e : ExprC) (r : Bool), memo[e]? = some r →
    r = ((Expr.fvarLeaves e).all fun l => B'.contains l)

theorem MemoSubInv.empty {B' : List (Nat × Name × Expr)} :
    MemoSubInv B' {} := by
  intro e r h
  simp at h

theorem MemoSubInv.insert {B' : List (Nat × Name × Expr)}
    {memo : Std.HashMap ExprC Bool} (hm : MemoSubInv B' memo) {e : ExprC}
    {r : Bool}
    (heq : r = ((Expr.fvarLeaves e).all fun l => B'.contains l)) :
    MemoSubInv B' (memo.insert e r) := by
  intro e' r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← beq_sound hbeq]
    exact heq
  · exact hm e' r' hk

/-- **The subset walk decides the `Expr`-level leaf-subset boolean.** -/
theorem leavesSubGo_spec {bl : List (Nat × Name × ExprC)}
    {B' : List (Nat × Name × Expr)} (hbl : LeafBase bl B') :
    ∀ {e : ExprC},
    ∀ {memo : Std.HashMap ExprC Bool}, MemoSubInv B' memo →
      (leavesSubGo bl memo e).1
          = ((Expr.fvarLeaves e).all fun l => B'.contains l) ∧
        MemoSubInv B' (leavesSubGo bl memo e).2 := by
  intro e
  induction e with
  | bvar i =>
    intro memo hm
    have hnil : (Expr.fvarLeaves (Expr.bvar i)) = [] := fvarLeaves_bvar i
    have hres : true = ((Expr.fvarLeaves (Expr.bvar i)).all
        fun l => B'.contains l) := by rw [hnil]; rfl
    rw [leavesSubGo.eq_def]
    split
    · exact ⟨hres, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · exact ⟨hres, hm.insert hres⟩
  | sort u =>
    intro memo hm
    have hnil : (Expr.fvarLeaves (Expr.sort u)) = [] := fvarLeaves_sort u
    have hres : true = ((Expr.fvarLeaves (Expr.sort u)).all
        fun l => B'.contains l) := by rw [hnil]; rfl
    rw [leavesSubGo.eq_def]
    split
    · exact ⟨hres, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · exact ⟨hres, hm.insert hres⟩
  | const n us =>
    intro memo hm
    have hnil : (Expr.fvarLeaves (Expr.const n us)) = [] := fvarLeaves_const n us
    have hres : true = ((Expr.fvarLeaves (Expr.const n us)).all
        fun l => B'.contains l) := by rw [hnil]; rfl
    rw [leavesSubGo.eq_def]
    split
    · exact ⟨hres, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · exact ⟨hres, hm.insert hres⟩
  | lit l =>
    intro memo hm
    have hnil : (Expr.fvarLeaves (Expr.lit l)) = [] := fvarLeaves_lit l
    have hres : true = ((Expr.fvarLeaves (Expr.lit l)).all
        fun l => B'.contains l) := by rw [hnil]; rfl
    rw [leavesSubGo.eq_def]
    split
    · exact ⟨hres, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · exact ⟨hres, hm.insert hres⟩
  | fvar idx n ty iht =>
    intro memo hm
    have hlv : (Expr.fvarLeaves (Expr.fvar idx n ty))
        = (idx, n, ty) :: (Expr.fvarLeaves ty) := fvarLeaves_fvar ..
    rw [leavesSubGo.eq_def]
    split
    · rename_i hcut
      exact ⟨by rw [fvarLeaves_nil_of_fvarsBelow_zero _
        (fvarB_le (Nat.le_of_eq (by simpa using hcut)))]; rfl, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · dsimp only
        split
        · rename_i hlm
          obtain ⟨h1, h2⟩ := iht hm
          rcases hp : leavesSubGo bl memo ty with ⟨rt, mt⟩
          rw [hp] at h1 h2
          have hres : rt
              = ((Expr.fvarLeaves (Expr.fvar idx n ty)).all
                  fun l => B'.contains l) := by
            rw [hlv, List.all_cons, ← leafMem_spec hbl, hlm, ← h1,
              Bool.true_and]
          exact ⟨hres, h2.insert hres⟩
        · rename_i hlm
          have hres : false
              = ((Expr.fvarLeaves (Expr.fvar idx n ty)).all
                  fun l => B'.contains l) := by
            rw [hlv, List.all_cons, ← leafMem_spec hbl]
            simp [hlm]
          exact ⟨hres, hm.insert hres⟩
  | app f a ihf iha =>
    intro memo hm
    have hlv : (Expr.fvarLeaves (Expr.app f a))
        = (Expr.fvarLeaves f) ++ (Expr.fvarLeaves a) := fvarLeaves_app ..
    rw [leavesSubGo.eq_def]
    split
    · rename_i hcut
      exact ⟨by rw [fvarLeaves_nil_of_fvarsBelow_zero _
        (fvarB_le (Nat.le_of_eq (by simpa using hcut)))]; rfl, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · obtain ⟨h1, h2⟩ := ihf hm
        rcases hp : leavesSubGo bl memo f with ⟨rf, mf⟩
        rw [hp] at h1 h2
        simp only [hp]
        cases rf with
        | true =>
          obtain ⟨h3, h4⟩ := iha h2
          rcases hq : leavesSubGo bl mf a with ⟨ra, ma⟩
          rw [hq] at h3 h4
          have hres : ra
              = ((Expr.fvarLeaves (Expr.app f a)).all
                  fun l => B'.contains l) := by
            rw [hlv, List.all_append, ← h1, ← h3, Bool.true_and]
          exact ⟨hres, h4.insert hres⟩
        | false =>
          have hres : false
              = ((Expr.fvarLeaves (Expr.app f a)).all
                  fun l => B'.contains l) := by
            rw [hlv, List.all_append, ← h1, Bool.false_and]
          exact ⟨hres, h2.insert hres⟩
  | lam n ty bd m iht ihb =>
    intro memo hm
    have hlv : (Expr.fvarLeaves (Expr.lam n ty bd m))
        = (Expr.fvarLeaves ty) ++ (Expr.fvarLeaves bd) := fvarLeaves_lam ..
    rw [leavesSubGo.eq_def]
    split
    · rename_i hcut
      exact ⟨by rw [fvarLeaves_nil_of_fvarsBelow_zero _
        (fvarB_le (Nat.le_of_eq (by simpa using hcut)))]; rfl, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · obtain ⟨h1, h2⟩ := iht hm
        rcases hp : leavesSubGo bl memo ty with ⟨rt, mt⟩
        rw [hp] at h1 h2
        simp only [hp]
        cases rt with
        | true =>
          obtain ⟨h3, h4⟩ := ihb h2
          rcases hq : leavesSubGo bl mt bd with ⟨rb, mb⟩
          rw [hq] at h3 h4
          have hres : rb
              = ((Expr.fvarLeaves (Expr.lam n ty bd m)).all
                  fun l => B'.contains l) := by
            rw [hlv, List.all_append, ← h1, ← h3, Bool.true_and]
          exact ⟨hres, h4.insert hres⟩
        | false =>
          have hres : false
              = ((Expr.fvarLeaves (Expr.lam n ty bd m)).all
                  fun l => B'.contains l) := by
            rw [hlv, List.all_append, ← h1, Bool.false_and]
          exact ⟨hres, h2.insert hres⟩
  | forallE n ty bd m iht ihb =>
    intro memo hm
    have hlv : (Expr.fvarLeaves (Expr.forallE n ty bd m))
        = (Expr.fvarLeaves ty) ++ (Expr.fvarLeaves bd) :=
      fvarLeaves_forallE ..
    rw [leavesSubGo.eq_def]
    split
    · rename_i hcut
      exact ⟨by rw [fvarLeaves_nil_of_fvarsBelow_zero _
        (fvarB_le (Nat.le_of_eq (by simpa using hcut)))]; rfl, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · obtain ⟨h1, h2⟩ := iht hm
        rcases hp : leavesSubGo bl memo ty with ⟨rt, mt⟩
        rw [hp] at h1 h2
        simp only [hp]
        cases rt with
        | true =>
          obtain ⟨h3, h4⟩ := ihb h2
          rcases hq : leavesSubGo bl mt bd with ⟨rb, mb⟩
          rw [hq] at h3 h4
          have hres : rb
              = ((Expr.fvarLeaves (Expr.forallE n ty bd m)).all
                  fun l => B'.contains l) := by
            rw [hlv, List.all_append, ← h1, ← h3, Bool.true_and]
          exact ⟨hres, h4.insert hres⟩
        | false =>
          have hres : false
              = ((Expr.fvarLeaves (Expr.forallE n ty bd m)).all
                  fun l => B'.contains l) := by
            rw [hlv, List.all_append, ← h1, Bool.false_and]
          exact ⟨hres, h2.insert hres⟩
  | letE n ty val bd iht ihv ihb =>
    intro memo hm
    have hlv : (Expr.fvarLeaves (Expr.letE n ty val bd))
        = (Expr.fvarLeaves ty) ++ (Expr.fvarLeaves val)
            ++ (Expr.fvarLeaves bd) := fvarLeaves_letE ..
    rw [leavesSubGo.eq_def]
    split
    · rename_i hcut
      exact ⟨by rw [fvarLeaves_nil_of_fvarsBelow_zero _
        (fvarB_le (Nat.le_of_eq (by simpa using hcut)))]; rfl, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · obtain ⟨h1, h2⟩ := iht hm
        rcases hp : leavesSubGo bl memo ty with ⟨rt, mt⟩
        rw [hp] at h1 h2
        simp only [hp]
        cases rt with
        | false =>
          have hres : false
              = ((Expr.fvarLeaves (Expr.letE n ty val bd)).all
                  fun l => B'.contains l) := by
            rw [hlv, List.all_append, List.all_append, ← h1]
            simp
          exact ⟨hres, h2.insert hres⟩
        | true =>
          obtain ⟨h3, h4⟩ := ihv h2
          rcases hq : leavesSubGo bl mt val with ⟨rv, mv⟩
          rw [hq] at h3 h4
          cases rv with
          | false =>
            have hres : false
                = ((Expr.fvarLeaves (Expr.letE n ty val bd)).all
                    fun l => B'.contains l) := by
              rw [hlv, List.all_append, List.all_append, ← h1, ← h3]
              simp
            exact ⟨hres, h4.insert hres⟩
          | true =>
            obtain ⟨h5, h6⟩ := ihb h4
            rcases hr : leavesSubGo bl mv bd with ⟨rb, mb⟩
            rw [hr] at h5 h6
            have hres : rb
                = ((Expr.fvarLeaves (Expr.letE n ty val bd)).all
                    fun l => B'.contains l) := by
              rw [hlv, List.all_append, List.all_append, ← h1, ← h3, ← h5]
              simp
            exact ⟨hres, h6.insert hres⟩
  | proj s i sub ihe =>
    intro memo hm
    have hlv : (Expr.fvarLeaves (Expr.proj s i sub))
        = (Expr.fvarLeaves sub) := fvarLeaves_proj ..
    rw [leavesSubGo.eq_def]
    split
    · rename_i hcut
      exact ⟨by rw [fvarLeaves_nil_of_fvarsBelow_zero _
        (fvarB_le (Nat.le_of_eq (by simpa using hcut)))]; rfl, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · dsimp only
        obtain ⟨h1, h2⟩ := ihe hm
        rcases hp : leavesSubGo bl memo sub with ⟨rs, ms⟩
        rw [hp] at h1 h2
        have hres : rs
            = ((Expr.fvarLeaves (Expr.proj s i sub)).all
                fun l => B'.contains l) := by
          rw [hlv, ← h1]
        exact ⟨hres, h2.insert hres⟩

/-- **The fabrication leaf guard agrees with the `Expr`-level
leaf-subset boolean** — `leafGuard_spec'`'s right-hand side, verbatim,
with the arena denotation replaced by the erasure. -/
theorem leafGuard_spec {fab base : ExprC} :
    ExprC.leafGuard fab base
      = ((Expr.fvarLeaves fab).all
          fun l => (Expr.fvarLeaves base).contains l) := by
  unfold leafGuard
  cases hhf : fab.hasFvar with
  | false =>
    have : (Expr.fvarLeaves fab) = [] :=
      fvarLeaves_nil_of_fvarsBelow_zero _
        (fvarB_le (Nat.le_of_eq (by simpa [hasFvar] using hhf)))
    simp [this]
  | true =>
    simp only [Bool.not_true, Bool.false_or]
    exact (leavesSubGo_spec (fvarLeaves_leafBase) MemoSubInv.empty).1

end ExprC

/-! ## Guard agreement

The environment-index guards of `Lech/Cached/StateC.lean` are pure
functions of the node, so each agrees with its `Expr`-side original.
Each comes in two forms: the plain equation, and (primed) the same
equation transported along the value equation the simulation
carries. -/

open ExprC in
/-- The `Nat`-literal readout agrees with the spec's `rawNatLit?` on
the erasure — a top-level match, so no invariant is needed. -/
theorem rawNatLitC?_spec (e : ExprC) :
    rawNatLitC? e = rawNatLit? e := by
  cases e with
  | lit l => cases l <;> rfl
  | const c us =>
    cases us with
    | nil =>
      show (if c == natZeroName then some 0 else none)
        = (if c = natZeroName then some 0 else none)
      by_cases hc : c = natZeroName <;> simp [hc]
    | cons u us => rfl
  | _ => rfl

open ExprC in
/-- `rawNatLitC?_spec` transported along the value equation the
simulation carries. -/
theorem rawNatLitC?_spec' {w : ExprC} {wx : Expr}
    (h : w = wx) : rawNatLitC? w = rawNatLit? wx := by
  rw [rawNatLitC?_spec, h]

open ExprC in
/-- The unit-like-type guard agrees with the spec's `isUnitLikeTy` on
the erasure — again a top-level match on the whnf'd node, so no
invariant is needed; only the `FEnv` index has to be resolved. -/
theorem isUnitLikeTyC_spec {env : Env} (e : ExprC) :
    isUnitLikeTyC (mkFEnv env) e = isUnitLikeTy env e := by
  cases e with
  | const cn us =>
    show (cn == punitName &&
      (match (mkFEnv env).find? punitName with
        | some (.indInfo _ _) => true
        | _ => false) &&
      (match (mkFEnv env).find? punitRecName with
        | some (.recInfo _ mI rP [r]) => mI == rP && r.nfields == 0
        | _ => false)) = _
    rw [mkFEnv_find?, mkFEnv_find?]
    rfl
  | _ => rfl

open ExprC in
/-- `isUnitLikeTyC_spec` transported along the value equation. -/
theorem isUnitLikeTyC_spec' {env : Env} {w : ExprC} {wx : Expr}
    (h : w = wx) :
    isUnitLikeTyC (mkFEnv env) w = isUnitLikeTy env wx := by
  rw [isUnitLikeTyC_spec, h]

open ExprC in
/-- The constructor-application guard agrees with the spec's
`isCtorApp` on the erasure.  Unlike the two above it reads the
*spine head*, so the node invariant is needed (`getAppFn_spec`). -/
theorem isCtorAppC_spec {env : Env} {e : ExprC} :
    isCtorAppC (mkFEnv env) e = isCtorApp env e := by
  have hfn := ExprC.getAppFn_spec e
  show (match ExprC.getAppFn e with
      | .const cn _ =>
        match (mkFEnv env).find? cn with
        | some (.ctorInfo _ _ _) => true
        | _ => false
      | _ => false) = _
  rw [isCtorApp, ← hfn]
  cases ExprC.getAppFn e with
  | const cn us =>
    show (match (mkFEnv env).find? cn with
        | some (.ctorInfo _ _ _) => true
        | _ => false) = _
    rw [mkFEnv_find?]
    rfl
  | _ => rfl

open ExprC in
/-- `isCtorAppC_spec` transported along the value equation. -/
theorem isCtorAppC_spec' {env : Env} {e : ExprC} {ex : Expr}
    (h : e = ex) :
    isCtorAppC (mkFEnv env) e = isCtorApp env ex := by
  rw [isCtorAppC_spec, h]

/-- `Expr.quickPair` transported along the value equations. -/
theorem quickPair_spec' {a b : ExprC} {ax bx : Expr}
    (ha : a = ax) (hb : b = bx) : Expr.quickPair a b = Expr.quickPair ax bx := by
  rw [ha, hb]

/-- The eta constructor-shape gate agrees with the spec's `etaCtorShape`
(`ExprC = Expr`; only the environment lookup differs). -/
theorem etaCtorShapeC_spec' {env : Env} {e : ExprC} {ex : Expr}
    (h : e = ex) :
    etaCtorShapeC (mkFEnv env) e = etaCtorShape env ex := by
  subst h
  unfold etaCtorShapeC etaCtorShape
  generalize Expr.getAppFn e = f
  cases f <;> simp only [mkFEnv_find?] <;> first
    | rfl
    | (generalize env.find? _ = ci
       rcases ci with _ | ci <;> try rfl
       cases ci <;> rfl)

open ExprC in
/-- The reducibility-hint readout agrees with the spec's `headHint` on
the erasure — like `isCtorAppC_spec` it reads the *spine head*, so the
node invariant is needed (`getAppFn_spec`). -/
theorem headHintC_spec {env : Env} {e : ExprC} :
    headHintC (mkFEnv env) e = headHint env e := by
  have hfn := ExprC.getAppFn_spec e
  show (match ExprC.getAppFn e with
      | .const nm _ =>
        match (mkFEnv env).find? nm with
        | some (.defnInfo _ _ hint) => hint
        | _ => .opaque
      | _ => .opaque) = _
  rw [headHint, ← hfn]
  cases ExprC.getAppFn e with
  | const nm us =>
    dsimp only
    rw [mkFEnv_find?]
    cases env.find? nm with
    | none => rfl
    | some ci => cases ci <;> rfl
  | _ => rfl

open ExprC in
/-- `headHintC_spec` transported along the value equation. -/
theorem headHintC_spec' {env : Env} {e : ExprC} {ex : Expr}
    (h : e = ex) :
    headHintC (mkFEnv env) e = headHint env ex := by
  rw [headHintC_spec, h]

open ExprC in
/-- The lazy-delta unfoldability decision agrees with the spec's
`unfoldableHead` on the erasure (again a spine-head read). -/
theorem unfoldableHeadC_spec {env : Env} {e : ExprC} :
    unfoldableHeadC (mkFEnv env) e = unfoldableHead env e := by
  have hfn := ExprC.getAppFn_spec e
  show (match ExprC.getAppFn e with
      | .const nm us =>
        match (mkFEnv env).find? nm with
        | some (.defnInfo cv _ _) => us.length == cv.levelParams.length
        | some (.thmInfo cv _) => us.length == cv.levelParams.length
        | _ => false
      | _ => false) = _
  rw [unfoldableHead, ← hfn]
  cases ExprC.getAppFn e with
  | const nm us =>
    dsimp only
    rw [mkFEnv_find?]
    cases env.find? nm with
    | none => rfl
    | some ci => cases ci <;> rfl
  | _ => rfl

open ExprC in
/-- `unfoldableHeadC_spec` transported along the value equation. -/
theorem unfoldableHeadC_spec' {env : Env} {e : ExprC} {ex : Expr}
    (h : e = ex) :
    unfoldableHeadC (mkFEnv env) e = unfoldableHead env ex := by
  rw [unfoldableHeadC_spec, h]

open ExprC in
/-- The same-constant-head short-circuit agrees with the spec's
`sameConstHeads` on the erasures: both sides must be applications, and
then the two *function parts'* spine heads are compared. -/
theorem sameConstHeadsC_spec {a b : ExprC} :
    sameConstHeadsC a b = sameConstHeads a b := by
  cases a with
  | app f₁ a₁ =>
    cases b with
    | app f₂ a₂ =>
      have hfn₁ := ExprC.getAppFn_spec f₁
      have hfn₂ := ExprC.getAppFn_spec f₂
      show (match ExprC.getAppFn f₁, ExprC.getAppFn f₂ with
          | .const n₁ _, .const n₂ _ => n₁ == n₂
          | _, _ => false) = _
      rw [show sameConstHeads ((Expr.app f₁ a₁))
              ((Expr.app f₂ a₂))
            = (match (Expr.getAppFn f₁), (Expr.getAppFn f₂) with
              | .const n₁ _, .const n₂ _ => n₁ == n₂
              | _, _ => false) from rfl, ← hfn₁, ← hfn₂]
      cases ExprC.getAppFn f₁ <;> cases ExprC.getAppFn f₂ <;> rfl
    | _ => rfl
  | _ => cases b <;> rfl

open ExprC in
/-- `sameConstHeadsC_spec` transported along the value equations. -/
theorem sameConstHeadsC_spec' {a b : ExprC} {xa xb : Expr}
    (h₁ : a = xa) (h₂ : b = xb) :
    sameConstHeadsC a b = sameConstHeads xa xb := by
  rw [sameConstHeadsC_spec, h₁, h₂]

open ExprC in
/-- The `O(1)` eager fvar-range field is exact (`fvarB_eq _`), so its
non-zeroness is the spec's `Expr.hasFvar`. -/
theorem hasFvar_spec' {e : ExprC} {ex : Expr}
    (h : e = ex) : ExprC.hasFvar e = ex.hasFvar := by
  show (e.fvarB != 0) = _
  rw [fvarB_eq e, h, Expr.fvarRange_bne_zero]

open ExprC in
/-- `ExprC.wscopedB_spec` transported along the value equation. -/
theorem wscopedB_spec' {d : Nat} {e : ExprC} {ex : Expr}
    (h : e = ex) :
    ExprC.wscopedB d e = ex.wscopedB d := by
  rw [ExprC.wscopedB_spec, h]

open ExprC in
/-- `ExprC.looseBVarsBounded_spec` transported along the value equation. -/
theorem looseBVarsBounded_spec' {k : Nat} {e : ExprC}
    {ex : Expr} (h : e = ex) :
    ExprC.looseBVarsBounded k e = ex.looseBVarsBounded k := by
  rw [ExprC.looseBVarsBounded_spec, h]

open ExprC in
/-- `ExprC.leafGuard_spec` transported along the value equations. -/
theorem leafGuard_spec' {fab base : ExprC} {fx bx : Expr}
    (h₁ : fab = fx) (h₂ : base = bx) :
    ExprC.leafGuard fab base
      = (fx.fvarLeaves.all fun l => bx.fvarLeaves.contains l) := by
  rw [ExprC.leafGuard_spec, h₁, h₂]

/-! ## Constant resolution

`constsResolveFCGo` (`Lech/Cached/StateC.lean`) is the cached
`Expr.constsResolveF`: an `ExprC`-keyed memoized walk with **no**
cutoff (the environment index is an ambient parameter of the call, so
only the node matters). -/

open ExprC in
/-- The constant-resolution walk's memo invariant. -/
def MemoCRInv (fe : FEnv) (memo : Std.HashMap ExprC Bool) : Prop :=
  ∀ (e : ExprC) (r : Bool), memo[e]? = some r →
    r = Expr.constsResolveF fe e

theorem MemoCRInv.empty {fe : FEnv} : MemoCRInv fe {} := by
  intro e r h
  simp at h

theorem MemoCRInv.insert {fe : FEnv} {memo : Std.HashMap ExprC Bool}
    (hm : MemoCRInv fe memo) {e : ExprC} {r : Bool}
    (heq : r = Expr.constsResolveF fe e) :
    MemoCRInv fe (memo.insert e r) := by
  intro e' r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← ExprC.beq_sound hbeq]
    exact heq
  · exact hm e' r' hk

open ExprC in
/-- **The constant-resolution walk agrees with `Expr.constsResolveF` on
the erasure.** -/
theorem constsResolveFCGo_spec {fe : FEnv} :
    ∀ {e : ExprC},
    ∀ {memo : Std.HashMap ExprC Bool}, MemoCRInv fe memo →
      (constsResolveFCGo fe memo e).1 = Expr.constsResolveF fe e ∧
        MemoCRInv fe (constsResolveFCGo fe memo e).2 := by
  intro e
  induction e with
  | bvar i =>
    intro memo hm
    rw [constsResolveFCGo.eq_def]
    split
    · rename_i r hhit
      exact ⟨hm _ _ hhit, hm⟩
    · exact ⟨rfl, hm.insert rfl⟩
  | sort u =>
    intro memo hm
    rw [constsResolveFCGo.eq_def]
    split
    · rename_i r hhit
      exact ⟨hm _ _ hhit, hm⟩
    · exact ⟨rfl, hm.insert rfl⟩
  | const n us =>
    intro memo hm
    rw [constsResolveFCGo.eq_def]
    split
    · rename_i r hhit
      exact ⟨hm _ _ hhit, hm⟩
    · exact ⟨rfl, hm.insert rfl⟩
  | lit l =>
    intro memo hm
    cases l <;>
      · rw [constsResolveFCGo.eq_def]
        split
        · rename_i r hhit
          exact ⟨hm _ _ hhit, hm⟩
        · exact ⟨rfl, hm.insert rfl⟩
  | fvar idx n ty iht =>
    intro memo hm
    rw [constsResolveFCGo.eq_def]
    split
    · rename_i r hhit
      exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      rcases hp : constsResolveFCGo fe memo ty with ⟨rt, mt⟩
      rw [hp] at h1 h2
      simp only [hp]
      exact ⟨h1, h2.insert h1⟩
  | app f a ihf iha =>
    intro memo hm
    rw [constsResolveFCGo.eq_def]
    split
    · rename_i r hhit
      exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, h2⟩ := ihf hm
      rcases hp : constsResolveFCGo fe memo f with ⟨rf, mf⟩
      rw [hp] at h1 h2
      simp only [hp]
      cases rf with
      | true =>
        obtain ⟨h3, h4⟩ := iha h2
        rcases hq : constsResolveFCGo fe mf a with ⟨ra, ma⟩
        rw [hq] at h3 h4
        have hres : ra
            = Expr.constsResolveF fe ((.app f a)) := by
          show ra = Expr.constsResolveF fe (Expr.app f a)
          rw [Expr.constsResolveF, ← h1, ← h3, Bool.true_and]
        exact ⟨hres, h4.insert hres⟩
      | false =>
        have hres : false
            = Expr.constsResolveF fe ((.app f a)) := by
          show false = Expr.constsResolveF fe (Expr.app f a)
          rw [Expr.constsResolveF, ← h1, Bool.false_and]
        exact ⟨hres, h2.insert hres⟩
  | lam n ty bd m iht ihb =>
    intro memo hm
    rw [constsResolveFCGo.eq_def]
    split
    · rename_i r hhit
      exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      rcases hp : constsResolveFCGo fe memo ty with ⟨rt, mt⟩
      rw [hp] at h1 h2
      simp only [hp]
      cases rt with
      | true =>
        obtain ⟨h3, h4⟩ := ihb h2
        rcases hq : constsResolveFCGo fe mt bd with ⟨rb, mb⟩
        rw [hq] at h3 h4
        have hres : rb = Expr.constsResolveF fe
            ((.lam n ty bd m)) := by
          show rb = Expr.constsResolveF fe
            (Expr.lam n ty bd m)
          rw [Expr.constsResolveF, ← h1, ← h3, Bool.true_and]
        exact ⟨hres, h4.insert hres⟩
      | false =>
        have hres : false = Expr.constsResolveF fe
            ((.lam n ty bd m)) := by
          show false = Expr.constsResolveF fe
            (Expr.lam n ty bd m)
          rw [Expr.constsResolveF, ← h1, Bool.false_and]
        exact ⟨hres, h2.insert hres⟩
  | forallE n ty bd m iht ihb =>
    intro memo hm
    rw [constsResolveFCGo.eq_def]
    split
    · rename_i r hhit
      exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      rcases hp : constsResolveFCGo fe memo ty with ⟨rt, mt⟩
      rw [hp] at h1 h2
      simp only [hp]
      cases rt with
      | true =>
        obtain ⟨h3, h4⟩ := ihb h2
        rcases hq : constsResolveFCGo fe mt bd with ⟨rb, mb⟩
        rw [hq] at h3 h4
        have hres : rb = Expr.constsResolveF fe
            ((.forallE n ty bd m)) := by
          show rb = Expr.constsResolveF fe
            (Expr.forallE n ty bd m)
          rw [Expr.constsResolveF, ← h1, ← h3, Bool.true_and]
        exact ⟨hres, h4.insert hres⟩
      | false =>
        have hres : false = Expr.constsResolveF fe
            ((.forallE n ty bd m)) := by
          show false = Expr.constsResolveF fe
            (Expr.forallE n ty bd m)
          rw [Expr.constsResolveF, ← h1, Bool.false_and]
        exact ⟨hres, h2.insert hres⟩
  | letE n ty val bd iht ihv ihb =>
    intro memo hm
    have herase : (Expr.letE n ty val bd)
        = Expr.letE n ty val bd := rfl
    rw [constsResolveFCGo.eq_def]
    split
    · rename_i r hhit
      exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      rcases hp : constsResolveFCGo fe memo ty with ⟨rt, mt⟩
      rw [hp] at h1 h2
      simp only [hp]
      cases rt with
      | false =>
        have hres : false = Expr.constsResolveF fe
            ((.letE n ty val bd)) := by
          rw [herase, Expr.constsResolveF, ← h1]
          simp
        exact ⟨hres, h2.insert hres⟩
      | true =>
        obtain ⟨h3, h4⟩ := ihv h2
        rcases hq : constsResolveFCGo fe mt val with ⟨rv, mv⟩
        rw [hq] at h3 h4
        cases rv with
        | false =>
          have hres : false = Expr.constsResolveF fe
              ((.letE n ty val bd)) := by
            rw [herase, Expr.constsResolveF, ← h1, ← h3]
            simp
          exact ⟨hres, h4.insert hres⟩
        | true =>
          obtain ⟨h5, h6⟩ := ihb h4
          rcases hr : constsResolveFCGo fe mv bd with ⟨rb, mb⟩
          rw [hr] at h5 h6
          have hres : rb = Expr.constsResolveF fe
              ((.letE n ty val bd)) := by
            rw [herase, Expr.constsResolveF, ← h1, ← h3, ← h5]
            simp
          exact ⟨hres, h6.insert hres⟩
  | proj s i sub ihe =>
    intro memo hm
    have herase : (Expr.proj s i sub)
        = Expr.proj s i sub := rfl
    rw [constsResolveFCGo.eq_def]
    split
    · rename_i r hhit
      exact ⟨hm _ _ hhit, hm⟩
    · dsimp only
      split
      · rename_i hfind
        obtain ⟨h1, h2⟩ := ihe hm
        rcases hp : constsResolveFCGo fe memo sub with ⟨rs, ms⟩
        rw [hp] at h1 h2
        have hres : rs = Expr.constsResolveF fe
            ((.proj s i sub)) := by
          rw [herase, Expr.constsResolveF, ← h1, hfind, Bool.true_and]
        exact ⟨hres, h2.insert hres⟩
      · rename_i hfind
        have hres : false = Expr.constsResolveF fe
            ((.proj s i sub)) := by
          rw [herase, Expr.constsResolveF]
          simp [hfind]
        exact ⟨hres, hm.insert hres⟩

open ExprC in
/-- **`constsResolveFC` is `Expr.constsResolveF` of the erasure.** -/
theorem constsResolveFC_spec {fe : FEnv} {e : ExprC} :
    constsResolveFC fe e = Expr.constsResolveF fe e :=
  (constsResolveFCGo_spec MemoCRInv.empty).1

/-! ### The zero-ness readout's memo (task #163, batch 9)

The binder-telescope loops call `zeronessOfLGo`, threading a `PWMemo`
across the `inferPisOutI` fold.  The keys are structural `Level`s, so
an entry simply *is* the readout of its key, and there is no `mono`
(nothing is state-indexed). -/

/-- Memo invariant of `zeronessOfLGo`: every entry is the
readout of its key. -/
def PWMemoInvC (memo : PWMemo) : Prop :=
  ∀ (u : Level) (pw : PropWhen), memo[u]? = some pw → pw = Level.zeronessOf u

theorem PWMemoInvC.empty : PWMemoInvC {} := by
  intro u pw hpw
  simp at hpw

theorem PWMemoInvC.insert {memo : PWMemo} {u : Level}
    (h : PWMemoInvC memo) :
    PWMemoInvC (memo.insert u (Level.zeronessOf u)) := by
  intro u' pw' hpw'
  rw [Std.HashMap.getElem?_insert] at hpw'
  by_cases hk : u = u'
  · subst hk
    rw [if_pos (by simp)] at hpw'
    cases hpw'
    rfl
  · rw [if_neg (by simpa using hk)] at hpw'
    exact h u' pw' hpw'

/-- The memoized zero-ness readout agrees with the tree readout and
maintains its memo invariant. -/
theorem zeronessOfLGo_spec (v : Level)
    {memo : PWMemo} {p : PropWhen} {memo' : PWMemo}
    (hminv : PWMemoInvC memo)
    (hgo : zeronessOfLGo memo v = (p, memo')) :
    PWMemoInvC memo' ∧ p = Level.zeronessOf v := by
  unfold zeronessOfLGo at hgo
  split at hgo
  · rename_i r hhit
    cases hgo
    exact ⟨hminv, hminv v _ hhit⟩
  · cases hgo
    exact ⟨hminv.insert, rfl⟩

end Lech.Cached

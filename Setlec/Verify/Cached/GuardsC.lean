import Setlec.Cached.ParsedC
import Setlec.Verify.Cached.OpsC
import Setlec.Verify.IExprOps

/-!
# The cached representation's guard walks and the conversion boundary

Task #163, batch 4.  The pieces of the cached clone that sit *between*
the parse arena and the core:

* the fabrication leaf guard (`fvarLeaves`/`leafMem`/`leavesSubGo`/
  `leafGuard`) — the transposition of `leafGuardI_spec`
  (`Setlec/Verify/IExprOps.lean`);
* the level-parameter definedness walk
  (`ExprC.allLevelParamsDefined`) — the transposition of
  `allLevelParamsDefinedI_spec`;
* the constant-resolution walk (`constsResolveFC`) — the transposition
  of `constsResolveFI_spec`;
* the arena→`ExprC` conversion (`ofStoreGo`/`ofStore`), the clone's
  counterpart of `EStore.readbackGo`: on a well-formed parse arena the
  conversion of a denoting index succeeds and yields a `WFc` term whose
  erasure *is* the denotation.

Two structural differences from the arena twins are paid for here.

1. The clone's `fvarLeaves` walk carries a **`seen` set** (the arena's
   is a result memo), so the leaf *list* it returns is deduplicated and
   is **not** `Expr.fvarLeaves` of the erasure — only its *set of
   elements* is.  Since the only consumer (`leafMem`) is a membership
   test, a membership characterization is exactly what is needed, and
   `leafGuard_spec` still lands on `leafGuardI_spec`'s `Expr`-side
   right-hand side verbatim.

   Marking a node *before* descending into it is what makes the `seen`
   invariant ("a marked node's leaves are already in the accumulator")
   momentarily false for the node being processed and for its
   ancestors.  The proof closes that gap the way a DFS on an acyclic
   graph does: the invariant is relaxed by a *gray* predicate `G` on
   erasures ("…*or* the marked node is gray"), the call at `e` requires
   every gray erasure to be strictly bigger than `eraseC e` — which is
   what rules a hit at `e` itself out — and the call's post-condition
   pops `eraseC e` off `G` again, because by then `e`'s leaves *are* in
   the accumulator.  Acyclicity is free here: `ExprC` is an inductive
   *tree*, so the size side-condition is discharged by each
   constructor's own `sizeF` recurrence.

2. `ofStoreGo` has `emlt` guards on every child (they make the
   traversal's `(etier, epos)` measure decrease without an arena
   hypothesis).  On a `TWF` store the children of a denoting node are
   `emlt`-below it (`denoteT_some_inv`), so no guard ever fires — the
   same discharge `readbackGo_spec` performs.
-/

namespace Setlec.Cached

open Setlec EStore

namespace ExprC

/-! ## Level-parameter definedness

`ExprC.allLevelParamsDefinedGo` is a plain `ExprC`-keyed memoized walk
with the `hasLP` cutoff; the memo invariant is the
erasure-function-of-key form, and the cutoff arm is discharged by
`hasLP_exact` plus `Expr.allLevelParamsDefined_of_not_hasLevelParam`. -/

/-- The definedness walk's memo invariant. -/
def MemoLPDInv (ps : List Name) (memo : Std.HashMap ExprC Bool) : Prop :=
  ∀ (e : ExprC) (r : Bool), memo[e]? = some r →
    r = (eraseC e).allLevelParamsDefined ps

theorem MemoLPDInv.empty {ps : List Name} : MemoLPDInv ps {} := by
  intro e r h
  simp at h

theorem MemoLPDInv.insert {ps : List Name} {memo : Std.HashMap ExprC Bool}
    (hm : MemoLPDInv ps memo) {e : ExprC} {r : Bool}
    (heq : r = (eraseC e).allLevelParamsDefined ps) :
    MemoLPDInv ps (memo.insert e r) := by
  intro e' r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← beqSpec_sound hbeq]
    exact heq
  · exact hm e' r' hk

/-- **The definedness walk agrees with `Expr.allLevelParamsDefined` on
the erasure.** -/
theorem allLevelParamsDefinedGo_spec {ps : List Name} :
    ∀ {e : ExprC}, WFc e →
    ∀ {memo : Std.HashMap ExprC Bool}, MemoLPDInv ps memo →
      (allLevelParamsDefinedGo ps memo e).1
          = (eraseC e).allLevelParamsDefined ps ∧
        MemoLPDInv ps (allLevelParamsDefinedGo ps memo e).2 := by
  intro e
  induction e with
  | bvar i hh bb fb lp =>
    intro hw memo hm
    rw [allLevelParamsDefinedGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(Expr.allLevelParamsDefined_of_not_hasLevelParam (params := ps)
        (by rw [← hasLP_exact hw]; simpa using hcut)).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · exact ⟨rfl, hm.insert rfl⟩
  | lit l hh bb fb lp =>
    intro hw memo hm
    rw [allLevelParamsDefinedGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(Expr.allLevelParamsDefined_of_not_hasLevelParam (params := ps)
        (by rw [← hasLP_exact hw]; simpa using hcut)).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · exact ⟨rfl, hm.insert rfl⟩
  | sort u hh bb fb lp =>
    intro hw memo hm
    rw [allLevelParamsDefinedGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(Expr.allLevelParamsDefined_of_not_hasLevelParam (params := ps)
        (by rw [← hasLP_exact hw]; simpa using hcut)).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · exact ⟨rfl, hm.insert rfl⟩
  | const n us hh bb fb lp =>
    intro hw memo hm
    rw [allLevelParamsDefinedGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(Expr.allLevelParamsDefined_of_not_hasLevelParam (params := ps)
        (by rw [← hasLP_exact hw]; simpa using hcut)).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · exact ⟨rfl, hm.insert rfl⟩
  | fvar idx n ty hh bb fb lp iht =>
    intro hw memo hm
    obtain ⟨hty, -⟩ := hw.fvar_inv
    rw [allLevelParamsDefinedGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(Expr.allLevelParamsDefined_of_not_hasLevelParam (params := ps)
        (by rw [← hasLP_exact hw]; simpa using hcut)).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · obtain ⟨h1, h2⟩ := iht hty hm
        rcases hp : allLevelParamsDefinedGo ps memo ty with ⟨rt, mt⟩
        rw [hp] at h1 h2
        simp only [hp]
        exact ⟨h1, h2.insert h1⟩
  | app f a hh bb fb lp ihf iha =>
    intro hw memo hm
    obtain ⟨hf, ha, -⟩ := hw.app_inv
    rw [allLevelParamsDefinedGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(Expr.allLevelParamsDefined_of_not_hasLevelParam (params := ps)
        (by rw [← hasLP_exact hw]; simpa using hcut)).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · obtain ⟨h1, h2⟩ := ihf hf hm
        rcases hp : allLevelParamsDefinedGo ps memo f with ⟨rf, mf⟩
        rw [hp] at h1 h2
        simp only [hp]
        cases rf with
        | true =>
          obtain ⟨h3, h4⟩ := iha ha h2
          rcases hq : allLevelParamsDefinedGo ps mf a with ⟨ra, ma⟩
          rw [hq] at h3 h4
          have hres : ra
              = (eraseC (.app f a hh bb fb lp)).allLevelParamsDefined ps := by
            show ra = (Expr.app (eraseC f) (eraseC a)).allLevelParamsDefined ps
            rw [Expr.allLevelParamsDefined, ← h1, ← h3, Bool.true_and]
          exact ⟨hres, h4.insert hres⟩
        | false =>
          have hres : false
              = (eraseC (.app f a hh bb fb lp)).allLevelParamsDefined ps := by
            show false
              = (Expr.app (eraseC f) (eraseC a)).allLevelParamsDefined ps
            rw [Expr.allLevelParamsDefined, ← h1, Bool.false_and]
          exact ⟨hres, h2.insert hres⟩
  | lam n ty bd m hh bb fb lp iht ihb =>
    intro hw memo hm
    obtain ⟨hty, hbd, -⟩ := hw.lam_inv
    rw [allLevelParamsDefinedGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(Expr.allLevelParamsDefined_of_not_hasLevelParam (params := ps)
        (by rw [← hasLP_exact hw]; simpa using hcut)).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · obtain ⟨h1, h2⟩ := iht hty hm
        rcases hp : allLevelParamsDefinedGo ps memo ty with ⟨rt, mt⟩
        rw [hp] at h1 h2
        simp only [hp]
        cases rt with
        | true =>
          obtain ⟨h3, h4⟩ := ihb hbd h2
          rcases hq : allLevelParamsDefinedGo ps mt bd with ⟨rb, mb⟩
          rw [hq] at h3 h4
          have hres : (rb && m.pw.paramsDefined ps)
              = (eraseC (.lam n ty bd m hh bb fb lp)).allLevelParamsDefined
                  ps := by
            show _ = (Expr.lam n (eraseC ty) (eraseC bd) m
              ).allLevelParamsDefined ps
            rw [Expr.allLevelParamsDefined, ← h1, ← h3, Bool.true_and]
          exact ⟨hres, h4.insert hres⟩
        | false =>
          have hres : false
              = (eraseC (.lam n ty bd m hh bb fb lp)).allLevelParamsDefined
                  ps := by
            show false = (Expr.lam n (eraseC ty) (eraseC bd) m
              ).allLevelParamsDefined ps
            rw [Expr.allLevelParamsDefined, ← h1]
            simp
          exact ⟨hres, h2.insert hres⟩
  | forallE n ty bd m hh bb fb lp iht ihb =>
    intro hw memo hm
    obtain ⟨hty, hbd, -⟩ := hw.forallE_inv
    rw [allLevelParamsDefinedGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(Expr.allLevelParamsDefined_of_not_hasLevelParam (params := ps)
        (by rw [← hasLP_exact hw]; simpa using hcut)).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · obtain ⟨h1, h2⟩ := iht hty hm
        rcases hp : allLevelParamsDefinedGo ps memo ty with ⟨rt, mt⟩
        rw [hp] at h1 h2
        simp only [hp]
        cases rt with
        | true =>
          obtain ⟨h3, h4⟩ := ihb hbd h2
          rcases hq : allLevelParamsDefinedGo ps mt bd with ⟨rb, mb⟩
          rw [hq] at h3 h4
          have hres : (rb && m.pw.paramsDefined ps)
              = (eraseC (.forallE n ty bd m hh bb fb lp)).allLevelParamsDefined
                  ps := by
            show _ = (Expr.forallE n (eraseC ty) (eraseC bd) m
              ).allLevelParamsDefined ps
            rw [Expr.allLevelParamsDefined, ← h1, ← h3, Bool.true_and]
          exact ⟨hres, h4.insert hres⟩
        | false =>
          have hres : false
              = (eraseC (.forallE n ty bd m hh bb fb lp)).allLevelParamsDefined
                  ps := by
            show false = (Expr.forallE n (eraseC ty) (eraseC bd) m
              ).allLevelParamsDefined ps
            rw [Expr.allLevelParamsDefined, ← h1]
            simp
          exact ⟨hres, h2.insert hres⟩
  | letE n ty val bd hh bb fb lp iht ihv ihb =>
    intro hw memo hm
    obtain ⟨hty, hval, hbd, -⟩ := hw.letE_inv
    rw [allLevelParamsDefinedGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(Expr.allLevelParamsDefined_of_not_hasLevelParam (params := ps)
        (by rw [← hasLP_exact hw]; simpa using hcut)).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · have herase : eraseC (ExprC.letE n ty val bd hh bb fb lp)
            = Expr.letE n (eraseC ty) (eraseC val) (eraseC bd) := rfl
        obtain ⟨h1, h2⟩ := iht hty hm
        rcases hp : allLevelParamsDefinedGo ps memo ty with ⟨rt, mt⟩
        rw [hp] at h1 h2
        simp only [hp]
        cases rt with
        | false =>
          have hres : false
              = (eraseC (.letE n ty val bd hh bb fb lp)).allLevelParamsDefined
                  ps := by
            rw [herase, Expr.allLevelParamsDefined, ← h1]
            simp
          exact ⟨hres, h2.insert hres⟩
        | true =>
          obtain ⟨h3, h4⟩ := ihv hval h2
          rcases hq : allLevelParamsDefinedGo ps mt val with ⟨rv, mv⟩
          rw [hq] at h3 h4
          cases rv with
          | false =>
            have hres : false
                = (eraseC (.letE n ty val bd hh bb fb lp)).allLevelParamsDefined
                    ps := by
              rw [herase, Expr.allLevelParamsDefined, ← h1, ← h3]
              simp
            exact ⟨hres, h4.insert hres⟩
          | true =>
            obtain ⟨h5, h6⟩ := ihb hbd h4
            rcases hr : allLevelParamsDefinedGo ps mv bd with ⟨rb, mb⟩
            rw [hr] at h5 h6
            have hres : rb
                = (eraseC (.letE n ty val bd hh bb fb lp)).allLevelParamsDefined
                    ps := by
              rw [herase, Expr.allLevelParamsDefined, ← h1, ← h3, ← h5]
              simp
            exact ⟨hres, h6.insert hres⟩
  | proj s i sub hh bb fb lp ihe =>
    intro hw memo hm
    obtain ⟨he, -⟩ := hw.proj_inv
    rw [allLevelParamsDefinedGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(Expr.allLevelParamsDefined_of_not_hasLevelParam (params := ps)
        (by rw [← hasLP_exact hw]; simpa using hcut)).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · obtain ⟨h1, h2⟩ := ihe he hm
        rcases hp : allLevelParamsDefinedGo ps memo sub with ⟨rs, ms⟩
        rw [hp] at h1 h2
        simp only [hp]
        exact ⟨h1, h2.insert h1⟩

/-- **`ExprC.allLevelParamsDefined` is `Expr.allLevelParamsDefined` of
the erasure.** -/
theorem allLevelParamsDefined_spec {ps : List Name} {e : ExprC} (hw : WFc e) :
    ExprC.allLevelParamsDefined ps e = (eraseC e).allLevelParamsDefined ps :=
  (allLevelParamsDefinedGo_spec hw MemoLPDInv.empty).1

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
  xs.map fun l => (l.1, l.2.1, eraseC l.2.2)

@[simp] theorem leavesEr_nil : leavesEr [] = [] := rfl

@[simp] theorem leavesEr_cons (idx : Nat) (n : Name) (ty : ExprC)
    (xs : List (Nat × Name × ExprC)) :
    leavesEr ((idx, n, ty) :: xs) = (idx, n, eraseC ty) :: leavesEr xs := rfl

/-! ### The `seen`-set walk

`fvarLeavesGo` marks a node **before** descending into it, so the
obvious invariant ("a marked node's leaves are already in the
accumulator") is false for the node currently being processed and for
its ancestors.  The invariant is therefore relaxed by a *gray*
predicate `G` on erasures, and the call at `e` requires every gray
erasure to be strictly bigger than `eraseC e` — which is what rules a
hit at `e` itself out.  Descending pushes `eraseC e` into `G`; the
call's post-condition pops it again, because by then `e`'s leaves *are*
in the accumulator.  `ExprC` is an inductive tree, so the size
condition is discharged by the constructor's own `sizeF`
recurrence. -/

/-- The leaf walk's `seen`-set invariant at a gray predicate `G`. -/
def SeenInv (G : Expr → Prop) (acc : List (Nat × Name × ExprC))
    (seen : Std.HashMap ExprC Unit) : Prop :=
  ∀ (k : ExprC) (u : Unit), seen[k]? = some u →
    (∀ l ∈ (eraseC k).fvarLeaves, l ∈ leavesEr acc) ∨ G (eraseC k)

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
    SeenInv (fun y => G y ∨ y = eraseC e) acc (seen.insert e ()) := by
  intro k u hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    exact Or.inr (Or.inr (beqSpec_sound hbeq).symm)
  · rcases h k u hk with hsub | hgray
    · exact Or.inl hsub
    · exact Or.inr (Or.inl hgray)

/-- …and, once the descent is finished and the node's leaves are in the
accumulator, it leaves it again. -/
theorem SeenInv.dropGray {G : Expr → Prop}
    {acc : List (Nat × Name × ExprC)} {seen : Std.HashMap ExprC Unit}
    {e : ExprC} (h : SeenInv (fun y => G y ∨ y = eraseC e) acc seen)
    (he : ∀ l ∈ (eraseC e).fvarLeaves, l ∈ leavesEr acc) :
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
theorem fvarLeavesGo_spec : ∀ {e : ExprC}, WFc e →
    ∀ {G : Expr → Prop} {acc : List (Nat × Name × ExprC)}
      {seen : Std.HashMap ExprC Unit},
      (∀ p ∈ acc, WFc p.2.2) → SeenInv G acc seen →
      (∀ y, G y → (eraseC e).sizeF < y.sizeF) →
      (∀ p ∈ (fvarLeavesGo acc seen e).1, WFc p.2.2) ∧
        (∀ l, l ∈ leavesEr (fvarLeavesGo acc seen e).1 ↔
          l ∈ leavesEr acc ∨ l ∈ (eraseC e).fvarLeaves) ∧
        SeenInv G (fvarLeavesGo acc seen e).1 (fvarLeavesGo acc seen e).2 := by
  intro e
  induction e with
  | bvar i hh bb fb lp =>
    intro hw G acc seen hacc hseen hG
    rw [fvarLeavesGo.eq_def]
    have hnil : (eraseC (ExprC.bvar i hh bb fb lp)).fvarLeaves = [] :=
      fvarLeaves_bvar i
    split
    · exact ⟨hacc, by simp [hnil], hseen⟩
    · split
      · rename_i u hhit
        exact ⟨hacc, by simp [hnil], hseen⟩
      · exact ⟨hacc, by simp [hnil],
          (hseen.insertGray _).dropGray (by simp [hnil])⟩
  | sort u hh bb fb lp =>
    intro hw G acc seen hacc hseen hG
    rw [fvarLeavesGo.eq_def]
    have hnil : (eraseC (ExprC.sort u hh bb fb lp)).fvarLeaves = [] :=
      fvarLeaves_sort u
    split
    · exact ⟨hacc, by simp [hnil], hseen⟩
    · split
      · rename_i v hhit
        exact ⟨hacc, by simp [hnil], hseen⟩
      · exact ⟨hacc, by simp [hnil],
          (hseen.insertGray _).dropGray (by simp [hnil])⟩
  | const n us hh bb fb lp =>
    intro hw G acc seen hacc hseen hG
    rw [fvarLeavesGo.eq_def]
    have hnil : (eraseC (ExprC.const n us hh bb fb lp)).fvarLeaves = [] :=
      fvarLeaves_const n us
    split
    · exact ⟨hacc, by simp [hnil], hseen⟩
    · split
      · rename_i v hhit
        exact ⟨hacc, by simp [hnil], hseen⟩
      · exact ⟨hacc, by simp [hnil],
          (hseen.insertGray _).dropGray (by simp [hnil])⟩
  | lit l hh bb fb lp =>
    intro hw G acc seen hacc hseen hG
    rw [fvarLeavesGo.eq_def]
    have hnil : (eraseC (ExprC.lit l hh bb fb lp)).fvarLeaves = [] :=
      fvarLeaves_lit l
    split
    · exact ⟨hacc, by simp [hnil], hseen⟩
    · split
      · rename_i v hhit
        exact ⟨hacc, by simp [hnil], hseen⟩
      · exact ⟨hacc, by simp [hnil],
          (hseen.insertGray _).dropGray (by simp [hnil])⟩
  | fvar idx n ty hh bb fb lp iht =>
    intro hw G acc seen hacc hseen hG
    obtain ⟨hty, -⟩ := hw.fvar_inv
    have herase : eraseC (ExprC.fvar idx n ty hh bb fb lp)
        = Expr.fvar idx n (eraseC ty) := rfl
    have hlv : (eraseC (ExprC.fvar idx n ty hh bb fb lp)).fvarLeaves
        = (idx, n, eraseC ty) :: (eraseC ty).fvarLeaves := by
      rw [herase, fvarLeaves_fvar]
    rw [fvarLeavesGo.eq_def]
    split
    · rename_i hcut
      have : (eraseC (ExprC.fvar idx n ty hh bb fb lp)).fvarLeaves = [] :=
        fvarLeaves_nil_of_fvarsBelow_zero _
          (fvarB_le hw (Nat.le_of_eq (by simpa using hcut)))
      exact ⟨hacc, by simp [this], hseen⟩
    · split
      · rename_i v hhit
        rcases hseen _ _ hhit with hsub | hgray
        · exact ⟨hacc, fun l => ⟨Or.inl, fun h => h.elim id (hsub l)⟩, hseen⟩
        · exact absurd (hG _ hgray) (Nat.lt_irrefl _)
      · dsimp only
        have hacc1 : ∀ p ∈ (idx, n, ty) :: acc, WFc p.2.2 := by
          intro p hp
          rcases List.mem_cons.mp hp with h | h
          · exact h ▸ hty
          · exact hacc p h
        have hGty : ∀ y, (G y ∨ y = eraseC (ExprC.fvar idx n ty hh bb fb lp)) →
            (eraseC ty).sizeF < y.sizeF := by
          intro y hy
          have hs : (eraseC (ExprC.fvar idx n ty hh bb fb lp)).sizeF
              = (eraseC ty).sizeF + 1 := by rw [herase]; rfl
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h1, h2, h3⟩ := iht hty hacc1
          ((hseen.insertGray _).mono (fun l h => by simp [h]) (fun _ h => h))
          hGty
        rcases hp : fvarLeavesGo ((idx, n, ty) :: acc) (seen.insert _ ()) ty
          with ⟨acc1, seen1⟩
        rw [hp] at h1 h2 h3
        have hmem : ∀ l, l ∈ leavesEr acc1 ↔
            l ∈ leavesEr acc ∨
              l ∈ (eraseC (ExprC.fvar idx n ty hh bb fb lp)).fvarLeaves := by
          intro l
          rw [h2, hlv]
          simp only [leavesEr_cons, List.mem_cons]
          grind
        exact ⟨h1, hmem, h3.dropGray (fun l hl => (hmem l).mpr (Or.inr hl))⟩
  | app f a hh bb fb lp ihf iha =>
    intro hw G acc seen hacc hseen hG
    obtain ⟨hf, ha, -⟩ := hw.app_inv
    have herase : eraseC (ExprC.app f a hh bb fb lp)
        = Expr.app (eraseC f) (eraseC a) := rfl
    have hlv : (eraseC (ExprC.app f a hh bb fb lp)).fvarLeaves
        = (eraseC f).fvarLeaves ++ (eraseC a).fvarLeaves := by
      rw [herase, fvarLeaves_app]
    have hsz : (eraseC (ExprC.app f a hh bb fb lp)).sizeF
        = (eraseC f).sizeF + (eraseC a).sizeF + 1 := by rw [herase]; rfl
    rw [fvarLeavesGo.eq_def]
    split
    · rename_i hcut
      have : (eraseC (ExprC.app f a hh bb fb lp)).fvarLeaves = [] :=
        fvarLeaves_nil_of_fvarsBelow_zero _
          (fvarB_le hw (Nat.le_of_eq (by simpa using hcut)))
      exact ⟨hacc, by simp [this], hseen⟩
    · split
      · rename_i v hhit
        rcases hseen _ _ hhit with hsub | hgray
        · exact ⟨hacc, fun l => ⟨Or.inl, fun h => h.elim id (hsub l)⟩, hseen⟩
        · exact absurd (hG _ hgray) (Nat.lt_irrefl _)
      · dsimp only
        have hGf : ∀ y, (G y ∨ y = eraseC (ExprC.app f a hh bb fb lp)) →
            (eraseC f).sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h1, h2, h3⟩ := ihf hf hacc (hseen.insertGray _) hGf
        rcases hp : fvarLeavesGo acc (seen.insert _ ()) f with ⟨acc1, seen1⟩
        rw [hp] at h1 h2 h3
        have hGa : ∀ y, (G y ∨ y = eraseC (ExprC.app f a hh bb fb lp)) →
            (eraseC a).sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h4, h5, h6⟩ := iha ha h1 h3 hGa
        rcases hq : fvarLeavesGo acc1 seen1 a with ⟨acc2, seen2⟩
        rw [hq] at h4 h5 h6
        have hmem : ∀ l, l ∈ leavesEr acc2 ↔
            l ∈ leavesEr acc ∨
              l ∈ (eraseC (ExprC.app f a hh bb fb lp)).fvarLeaves := by
          intro l
          rw [h5, h2, hlv, List.mem_append]
          grind
        exact ⟨h4, hmem, h6.dropGray (fun l hl => (hmem l).mpr (Or.inr hl))⟩
  | lam n ty bd m hh bb fb lp iht ihb =>
    intro hw G acc seen hacc hseen hG
    obtain ⟨hty, hbd, -⟩ := hw.lam_inv
    have herase : eraseC (ExprC.lam n ty bd m hh bb fb lp)
        = Expr.lam n (eraseC ty) (eraseC bd) m := rfl
    have hlv : (eraseC (ExprC.lam n ty bd m hh bb fb lp)).fvarLeaves
        = (eraseC ty).fvarLeaves ++ (eraseC bd).fvarLeaves := by
      rw [herase, fvarLeaves_lam]
    have hsz : (eraseC (ExprC.lam n ty bd m hh bb fb lp)).sizeF
        = (eraseC ty).sizeF + (eraseC bd).sizeF + 1 := by rw [herase]; rfl
    rw [fvarLeavesGo.eq_def]
    split
    · rename_i hcut
      have : (eraseC (ExprC.lam n ty bd m hh bb fb lp)).fvarLeaves = [] :=
        fvarLeaves_nil_of_fvarsBelow_zero _
          (fvarB_le hw (Nat.le_of_eq (by simpa using hcut)))
      exact ⟨hacc, by simp [this], hseen⟩
    · split
      · rename_i v hhit
        rcases hseen _ _ hhit with hsub | hgray
        · exact ⟨hacc, fun l => ⟨Or.inl, fun h => h.elim id (hsub l)⟩, hseen⟩
        · exact absurd (hG _ hgray) (Nat.lt_irrefl _)
      · dsimp only
        have hGt : ∀ y, (G y ∨ y = eraseC (ExprC.lam n ty bd m hh bb fb lp)) →
            (eraseC ty).sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h1, h2, h3⟩ := iht hty hacc (hseen.insertGray _) hGt
        rcases hp : fvarLeavesGo acc (seen.insert _ ()) ty with ⟨acc1, seen1⟩
        rw [hp] at h1 h2 h3
        have hGb : ∀ y, (G y ∨ y = eraseC (ExprC.lam n ty bd m hh bb fb lp)) →
            (eraseC bd).sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h4, h5, h6⟩ := ihb hbd h1 h3 hGb
        rcases hq : fvarLeavesGo acc1 seen1 bd with ⟨acc2, seen2⟩
        rw [hq] at h4 h5 h6
        have hmem : ∀ l, l ∈ leavesEr acc2 ↔
            l ∈ leavesEr acc ∨
              l ∈ (eraseC (ExprC.lam n ty bd m hh bb fb lp)).fvarLeaves := by
          intro l
          rw [h5, h2, hlv, List.mem_append]
          grind
        exact ⟨h4, hmem, h6.dropGray (fun l hl => (hmem l).mpr (Or.inr hl))⟩
  | forallE n ty bd m hh bb fb lp iht ihb =>
    intro hw G acc seen hacc hseen hG
    obtain ⟨hty, hbd, -⟩ := hw.forallE_inv
    have herase : eraseC (ExprC.forallE n ty bd m hh bb fb lp)
        = Expr.forallE n (eraseC ty) (eraseC bd) m := rfl
    have hlv : (eraseC (ExprC.forallE n ty bd m hh bb fb lp)).fvarLeaves
        = (eraseC ty).fvarLeaves ++ (eraseC bd).fvarLeaves := by
      rw [herase, fvarLeaves_forallE]
    have hsz : (eraseC (ExprC.forallE n ty bd m hh bb fb lp)).sizeF
        = (eraseC ty).sizeF + (eraseC bd).sizeF + 1 := by rw [herase]; rfl
    rw [fvarLeavesGo.eq_def]
    split
    · rename_i hcut
      have : (eraseC (ExprC.forallE n ty bd m hh bb fb lp)).fvarLeaves = [] :=
        fvarLeaves_nil_of_fvarsBelow_zero _
          (fvarB_le hw (Nat.le_of_eq (by simpa using hcut)))
      exact ⟨hacc, by simp [this], hseen⟩
    · split
      · rename_i v hhit
        rcases hseen _ _ hhit with hsub | hgray
        · exact ⟨hacc, fun l => ⟨Or.inl, fun h => h.elim id (hsub l)⟩, hseen⟩
        · exact absurd (hG _ hgray) (Nat.lt_irrefl _)
      · dsimp only
        have hGt : ∀ y,
            (G y ∨ y = eraseC (ExprC.forallE n ty bd m hh bb fb lp)) →
            (eraseC ty).sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h1, h2, h3⟩ := iht hty hacc (hseen.insertGray _) hGt
        rcases hp : fvarLeavesGo acc (seen.insert _ ()) ty with ⟨acc1, seen1⟩
        rw [hp] at h1 h2 h3
        have hGb : ∀ y,
            (G y ∨ y = eraseC (ExprC.forallE n ty bd m hh bb fb lp)) →
            (eraseC bd).sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h4, h5, h6⟩ := ihb hbd h1 h3 hGb
        rcases hq : fvarLeavesGo acc1 seen1 bd with ⟨acc2, seen2⟩
        rw [hq] at h4 h5 h6
        have hmem : ∀ l, l ∈ leavesEr acc2 ↔
            l ∈ leavesEr acc ∨
              l ∈ (eraseC (ExprC.forallE n ty bd m hh bb fb lp)).fvarLeaves := by
          intro l
          rw [h5, h2, hlv, List.mem_append]
          grind
        exact ⟨h4, hmem, h6.dropGray (fun l hl => (hmem l).mpr (Or.inr hl))⟩
  | letE n ty val bd hh bb fb lp iht ihv ihb =>
    intro hw G acc seen hacc hseen hG
    obtain ⟨hty, hval, hbd, -⟩ := hw.letE_inv
    have herase : eraseC (ExprC.letE n ty val bd hh bb fb lp)
        = Expr.letE n (eraseC ty) (eraseC val) (eraseC bd) := rfl
    have hlv : (eraseC (ExprC.letE n ty val bd hh bb fb lp)).fvarLeaves
        = (eraseC ty).fvarLeaves ++ (eraseC val).fvarLeaves
            ++ (eraseC bd).fvarLeaves := by
      rw [herase, fvarLeaves_letE]
    have hsz : (eraseC (ExprC.letE n ty val bd hh bb fb lp)).sizeF
        = (eraseC ty).sizeF + (eraseC val).sizeF + (eraseC bd).sizeF + 1 := by
      rw [herase]; rfl
    rw [fvarLeavesGo.eq_def]
    split
    · rename_i hcut
      have : (eraseC (ExprC.letE n ty val bd hh bb fb lp)).fvarLeaves = [] :=
        fvarLeaves_nil_of_fvarsBelow_zero _
          (fvarB_le hw (Nat.le_of_eq (by simpa using hcut)))
      exact ⟨hacc, by simp [this], hseen⟩
    · split
      · rename_i v hhit
        rcases hseen _ _ hhit with hsub | hgray
        · exact ⟨hacc, fun l => ⟨Or.inl, fun h => h.elim id (hsub l)⟩, hseen⟩
        · exact absurd (hG _ hgray) (Nat.lt_irrefl _)
      · dsimp only
        have hGt : ∀ y,
            (G y ∨ y = eraseC (ExprC.letE n ty val bd hh bb fb lp)) →
            (eraseC ty).sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h1, h2, h3⟩ := iht hty hacc (hseen.insertGray _) hGt
        rcases hp : fvarLeavesGo acc (seen.insert _ ()) ty with ⟨acc1, seen1⟩
        rw [hp] at h1 h2 h3
        have hGv : ∀ y,
            (G y ∨ y = eraseC (ExprC.letE n ty val bd hh bb fb lp)) →
            (eraseC val).sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h4, h5, h6⟩ := ihv hval h1 h3 hGv
        rcases hq : fvarLeavesGo acc1 seen1 val with ⟨acc2, seen2⟩
        rw [hq] at h4 h5 h6
        have hGb : ∀ y,
            (G y ∨ y = eraseC (ExprC.letE n ty val bd hh bb fb lp)) →
            (eraseC bd).sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h7, h8, h9⟩ := ihb hbd h4 h6 hGb
        rcases hr : fvarLeavesGo acc2 seen2 bd with ⟨acc3, seen3⟩
        rw [hr] at h7 h8 h9
        have hmem : ∀ l, l ∈ leavesEr acc3 ↔
            l ∈ leavesEr acc ∨
              l ∈ (eraseC (ExprC.letE n ty val bd hh bb fb lp)).fvarLeaves := by
          intro l
          rw [h8, h5, h2, hlv, List.mem_append, List.mem_append]
          grind
        exact ⟨h7, hmem, h9.dropGray (fun l hl => (hmem l).mpr (Or.inr hl))⟩
  | proj s i sub hh bb fb lp ihe =>
    intro hw G acc seen hacc hseen hG
    obtain ⟨he, -⟩ := hw.proj_inv
    have herase : eraseC (ExprC.proj s i sub hh bb fb lp)
        = Expr.proj s i (eraseC sub) := rfl
    have hlv : (eraseC (ExprC.proj s i sub hh bb fb lp)).fvarLeaves
        = (eraseC sub).fvarLeaves := by rw [herase, fvarLeaves_proj]
    have hsz : (eraseC (ExprC.proj s i sub hh bb fb lp)).sizeF
        = (eraseC sub).sizeF + 1 := by rw [herase]; rfl
    rw [fvarLeavesGo.eq_def]
    split
    · rename_i hcut
      have : (eraseC (ExprC.proj s i sub hh bb fb lp)).fvarLeaves = [] :=
        fvarLeaves_nil_of_fvarsBelow_zero _
          (fvarB_le hw (Nat.le_of_eq (by simpa using hcut)))
      exact ⟨hacc, by simp [this], hseen⟩
    · split
      · rename_i v hhit
        rcases hseen _ _ hhit with hsub | hgray
        · exact ⟨hacc, fun l => ⟨Or.inl, fun h => h.elim id (hsub l)⟩, hseen⟩
        · exact absurd (hG _ hgray) (Nat.lt_irrefl _)
      · dsimp only
        have hGs : ∀ y, (G y ∨ y = eraseC (ExprC.proj s i sub hh bb fb lp)) →
            (eraseC sub).sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h1, h2, h3⟩ := ihe he hacc (hseen.insertGray _) hGs
        rcases hp : fvarLeavesGo acc (seen.insert _ ()) sub with ⟨acc1, seen1⟩
        rw [hp] at h1 h2 h3
        have hmem : ∀ l, l ∈ leavesEr acc1 ↔
            l ∈ leavesEr acc ∨
              l ∈ (eraseC (ExprC.proj s i sub hh bb fb lp)).fvarLeaves := by
          intro l
          rw [h2, hlv]
        exact ⟨h1, hmem, h3.dropGray (fun l hl => (hmem l).mpr (Or.inr hl))⟩

/-! ### The base leaf list

`leafMem` compares annotations with `ExprC`'s `==`, so on a
field-correct base list it decides `Expr`-level membership.  What the
subset walk needs of the base is exactly this pair of facts. -/

/-- A cached base leaf list is a faithful stand-in for an `Expr`-side
one: field-correct annotations, and the same *set* of erased leaves. -/
def LeafBase (bl : List (Nat × Name × ExprC))
    (B' : List (Nat × Name × Expr)) : Prop :=
  (∀ p ∈ bl, WFc p.2.2) ∧ ∀ l, l ∈ leavesEr bl ↔ l ∈ B'

/-- `leafMem` decides membership in the erased list. -/
theorem leafMem_iff : ∀ {bl : List (Nat × Name × ExprC)},
    (∀ p ∈ bl, WFc p.2.2) → ∀ {idx : Nat} {nm : Name} {ty : ExprC}, WFc ty →
      (leafMem bl idx nm ty = true ↔ (idx, nm, eraseC ty) ∈ leavesEr bl) := by
  intro bl
  induction bl with
  | nil => intro _ idx nm ty _; simp [leafMem]
  | cons p rest ih =>
    obtain ⟨i, n, t⟩ := p
    intro hbl idx nm ty hty
    have ht : WFc t := hbl (i, n, t) (by simp)
    have hrest : ∀ q ∈ rest, WFc q.2.2 := fun q hq => hbl q (by simp [hq])
    rw [show leafMem ((i, n, t) :: rest) idx nm ty
        = ((i == idx && n == nm && (t == ty)) || leafMem rest idx nm ty)
      from rfl]
    rw [leavesEr_cons, List.mem_cons, Bool.or_eq_true, ih hrest hty,
      Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq,
      beq_iff (a := t) ht hty]
    simp only [Prod.mk.injEq]
    grind

/-- …hence agrees with the `Expr`-side `contains` on a `LeafBase`. -/
theorem leafMem_spec {bl : List (Nat × Name × ExprC)}
    {B' : List (Nat × Name × Expr)} (h : LeafBase bl B')
    {idx : Nat} {nm : Name} {ty : ExprC} (hty : WFc ty) :
    leafMem bl idx nm ty = B'.contains (idx, nm, eraseC ty) := by
  rw [Bool.eq_iff_iff, List.contains_eq_mem, decide_eq_true_iff,
    leafMem_iff h.1 hty, h.2]

/-- The base list built by the leaf walk *is* a `LeafBase` for the
erasure's leaves. -/
theorem fvarLeaves_leafBase {base : ExprC} (hb : WFc base) :
    LeafBase (fvarLeaves base) (eraseC base).fvarLeaves := by
  obtain ⟨h1, h2, -⟩ := fvarLeavesGo_spec (e := base) hb
    (G := fun _ => False) (acc := []) (seen := {})
    (by intro p hp; cases hp) SeenInv.empty (by intro y hy; exact hy.elim)
  refine ⟨h1, fun l => ?_⟩
  simp only [ExprC.fvarLeaves, h2]
  simp

/-! ### The subset walk -/

/-- The subset walk's memo invariant. -/
def MemoSubInv (B' : List (Nat × Name × Expr))
    (memo : Std.HashMap ExprC Bool) : Prop :=
  ∀ (e : ExprC) (r : Bool), memo[e]? = some r →
    r = ((eraseC e).fvarLeaves.all fun l => B'.contains l)

theorem MemoSubInv.empty {B' : List (Nat × Name × Expr)} :
    MemoSubInv B' {} := by
  intro e r h
  simp at h

theorem MemoSubInv.insert {B' : List (Nat × Name × Expr)}
    {memo : Std.HashMap ExprC Bool} (hm : MemoSubInv B' memo) {e : ExprC}
    {r : Bool}
    (heq : r = ((eraseC e).fvarLeaves.all fun l => B'.contains l)) :
    MemoSubInv B' (memo.insert e r) := by
  intro e' r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← beqSpec_sound hbeq]
    exact heq
  · exact hm e' r' hk

/-- **The subset walk decides the `Expr`-level leaf-subset boolean.** -/
theorem leavesSubGo_spec {bl : List (Nat × Name × ExprC)}
    {B' : List (Nat × Name × Expr)} (hbl : LeafBase bl B') :
    ∀ {e : ExprC}, WFc e →
    ∀ {memo : Std.HashMap ExprC Bool}, MemoSubInv B' memo →
      (leavesSubGo bl memo e).1
          = ((eraseC e).fvarLeaves.all fun l => B'.contains l) ∧
        MemoSubInv B' (leavesSubGo bl memo e).2 := by
  intro e
  induction e with
  | bvar i hh bb fb lp =>
    intro hw memo hm
    have hnil : (eraseC (ExprC.bvar i hh bb fb lp)).fvarLeaves = [] := fvarLeaves_bvar i
    have hres : true = ((eraseC (ExprC.bvar i hh bb fb lp)).fvarLeaves.all
        fun l => B'.contains l) := by rw [hnil]; rfl
    rw [leavesSubGo.eq_def]
    split
    · exact ⟨hres, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · exact ⟨hres, hm.insert hres⟩
  | sort u hh bb fb lp =>
    intro hw memo hm
    have hnil : (eraseC (ExprC.sort u hh bb fb lp)).fvarLeaves = [] := fvarLeaves_sort u
    have hres : true = ((eraseC (ExprC.sort u hh bb fb lp)).fvarLeaves.all
        fun l => B'.contains l) := by rw [hnil]; rfl
    rw [leavesSubGo.eq_def]
    split
    · exact ⟨hres, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · exact ⟨hres, hm.insert hres⟩
  | const n us hh bb fb lp =>
    intro hw memo hm
    have hnil : (eraseC (ExprC.const n us hh bb fb lp)).fvarLeaves = [] := fvarLeaves_const n us
    have hres : true = ((eraseC (ExprC.const n us hh bb fb lp)).fvarLeaves.all
        fun l => B'.contains l) := by rw [hnil]; rfl
    rw [leavesSubGo.eq_def]
    split
    · exact ⟨hres, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · exact ⟨hres, hm.insert hres⟩
  | lit l hh bb fb lp =>
    intro hw memo hm
    have hnil : (eraseC (ExprC.lit l hh bb fb lp)).fvarLeaves = [] := fvarLeaves_lit l
    have hres : true = ((eraseC (ExprC.lit l hh bb fb lp)).fvarLeaves.all
        fun l => B'.contains l) := by rw [hnil]; rfl
    rw [leavesSubGo.eq_def]
    split
    · exact ⟨hres, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · exact ⟨hres, hm.insert hres⟩
  | fvar idx n ty hh bb fb lp iht =>
    intro hw memo hm
    obtain ⟨hty, -⟩ := hw.fvar_inv
    have hlv : (eraseC (ExprC.fvar idx n ty hh bb fb lp)).fvarLeaves
        = (idx, n, eraseC ty) :: (eraseC ty).fvarLeaves := fvarLeaves_fvar ..
    rw [leavesSubGo.eq_def]
    split
    · rename_i hcut
      exact ⟨by rw [fvarLeaves_nil_of_fvarsBelow_zero _
        (fvarB_le hw (Nat.le_of_eq (by simpa using hcut)))]; rfl, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · dsimp only
        split
        · rename_i hlm
          obtain ⟨h1, h2⟩ := iht hty hm
          rcases hp : leavesSubGo bl memo ty with ⟨rt, mt⟩
          rw [hp] at h1 h2
          have hres : rt
              = ((eraseC (ExprC.fvar idx n ty hh bb fb lp)).fvarLeaves.all
                  fun l => B'.contains l) := by
            rw [hlv, List.all_cons, ← leafMem_spec hbl hty, hlm, ← h1,
              Bool.true_and]
          exact ⟨hres, h2.insert hres⟩
        · rename_i hlm
          have hres : false
              = ((eraseC (ExprC.fvar idx n ty hh bb fb lp)).fvarLeaves.all
                  fun l => B'.contains l) := by
            rw [hlv, List.all_cons, ← leafMem_spec hbl hty]
            simp [hlm]
          exact ⟨hres, hm.insert hres⟩
  | app f a hh bb fb lp ihf iha =>
    intro hw memo hm
    obtain ⟨hf, ha, -⟩ := hw.app_inv
    have hlv : (eraseC (ExprC.app f a hh bb fb lp)).fvarLeaves
        = (eraseC f).fvarLeaves ++ (eraseC a).fvarLeaves := fvarLeaves_app ..
    rw [leavesSubGo.eq_def]
    split
    · rename_i hcut
      exact ⟨by rw [fvarLeaves_nil_of_fvarsBelow_zero _
        (fvarB_le hw (Nat.le_of_eq (by simpa using hcut)))]; rfl, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · obtain ⟨h1, h2⟩ := ihf hf hm
        rcases hp : leavesSubGo bl memo f with ⟨rf, mf⟩
        rw [hp] at h1 h2
        simp only [hp]
        cases rf with
        | true =>
          obtain ⟨h3, h4⟩ := iha ha h2
          rcases hq : leavesSubGo bl mf a with ⟨ra, ma⟩
          rw [hq] at h3 h4
          have hres : ra
              = ((eraseC (ExprC.app f a hh bb fb lp)).fvarLeaves.all
                  fun l => B'.contains l) := by
            rw [hlv, List.all_append, ← h1, ← h3, Bool.true_and]
          exact ⟨hres, h4.insert hres⟩
        | false =>
          have hres : false
              = ((eraseC (ExprC.app f a hh bb fb lp)).fvarLeaves.all
                  fun l => B'.contains l) := by
            rw [hlv, List.all_append, ← h1, Bool.false_and]
          exact ⟨hres, h2.insert hres⟩
  | lam n ty bd m hh bb fb lp iht ihb =>
    intro hw memo hm
    obtain ⟨hty, hbd, -⟩ := hw.lam_inv
    have hlv : (eraseC (ExprC.lam n ty bd m hh bb fb lp)).fvarLeaves
        = (eraseC ty).fvarLeaves ++ (eraseC bd).fvarLeaves := fvarLeaves_lam ..
    rw [leavesSubGo.eq_def]
    split
    · rename_i hcut
      exact ⟨by rw [fvarLeaves_nil_of_fvarsBelow_zero _
        (fvarB_le hw (Nat.le_of_eq (by simpa using hcut)))]; rfl, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · obtain ⟨h1, h2⟩ := iht hty hm
        rcases hp : leavesSubGo bl memo ty with ⟨rt, mt⟩
        rw [hp] at h1 h2
        simp only [hp]
        cases rt with
        | true =>
          obtain ⟨h3, h4⟩ := ihb hbd h2
          rcases hq : leavesSubGo bl mt bd with ⟨rb, mb⟩
          rw [hq] at h3 h4
          have hres : rb
              = ((eraseC (ExprC.lam n ty bd m hh bb fb lp)).fvarLeaves.all
                  fun l => B'.contains l) := by
            rw [hlv, List.all_append, ← h1, ← h3, Bool.true_and]
          exact ⟨hres, h4.insert hres⟩
        | false =>
          have hres : false
              = ((eraseC (ExprC.lam n ty bd m hh bb fb lp)).fvarLeaves.all
                  fun l => B'.contains l) := by
            rw [hlv, List.all_append, ← h1, Bool.false_and]
          exact ⟨hres, h2.insert hres⟩
  | forallE n ty bd m hh bb fb lp iht ihb =>
    intro hw memo hm
    obtain ⟨hty, hbd, -⟩ := hw.forallE_inv
    have hlv : (eraseC (ExprC.forallE n ty bd m hh bb fb lp)).fvarLeaves
        = (eraseC ty).fvarLeaves ++ (eraseC bd).fvarLeaves :=
      fvarLeaves_forallE ..
    rw [leavesSubGo.eq_def]
    split
    · rename_i hcut
      exact ⟨by rw [fvarLeaves_nil_of_fvarsBelow_zero _
        (fvarB_le hw (Nat.le_of_eq (by simpa using hcut)))]; rfl, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · obtain ⟨h1, h2⟩ := iht hty hm
        rcases hp : leavesSubGo bl memo ty with ⟨rt, mt⟩
        rw [hp] at h1 h2
        simp only [hp]
        cases rt with
        | true =>
          obtain ⟨h3, h4⟩ := ihb hbd h2
          rcases hq : leavesSubGo bl mt bd with ⟨rb, mb⟩
          rw [hq] at h3 h4
          have hres : rb
              = ((eraseC (ExprC.forallE n ty bd m hh bb fb lp)).fvarLeaves.all
                  fun l => B'.contains l) := by
            rw [hlv, List.all_append, ← h1, ← h3, Bool.true_and]
          exact ⟨hres, h4.insert hres⟩
        | false =>
          have hres : false
              = ((eraseC (ExprC.forallE n ty bd m hh bb fb lp)).fvarLeaves.all
                  fun l => B'.contains l) := by
            rw [hlv, List.all_append, ← h1, Bool.false_and]
          exact ⟨hres, h2.insert hres⟩
  | letE n ty val bd hh bb fb lp iht ihv ihb =>
    intro hw memo hm
    obtain ⟨hty, hval, hbd, -⟩ := hw.letE_inv
    have hlv : (eraseC (ExprC.letE n ty val bd hh bb fb lp)).fvarLeaves
        = (eraseC ty).fvarLeaves ++ (eraseC val).fvarLeaves
            ++ (eraseC bd).fvarLeaves := fvarLeaves_letE ..
    rw [leavesSubGo.eq_def]
    split
    · rename_i hcut
      exact ⟨by rw [fvarLeaves_nil_of_fvarsBelow_zero _
        (fvarB_le hw (Nat.le_of_eq (by simpa using hcut)))]; rfl, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · obtain ⟨h1, h2⟩ := iht hty hm
        rcases hp : leavesSubGo bl memo ty with ⟨rt, mt⟩
        rw [hp] at h1 h2
        simp only [hp]
        cases rt with
        | false =>
          have hres : false
              = ((eraseC (ExprC.letE n ty val bd hh bb fb lp)).fvarLeaves.all
                  fun l => B'.contains l) := by
            rw [hlv, List.all_append, List.all_append, ← h1]
            simp
          exact ⟨hres, h2.insert hres⟩
        | true =>
          obtain ⟨h3, h4⟩ := ihv hval h2
          rcases hq : leavesSubGo bl mt val with ⟨rv, mv⟩
          rw [hq] at h3 h4
          cases rv with
          | false =>
            have hres : false
                = ((eraseC (ExprC.letE n ty val bd hh bb fb lp)).fvarLeaves.all
                    fun l => B'.contains l) := by
              rw [hlv, List.all_append, List.all_append, ← h1, ← h3]
              simp
            exact ⟨hres, h4.insert hres⟩
          | true =>
            obtain ⟨h5, h6⟩ := ihb hbd h4
            rcases hr : leavesSubGo bl mv bd with ⟨rb, mb⟩
            rw [hr] at h5 h6
            have hres : rb
                = ((eraseC (ExprC.letE n ty val bd hh bb fb lp)).fvarLeaves.all
                    fun l => B'.contains l) := by
              rw [hlv, List.all_append, List.all_append, ← h1, ← h3, ← h5]
              simp
            exact ⟨hres, h6.insert hres⟩
  | proj s i sub hh bb fb lp ihe =>
    intro hw memo hm
    obtain ⟨he, -⟩ := hw.proj_inv
    have hlv : (eraseC (ExprC.proj s i sub hh bb fb lp)).fvarLeaves
        = (eraseC sub).fvarLeaves := fvarLeaves_proj ..
    rw [leavesSubGo.eq_def]
    split
    · rename_i hcut
      exact ⟨by rw [fvarLeaves_nil_of_fvarsBelow_zero _
        (fvarB_le hw (Nat.le_of_eq (by simpa using hcut)))]; rfl, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ hhit, hm⟩
      · dsimp only
        obtain ⟨h1, h2⟩ := ihe he hm
        rcases hp : leavesSubGo bl memo sub with ⟨rs, ms⟩
        rw [hp] at h1 h2
        have hres : rs
            = ((eraseC (ExprC.proj s i sub hh bb fb lp)).fvarLeaves.all
                fun l => B'.contains l) := by
          rw [hlv, ← h1]
        exact ⟨hres, h2.insert hres⟩

/-- **The fabrication leaf guard agrees with the `Expr`-level
leaf-subset boolean** — `leafGuardI_spec`'s right-hand side, verbatim,
with the arena denotation replaced by the erasure. -/
theorem leafGuard_spec {fab base : ExprC} (hf : WFc fab) (hb : WFc base) :
    ExprC.leafGuard fab base
      = ((eraseC fab).fvarLeaves.all
          fun l => (eraseC base).fvarLeaves.contains l) := by
  unfold leafGuard
  cases hhf : fab.hasFvar with
  | false =>
    have : (eraseC fab).fvarLeaves = [] :=
      fvarLeaves_nil_of_fvarsBelow_zero _
        (fvarB_le hf (Nat.le_of_eq (by simpa [hasFvar] using hhf)))
    simp [this]
  | true =>
    simp only [Bool.not_true, Bool.false_or]
    exact (leavesSubGo_spec (fvarLeaves_leafBase hb) hf MemoSubInv.empty).1

end ExprC

/-! ## Store-guard agreement

The store-shaped guard twins of `Setlec/Cached/StateC.lean` are pure
functions of the node, so each agrees with its `Expr`-side original on
the erasure.  (Only the ones the body walks consume are proved; more
land with the walks that need them.) -/

open ExprC in
/-- The `Nat`-literal readout agrees with the spec's `rawNatLit?` on
the erasure — a top-level match, so no invariant is needed. -/
theorem rawNatLitC?_spec (e : ExprC) :
    rawNatLitC? e = rawNatLit? (eraseC e) := by
  cases e with
  | lit l h bb fb lp => cases l <;> rfl
  | const c us h bb fb lp =>
    cases us with
    | nil =>
      show (if c == natZeroName then some 0 else none)
        = (if c = natZeroName then some 0 else none)
      by_cases hc : c = natZeroName <;> simp [hc]
    | cons u us => rfl
  | _ => rfl

open ExprC in
/-- The store-shaped spelling the core bodies use (`withStore
(rawNatLitI? · w)`), stated against the erasure of the queried node —
the transposition of `rawNatLitI?_spec` (`Setlec/Verify/IExprOps.lean`),
whose arena denotation hypothesis becomes the erasure equation. -/
theorem rawNatLitI?_spec {st : CStore} {w : ExprC} {wx : Expr}
    (h : eraseC w = wx) : rawNatLitI? st w = rawNatLit? wx := by
  rw [rawNatLitI?, rawNatLitC?_spec, h]

/-! ## Constant resolution

`constsResolveFCGo` (`Setlec/Cached/StateC.lean`) is the clone's
`Expr.constsResolveF`: an `ExprC`-keyed memoized walk with **no**
cutoff (the environment index is an ambient parameter of the call, so
only the node matters). -/

open ExprC in
/-- The constant-resolution walk's memo invariant. -/
def MemoCRInv (fe : FEnv) (memo : Std.HashMap ExprC Bool) : Prop :=
  ∀ (e : ExprC) (r : Bool), memo[e]? = some r →
    r = Expr.constsResolveF fe (eraseC e)

theorem MemoCRInv.empty {fe : FEnv} : MemoCRInv fe {} := by
  intro e r h
  simp at h

theorem MemoCRInv.insert {fe : FEnv} {memo : Std.HashMap ExprC Bool}
    (hm : MemoCRInv fe memo) {e : ExprC} {r : Bool}
    (heq : r = Expr.constsResolveF fe (ExprC.eraseC e)) :
    MemoCRInv fe (memo.insert e r) := by
  intro e' r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← ExprC.beqSpec_sound hbeq]
    exact heq
  · exact hm e' r' hk

open ExprC in
/-- **The constant-resolution walk agrees with `Expr.constsResolveF` on
the erasure.** -/
theorem constsResolveFCGo_spec {fe : FEnv} :
    ∀ {e : ExprC}, WFc e →
    ∀ {memo : Std.HashMap ExprC Bool}, MemoCRInv fe memo →
      (constsResolveFCGo fe memo e).1 = Expr.constsResolveF fe (eraseC e) ∧
        MemoCRInv fe (constsResolveFCGo fe memo e).2 := by
  intro e
  induction e with
  | bvar i hh bb fb lp =>
    intro _ memo hm
    rw [constsResolveFCGo.eq_def]
    split
    · rename_i r hhit
      exact ⟨hm _ _ hhit, hm⟩
    · exact ⟨rfl, hm.insert rfl⟩
  | sort u hh bb fb lp =>
    intro _ memo hm
    rw [constsResolveFCGo.eq_def]
    split
    · rename_i r hhit
      exact ⟨hm _ _ hhit, hm⟩
    · exact ⟨rfl, hm.insert rfl⟩
  | const n us hh bb fb lp =>
    intro _ memo hm
    rw [constsResolveFCGo.eq_def]
    split
    · rename_i r hhit
      exact ⟨hm _ _ hhit, hm⟩
    · exact ⟨rfl, hm.insert rfl⟩
  | lit l hh bb fb lp =>
    intro _ memo hm
    cases l <;>
      · rw [constsResolveFCGo.eq_def]
        split
        · rename_i r hhit
          exact ⟨hm _ _ hhit, hm⟩
        · exact ⟨rfl, hm.insert rfl⟩
  | fvar idx n ty hh bb fb lp iht =>
    intro hw memo hm
    obtain ⟨hty, -⟩ := hw.fvar_inv
    rw [constsResolveFCGo.eq_def]
    split
    · rename_i r hhit
      exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, h2⟩ := iht hty hm
      rcases hp : constsResolveFCGo fe memo ty with ⟨rt, mt⟩
      rw [hp] at h1 h2
      simp only [hp]
      exact ⟨h1, h2.insert h1⟩
  | app f a hh bb fb lp ihf iha =>
    intro hw memo hm
    obtain ⟨hf, ha, -⟩ := hw.app_inv
    rw [constsResolveFCGo.eq_def]
    split
    · rename_i r hhit
      exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, h2⟩ := ihf hf hm
      rcases hp : constsResolveFCGo fe memo f with ⟨rf, mf⟩
      rw [hp] at h1 h2
      simp only [hp]
      cases rf with
      | true =>
        obtain ⟨h3, h4⟩ := iha ha h2
        rcases hq : constsResolveFCGo fe mf a with ⟨ra, ma⟩
        rw [hq] at h3 h4
        have hres : ra
            = Expr.constsResolveF fe (eraseC (.app f a hh bb fb lp)) := by
          show ra = Expr.constsResolveF fe (Expr.app (eraseC f) (eraseC a))
          rw [Expr.constsResolveF, ← h1, ← h3, Bool.true_and]
        exact ⟨hres, h4.insert hres⟩
      | false =>
        have hres : false
            = Expr.constsResolveF fe (eraseC (.app f a hh bb fb lp)) := by
          show false = Expr.constsResolveF fe (Expr.app (eraseC f) (eraseC a))
          rw [Expr.constsResolveF, ← h1, Bool.false_and]
        exact ⟨hres, h2.insert hres⟩
  | lam n ty bd m hh bb fb lp iht ihb =>
    intro hw memo hm
    obtain ⟨hty, hbd, -⟩ := hw.lam_inv
    rw [constsResolveFCGo.eq_def]
    split
    · rename_i r hhit
      exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, h2⟩ := iht hty hm
      rcases hp : constsResolveFCGo fe memo ty with ⟨rt, mt⟩
      rw [hp] at h1 h2
      simp only [hp]
      cases rt with
      | true =>
        obtain ⟨h3, h4⟩ := ihb hbd h2
        rcases hq : constsResolveFCGo fe mt bd with ⟨rb, mb⟩
        rw [hq] at h3 h4
        have hres : rb = Expr.constsResolveF fe
            (eraseC (.lam n ty bd m hh bb fb lp)) := by
          show rb = Expr.constsResolveF fe
            (Expr.lam n (eraseC ty) (eraseC bd) m)
          rw [Expr.constsResolveF, ← h1, ← h3, Bool.true_and]
        exact ⟨hres, h4.insert hres⟩
      | false =>
        have hres : false = Expr.constsResolveF fe
            (eraseC (.lam n ty bd m hh bb fb lp)) := by
          show false = Expr.constsResolveF fe
            (Expr.lam n (eraseC ty) (eraseC bd) m)
          rw [Expr.constsResolveF, ← h1, Bool.false_and]
        exact ⟨hres, h2.insert hres⟩
  | forallE n ty bd m hh bb fb lp iht ihb =>
    intro hw memo hm
    obtain ⟨hty, hbd, -⟩ := hw.forallE_inv
    rw [constsResolveFCGo.eq_def]
    split
    · rename_i r hhit
      exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, h2⟩ := iht hty hm
      rcases hp : constsResolveFCGo fe memo ty with ⟨rt, mt⟩
      rw [hp] at h1 h2
      simp only [hp]
      cases rt with
      | true =>
        obtain ⟨h3, h4⟩ := ihb hbd h2
        rcases hq : constsResolveFCGo fe mt bd with ⟨rb, mb⟩
        rw [hq] at h3 h4
        have hres : rb = Expr.constsResolveF fe
            (eraseC (.forallE n ty bd m hh bb fb lp)) := by
          show rb = Expr.constsResolveF fe
            (Expr.forallE n (eraseC ty) (eraseC bd) m)
          rw [Expr.constsResolveF, ← h1, ← h3, Bool.true_and]
        exact ⟨hres, h4.insert hres⟩
      | false =>
        have hres : false = Expr.constsResolveF fe
            (eraseC (.forallE n ty bd m hh bb fb lp)) := by
          show false = Expr.constsResolveF fe
            (Expr.forallE n (eraseC ty) (eraseC bd) m)
          rw [Expr.constsResolveF, ← h1, Bool.false_and]
        exact ⟨hres, h2.insert hres⟩
  | letE n ty val bd hh bb fb lp iht ihv ihb =>
    intro hw memo hm
    obtain ⟨hty, hval, hbd, -⟩ := hw.letE_inv
    have herase : eraseC (ExprC.letE n ty val bd hh bb fb lp)
        = Expr.letE n (eraseC ty) (eraseC val) (eraseC bd) := rfl
    rw [constsResolveFCGo.eq_def]
    split
    · rename_i r hhit
      exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, h2⟩ := iht hty hm
      rcases hp : constsResolveFCGo fe memo ty with ⟨rt, mt⟩
      rw [hp] at h1 h2
      simp only [hp]
      cases rt with
      | false =>
        have hres : false = Expr.constsResolveF fe
            (eraseC (.letE n ty val bd hh bb fb lp)) := by
          rw [herase, Expr.constsResolveF, ← h1]
          simp
        exact ⟨hres, h2.insert hres⟩
      | true =>
        obtain ⟨h3, h4⟩ := ihv hval h2
        rcases hq : constsResolveFCGo fe mt val with ⟨rv, mv⟩
        rw [hq] at h3 h4
        cases rv with
        | false =>
          have hres : false = Expr.constsResolveF fe
              (eraseC (.letE n ty val bd hh bb fb lp)) := by
            rw [herase, Expr.constsResolveF, ← h1, ← h3]
            simp
          exact ⟨hres, h4.insert hres⟩
        | true =>
          obtain ⟨h5, h6⟩ := ihb hbd h4
          rcases hr : constsResolveFCGo fe mv bd with ⟨rb, mb⟩
          rw [hr] at h5 h6
          have hres : rb = Expr.constsResolveF fe
              (eraseC (.letE n ty val bd hh bb fb lp)) := by
            rw [herase, Expr.constsResolveF, ← h1, ← h3, ← h5]
            simp
          exact ⟨hres, h6.insert hres⟩
  | proj s i sub hh bb fb lp ihe =>
    intro hw memo hm
    obtain ⟨he, -⟩ := hw.proj_inv
    have herase : eraseC (ExprC.proj s i sub hh bb fb lp)
        = Expr.proj s i (eraseC sub) := rfl
    rw [constsResolveFCGo.eq_def]
    split
    · rename_i r hhit
      exact ⟨hm _ _ hhit, hm⟩
    · dsimp only
      split
      · rename_i hfind
        obtain ⟨h1, h2⟩ := ihe he hm
        rcases hp : constsResolveFCGo fe memo sub with ⟨rs, ms⟩
        rw [hp] at h1 h2
        have hres : rs = Expr.constsResolveF fe
            (eraseC (.proj s i sub hh bb fb lp)) := by
          rw [herase, Expr.constsResolveF, ← h1, hfind, Bool.true_and]
        exact ⟨hres, h2.insert hres⟩
      · rename_i hfind
        have hres : false = Expr.constsResolveF fe
            (eraseC (.proj s i sub hh bb fb lp)) := by
          rw [herase, Expr.constsResolveF]
          simp [hfind]
        exact ⟨hres, hm.insert hres⟩

open ExprC in
/-- **`constsResolveFC` is `Expr.constsResolveF` of the erasure.** -/
theorem constsResolveFC_spec {fe : FEnv} {e : ExprC} (hw : WFc e) :
    constsResolveFC fe e = Expr.constsResolveF fe (eraseC e) :=
  (constsResolveFCGo_spec hw MemoCRInv.empty).1

/-! ## The conversion boundary: the parse arena becomes an `ExprC` DAG

`ofStoreGo` is `EStore.readbackGo` with the smart constructors in place
of the plain ones, so the proof is `readbackGo_spec`'s, one existential
wider: the produced node carries the field invariant and *erases to*
the index's denotation.  The level memo is shared with the interned
readback (`EStore.readbackLGo`), so its invariant `RLInv` and the
lemmas `readbackLGo_spec` / `readbackLList_spec` are reused verbatim.

The `emlt` guards (batch 2) are discharged where `readbackGo_spec`
discharges its own: `denoteT_some_inv` hands out `∀ c ∈ n.children,
emlt c e` for a denoting index, so `dif_pos` applies at every child. -/

open ExprC in
/-- Invariant of the conversion memo: every stored node is well formed
and erases to the denotation of the index it is filed under (the
`ExprC` counterpart of `RInv`). -/
def OfStoreInv (st : EStore) (memo : Std.HashMap EIdx ExprC) : Prop :=
  ∀ i c, memo[i]? = some c → WFc c ∧ st.denoteT i = some (eraseC c)

theorem OfStoreInv.empty {st : EStore} : OfStoreInv st {} := by
  intro i c h
  simp at h

theorem OfStoreInv.insert {st : EStore} {memo : Std.HashMap EIdx ExprC}
    {e : EIdx} {c : ExprC} (h : OfStoreInv st memo) (hw : ExprC.WFc c)
    (hx : st.denoteT e = some (ExprC.eraseC c)) :
    OfStoreInv st (memo.insert e c) := by
  intro i y hy
  rw [Std.HashMap.getElem?_insert] at hy
  by_cases hk : e = i
  · subst hk
    rw [if_pos (by simp)] at hy
    cases hy
    exact ⟨hw, hx⟩
  · rw [if_neg (by simpa using hk)] at hy
    exact h i y hy

open ExprC in
/-- **The conversion core is correct on a well-formed parse arena**: at
a denoting index it succeeds, and the node it returns is field-correct
and erases to the denotation. -/
theorem ofStoreGo_spec {st : EStore} (hwf : st.TWF) :
    ∀ (e : EIdx) {x : Expr} {memo : Std.HashMap EIdx ExprC}
      {lmemo : Std.HashMap LIdx Level}
      {r : Option ExprC} {memo' : Std.HashMap EIdx ExprC}
      {lmemo' : Std.HashMap LIdx Level},
      st.denoteT e = some x → OfStoreInv st memo → RLInv st lmemo →
      ofStoreGo st memo lmemo e = (r, memo', lmemo') →
      (∃ c, r = some c ∧ WFc c ∧ eraseC c = x) ∧
        OfStoreInv st memo' ∧ RLInv st lmemo' := by
  intro e
  induction e using emlt_induction with
  | ind e ih =>
    intro x memo lmemo r memo' lmemo' hx hinv hlinv hgo
    obtain ⟨n, hn, hc, hd⟩ := denoteT_some_inv hx
    have hml : ∀ c ∈ n.children, emlt c e := hc
    unfold ofStoreGo at hgo
    cases hm : memo[e]? with
    | some y =>
      rw [hm] at hgo
      injection hgo with h1 h2
      injection h2 with h2 h3
      subst h1; subst h2; subst h3
      obtain ⟨hwy, hdy⟩ := hinv e y hm
      rw [hx] at hdy
      exact ⟨⟨y, rfl, hwy, by injection hdy with h; rw [h]⟩, hinv, hlinv⟩
    | none =>
      rw [hm, hn] at hgo
      cases n with
      | bvar i =>
        cases hd
        dsimp only at hgo
        injection hgo with h1 h2
        injection h2 with h2 h3
        subst h1; subst h2; subst h3
        exact ⟨⟨_, rfl, ExprC.WFc.mkBVar i, rfl⟩,
          hinv.insert (ExprC.WFc.mkBVar i) hx, hlinv⟩
      | sort u =>
        rw [denoteNode, Option.map_eq_some_iff] at hd
        obtain ⟨lu, hlu, rfl⟩ := hd
        dsimp only at hgo
        rcases hg₁ : EStore.readbackLGo st lmemo u with ⟨r₁, lmemo₁⟩
        rw [hg₁] at hgo
        obtain ⟨rfl, hlinv₁⟩ := readbackLGo_spec u hlu hlinv hg₁
        dsimp only at hgo
        injection hgo with h1 h2
        injection h2 with h2 h3
        subst h1; subst h2; subst h3
        exact ⟨⟨_, rfl, ExprC.WFc.mkSort lu, rfl⟩,
          hinv.insert (ExprC.WFc.mkSort lu) hx, hlinv₁⟩
      | const nm us =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨lus, hlus, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨_nmv, _hnmv, rfl⟩ := hd
        dsimp only at hgo
        rcases hg₁ : EStore.readbackLList st lmemo us with ⟨r₁, lmemo₁⟩
        rw [hg₁] at hgo
        obtain ⟨rfl, hlinv₁⟩ := readbackLList_spec us hlus hlinv hg₁
        dsimp only at hgo
        rw [hwf.readbackN_eq_denoteN, _hnmv] at hgo
        dsimp only at hgo
        injection hgo with h1 h2
        injection h2 with h2 h3
        subst h1; subst h2; subst h3
        exact ⟨⟨_, rfl, ExprC.WFc.mkConst _nmv lus, rfl⟩,
          hinv.insert (ExprC.WFc.mkConst _nmv lus) hx, hlinv₁⟩
      | lit l =>
        cases hd
        dsimp only at hgo
        injection hgo with h1 h2
        injection h2 with h2 h3
        subst h1; subst h2; subst h3
        exact ⟨⟨_, rfl, ExprC.WFc.mkLit l, rfl⟩,
          hinv.insert (ExprC.WFc.mkLit l) hx, hlinv⟩
      | fvar idx nm t =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨xt, ht, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨_nmv, _hnmv, rfl⟩ := hd
        have hlt : emlt t e := hc t (by simp [ENode.children])
        dsimp only at hgo
        rw [dif_pos hlt] at hgo
        rcases hgt : ofStoreGo st memo lmemo t with ⟨rt, memo₁, lmemo₁⟩
        obtain ⟨⟨ct, rfl, hwct, rfl⟩, hinv₁, hlinv₁⟩ :=
          ih t hlt ht hinv hlinv hgt
        rw [hgt] at hgo
        dsimp only at hgo
        rw [hwf.readbackN_eq_denoteN, _hnmv] at hgo
        dsimp only at hgo
        injection hgo with h1 h2
        injection h2 with h2 h3
        subst h1; subst h2; subst h3
        exact ⟨⟨_, rfl, ExprC.WFc.mkFVar idx _nmv hwct, rfl⟩,
          hinv₁.insert (ExprC.WFc.mkFVar idx _nmv hwct) hx, hlinv₁⟩
      | app f a =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨xf, hf, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨xa, ha, rfl⟩ := hd
        have hltf : emlt f e := hc f (by simp [ENode.children])
        have hlta : emlt a e := hc a (by simp [ENode.children])
        dsimp only at hgo
        rw [dif_pos ⟨hltf, hlta⟩] at hgo
        rcases hgf : ofStoreGo st memo lmemo f with ⟨rf, memo₁, lmemo₁⟩
        obtain ⟨⟨cf, rfl, hwcf, rfl⟩, hinv₁, hlinv₁⟩ :=
          ih f hltf hf hinv hlinv hgf
        rcases hga : ofStoreGo st memo₁ lmemo₁ a with ⟨ra, memo₂, lmemo₂⟩
        obtain ⟨⟨ca, rfl, hwca, rfl⟩, hinv₂, hlinv₂⟩ :=
          ih a hlta ha hinv₁ hlinv₁ hga
        rw [hgf] at hgo
        dsimp only at hgo
        rw [hga] at hgo
        dsimp only at hgo
        injection hgo with h1 h2
        injection h2 with h2 h3
        subst h1; subst h2; subst h3
        exact ⟨⟨_, rfl, ExprC.WFc.mkApp hwcf hwca, rfl⟩,
          hinv₂.insert (ExprC.WFc.mkApp hwcf hwca) hx, hlinv₂⟩
      | lam nm t b m =>
        obtain ⟨bi, pw⟩ := m
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨xt, ht, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨xb, hb, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨bm, hbm', hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨_nmv, _hnmv, rfl⟩ := hd
        simp only [denoteBM, Option.some.injEq] at hbm'
        subst hbm'
        have hltt : emlt t e := hc t (by simp [ENode.children])
        have hltb : emlt b e := hc b (by simp [ENode.children])
        dsimp only at hgo
        rw [dif_pos ⟨hltt, hltb⟩] at hgo
        rcases hgt : ofStoreGo st memo lmemo t with ⟨rt, memo₁, lmemo₁⟩
        obtain ⟨⟨ct, rfl, hwct, rfl⟩, hinv₁, hlinv₁⟩ :=
          ih t hltt ht hinv hlinv hgt
        rcases hgb : ofStoreGo st memo₁ lmemo₁ b with ⟨rb, memo₂, lmemo₂⟩
        obtain ⟨⟨cb, rfl, hwcb, rfl⟩, hinv₂, hlinv₂⟩ :=
          ih b hltb hb hinv₁ hlinv₁ hgb
        rw [hgt] at hgo
        dsimp only at hgo
        rw [hgb] at hgo
        dsimp only at hgo
        rw [hwf.readbackN_eq_denoteN, _hnmv] at hgo
        dsimp only at hgo
        injection hgo with h1 h2
        injection h2 with h2 h3
        subst h1; subst h2; subst h3
        exact ⟨⟨_, rfl, ExprC.WFc.mkLam _nmv ⟨bi, pw⟩ hwct hwcb, rfl⟩,
          hinv₂.insert (ExprC.WFc.mkLam _nmv ⟨bi, pw⟩ hwct hwcb) hx, hlinv₂⟩
      | forallE nm t b m =>
        obtain ⟨bi, pw⟩ := m
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨xt, ht, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨xb, hb, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨bm, hbm', hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨_nmv, _hnmv, rfl⟩ := hd
        simp only [denoteBM, Option.some.injEq] at hbm'
        subst hbm'
        have hltt : emlt t e := hc t (by simp [ENode.children])
        have hltb : emlt b e := hc b (by simp [ENode.children])
        dsimp only at hgo
        rw [dif_pos ⟨hltt, hltb⟩] at hgo
        rcases hgt : ofStoreGo st memo lmemo t with ⟨rt, memo₁, lmemo₁⟩
        obtain ⟨⟨ct, rfl, hwct, rfl⟩, hinv₁, hlinv₁⟩ :=
          ih t hltt ht hinv hlinv hgt
        rcases hgb : ofStoreGo st memo₁ lmemo₁ b with ⟨rb, memo₂, lmemo₂⟩
        obtain ⟨⟨cb, rfl, hwcb, rfl⟩, hinv₂, hlinv₂⟩ :=
          ih b hltb hb hinv₁ hlinv₁ hgb
        rw [hgt] at hgo
        dsimp only at hgo
        rw [hgb] at hgo
        dsimp only at hgo
        rw [hwf.readbackN_eq_denoteN, _hnmv] at hgo
        dsimp only at hgo
        injection hgo with h1 h2
        injection h2 with h2 h3
        subst h1; subst h2; subst h3
        exact ⟨⟨_, rfl, ExprC.WFc.mkForallE _nmv ⟨bi, pw⟩ hwct hwcb, rfl⟩,
          hinv₂.insert (ExprC.WFc.mkForallE _nmv ⟨bi, pw⟩ hwct hwcb) hx,
          hlinv₂⟩
      | letE nm t v b =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨xt, ht, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨xv, hv, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨xb, hb, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨_nmv, _hnmv, rfl⟩ := hd
        have hltt : emlt t e := hc t (by simp [ENode.children])
        have hltv : emlt v e := hc v (by simp [ENode.children])
        have hltb : emlt b e := hc b (by simp [ENode.children])
        dsimp only at hgo
        rw [dif_pos ⟨hltt, hltv, hltb⟩] at hgo
        rcases hgt : ofStoreGo st memo lmemo t with ⟨rt, memo₁, lmemo₁⟩
        obtain ⟨⟨ct, rfl, hwct, rfl⟩, hinv₁, hlinv₁⟩ :=
          ih t hltt ht hinv hlinv hgt
        rcases hgv : ofStoreGo st memo₁ lmemo₁ v with ⟨rv, memo₂, lmemo₂⟩
        obtain ⟨⟨cv, rfl, hwcv, rfl⟩, hinv₂, hlinv₂⟩ :=
          ih v hltv hv hinv₁ hlinv₁ hgv
        rcases hgb : ofStoreGo st memo₂ lmemo₂ b with ⟨rb, memo₃, lmemo₃⟩
        obtain ⟨⟨cb, rfl, hwcb, rfl⟩, hinv₃, hlinv₃⟩ :=
          ih b hltb hb hinv₂ hlinv₂ hgb
        rw [hgt] at hgo
        dsimp only at hgo
        rw [hgv] at hgo
        dsimp only at hgo
        rw [hgb] at hgo
        dsimp only at hgo
        rw [hwf.readbackN_eq_denoteN, _hnmv] at hgo
        dsimp only at hgo
        injection hgo with h1 h2
        injection h2 with h2 h3
        subst h1; subst h2; subst h3
        exact ⟨⟨_, rfl, ExprC.WFc.mkLetE _nmv hwct hwcv hwcb, rfl⟩,
          hinv₃.insert (ExprC.WFc.mkLetE _nmv hwct hwcv hwcb) hx, hlinv₃⟩
      | proj s j e' =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨xe, he, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨_nmv, _hnmv, rfl⟩ := hd
        have hlt : emlt e' e := hc e' (by simp [ENode.children])
        dsimp only at hgo
        rw [dif_pos hlt] at hgo
        rcases hge : ofStoreGo st memo lmemo e' with ⟨re, memo₁, lmemo₁⟩
        obtain ⟨⟨ce, rfl, hwce, rfl⟩, hinv₁, hlinv₁⟩ :=
          ih e' hlt he hinv hlinv hge
        rw [hge] at hgo
        dsimp only at hgo
        rw [hwf.readbackN_eq_denoteN, _hnmv] at hgo
        dsimp only at hgo
        injection hgo with h1 h2
        injection h2 with h2 h3
        subst h1; subst h2; subst h3
        exact ⟨⟨_, rfl, ExprC.WFc.mkProj _nmv j hwce, rfl⟩,
          hinv₁.insert (ExprC.WFc.mkProj _nmv j hwce) hx, hlinv₁⟩

/-! ### The threaded conversion state

`declCOfP` threads one `OfStoreS` through the whole declaration list;
its invariant is the pair of the two memo invariants, so `ofStore`
consumes and re-establishes it. -/

/-- The threaded conversion state's invariant. -/
def OfStoreS.Inv (st : EStore) (s : OfStoreS) : Prop :=
  OfStoreInv st s.memo ∧ RLInv st s.lmemo

theorem OfStoreS.Inv.empty {st : EStore} : OfStoreS.Inv st {} :=
  ⟨OfStoreInv.empty, RLInv.empty⟩

open ExprC in
/-- **`ofStore` is correct on a well-formed parse arena** (the form
`declCOfP` consumes: the state invariant in, the converted node and the
state invariant out). -/
theorem ofStore_spec {st : EStore} (hwf : st.TWF) {s : OfStoreS} {e : EIdx}
    {x : Expr} (hs : OfStoreS.Inv st s) (hx : st.denoteT e = some x) :
    ∃ c, (ofStore st s e).1 = some c ∧ WFc c ∧ eraseC c = x ∧
      OfStoreS.Inv st (ofStore st s e).2 := by
  rcases hgo : ofStoreGo st s.memo s.lmemo e with ⟨r, memo', lmemo'⟩
  obtain ⟨⟨c, rfl, hwc, hec⟩, hinv', hlinv'⟩ :=
    ofStoreGo_spec hwf e hx hs.1 hs.2 hgo
  exact ⟨c, by rw [ofStore, hgo], hwc, hec, by rw [ofStore, hgo]; exact
    ⟨hinv', hlinv'⟩⟩

open ExprC in
/-- The canonical-store form: on `st.WF` the tier-aware denotation is
the structural one (`WF.denoteT_eq`), which is the denotation
`denoteDeclP` — the parsed-declaration layer the capstone consumes — is
stated against. -/
theorem ofStore_spec_denote {st : EStore} (hwf : st.WF) {s : OfStoreS}
    {e : EIdx} {x : Expr} (hs : OfStoreS.Inv st s)
    (hx : st.denote e = some x) :
    ∃ c, (ofStore st s e).1 = some c ∧ WFc c ∧ eraseC c = x ∧
      OfStoreS.Inv st (ofStore st s e).2 :=
  ofStore_spec hwf.toTWF hs (by rw [hwf.denoteT_eq]; exact hx)

end Setlec.Cached

module

public import Fragment.ModularInstance

@[expose] public section

/-!
# Comparing a challenge with a solution

A **challenge** is a module whose own declarations state what is
asked; its **holes** are the ones the solution must supply (Lean's
axioms and `sorry` declarations), stored as assumptions.  A
**solution** is an earlier module that declares the challenge's names.
The challenge is a module of the development validated by comparison
(`Compared`): its own environment is its context, assembled from the
views of its imports, among them the solution.  It reads each of its
own names from the solution, and every name it imports from the module
that declares it, its **home**.

* `compare_solves`: if the modules up to the challenge are valid, there
  is a compatible family of models in which the challenge gives every
  name the value of the module it reads it from, and every constant of
  the challenge's environment, every hole among them, has its type
  inhabited by that value.  For a hole, read from the solution, the
  inhabitant is the solution's value; for an imported name, its value
  is its home's.
* `Valid.redeclared_is_proof`: the home rule needs no check of its own.
  A view of a module other than the home that stores an imported name,
  without that module having the name in its own context (the module
  declares it itself), agrees only as a proof.
* `Expr.instL_rename`: renaming a constant's level parameters
  position by position changes none of its instances, so it changes
  none of its laws in a model, whose values are read off lists of
  levels by position.  The modules here compare at equal names.
-/

namespace Fragment

open SetLib IndLib

/-! ## Renaming level parameters -/

theorem Level.lookupLevel_rename : ∀ {ps ps' : List Name} {ls : List Level} {n : Name},
    ps'.Nodup → ps'.length = ps.length → ls.length = ps.length → n ∈ ps →
    ∃ q ∈ ps', Level.lookupLevel ps (ps'.map .param) n = .param q ∧
      Level.lookupLevel ps' ls q = Level.lookupLevel ps ls n
  | [], _, _, _, _, _, _, hn => by simp at hn
  | _ :: _, [], _, _, _, h, _, _ => by simp at h
  | _ :: _, _ :: _, [], _, _, _, h, _ => by simp at h
  | p :: ps, q :: ps', l :: ls, n, hnd, hl', hl, hn => by
    simp only [List.nodup_cons] at hnd
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl' hl
    by_cases hnp : n = p
    · subst hnp
      refine ⟨q, List.mem_cons_self .., ?_, ?_⟩ <;>
        simp [Level.lookupLevel]
    · have hb : (n == p) = false := beq_eq_false_iff_ne.mpr hnp
      have hn' : n ∈ ps := by
        rcases List.mem_cons.mp hn with h | h
        · exact absurd h hnp
        · exact h
      obtain ⟨q', hq', h1, h2⟩ := lookupLevel_rename (ls := ls) hnd.2 hl' hl hn'
      have hqq : (q' == q) = false := beq_eq_false_iff_ne.mpr fun h => hnd.1 (h ▸ hq')
      refine ⟨q', List.mem_cons_of_mem _ hq', ?_, ?_⟩
      · simp only [Level.lookupLevel, List.map_cons, List.zip_cons_cons, List.lookup, hb] at h1 ⊢
        exact h1
      · simp only [Level.lookupLevel, List.zip_cons_cons, List.lookup, hqq, hb] at h2 ⊢
        exact h2

theorem Level.subst_rename {ps ps' : List Name} {ls : List Level}
    (hnd : ps'.Nodup) (hl' : ps'.length = ps.length) (hl : ls.length = ps.length) :
    ∀ l : Level, l.paramsIn ps = true →
      Level.subst ps' ls (Level.subst ps (ps'.map .param) l) = Level.subst ps ls l
  | .zero, _ => rfl
  | .succ l, h => by
    simp only [Level.subst, Level.paramsIn] at h ⊢
    rw [subst_rename hnd hl' hl l h]
  | .max a b, h => by
    simp only [Level.subst, Level.paramsIn, Bool.and_eq_true] at h ⊢
    rw [subst_rename hnd hl' hl a h.1, subst_rename hnd hl' hl b h.2]
  | .imax a b, h => by
    simp only [Level.subst, Level.paramsIn, Bool.and_eq_true] at h ⊢
    rw [subst_rename hnd hl' hl a h.1, subst_rename hnd hl' hl b h.2]
  | .param n, h => by
    simp only [Level.paramsIn, List.contains_iff_mem] at h
    obtain ⟨q, -, h1, h2⟩ := Level.lookupLevel_rename (ls := ls) hnd hl' hl h
    simp only [Level.subst, h1]
    exact h2

/-- **Renaming level parameters changes no instance**: a term over the
level parameters `ps`, renamed position by position to the distinct
names `ps'`, has at `ps'` the instances it had at `ps`. -/
theorem Expr.instL_rename {ps ps' : List Name} {ls : List Level}
    (hnd : ps'.Nodup) (hl' : ps'.length = ps.length) (hl : ls.length = ps.length) :
    ∀ e : Expr, e.lparamsIn ps = true →
      (e.instL ps (ps'.map .param)).instL ps' ls = e.instL ps ls
  | .bvar _, _ => rfl
  | .sort u, h => by
    simp only [Expr.lparamsIn] at h
    simp only [Expr.instL_sort, Level.subst_rename hnd hl' hl u h]
  | .const c us, h => by
    simp only [Expr.lparamsIn, List.all_eq_true] at h
    simp only [Expr.instL_const, List.map_map, Expr.const.injEq, true_and]
    exact List.map_congr_left fun u hu => Level.subst_rename hnd hl' hl u (h u hu)
  | .app f a, h => by
    simp only [Expr.lparamsIn, Bool.and_eq_true] at h
    simp only [Expr.instL_app, instL_rename hnd hl' hl f h.1, instL_rename hnd hl' hl a h.2]
  | .lam A b, h => by
    simp only [Expr.lparamsIn, Bool.and_eq_true] at h
    simp only [Expr.instL_lam, instL_rename hnd hl' hl A h.1, instL_rename hnd hl' hl b h.2]
  | .pi A B, h => by
    simp only [Expr.lparamsIn, Bool.and_eq_true] at h
    simp only [Expr.instL_pi, instL_rename hnd hl' hl A h.1, instL_rename hnd hl' hl B h.2]
  | .letE T v b, h => by
    simp only [Expr.lparamsIn, Bool.and_eq_true] at h
    simp only [Expr.instL_letE, instL_rename hnd hl' hl T h.1.1, instL_rename hnd hl' hl v h.1.2,
      instL_rename hnd hl' hl b h.2]

/-! ## The home rule -/

universe u

variable [LevelOracle]

/-- **A copy at a module other than the home agrees only as a proof**,
unless that module reads the name itself: a view of module `j` that
stores a name `n` the validated module `i` reads from another module,
where `n` is not in `j`'s context (`j` declares it), is a proof at `n`,
as is every copy of the module `n` is read from. -/
theorem Valid.redeclared_is_proof {dev : Nat → Module} {i : Nat} (hv : Valid dev i)
    {n : Name} (hn : ((dev i).context.find? n).isSome = true) {x : Nat × Env}
    (hx : x ∈ sources dev i) (hs : (x.2.find? n).isSome = true)
    (hne : x.1 ≠ (dev i).src n) (hctx : ((dev x.1).context.find? n).isSome = false) :
    ProofSide dev i n x ∧
      ∀ y ∈ sources dev i, y.1 = (dev i).src n → (y.2.find? n).isSome = true →
        ProofSide dev i n y := by
  rcases (hv.importOk.reads.2 n hn).agree x hx hs with h | ⟨h, -⟩ | h
  · exact absurd h hne
  · rw [hctx] at h; cases h
  · exact h

/-! ## The theorem -/

variable {V : Type u} [IndLib V]

variable (V) in
/-- **An accepted comparison solves the challenge.**  If the modules up
to the challenge `c` are valid, there is a compatible family of models,
one of each module's own environment, in which the challenge gives
every name of its context the value of the module it reads the name
from, and every constant of the challenge's environment has its type
inhabited, at every correctly sized level list, by that module's
value: for a hole, read from the solution, the solution's value. -/
theorem compare_solves (dev : Nat → Module) (c : Nat) (h : ∀ j ≤ c, Valid dev j)
    (hc : Compared dev c) :
    ∃ m : (i : Nat) → i < c + 1 → BlockModel V (dev i).own,
      (∀ j (hj : j < c + 1) n, ((dev j).context.find? n).isSome = true →
        ∃ h : (dev j).src n < c + 1, (m j hj).M n = (m ((dev j).src n) h).M n) ∧
      ∀ n ci, (dev c).own.find? n = some ci →
        ∃ h : (dev c).src n < c + 1,
          ∀ (φ : Name → Nat) (ρ : Nat → V) (ls : List Level), ls.length = ci.lparams.length →
            (m ((dev c).src n) h).M n (ls.map (Level.eval φ)) ∈ˢ
              interp (m c (Nat.lt_succ_self c)).M φ ρ (ci.type.instL ci.lparams ls) := by
  obtain ⟨m, hcomp, -⟩ := modular V dev (c + 1) fun j hj => h j (Nat.le_of_lt_succ hj)
  refine ⟨m, hcomp, fun n ci hf => ?_⟩
  have hn : ((dev c).context.find? n).isSome = true := by
    rw [← hc.own, hf]; rfl
  obtain ⟨hs, he⟩ := hcomp c (Nat.lt_succ_self c) n hn
  refine ⟨hs, fun φ ρ ls hls => ?_⟩
  rw [← he]
  exact ((m c (Nat.lt_succ_self c)).type_ok n ci hf φ ρ ls hls).2.2

end Fragment

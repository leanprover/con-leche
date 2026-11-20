module

public import Fragment.ModularInstance

@[expose] public section

/-!
# Comparing a challenge with a solution

A **challenge** states what is asked; its **holes** are its assumptions
(Lean's axioms, and the declarations whose value uses `sorry`, read as
the assumptions of their statements).  A **solution** is a second,
checked environment.

**Justified assumptions.**  The challenge is checked like any input,
except that a hole may be added to its environment when the solution
justifies it: the solution stores the hole's name with the same
statement, up to the names of the level parameters, and the two models
agree on every constant the statement reads.  The model of the
challenge then takes the solution model's value at the hole.

* `denote_agree`: two assignments that agree on every constant a term
  reads give it the same denotation, and make it well-denoted alike.
* `EnvModel.extend_stmt`: an environment model extends to a fresh
  statement-kind constant whose laws hold at a given set.
* `install_justified`: a model of the challenge's environment extends
  to a justified hole, with the solution model's value at it.
  `install_shared`: likewise for a constant the two environments store
  alike, whose type and value read only constants on which the models
  agree.  Together these keep the models in agreement on the shared
  constants along the challenge's check.
* `Expr.instL_rename`: renaming a constant's level parameters
  position by position changes none of its instances, so it changes
  none of its laws in a model, whose values are read off lists of
  levels by position.

**The module comparison.**  The challenge may instead be a module of a
development validated by comparison (`Compared`): its own environment
is its context, assembled from the views of its imports, among them
the solution.  It reads each of its own names from the solution, and
every name it imports from the module that declares it, its **home**.

* `compare_solves`: if the modules up to the challenge are valid, there
  is a compatible family of models in which every constant of the
  challenge's environment, every hole among them, has its type
  inhabited by the value of the module it is read from.
* `Valid.redeclared_is_proof`: the home rule needs no check of its own.
  A view of a module other than the home that stores an imported name,
  without that module having the name in its own context (the module
  declares it itself), agrees only as a proof.
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

/-! ## Justified assumptions -/

universe u

section Justified

variable {V : Type u} [IndLib V]

/-- **Denotation reads only the constants a term reads**: two
assignments that agree on them give the term the same set, and make it
well-denoted alike. -/
theorem denote_agree {M M' : Name → List Nat → V} {e : Expr}
    (h : ∀ c ∈ e.consts, ∀ ls, M c ls = M' c ls) (φ : Name → Nat) (ρ : Nat → V) :
    interp M φ ρ e = interp M' φ ρ e ∧ (WellDenoted M φ ρ e ↔ WellDenoted M' φ ρ e) :=
  ⟨interp_consts h, WellDenoted_consts h⟩

theorem ConstInfo.IsStmt.not_recursor {ci : ConstInfo} (hk : ci.IsStmt)
    {nP nM nMin nI : Nat} {rules : List RecRule} : ci.kind ≠ .recursor nP nM nMin nI rules := by
  rcases hk with h | ⟨v, h⟩ <;> rw [h] <;> exact fun h' => by cases h'

theorem ConstInfo.IsStmt.not_induct {ci : ConstInfo} (hk : ci.IsStmt)
    {nP nI : Nat} {cs : List Name} {S : IndSpec} : ci.kind ≠ .induct nP nI cs S := by
  rcases hk with h | ⟨v, h⟩ <;> rw [h] <;> exact fun h' => by cases h'

/-- **A model extends to a fresh statement at a given set.**  A fresh
constant of a statement kind (an assumption or a definition), whose
type and value are in scope of a closed environment, is added with the
set `A` wherever `A` satisfies its typing and unfolding laws in the old
model; every stored constant keeps its set. -/
theorem EnvModel.extend_stmt {E : Env} (hs : Env.Scoped E) (m : EnvModel V E) {a : Name}
    {ci : ConstInfo} (hfresh : E.find? a = none) (hk : ci.IsStmt)
    (hty : Expr.Scoped E ci.lparams 0 ci.type)
    (hvs : ∀ v, ci.value? = some v → Expr.Scoped E ci.lparams 0 v) (A : List Nat → V)
    (htype : ∀ (φ : Name → Nat) (ρ : Nat → V) (ls : List Level), ls.length = ci.lparams.length →
      WellDenoted m.M φ ρ (ci.type.instL ci.lparams ls) ∧
      IsTy (interp m.M φ ρ (ci.type.instL ci.lparams ls)) ∧
      A (ls.map (Level.eval φ)) ∈ˢ interp m.M φ ρ (ci.type.instL ci.lparams ls))
    (hunfold : ∀ v, ci.value? = some v →
      ∀ (φ : Name → Nat) (ρ : Nat → V) (ls : List Level), ls.length = ci.lparams.length →
        WellDenoted m.M φ ρ (v.instL ci.lparams ls) ∧
        interp m.M φ ρ (v.instL ci.lparams ls) = A (ls.map (Level.eval φ))) :
    ∃ m' : EnvModel V (E.add a ci), (∀ n, (E.find? n).isSome → ∀ ls, m'.M n ls = m.M n ls) ∧
      ∀ ls, m'.M a ls = A ls := by
  obtain ⟨M', hM'a, hM'n⟩ : ∃ M' : Name → List Nat → V,
      (∀ ls, M' a ls = A ls) ∧ (∀ n, n ≠ a → ∀ ls, M' n ls = m.M n ls) :=
    ⟨fun n ls => if n = a then A ls else m.M n ls, fun ls => by simp,
      fun n hn ls => by simp [hn]⟩
  have hM' : ∀ n, (E.find? n).isSome → ∀ ls, m.M n ls = M' n ls :=
    fun n hn ls => (hM'n n (Env.ne_of_isSome_find? hn hfresh) ls).symm
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : EnvModel V E, m₀.M = M' := ⟨m.transport hs M' hM', rfl⟩
  refine ⟨{ M := M', type_ok := ?_, unfold := ?_, rec_rules := ?_,
              rec_rules_nested := ?_, ind_fib := ?_, rec_rules_slot := ?_, rec_rules_k := ?_ },
    fun n hn ls => hM'n n (Env.ne_of_isSome_find? hn hfresh) ls, hM'a⟩
  · -- `type_ok`
    intro n ci' hfind φ ρ ls hlen
    rw [Env.find?_add] at hfind
    split at hfind
    · rename_i h
      cases hfind
      subst h
      have hc := consts_agree hty hM' ls
      have := htype φ ρ ls hlen
      rwa [WellDenoted_consts hc, interp_consts hc, ← hM'a] at this
    · have := m₀.type_ok n ci' hfind φ ρ ls hlen
      rwa [hm₀] at this
  · -- `unfold`
    intro n ci' v hfind hv φ ρ ls hlen
    rw [Env.find?_add] at hfind
    split at hfind
    · rename_i h
      cases hfind
      subst h
      have hc := consts_agree (hvs v hv) hM' ls
      have := hunfold v hv φ ρ ls hlen
      rwa [WellDenoted_consts hc, interp_consts hc, ← hM'a] at this
    · have := m₀.unfold n ci' v hfind hv φ ρ ls hlen
      rwa [hm₀] at this
  · -- `rec_rules`: the new constant is no recursor
    intro n ci' nP nM nMin nI rules hfind hkr rl hrl hinst cij hcij
    rw [Env.find?_add] at hfind
    split at hfind
    · cases hfind
      exact absurd hkr hk.not_recursor
    · have hctor := ((hs n ci' hfind).2.2 nP nM nMin nI rules hkr rl hrl).2
      rw [Env.find?_add_of_ne E ci (Env.ne_of_isSome_find? hctor hfresh)] at hcij
      have := m₀.rec_rules n ci' nP nM nMin nI rules hfind hkr rl hrl hinst cij hcij
      rwa [hm₀] at this
  · -- `rec_rules_nested`: likewise
    intro n ci' nP nM nMin nI rules hfind hkr rl hrl lvs pinst hinst cij I nPc nf hcij hcijk
    rw [Env.find?_add] at hfind
    split at hfind
    · cases hfind
      exact absurd hkr hk.not_recursor
    · have hctor := ((hs n ci' hfind).2.2 nP nM nMin nI rules hkr rl hrl).2
      rw [Env.find?_add_of_ne E ci (Env.ne_of_isSome_find? hctor hfresh)] at hcij
      have := m₀.rec_rules_nested n ci' nP nM nMin nI rules hfind hkr rl hrl lvs pinst hinst cij I
        nPc nf hcij hcijk
      rwa [hm₀] at this
  · -- `ind_fib`: the new constant is no type former
    intro n ci' nP nI cs S' hfind hki
    rw [Env.find?_add] at hfind
    split at hfind
    · cases hfind
      exact absurd hki hk.not_induct
    · have := m₀.ind_fib n ci' nP nI cs S' hfind hki
      rwa [hm₀] at this
  · -- `rec_rules_slot`: likewise
    intro n ci' nP nM nMin nI rules hfind hkr rl hrl cij hcij
    rw [Env.find?_add] at hfind
    split at hfind
    · cases hfind
      exact absurd hkr hk.not_recursor
    · have hctor := ((hs n ci' hfind).2.2 nP nM nMin nI rules hkr rl hrl).2
      rw [Env.find?_add_of_ne E ci (Env.ne_of_isSome_find? hctor hfresh)] at hcij
      have := m₀.rec_rules_slot n ci' nP nM nMin nI rules hfind hkr rl hrl cij hcij
      rwa [hm₀] at this
  · -- `rec_rules_k`: the new constant is no recursor
    intro n ci' nP nM nMin nI rules hfind hkr rl hrl hkk
    rw [Env.find?_add] at hfind
    split at hfind
    · cases hfind
      exact absurd hkr hk.not_recursor
    · have := m₀.rec_rules_k n ci' nP nM nMin nI rules hfind hkr rl hrl hkk
      rwa [hm₀] at this

/-- **A justified hole takes the solution's value.**  Let the
challenge's environment `E` be closed, with a model `m`, and let `a` be
a fresh hole: an assumption `ci` whose type is in scope of `E`.  Let
the solution's environment `ES`, with a model `mS`, store `a` as `ciS`
of any kind, whose type renamed to `ci`'s level parameters, position
by position, is `ci`'s type.  If `m` and `mS` agree on every constant
the hole's type reads, then `m` extends to a model of `E` with the
hole, which keeps every stored constant's set and gives the hole the
solution model's set. -/
theorem install_justified {E ES : Env} (hs : Env.Scoped E) (m : EnvModel V E)
    (mS : EnvModel V ES) {a : Name} {ci ciS : ConstInfo}
    (hfresh : E.find? a = none) (hk : ci.kind = .assumed)
    (hty : Expr.Scoped E ci.lparams 0 ci.type)
    (hS : ES.find? a = some ciS) (hnd : ci.lparams.Nodup)
    (hlen : ci.lparams.length = ciS.lparams.length) (hSty : ciS.type.lparamsIn ciS.lparams = true)
    (hren : ci.type = ciS.type.instL ciS.lparams (ci.lparams.map .param))
    (hagree : ∀ d ∈ ci.type.consts, ∀ ls, m.M d ls = mS.M d ls) :
    ∃ m' : EnvModel V (E.add a ci), (∀ n, (E.find? n).isSome → ∀ ls, m'.M n ls = m.M n ls) ∧
      ∀ ls, m'.M a ls = mS.M a ls := by
  refine m.extend_stmt hs hfresh (Or.inl hk) hty
    (fun v hv => by simp [ConstInfo.value?, hk, ConstKind.value?] at hv) (mS.M a)
    (fun φ ρ ls hl => ?_)
    (fun v hv => by simp [ConstInfo.value?, hk, ConstKind.value?] at hv)
  have hl' : ls.length = ciS.lparams.length := hl.trans hlen
  have hinst : ci.type.instL ci.lparams ls = ciS.type.instL ciS.lparams ls := by
    rw [hren]
    exact Expr.instL_rename hnd hlen hl' ciS.type hSty
  have hc : ∀ d ∈ (ciS.type.instL ciS.lparams ls).consts, ∀ ls', m.M d ls' = mS.M d ls' := by
    intro d hd
    apply hagree
    rw [hren, Expr.consts_instL]
    rwa [Expr.consts_instL] at hd
  obtain ⟨hw, hT, hmem⟩ := mS.type_ok a ciS hS φ ρ ls hl'
  have hd := denote_agree hc φ ρ
  rw [hinst, hd.1, hd.2]
  exact ⟨hw, hT, hmem⟩

/-- **A shared constant takes the solution's value.**  Let the
challenge's environment `E` be closed, with a model `m`, and let the
solution's environment `ES`, with a model `mS`, store a fresh name `a`
as the statement-kind constant `ci`, whose type and value are in scope
of `E`.  If `m` and `mS` agree on every constant the type and the value
read, then `m` extends to a model of `E` with `ci`, which keeps every
stored constant's set and gives `a` the solution model's set. -/
theorem install_shared {E ES : Env} (hs : Env.Scoped E) (m : EnvModel V E)
    (mS : EnvModel V ES) {a : Name} {ci : ConstInfo}
    (hfresh : E.find? a = none) (hk : ci.IsStmt)
    (hty : Expr.Scoped E ci.lparams 0 ci.type)
    (hvs : ∀ v, ci.value? = some v → Expr.Scoped E ci.lparams 0 v)
    (hS : ES.find? a = some ci)
    (hagree : ∀ d, (d ∈ ci.type.consts ∨ ∃ v, ci.value? = some v ∧ d ∈ v.consts) →
      ∀ ls, m.M d ls = mS.M d ls) :
    ∃ m' : EnvModel V (E.add a ci), (∀ n, (E.find? n).isSome → ∀ ls, m'.M n ls = m.M n ls) ∧
      ∀ ls, m'.M a ls = mS.M a ls := by
  refine m.extend_stmt hs hfresh hk hty hvs (mS.M a) (fun φ ρ ls hl => ?_)
    (fun v hv φ ρ ls hl => ?_)
  · have hc : ∀ d ∈ (ci.type.instL ci.lparams ls).consts, ∀ ls', m.M d ls' = mS.M d ls' := by
      intro d hd
      rw [Expr.consts_instL] at hd
      exact hagree d (Or.inl hd)
    have hd := denote_agree hc φ ρ
    rw [hd.1, hd.2]
    exact mS.type_ok a ci hS φ ρ ls hl
  · have hc : ∀ d ∈ (v.instL ci.lparams ls).consts, ∀ ls', m.M d ls' = mS.M d ls' := by
      intro d hd
      rw [Expr.consts_instL] at hd
      exact hagree d (Or.inr ⟨v, hv, hd⟩)
    have hd := denote_agree hc φ ρ
    rw [hd.1, hd.2]
    exact mS.unfold a ci v hS hv φ ρ ls hl

end Justified

/-! ## The home rule -/

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

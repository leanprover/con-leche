module

public import Fragment.ModularInstance

@[expose] public section

/-!
# Comparing a challenge with a solution

A **challenge** states what is asked; its **holes** are its assumptions
(`Decl.hole`: Lean's axioms, and the declarations whose value uses
`sorry`, read as the assumptions of their statements).  A **solution**
is a second, checked list of declarations.

**Justified assumptions.**  The challenge is checked like any input
(`ChallengeChecks`), except that a hole is accepted when the solution
justifies it (`Justified`): its name lies in a set of names **shared**
between the two environments (`Shared`) — each stored by the solution,
and by the challenge either with the same entry or as an assumption of
the solution's type with its level parameters renamed position by
position, everything its type and value read shared again.  The
theorem (`solution_model_exists`) is over the input: the challenge has
a model of its constants.  The proof builds the challenge's model
along its check, agreeing with the solution's on the shared names: a
justified hole and a shared constant take the solution model's value.

* `denote_agree`: two assignments that agree on every constant a term
  reads give it the same denotation, and make it well-denoted alike.
* `EnvModel.extend_stmt`: an environment model extends to a fresh
  statement-kind constant whose laws hold at a given set.
* `install_justified`: a model of the challenge's environment extends
  to a justified hole, with the solution model's value at it.
  `install_shared`: likewise for a constant the two environments store
  alike, whose type and value read only constants on which the models
  agree.  Together these keep the models in agreement on the shared
  constants along the challenge's check (`step_shared`,
  `ChallengeChecks.model`).
* `Expr.instL_rename`: renaming a constant's level parameters
  position by position changes none of its instances, so it changes
  none of its laws in a model, whose values are read off lists of
  levels by position.

**The module comparison.**  The challenge may instead be a module of
a development, which passes the local checks like any other module
(`LocalOk`).  It imports the solution besides its own imports, so its
context is assembled from the views of both, every two copies of a
name agreeing.  A declaration of the challenge whose name a view stores
is a **copy**: it is not one of the module's declarations, and its name
is read into the context like any imported name, from the module the
context reads it from.  A copy states what that module's constant
states, up to the names of the level parameters.  Every other
declaration of the challenge is its own, and is checked.

* `Checks.find?_context` (`ModularModel.lean`): an entry of the
  context is an entry of the module's own environment.
* `compare_solves`: if the modules up to the challenge pass their local
  checks, every module has a model of its own constants, the models
  agree on every name a module sees as another's (`Sees`), and every
  entry of the challenge's context holds in the challenge's model as a
  copy (`ConstInfo.copyAt`): renamed to distinct level parameters, an
  assumption by its statement, a definition with its value.
* `LocalOk.redeclared_is_proof`: a view of a module other than the one
  a name is read from, which stores the name without that module
  having it in its context (the module declares it itself), agrees
  only as a proof.  So a solution that declares a name the challenge
  imports, other than as a proof, fails the agreement of copies.
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

/-! ## The challenge check -/

section Challenge

variable {V : Type u} [IndLib V] [LevelOracle]

/-- **A shared set of names** between the challenge's environment `EC`
and the solution's `ES`: for every name `d` of the set, `EC` stores a
definition or an assumption at `d` and `ES` stores `d`, and either the
two entries are the same, or `EC`'s is an assumption whose type is
`ES`'s type with `ES`'s level parameters renamed, position by position,
to `EC`'s distinct ones; and every constant the type or the value of
`EC`'s entry reads is in the set again. -/
def Shared (EC ES : Env) (Sh : Name → Prop) : Prop :=
  ∀ d, Sh d → ∃ ci ciS, EC.find? d = some ci ∧ ES.find? d = some ciS ∧ ci.IsStmt ∧
    (ci = ciS ∨ (ci.kind = .assumed ∧ ci.lparams.Nodup ∧ ci.lparams.length = ciS.lparams.length ∧
      ci.type = ciS.type.instL ciS.lparams (ci.lparams.map .param))) ∧
    (∀ c ∈ ci.type.consts, Sh c) ∧ (∀ v, ci.value? = some v → ∀ c ∈ v.consts, Sh c)

/-- **A hole is justified** by the solution when its name lies in a
shared set. -/
def Justified (EC ES : Env) (n : Name) : Prop := ∃ Sh, Shared EC ES Sh ∧ Sh n

/-- **The challenge check**: the challenge's declarations checked one
after another, as `Checks` does, except that a hole (`Decl.hole`) is
accepted when the solution's environment `ES` justifies it in the
challenge's final environment `EC` — its name fresh and its type in
scope. -/
inductive ChallengeChecks (ES EC : Env) : Env → List Decl → Prop
  | nil {E : Env} : ChallengeChecks ES EC E []
  | cons {E : Env} {d : Decl} {ds : List Decl} : d.Ok E → ChallengeChecks ES EC (d.apply E) ds →
      ChallengeChecks ES EC E (d :: ds)
  | hole {E : Env} {c : Name} {ps : List Name} {T : Expr} {ds : List Decl} :
      E.find? c = none → Expr.Scoped E ps 0 T → Justified EC ES c →
      ChallengeChecks ES EC ((Decl.hole c ps T).apply E) ds →
      ChallengeChecks ES EC E (.hole c ps T :: ds)

omit [IndLib V] [LevelOracle] in
/-- The union of all shared sets is shared. -/
theorem Shared.union {EC ES : Env} : Shared EC ES (Justified EC ES) := by
  intro d ⟨Sh, hSh, hd⟩
  obtain ⟨ci, ciS, h1, h2, h3, h4, h5, h6⟩ := hSh d hd
  exact ⟨ci, ciS, h1, h2, h3, h4, fun c hc => ⟨Sh, hSh, h5 c hc⟩,
    fun v hv c hc => ⟨Sh, hSh, h6 v hv c hc⟩⟩

omit [IndLib V] in
/-- The challenge check stores only fresh names. -/
theorem ChallengeChecks.find?_context {ES EC E : Env} {ds : List Decl}
    (hc : ChallengeChecks ES EC E ds) {n : Name} {ci : ConstInfo} (h : E.find? n = some ci) :
    (applyAll ds E).find? n = some ci := by
  induction hc with
  | nil => exact h
  | @cons E d ds hd _ ih =>
    apply ih
    rw [Decl.apply_eq]
    cases hl : d.stores.lookup n with
    | none => simpa only [Env.find?, lookup_append_of_none hl] using h
    | some e =>
      have hm : n ∈ d.names := (Decl.mem_names_iff d n).mpr ⟨e, key_of_lookup hl⟩
      rw [hd.fresh n hm] at h; cases h
  | @hole E c ps T ds hf _ _ _ ih =>
    apply ih
    show (E.add c _).find? n = some ci
    rw [Env.find?_add]
    split
    · rename_i h'; subst h'; rw [hf] at h; cases h
    · exact h

omit [IndLib V] in
theorem ChallengeChecks.find?_of_stores {ES EC E : Env} {ds : List Decl}
    (hc : ChallengeChecks ES EC E ds) {d : Decl} {n : Name} {ci : ConstInfo} (hd : d ∈ ds)
    (hm : (n, ci) ∈ d.stores) : (applyAll ds E).find? n = some ci := by
  induction hc with
  | nil => cases hd
  | @cons E d' ds hd' hc' ih =>
    rcases List.mem_cons.mp hd with rfl | hd
    · apply hc'.find?_context
      rw [Decl.apply_eq]
      exact lookup_append_of_some (lookup_of_mem_nodup hd'.keys_nodup hm)
    · exact ih hd
  | @hole E c ps T ds _ _ _ hc' ih =>
    rcases List.mem_cons.mp hd with rfl | hd
    · apply hc'.find?_context
      simp only [Decl.stores, Decl.apply, Env.add, Env.empty, List.mem_singleton,
        Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      simp [Decl.apply, Env.find?_add]
    · exact ih hd

omit [IndLib V] in
/-- A checked list keeps its environment closed. -/
theorem Checks.scoped {E : Env} {ds : List Decl} (hc : Checks E ds) (hs : Env.Scoped E) :
    Env.Scoped (applyAll ds E) := by
  induction hc with
  | nil => exact hs
  | @cons E d ds hd _ ih =>
    apply ih
    cases d with
    | defn c ci => exact hs.add_def hd
    | thm c ci v => exact hs.add_thm hd
    | ind S => exact hs.install_any hd
    | hole _ _ _ => exact hd.elim

/-- **A model extends to a fresh constant other than a type former**,
given a model of the environment with it that keeps every stored
constant's set: the block laws carry over. -/
def BlockModel.ofAdd {E : Env} (m : BlockModel V E) {c : Name} {ci : ConstInfo}
    (hfresh : E.find? c = none) (hk : ∀ nP nI cs S, ci.kind ≠ .induct nP nI cs S)
    (m' : EnvModel V (E.add c ci)) (hag : ∀ n, (E.find? n).isSome → ∀ ls, m'.M n ls = m.M n ls) :
    BlockModel V (E.add c ci) where
  toEnvModel := m'
  blocks := by
    intro K ci' nP nI cs spec hfind hkind
    rw [Env.find?_add] at hfind
    split at hfind
    · cases hfind; exact absurd hkind (hk nP nI cs spec)
    · exact spec.BlockLaw_add (spec.BlockLaw_transport (fun n hn ls => (hag n hn ls).symm)
        (m.blocks K ci' nP nI cs spec hfind hkind)) c ci hfresh

/-- **A checked declaration's own step**: a model of the environment
extends to the declaration's, keeping every stored constant's set, with
every stored constant holding. -/
theorem Decl.Ok.step {E : Env} {d : Decl} (hd : d.Ok E) (hs : Env.Scoped E) (m : BlockModel V E)
    (hh : Holds E m.M) : ∃ m₁ : BlockModel V (d.apply E),
      (∀ n, (E.find? n).isSome → ∀ ls, m₁.M n ls = m.M n ls) ∧ Holds (d.apply E) m₁.M := by
  have hone : ∀ (m₁ : BlockModel V (d.apply E)) (c : Name) (ci : ConstInfo),
      (∀ n, (E.find? n).isSome → ∀ ls, m₁.M n ls = m.M n ls) → d.stores = [(c, ci)] →
      ci.IsStmt → Holds (d.apply E) m₁.M := by
    intro m₁ c ci hag hst hk
    refine Holds.apply hs hh (fun n hn ls => (hag n hn ls).symm) fun n ci' hl => ?_
    rw [hst] at hl
    simp only [List.lookup] at hl
    split at hl
    · cases hl
      rename_i hnc
      have hnc' : n = c := beq_iff_eq.mp hnc
      subst hnc'
      refine m₁.toEnvModel.modelOf ?_ fun _ _ _ _ _ h => ?_
      · rw [Decl.apply_eq, hst]; simp [Env.find?]
      · rcases hk with h' | ⟨v, h'⟩ <;> rw [h'] at h <;> cases h
    · cases hl
  cases d with
  | defn c ci =>
    obtain ⟨m₁, hag, -⟩ := install_def' hs m hd
    obtain ⟨v, -, hk, -⟩ := hd.2.2.1
    exact ⟨m₁, hag, hone m₁ c ci hag rfl (.inr ⟨v, hk⟩)⟩
  | thm c ci v =>
    obtain ⟨m₁, hag, -⟩ := install_thm hs m hd
    exact ⟨m₁, hag, hone m₁ c ci hag rfl (.inl hd.1)⟩
  | ind S =>
    obtain ⟨m₁, hag, hnewS⟩ := install_ind_holds hs m hd
    exact ⟨m₁, hag, Holds.apply hs hh (fun n hn ls => (hag n hn ls).symm) hnewS⟩
  | hole _ _ _ => exact hd.elim

omit [LevelOracle] in
/-- **A shared statement takes the solution's set**: a fresh name of a
shared set, stored as a statement whose type and value are in scope,
extends a model agreeing with the solution's on the shared names
stored so far to one that agrees at the new name too. -/
theorem step_shared {ES EC E : Env} (mS : EnvModel V ES) (hSs : Env.Scoped ES)
    (hs : Env.Scoped E) (m : BlockModel V E) (hh : Holds E m.M)
    (hinv : ∀ d, Justified EC ES d → (E.find? d).isSome → m.M d = mS.M d)
    {c : Name} {ci : ConstInfo} (hfresh : E.find? c = none) (hk : ci.IsStmt)
    (hty : Expr.Scoped E ci.lparams 0 ci.type)
    (hvs : ∀ v, ci.value? = some v → Expr.Scoped E ci.lparams 0 v)
    (hEC : EC.find? c = some ci) (hJ : Justified EC ES c) :
    ∃ m₁ : BlockModel V (E.add c ci),
      (∀ n, (E.find? n).isSome → ∀ ls, m₁.M n ls = m.M n ls) ∧ (∀ ls, m₁.M c ls = mS.M c ls) ∧
      Holds (E.add c ci) m₁.M := by
  obtain ⟨ci', ciS, hEC', hS, -, hcase, hT, hV⟩ := Shared.union c hJ
  rw [hEC] at hEC'; cases hEC'
  have hag : ∀ d ∈ ci.type.consts, ∀ ls, m.M d ls = mS.M d ls := fun d hd ls => by
    rw [hinv d (hT d hd) (hty.2.1 d hd)]
  obtain ⟨m', hag', hc'⟩ : ∃ m' : EnvModel V (E.add c ci),
      (∀ n, (E.find? n).isSome → ∀ ls, m'.M n ls = m.M n ls) ∧ ∀ ls, m'.M c ls = mS.M c ls := by
    rcases hcase with rfl | ⟨hka, hnd, hlen, hren⟩
    · refine install_shared hs m.toEnvModel mS hfresh hk hty hvs hS fun d hd ls => ?_
      rcases hd with hd | ⟨v, hv, hd⟩
      · exact hag d hd ls
      · rw [hinv d (hV v hv d hd) ((hvs v hv).2.1 d hd)]
    · exact install_justified hs m.toEnvModel mS hfresh hka hty hS hnd hlen
        ((hSs c ciS hS).1.2.2) hren hag
  have hnk : ∀ nP nI cs S, ci.kind ≠ .induct nP nI cs S := fun _ _ _ _ h => by
    rcases hk with h' | ⟨v, h'⟩ <;> rw [h'] at h <;> cases h
  let m₁ := m.ofAdd hfresh hnk m' hag'
  refine ⟨m₁, hag', hc', ?_⟩
  have hsub : (E.add c ci) = (Decl.defn c ci).apply E := rfl
  intro n ci₀ hf
  rw [Env.find?_add] at hf
  split at hf
  · cases hf
    rename_i hn; subst hn
    exact m'.modelOf (by simp [Env.find?_add]) fun _ _ _ _ _ h => by
      rcases hk with h' | ⟨v, h'⟩ <;> rw [h'] at h <;> cases h
  · exact (hh n ci₀ hf).congr_env hs hf fun d hd ls => (hag' d hd ls).symm

/-- **The challenge's model, built along its check**: a model of the
environment, agreeing with the solution's on the shared names stored
so far, extends along the challenge check to a model of its end in
which every stored constant holds. -/
theorem ChallengeChecks.model {ES EC : Env} (mS : EnvModel V ES) (hSs : Env.Scoped ES)
    {E : Env} {ds : List Decl} (hc : ChallengeChecks ES EC E ds)
    (hEC : ∀ n ci, (applyAll ds E).find? n = some ci → EC.find? n = some ci) :
    Env.Scoped E → ∀ m : BlockModel V E, Holds E m.M →
      (∀ d, Justified EC ES d → (E.find? d).isSome → m.M d = mS.M d) →
      ∃ m' : BlockModel V (applyAll ds E), Holds (applyAll ds E) m'.M := by
  induction hc with
  | nil => intro _ m hh _; exact ⟨m, hh⟩
  | @cons E d ds hd hc' ih =>
    intro hs m hh hinv
    have hEC' : ∀ n ci, (d.apply E).find? n = some ci → EC.find? n = some ci :=
      fun n ci hf => hEC n ci (hc'.find?_context hf)
    -- the next model, agreeing with the solution's on the shared names
    obtain ⟨m₁, hh₁, hinv₁⟩ : ∃ m₁ : BlockModel V (d.apply E), Holds (d.apply E) m₁.M ∧
        ∀ x, Justified EC ES x → ((d.apply E).find? x).isSome → m₁.M x = mS.M x := by
      -- a statement at a shared name
      have hshared : ∀ (c : Name) (ci : ConstInfo), d.apply E = E.add c ci → E.find? c = none →
          ci.IsStmt → Expr.Scoped E ci.lparams 0 ci.type →
          (∀ v, ci.value? = some v → Expr.Scoped E ci.lparams 0 v) → Justified EC ES c →
          ∃ m₁ : BlockModel V (d.apply E), Holds (d.apply E) m₁.M ∧
            ∀ x, Justified EC ES x → ((d.apply E).find? x).isSome → m₁.M x = mS.M x := by
        intro c ci hap hfresh hk hty hvs hJ
        rw [hap] at hEC' ⊢
        obtain ⟨m₁, hag, hcS, hh₁⟩ := step_shared mS hSs hs m hh hinv hfresh hk hty hvs
          (hEC' c ci (by simp [Env.find?_add])) hJ
        refine ⟨m₁, hh₁, fun x hx hxs => ?_⟩
        by_cases hxc : x = c
        · subst hxc; exact funext hcS
        · have hxE : (E.find? x).isSome := by rwa [Env.find?_add, ite_eq_right hxc] at hxs
          exact (funext (hag x hxE)).trans (hinv x hx hxE)
      -- a declaration storing no shared name: its own step
      have hown : (∀ x, Justified EC ES x → ((d.apply E).find? x).isSome → (E.find? x).isSome) →
          ∃ m₁ : BlockModel V (d.apply E), Holds (d.apply E) m₁.M ∧
            ∀ x, Justified EC ES x → ((d.apply E).find? x).isSome → m₁.M x = mS.M x := by
        intro hno
        obtain ⟨m₁, hag, hh₁⟩ := hd.step hs m hh
        exact ⟨m₁, hh₁, fun x hx hxs => (funext (hag x (hno x hx hxs))).trans
          (hinv x hx (hno x hx hxs))⟩
      have hnew : ∀ x, ((d.apply E).find? x).isSome → ¬ (E.find? x).isSome →
          ∃ e, d.stores.lookup x = some e := by
        intro x hx hnx
        rw [Decl.apply_eq] at hx
        cases hl : d.stores.lookup x with
        | some e => exact ⟨e, rfl⟩
        | none =>
          simp only [Env.find?, lookup_append_of_none hl] at hx
          exact absurd hx hnx
      cases d with
      | defn c ci =>
        by_cases hJ : Justified EC ES c
        · obtain ⟨v, -, hk, -⟩ := hd.2.2.1
          exact hshared c ci rfl hd.1 (.inr ⟨v, hk⟩) hd.type_scoped
            (fun v hv => hd.value_scoped v (by
              simp only [ConstInfo.value?, ConstKind.value?] at hv; revert hv
              cases ci.kind <;> simp_all)) hJ
        · refine hown fun x hx hxs => ?_
          by_cases hnx : (E.find? x).isSome = true
          · exact hnx
          exfalso
          obtain ⟨e, hl⟩ := hnew x hxs hnx
          simp only [Decl.stores, Decl.apply, Env.add, Env.empty, List.lookup] at hl
          split at hl
          · rename_i h; rw [beq_iff_eq.mp h] at hx; exact hJ hx
          · cases hl
      | thm c ci v =>
        by_cases hJ : Justified EC ES c
        · exact hshared c ci rfl hd.2.1.1 (.inl hd.1) hd.2.1.type_scoped
            (fun v hv => by simp [ConstInfo.value?, hd.1, ConstKind.value?] at hv) hJ
        · refine hown fun x hx hxs => ?_
          by_cases hnx : (E.find? x).isSome = true
          · exact hnx
          exfalso
          obtain ⟨e, hl⟩ := hnew x hxs hnx
          simp only [Decl.stores, Decl.apply, Env.add, Env.empty, List.lookup] at hl
          split at hl
          · rename_i h; rw [beq_iff_eq.mp h] at hx; exact hJ hx
          · cases hl
      | ind S =>
        -- a block stores no statement, so none of its names is shared
        refine hown fun x hx hxs => ?_
        by_cases hnx : (E.find? x).isSome = true
        · exact hnx
        exfalso
        obtain ⟨e, hl⟩ := hnew x hxs hnx
        obtain ⟨ci, -, hECx, -, hst, -⟩ := Shared.union x hx
        have hf : ((Decl.ind S).apply E).find? x = some e := by
          rw [Decl.apply_eq]; exact lookup_append_of_some hl
        rw [hEC' x e hf] at hECx
        cases hECx
        exact ind_stores_not_stmt hl hst
      | hole _ _ _ => exact hd.elim
    have hs₁ : Env.Scoped (d.apply E) := by
      cases d with
      | defn c ci => exact hs.add_def hd
      | thm c ci v => exact hs.add_thm hd
      | ind S => exact hs.install_any hd
      | hole _ _ _ => exact hd.elim
    exact ih hEC hs₁ m₁ hh₁ hinv₁
  | @hole E c ps T ds hfresh hty hJ hc' ih =>
    intro hs m hh hinv
    have hEC' : ∀ n ci, ((Decl.hole c ps T).apply E).find? n = some ci → EC.find? n = some ci :=
      fun n ci hf => hEC n ci (hc'.find?_context hf)
    obtain ⟨m₁, hag, hcS, hh₁⟩ := step_shared (ci := ⟨ps, T, .assumed⟩) mS hSs hs m hh hinv hfresh
      (.inl rfl) hty (fun v hv => by simp [ConstInfo.value?, ConstKind.value?] at hv)
      (hEC' c _ (by simp [Decl.apply, Env.find?_add])) hJ
    have hs₁ : Env.Scoped ((Decl.hole c ps T).apply E) :=
      hs.add hfresh hty (fun v hv => by simp [ConstInfo.value?, ConstKind.value?] at hv)
        (fun _ _ _ _ _ h => by cases h)
    refine ih hEC hs₁ m₁ hh₁ fun x hx hxs => ?_
    by_cases hxc : x = c
    · subst hxc; exact funext hcS
    · have hxE : (E.find? x).isSome := by
        simpa [Decl.apply, Env.find?_add, hxc] using hxs
      exact (funext (hag x hxE)).trans (hinv x hx hxE)

variable (V) in
/-- **The main theorem, with a solution.**  A challenge whose holes the
solution's environment justifies, the solution itself accepted, has a
model of its constants, in any set theory with libraries.  The
statement does not mention the solution's model: the agreement on the
shared names is the proof's invariant.

Simplified relative to con-leche (`ConLeche/Model/Solution`): a shared
name is a definition or an assumption — the fragment does not share
inductive blocks, whose sets con-leche shows determined by what they
read — and the shared sets are read in the challenge's final
environment, where con-leche's check computes them along the fold. -/
theorem solution_model_exists {dsS dsC : List Decl} (hS : Checks Env.empty dsS)
    (hC : ChallengeChecks (applyAll dsS Env.empty) (applyAll dsC Env.empty) Env.empty dsC) :
    ∃ M : Name → List Nat → V, IsModel V M (constantsOf dsC) := by
  obtain ⟨mS, -, -, -⟩ := hS.blockModel Env.Scoped.empty (BlockModel.empty (V := V) fun _ _ => pt)
    (fun _ _ hf => by simp at hf) (Holds.empty _)
  obtain ⟨m, hh⟩ := hC.model mS.toEnvModel (hS.scoped Env.Scoped.empty) (fun _ _ h => h)
    Env.Scoped.empty (BlockModel.empty fun _ _ => pt) (Holds.empty _) (fun _ _ h => by simp at h)
  exact ⟨m.M, fun n ci ⟨d, hd, hm⟩ => hh n ci (hC.find?_of_stores hd hm)⟩

end Challenge

/-! ## The agreement of copies -/

variable [LevelOracle]

/-- **A copy at a module other than the one a name is read from agrees
only as a proof**, unless that module reads the name itself: a view of
module `j` that stores a name `n` the module `i` reads from another
module, where `n` is not in `j`'s context (`j` declares it), is a proof
at `n`, as is every copy of the module `n` is read from. -/
theorem LocalOk.redeclared_is_proof {dev : Nat → Module} {i : Nat} (hv : LocalOk dev i)
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

/-- **A copy of a constant at the level parameters `ps`**: its level
parameters renamed, position by position — an assumption by its
statement, a definition with its value renamed too; an inductive
block's constants are copied unchanged. -/
def ConstInfo.copyAt (ci : ConstInfo) (ps : List Name) : ConstInfo :=
  match ci.kind with
  | .defn v => ⟨ps, ci.type.instL ci.lparams (ps.map .param),
      .defn (v.instL ci.lparams (ps.map .param))⟩
  | .assumed => ⟨ps, ci.type.instL ci.lparams (ps.map .param), .assumed⟩
  | _ => ci

omit [LevelOracle] in
/-- A renamed term read at the renamed parameters' values is the term
read at the original ones. -/
theorem interp_rename {M : Name → List Nat → V} {lp ps : List Name} {vals : List Nat}
    (hnd : ps.Nodup) (hlen : ps.length = lp.length) (hv : vals.length = ps.length) {e : Expr}
    (he : e.lparamsIn lp = true) (ρ : Nat → V) :
    interp M (valOf ps vals) ρ (e.instL lp (ps.map .param)) = interp M (valOf lp vals) ρ e := by
  rw [interp_instL]
  refine interp_lparams he fun n hn => ?_
  obtain ⟨q, hq, h1, h2⟩ := Level.lookupLevel_rename (ls := vals.map Level.ofNat) hnd hlen
    (by simp [hv, hlen]) hn
  simp only [Level.substVal, h1, Level.eval_param]
  have e1 := valOf_map_eval (valOf ps vals) (ls := vals.map Level.ofNat) (by simp [hv]) hq
  have e2 := valOf_map_eval (valOf ps vals) (ls := vals.map Level.ofNat) (ps := lp)
    (by simp [hv, hlen]) hn
  rw [Level.map_eval_ofNat] at e1 e2
  rw [e1, e2]
  simp only [Level.substVal, h2]

omit [LevelOracle] in
/-- **A copy holds where the constant does.** -/
theorem ModelOf.copyAt {M : Name → List Nat → V} {n : Name} {ci : ConstInfo} (h : ModelOf M n ci)
    (hT : ci.type.lparamsIn ci.lparams = true)
    (hV : ∀ v, ci.value? = some v → v.lparamsIn ci.lparams = true)
    {ps : List Name} (hnd : ps.Nodup) (hlen : ps.length = ci.lparams.length) :
    ModelOf M n (ci.copyAt ps) := by
  obtain ⟨lp, T, k⟩ := ci
  cases k with
  | defn v =>
    intro vals hvals
    simp only [ConstInfo.copyAt] at hvals ⊢
    obtain ⟨hmem, hval⟩ := h vals (hvals.trans hlen)
    exact ⟨by rw [interp_rename hnd hlen hvals hT]; exact hmem,
      by rw [interp_rename hnd hlen hvals (hV v rfl)]; exact hval⟩
  | assumed =>
    intro vals hvals
    simp only [ConstInfo.copyAt] at hvals ⊢
    exact ⟨by rw [interp_rename hnd hlen hvals hT]; exact (h vals (hvals.trans hlen)).1, trivial⟩
  | _ => exact h

variable (V) in
/-- **An accepted comparison solves the challenge.**  If the modules up
to the challenge `c` pass their local checks, every module has a model
of its own declarations' constants, the models agree on every name a
module sees as another module's (`Sees`) — the challenge sees the
solution's names, so its copies take the solution's sets —, and every
entry of the challenge's context holds in the challenge's model as a
copy, at any distinct level parameters (`ConstInfo.copyAt`): a copy
of a statement by its statement, of a definition by its value too. -/
theorem compare_solves (dev : Nat → Module) (c : Nat) (h : ∀ j ≤ c, LocalOk dev j) :
    ∃ model : Nat → Name → List Nat → V,
      (∀ j ≤ c, IsModel V (model j) (constantsOf (dev j).decls)) ∧
      (∀ j ≤ c, ∀ n j', Sees dev j n j' → model j n = model j' n) ∧
      ∀ n ci ps, (dev c).context.find? n = some ci → ps.Nodup → ps.length = ci.lparams.length →
        ModelOf (model c) n (ci.copyAt ps) := by
  have h' : ∀ j < c + 1, LocalOk dev j := fun j hj => h j (Nat.le_of_lt_succ hj)
  obtain ⟨model, hh, hsees⟩ := modular_holds V dev (c + 1) h'
  refine ⟨model, fun j hj n ci ⟨d, hd, hm⟩ =>
      hh j (Nat.lt_succ_of_le hj) n ci ((h j hj).checks.find?_of_stores hd hm),
    fun j hj => hsees j (Nat.lt_succ_of_le hj), fun n ci ps hf hnd hlen => ?_⟩
  have hok := h c (Nat.le_refl c)
  have hsc := hok.importOk.reads.1.scoped n ci hf
  exact (hh c (Nat.lt_succ_self c) n ci (hok.checks.find?_context hf)).copyAt hsc.1.2.2
    (fun v hv => (hsc.2.1 v hv).2.2) hnd hlen

end Fragment

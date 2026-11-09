module

import ConLeche.Verify.EnvBound
import ConLeche.Verify.Level
public import ConLeche.Verify.Cached.SimC
import ConLeche.Verify.Cached.Grind
public import Std.WP

public section

/-!
# Effect specs for the cached checker's state wrappers (task #163, batch 5)

One `Std.WP` triple (`…_spec`) per `ConLeche/Cached/StateC.lean`
wrapper the walks call, stated over the program's own arguments (an
argument the program does not determine would stay a metavariable in
`vcgen`'s instantiation).

The pure wrappers are `CEff.pure` at the commutation spec (`OpsC.lean`)
of the underlying `Expr` operation.  The persistent memos — the
bulk-instantiation cache (`instListM`), the level memo (`isEquivLM`) and
the lazy stored-constant caches (`constTyAtM`/`constValAtM`/
`ruleRhsAtM`) — are proved by `vcgen` and `grind` from hit and insert
lemmas against the matching `CSOK` clause; a lazy cache's spec at a
stored entry (`…_spec_of_find`) is read at the walks' named lookups
(`constTyOf`, `constValAt?`, `ruleRhsOf`).  The memo keys are lawful
(`LawfulBEq`), so a colliding key is the inserted one
(`HashMap.insert_backed`, `SimC.lean`).
-/

set_option experimental.vcgen true

namespace ConLeche.Cached

open ConLeche
open Expr Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {eager : Bool}

variable {env : Env}

/-! ## The pure syntactic wrappers

Each a `pure` of the cached operation, so each triple is `CEff.pure` at
the operation's commutation spec (`OpsC.lean`), stated over the
program's own arguments. -/

section Effects

variable {s₀ : CState}

theorem inst1M_spec (hs : CSOK mode eager env s₀) (e v : Expr) (d : Nat) :
    ⦃fun s => s = s₀⦄ inst1M e v d
    ⦃fun r s' => CSOK mode eager env s' ∧ r = e.instantiate1 v d; ⊤⦄ :=
  CEff.triple (CEff.pure hs (by show _ = _; rw [instantiate1C_spec (d := d)]))

theorem instListRevM_spec (hs : CSOK mode eager env s₀) (e : Expr) (vs : Array Expr) (d : Nat) :
    ⦃fun s => s = s₀⦄ instListRevM e vs d
    ⦃fun r s' => CSOK mode eager env s' ∧ r = e.instantiateList vs.toList.reverse d; ⊤⦄ :=
  CEff.triple (CEff.pure hs (by show _ = _; rw [instantiateRev_spec (d := d)]))

theorem abstractRangeM_spec (hs : CSOK mode eager env s₀) (e : Expr) (d k : Nat) :
    ⦃fun s => s = s₀⦄ abstractRangeM e d k
    ⦃fun r s' => CSOK mode eager env s' ∧ r = e.abstractRange d k; ⊤⦄ :=
  CEff.triple (CEff.pure hs (by show _ = _; rw [abstractRangeC_spec (d := d) (k := k) (c := 0)]))

theorem piResidualM_spec (hs : CSOK mode eager env s₀) (e : Expr) (args : List Expr) :
    ⦃fun s => s = s₀⦄ piResidualM e args
    ⦃fun o s' => CSOK mode eager env s' ∧ o = piResidual e args; ⊤⦄ := by
  refine triple_iff_run.mpr fun o s' hr => ?_
  obtain ⟨hs', h⟩ := (CEff.pure hs (piResidual_spec (e := e) (args := args)) :
    CEff mode eager env s₀ (fun o => OptEr o (piResidual e args)) (piResidualM e args)) o s' hr
  refine ⟨hs', ?_⟩
  revert h
  cases o <;> cases piResidual e args <;> simp [OptEr]

end Effects

/-! ## The persistent level memos

`isEquivLM` restated with `get`/`set` (`isEquivLM_eq`) so that `vcgen`
splits its cascade; the `lsimpC` memo's entries are the spec values
(`LsimpOK`), so a memoized `simplify` is `simplify`, and `Level.isEquiv`
is the same cascade over the simplified forms (`isEquiv_cascade_eq`). -/

section LevelEffects

variable {s₀ : CState}

/-- The inlined `simplify`-with-memo step of `isEquivLM`. -/
def simplifyMemo (mp : Std.HashMap Level Level) (u : Level) :
    Level × Std.HashMap Level Level :=
  match mp[u]? with
  | some x => (x, mp)
  | none => let x := Level.simplify u; (x, mp.insert u x)

/-- Every entry of a `simplify` memo is the spec value. -/
def LsimpOK (mp : Std.HashMap Level Level) : Prop :=
  ∀ u v, mp[u]? = some v → v = Level.simplify u

theorem CSOK.lsimpOK {s : CState} (hs : CSOK mode eager env s) : LsimpOK s.lsimpC := hs.lsimp
grind_pattern [conleche_grind] CSOK.lsimpOK => CSOK mode eager env s, s.lsimpC

theorem LsimpOK.simplifyMemo_fst {mp : Std.HashMap Level Level} (h : LsimpOK mp) (u : Level) :
    (simplifyMemo mp u).1 = Level.simplify u := by
  unfold simplifyMemo
  cases hc : mp[u]? with
  | some x => exact h u x hc
  | none => rfl
grind_pattern [conleche_grind] LsimpOK.simplifyMemo_fst => LsimpOK mp, simplifyMemo mp u

theorem LsimpOK.simplifyMemo_snd {mp : Std.HashMap Level Level} (h : LsimpOK mp) (u : Level) :
    LsimpOK (simplifyMemo mp u).2 := by
  unfold simplifyMemo
  cases mp[u]? with
  | some x => exact h
  | none => exact HashMap.insert_backed (P := fun u v => v = Level.simplify u) h rfl
grind_pattern [conleche_grind] LsimpOK.simplifyMemo_snd => LsimpOK mp, simplifyMemo mp u

theorem CSOK.withLsimp {s : CState} (hs : CSOK mode eager env s) {mp : Std.HashMap Level Level}
    (hm : LsimpOK mp) : CSOK mode eager env { s with lsimpC := mp } :=
  { hs with lsimp := hm }

/-- Replace the `simplify` memo and insert a certified verdict. -/
theorem CSOK.withLsimpEqv {s : CState} (hs : CSOK mode eager env s) {mp : Std.HashMap Level Level}
    (hm : LsimpOK mp) {l r : Level} {b : Bool} (hb : Level.isEquiv l r = some b) :
    CSOK mode eager env { s with lsimpC := mp, eqvC := s.eqvC.insert (l, r) b } :=
  { hs with
    lsimp := hm
    eqv := fun l' r' => HashMap.insert_backed (P := fun k b => Level.isEquiv k.1 k.2 = some b)
      (i := (l, r)) (fun k v => hs.eqv k.1 k.2 v) hb (l', r') }

/-- An `isEquiv` cache hit is the spec verdict. -/
theorem CSOK.eqv_hit {s : CState} (hs : CSOK mode eager env s) {l r : Level}
    (hne : s.eqvC[(l, r)]? ≠ none) : s.eqvC[(l, r)]? = Level.isEquiv l r := by
  obtain ⟨b, hl⟩ := Option.ne_none_iff_exists'.mp hne
  rw [hl, hs.eqv l r b hl]
grind_pattern [conleche_grind] CSOK.eqv_hit => CSOK mode eager env s, s.eqvC[(l, r)]?

/-- `isEquivLM` with its state accesses as `get`/`set`. -/
theorem isEquivLM_eq (l r : Level) :
    isEquivLM l r =
      (if l == r then pure (some true) else do
        let s ← get
        match s.eqvC[(l, r)]? with
        | some b => pure (some b)
        | none =>
          let (ls, mp) := simplifyMemo s.lsimpC l
          let (rs, mp) := simplifyMemo mp r
          if ls == rs then
            set { s with lsimpC := mp, eqvC := s.eqvC.insert (l, r) true }
            pure (some true)
          else
            match Level.leqCore Level.defaultFuel ls rs 0 with
            | some false =>
              set { s with lsimpC := mp, eqvC := s.eqvC.insert (l, r) false }
              pure (some false)
            | some true =>
              match Level.leqCore Level.defaultFuel rs ls 0 with
              | some b =>
                set { s with lsimpC := mp, eqvC := s.eqvC.insert (l, r) b }
                pure (some b)
              | none =>
                set { s with lsimpC := mp }
                pure none
            | none =>
              set { s with lsimpC := mp }
              pure none) := by
  have h : isEquivLM l r =
      if l == r then pure (some true) else
      modifyGet fun s =>
        match s.eqvC[(l, r)]? with
        | some b => (some b, s)
        | none =>
          let (ls, mp) := simplifyMemo s.lsimpC l
          let (rs, mp) := simplifyMemo mp r
          if ls == rs then (some true, { s with lsimpC := mp, eqvC := s.eqvC.insert (l, r) true })
          else
            match Level.leqCore Level.defaultFuel ls rs 0 with
            | some false => (some false, { s with lsimpC := mp, eqvC := s.eqvC.insert (l, r) false })
            | some true =>
              match Level.leqCore Level.defaultFuel rs ls 0 with
              | some b => (some b, { s with lsimpC := mp, eqvC := s.eqvC.insert (l, r) b })
              | none => (none, { s with lsimpC := mp })
            | none => (none, { s with lsimpC := mp }) := rfl
  rw [h]
  split
  · rfl
  · funext s
    simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, set,
      modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure, Except.pure, Except.bind]
    cases h : s.eqvC[(l, r)]? with
    | some b => rfl
    | none =>
      simp only
      generalize simplifyMemo s.lsimpC l = p1
      generalize simplifyMemo p1.snd r = p2
      by_cases hc : (p1.fst == p2.fst) = true
      · simp only [hc, ↓reduceIte]; rfl
      · simp only [hc, ↓reduceIte, Bool.false_eq_true]
        cases Level.leqCore Level.defaultFuel p1.fst p2.fst 0 with
        | none => rfl
        | some b1 =>
          cases b1
          · rfl
          · cases Level.leqCore Level.defaultFuel p2.fst p1.fst 0 <;> rfl

/-- `Level.isEquiv` in the shape the cascade decides it. -/
theorem isEquiv_cascade_eq (l r : Level) :
    Level.isEquiv l r =
      if Level.simplify l = Level.simplify r then some true else
      match Level.leqCore Level.defaultFuel (Level.simplify l) (Level.simplify r) 0 with
      | none => none
      | some false => some false
      | some true => Level.leqCore Level.defaultFuel (Level.simplify r) (Level.simplify l) 0 := by
  rw [Level.isEquiv_eq_withoutPtr]
  split
  · rfl
  · simp only [Level.leq, Bind.bind, Option.bind]
    cases Level.leqCore Level.defaultFuel (Level.simplify l) (Level.simplify r) 0 with
    | none => rfl
    | some b1 => cases b1 <;> rfl

/-- The `isEquiv` result cache: a hit is certified by the `eqvC`
clause, a miss runs the spec's `simplify`/`leqCore` cascade through the
`lsimpC` memo. -/
theorem isEquivLM_spec (hs : CSOK mode eager env s₀) (l r : Level) :
    ⦃fun s => s = s₀⦄ isEquivLM l r
    ⦃fun ob s' => CSOK mode eager env s' ∧ ob = Level.isEquiv l r; ⊤⦄ := by
  sym only [conleche_grind, Level.isEquiv_of_beq, isEquiv_cascade_eq,
      CSOK.withLsimp, CSOK.withLsimpEqv] =>
    vcgen [isEquivLM_eq] <;> finish

/-- `Level.isEquivList`'s step as one `match`. -/
theorem isEquivList_cons (l r : Level) (ls rs : List Level) :
    Level.isEquivList (l :: ls) (r :: rs) =
      match Level.isEquiv l r with
      | none => none
      | some false => some false
      | some true => Level.isEquivList ls rs := by
  rw [Level.isEquivList]
  cases Level.isEquiv l r with
  | none => rfl
  | some b => cases b <;> rfl

/-- Pointwise `isEquivLM`. -/
theorem isEquivListLM_spec :
    ∀ {ls rs : List Level} {s₀ : CState}, CSOK mode eager env s₀ →
      ⦃fun s => s = s₀⦄ isEquivListLM ls rs
      ⦃fun ob s' => CSOK mode eager env s' ∧ ob = Level.isEquivList ls rs; ⊤⦄ := by
  intro ls
  induction ls with
  | nil =>
    intro rs
    cases rs with
    | nil =>
      intro _ _
      sym only [conleche_grind, Level.isEquivList] => vcgen [isEquivListLM] <;> finish
    | cons _ _ =>
      intro _ _
      sym only [conleche_grind, Level.isEquivList] => vcgen [isEquivListLM.eq_def] <;> finish
  | cons l ls ihL =>
    intro rs
    cases rs with
    | nil =>
      intro _ _
      sym only [conleche_grind, Level.isEquivList] => vcgen [isEquivListLM.eq_def] <;> finish
    | cons r rs =>
      intro _ hs
      sym only [conleche_grind, isEquivList_cons] =>
        vcgen [isEquivListLM, isEquivLM_spec hs, ihL] <;>
          finish

end LevelEffects

/-! ## The persistent bulk-instantiation memo

A hit is *exact*: the stored key is the query key (`Expr`, `List` and
the tuple are lawful), and the entry is the spec value by the `instC`
clause.  The overflow branch inserts into the empty table instead. -/

section InstMemo

variable {s₀ : CState}

/-- `instListM` with its state accesses as `get`/`set`. -/
theorem instListM_eq (e : Expr) (vs : List Expr) (d : Nat) :
    instListM e vs d =
      (if e.bvarB ≤ d then pure e else do
        let s ← get
        match s.instC[(e, vs, d)]? with
        | some r => pure r
        | none =>
          set { s with instC := ((if s.instC.size < instCCapC then s.instC else {}).insert
            (e, vs, d) (Expr.instantiateListC e vs d)) }
          pure (Expr.instantiateListC e vs d)) := by
  unfold instListM
  split
  · rfl
  · funext s
    simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, set,
      modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure, Except.pure, Except.bind]
    cases s.instC[(e, vs, d)]? <;> rfl

theorem CSOK.instC_hit {s : CState} (hs : CSOK mode eager env s) {e : Expr} {vs : List Expr}
    {d : Nat} (hne : s.instC[(e, vs, d)]? ≠ none) :
    s.instC[(e, vs, d)]? = some (e.instantiateList vs d) := by
  obtain ⟨r, hl⟩ := Option.ne_none_iff_exists'.mp hne
  rw [hl, hs.instC e vs d r hl]
grind_pattern [conleche_grind] CSOK.instC_hit => CSOK mode eager env s, s.instC[(e, vs, d)]?

/-- Inserting the computed instance into the (possibly emptied)
bulk-instantiation memo keeps the invariant. -/
theorem CSOK.instC_insert {s : CState} (hs : CSOK mode eager env s) (e : Expr) (vs : List Expr)
    (d : Nat) :
    CSOK mode eager env { s with instC := ((if s.instC.size < instCCapC then s.instC else {}).insert
      (e, vs, d) (Expr.instantiateListC e vs d)) } :=
  { hs with
    instC := fun k vs' d' => HashMap.insert_backed
      (P := fun k r => r = Expr.instantiateList k.1 k.2.1 k.2.2) (i := (e, vs, d))
      (fun k v h => by
        split at h
        · exact hs.instC k.1 k.2.1 k.2.2 v h
        · simp at h)
      Expr.instantiateListC_spec (k, vs', d') }

/-- Below the cursor's bound, instantiation is the identity. -/
theorem instantiateList_of_bvarB {e : Expr} {d : Nat} (h : e.bvarB ≤ d) (vs : List Expr) :
    e.instantiateList vs d = e :=
  Expr.instantiateList_eq_self (bvarB_le h)

/-- Bulk instantiation through the persistent memo. -/
theorem instListM_spec (hs : CSOK mode eager env s₀) (e : Expr) (vs : List Expr) (d : Nat) :
    ⦃fun s => s = s₀⦄ instListM e vs d
    ⦃fun r s' => CSOK mode eager env s' ∧ r = e.instantiateList vs d; ⊤⦄ := by
  sym only [conleche_grind, instantiateList_of_bvarB, Expr.instantiateListC_spec,
      CSOK.instC_insert] =>
    vcgen [instListM_eq] <;> finish

end InstMemo

/-! ## The lazy stored-constant caches

A hit is the spec value by the cache's `CSOK` clause at the environment
entry the caller found (`CSOK.constTy_hit` …, instantiated at that
entry in the `sym` list); a miss instantiates and inserts it. -/

section CacheFill

variable {s₀ : CState}

theorem CSOK.constTy_hit {s : CState} {n : Name} {us : List Level} {ci : ConstantInfo}
    (hfind : env.find? n = some ci) (hs : CSOK mode eager env s)
    (hne : s.constTyAt[(n, us)]? ≠ none) :
    s.constTyAt[(n, us)]? =
      some (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us) := by
  obtain ⟨i, hl⟩ := Option.ne_none_iff_exists'.mp hne
  obtain ⟨ci', hfind', hrel⟩ := hs.constTy n us i hl
  rw [hfind] at hfind'; cases hfind'; rw [hl, hrel.erase]

theorem CSOK.constTy_insert {s : CState} {n : Name} {us : List Level} {ci : ConstantInfo}
    (hfind : env.find? n = some ci) (hs : CSOK mode eager env s) :
    CSOK mode eager env { s with constTyAt := (s.constTyAt.insert (n, us)
      (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us)) } :=
  { hs with
    constTy := fun n' us' => HashMap.insert_backed
      (P := fun k i => ∃ ci, env.find? k.1 = some ci ∧
        RelC i (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams k.2))
      (i := (n, us)) (fun k v => hs.constTy k.1 k.2 v) ⟨ci, hfind, RelC.refl _⟩ (n', us') }

/-- The stored type of a constant at levels `us` (a dummy where there is
no constant). -/
@[expose] def constTyOf (env : Env) (n : Name) (us : List Level) : Expr :=
  match env.find? n with
  | some ci => ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us
  | none => .bvar 0

/-- `constTyAtM` under the index of `env`, at a stored constant: the
level-instantiated stored type. -/
theorem constTyAtM_spec (hs : CSOK mode eager env s₀) (nI n : Name) (us : List Level)
    (hfind : (env.find? n).isSome = true) :
    ⦃fun s => s = s₀⦄ constTyAtM (mkFEnv env) nI n us
    ⦃fun t s' => CSOK mode eager env s' ∧ t = constTyOf env n us; ⊤⦄ := by
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hfind
  sym only [conleche_grind, constTyOf, CSOK.constTy_hit (mode := mode) (eager := eager) hci,
      CSOK.constTy_insert hci] =>
    vcgen [constTyAtM, instLevelParamsM] <;> finish

theorem CSOK.constVal_hit {s : CState} {n : Name} {us : List Level}
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hfind : env.find? n = some (.defnInfo cv v hint)) (hs : CSOK mode eager env s)
    (hne : s.constValAt[(n, us)]? ≠ none) :
    s.constValAt[(n, us)]? = some (v.instantiateLevelParams cv.levelParams us) := by
  obtain ⟨i, hl⟩ := Option.ne_none_iff_exists'.mp hne
  obtain ⟨cv', v', hint', hfind', hrel⟩ := hs.constVal n us i hl
  rw [hfind] at hfind'; cases hfind'; rw [hl, hrel.erase]

theorem CSOK.constVal_insert {s : CState} {n : Name} {us : List Level}
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hfind : env.find? n = some (.defnInfo cv v hint)) (hs : CSOK mode eager env s) :
    CSOK mode eager env { s with constValAt := (s.constValAt.insert (n, us)
      (v.instantiateLevelParams cv.levelParams us)) } :=
  { hs with
    constVal := fun n' us' => HashMap.insert_backed
      (P := fun k i => ∃ cv v h, env.find? k.1 = some (.defnInfo cv v h) ∧
        RelC i (v.instantiateLevelParams cv.levelParams k.2))
      (i := (n, us)) (fun k v => hs.constVal k.1 k.2 v) ⟨cv, v, hint, hfind, RelC.refl _⟩
      (n', us') }

/-- `constValAtM` under the index of `env` (the head is a stored
definition). -/
theorem constValAtM_spec_of_find (hs : CSOK mode eager env s₀) {nI n : Name}
    {us : List Level} {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hfind : env.find? n = some (.defnInfo cv v hint)) :
    ⦃fun s => s = s₀⦄ constValAtM (mkFEnv env) nI n us
    ⦃fun i s' => CSOK mode eager env s' ∧ i = v.instantiateLevelParams cv.levelParams us; ⊤⦄ := by
  sym only [conleche_grind,
      CSOK.constVal_hit (mode := mode) (eager := eager) hfind, CSOK.constVal_insert hfind] =>
    vcgen [constValAtM, instLevelParamsM] <;> finish

/-- The level-instantiated value of the stored definition `n`, where
there is one: what `constValAtM` answers. -/
@[expose] def constValAt? (env : Env) (n : Name) (us : List Level) : Option Expr :=
  match env.find? n with
  | some (.defnInfo cv v _) => some (v.instantiateLevelParams cv.levelParams us)
  | _ => none

/-- `constValAtM` answers the stored definition's instantiated value
(a run succeeds only at a stored definition: a hit is backed by the
invariant, a miss elsewhere throws). -/
theorem constValAtM_spec (hs : CSOK mode eager env s₀) (nI n : Name) (us : List Level) :
    ⦃fun s => s = s₀⦄ constValAtM (mkFEnv env) nI n us
    ⦃fun r s' => CSOK mode eager env s' ∧ constValAt? env n us = some r; ⊤⦄ := by
  refine triple_iff_run.mpr fun r s' hr => ?_
  have hdef : ∃ cv v h, env.find? n = some (.defnInfo cv v h) := by
    cases hl : s₀.constValAt[(n, us)]? with
    | some i =>
      obtain ⟨cv, v, h, hf, -⟩ := hs.constVal n us i hl
      exact ⟨cv, v, h, hf⟩
    | none =>
      -- a miss: off a stored definition the run throws
      cases hf : env.find? n with
      | some ci =>
        cases ci <;> first | exact ⟨_, _, _, rfl⟩ | (exfalso; revert hr; simp [constValAtM,
          bind, StateT.bind, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Except.bind,
          pure, Except.pure, hl, mkFEnv_find?, hf] <;> exact fun h => nomatch h)
      | none =>
        exfalso; revert hr; simp [constValAtM, bind, StateT.bind, modifyGet,
          MonadStateOf.modifyGet, StateT.modifyGet, Except.bind, pure, Except.pure, hl,
          mkFEnv_find?, hf] <;> exact fun h => nomatch h
  obtain ⟨cv, v, h, hf⟩ := hdef
  obtain ⟨hs', hrel⟩ := triple_iff_run.mp (constValAtM_spec_of_find hs hf) r s' hr
  exact ⟨hs', by rw [constValAt?, hf, hrel]⟩

theorem CSOK.ruleRhs_hit {s : CState} {c j : Name} {us : List Level}
    {cv : ConstantVal} {mI rP : Nat} {isK : Bool} {rules : List RecRule} {rl : RecRule}
    (hfind : env.find? c = some (.recInfo cv mI rP isK rules))
    (hrl : rules.find? (fun r' => r'.ctor == j) = some rl) (hs : CSOK mode eager env s)
    (hne : s.ruleRhsAt[(c, j, us)]? ≠ none) :
    s.ruleRhsAt[(c, j, us)]? = some (rl.rhs.instantiateLevelParams cv.levelParams us) := by
  obtain ⟨i, hl⟩ := Option.ne_none_iff_exists'.mp hne
  obtain ⟨cv', mI', rP', isK', rules', rl', hfind', hrl', hrel⟩ := hs.ruleRhs c j us i hl
  rw [hfind] at hfind'; cases hfind'; rw [hrl] at hrl'; cases hrl'; rw [hl, hrel.erase]

theorem CSOK.ruleRhs_insert {s : CState} {c j : Name} {us : List Level}
    {cv : ConstantVal} {mI rP : Nat} {isK : Bool} {rules : List RecRule} {rl : RecRule}
    (hfind : env.find? c = some (.recInfo cv mI rP isK rules))
    (hrl : rules.find? (fun r' => r'.ctor == j) = some rl) (hs : CSOK mode eager env s) :
    CSOK mode eager env { s with ruleRhsAt := (s.ruleRhsAt.insert (c, j, us)
      (rl.rhs.instantiateLevelParams cv.levelParams us)) } :=
  { hs with
    ruleRhs := fun c' j' us' => HashMap.insert_backed
      (P := fun k i => ∃ cv mI rP isK rules rl, env.find? k.1 = some (.recInfo cv mI rP isK rules) ∧
        rules.find? (fun r' => r'.ctor == k.2.1) = some rl ∧
        RelC i (rl.rhs.instantiateLevelParams cv.levelParams k.2.2))
      (i := (c, j, us)) (fun k v => hs.ruleRhs k.1 k.2.1 k.2.2 v)
      ⟨cv, mI, rP, isK, rules, rl, hfind, hrl, RelC.refl _⟩ (c', j', us') }

/-- `ruleRhsAtM` under the index of `env`. -/
theorem ruleRhsAtM_spec_of_find (hs : CSOK mode eager env s₀) {cI jI c j : Name}
    {us : List Level} {cv : ConstantVal} {mI rP : Nat}
    {rules : List RecRule} {rl : RecRule}
    (hfind : env.find? c = some (.recInfo cv mI rP isK rules))
    (hrl : rules.find? (fun r' => r'.ctor == j) = some rl) :
    ⦃fun s => s = s₀⦄ ruleRhsAtM (mkFEnv env) cI jI c j us
    ⦃fun i s' => CSOK mode eager env s' ∧ i = rl.rhs.instantiateLevelParams cv.levelParams us; ⊤⦄
        := by
  sym only [conleche_grind,
      CSOK.ruleRhs_hit (mode := mode) (eager := eager) hfind hrl, CSOK.ruleRhs_insert hfind hrl] =>
    vcgen [ruleRhsAtM, instLevelParamsM] <;> finish

/-- The rule a recursor stores for constructor `cj` (the lookup's `fun`
named, so that two lookups at equal names are congruent). -/
@[expose] def findRule (rules : List RecRule) (cj : Name) : Option RecRule :=
  rules.find? (fun r' => r'.ctor == cj)

/-- A recursor's rule right-hand side for constructor `j` at levels `us`. -/
@[expose] def ruleRhsOf (env : Env) (c j : Name) (us : List Level) : Option Expr :=
  match env.find? c with
  | some (.recInfo cv _ _ _ rules) =>
    match findRule rules j with
    | some rl => some (rl.rhs.instantiateLevelParams cv.levelParams us)
    | none => none
  | _ => none

/-- `ruleRhsAtM` under the index of `env`, where the recursor stores a
rule for the constructor. -/
theorem ruleRhsAtM_spec (hs : CSOK mode eager env s₀) (cI jI c j : Name)
    (us : List Level) (hfind : (ruleRhsOf env c j us).isSome = true) :
    ⦃fun s => s = s₀⦄ ruleRhsAtM (mkFEnv env) cI jI c j us
    ⦃fun t s' => CSOK mode eager env s' ∧ some t = ruleRhsOf env c j us; ⊤⦄ := by
  refine triple_iff_run.mpr fun t s' hr => ?_
  unfold ruleRhsOf at hfind ⊢
  split at hfind
  · rename_i cv mI rP isK rules hc
    split at hfind
    · rename_i rl hrl
      obtain ⟨hs', h⟩ := triple_iff_run.mp (ruleRhsAtM_spec_of_find hs hc hrl) t s' hr
      exact ⟨hs', congrArg some h⟩
    · exact nomatch hfind
  · exact nomatch hfind

end CacheFill

end ConLeche.Cached

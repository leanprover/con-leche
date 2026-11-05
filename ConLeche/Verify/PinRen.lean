module

public import ConLeche.Verify.Denote.Pinned
public import ConLeche.Verify.EnvWF
public import ConLeche.Verify.InstLevels

public section

/-!
# Two environments that differ in their basis constants' level names

A stream's pinned constants are stored at the level-parameter names the
stream declares.  `RenEnv env env'` says two environments hold the same
constants except that reserved ones may be different copies of their pin
(`PinCopy`).  The model tier carries its invariant across this relation
(`Model/BasisRename.lean`), which is what lets the basis stages be stated at
the pins' own names.  This file is the relation's syntactic half.
-/

namespace ConLeche.Verify

open ConLeche

/-! ## Renaming level parameters, positionally -/

/-- A renaming's result is one of the new names. -/
theorem subst_go_param_mem :
    ∀ {ks ps : List Name} {n : Name}, ks.length = ps.length → n ∈ ks →
      ∃ q ∈ ps, Level.subst.go ks (ps.map Level.param) n = .param q
  | k :: ks, p :: ps, n, hl, hn => by
    simp only [Level.subst.go, List.map_cons]
    by_cases h : k = n
    · exact ⟨p, List.mem_cons_self, by rw [if_pos h]⟩
    · rw [if_neg h]
      have hn' : n ∈ ks := by
        rcases List.mem_cons.mp hn with rfl | h'
        · exact absurd rfl h
        · exact h'
      obtain ⟨q, hq, he⟩ := subst_go_param_mem (Nat.succ.inj hl) hn'
      exact ⟨q, List.mem_cons_of_mem _ hq, he⟩
  | [], _, _, _, hn => absurd hn List.not_mem_nil
  | _ :: _, [], _, hl, _ => nomatch hl

/-- A parameter the head does not name is the tail's business. -/
theorem subst_go_cons_ne {p q : Name} (hne : p ≠ q) (ps : List Name) (u : Level) (us : List Level) :
    Level.subst.go (p :: ps) (u :: us) q = Level.subst.go ps us q := by
  simp only [Level.subst.go]
  rw [if_neg hne]

/-- **Renaming and then instantiating is instantiating**, at a parameter. -/
theorem subst_go_ren :
    ∀ {ks ps : List Name} {us : List Level} {n : Name}, ps.Nodup → ks.length = ps.length →
      us.length = ps.length → n ∈ ks →
      Level.subst ps us (Level.subst.go ks (ps.map Level.param) n) = Level.subst.go ks us n
  | k :: ks, p :: ps, u :: us, n, hnd, hl, hu, hn => by
    simp only [List.map_cons, Level.subst.go]
    by_cases h : k = n
    · rw [if_pos h, if_pos h]
      simp [Level.subst, Level.subst.go]
    · rw [if_neg h, if_neg h]
      have hn' : n ∈ ks := by
        rcases List.mem_cons.mp hn with rfl | h'
        · exact absurd rfl h
        · exact h'
      have hl' := Nat.succ.inj hl
      have hu' := Nat.succ.inj hu
      obtain ⟨hp, hnd'⟩ := List.nodup_cons.mp hnd
      obtain ⟨q, hq, he⟩ := subst_go_param_mem hl' hn'
      have ih := subst_go_ren (us := us) hnd' hl' hu' hn'
      rw [he] at ih ⊢
      simp only [Level.subst] at ih ⊢
      have hne : p ≠ q := fun h' => hp (h' ▸ hq)
      rw [subst_go_cons_ne hne]
      exact ih
  | [], _, _, _, _, _, _, hn => absurd hn List.not_mem_nil
  | _ :: _, [], _, _, _, hl, _, _ => nomatch hl
  | _ :: _, _ :: _, [], _, _, _, hu, _ => nomatch hu

theorem level_subst_ren {ks ps : List Name} {us : List Level} (hnd : ps.Nodup)
    (hl : ks.length = ps.length) (hu : us.length = ps.length) :
    ∀ l : Level, l.allParamsDefined ks = true →
      Level.subst ps us (Level.subst ks (ps.map Level.param) l) = Level.subst ks us l := by
  intro l
  induction l with
  | zero => intro _; rfl
  | succ l ih => intro h; simp only [Level.subst]; rw [ih h]
  | max a b iha ihb =>
    intro h
    simp only [Level.allParamsDefined, Bool.and_eq_true] at h
    simp only [Level.subst]; rw [iha h.1, ihb h.2]
  | imax a b iha ihb =>
    intro h
    simp only [Level.allParamsDefined, Bool.and_eq_true] at h
    simp only [Level.subst]; rw [iha h.1, ihb h.2]
  | param n =>
    intro h
    simp only [Level.allParamsDefined, List.contains_iff_mem] at h
    exact subst_go_ren hnd hl hu h

/-- **Renaming and then instantiating is instantiating.** -/
theorem inst_ren {ks ps : List Name} {us : List Level} (hnd : ps.Nodup)
    (hl : ks.length = ps.length) (hu : us.length = ps.length) :
    ∀ e : Expr, e.allLevelParamsDefined ks = true →
      (e.instantiateLevelParams ks (ps.map Level.param)).instantiateLevelParams ps us
        = e.instantiateLevelParams ks us := by
  intro e
  induction e with
  | bvar i => intro _; rfl
  | fvar i t ih => intro h; simp only [Expr.instantiateLevelParams]; rw [ih h]
  | sort u =>
    intro h
    simp only [Expr.instantiateLevelParams]
    rw [level_subst_ren hnd hl hu u h]
  | const n vs =>
    intro h
    simp only [Expr.allLevelParamsDefined, List.all_eq_true] at h
    simp only [Expr.instantiateLevelParams, List.map_map]
    congr 1
    exact List.map_congr_left fun v hv => level_subst_ren hnd hl hu v (h v hv)
  | app f a ihf iha =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams]; rw [ihf h.1, iha h.2]
  | lam t b iht ihb =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams]; rw [iht h.1, ihb h.2]
  | forallE t b iht ihb =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams]; rw [iht h.1, ihb h.2]
  | letE t v b iht ihv ihb =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams]; rw [iht h.1.1, ihv h.1.2, ihb h.2]
  | lit l => intro _; rfl
  | proj s i e ih => intro h; simp only [Expr.instantiateLevelParams]; rw [ih h]

/-- Renamed parameters are the new names. -/
theorem level_defined_ren {ks ps : List Name} (hl : ks.length = ps.length) :
    ∀ l : Level, l.allParamsDefined ks = true →
      (Level.subst ks (ps.map Level.param) l).allParamsDefined ps = true := by
  intro l
  induction l with
  | zero => intro _; rfl
  | succ l ih => intro h; exact ih h
  | max a b iha ihb =>
    intro h
    simp only [Level.allParamsDefined, Bool.and_eq_true] at h
    simp only [Level.subst, Level.allParamsDefined, Bool.and_eq_true]
    exact ⟨iha h.1, ihb h.2⟩
  | imax a b iha ihb =>
    intro h
    simp only [Level.allParamsDefined, Bool.and_eq_true] at h
    simp only [Level.subst, Level.allParamsDefined, Bool.and_eq_true]
    exact ⟨iha h.1, ihb h.2⟩
  | param n =>
    intro h
    simp only [Level.allParamsDefined, List.contains_iff_mem] at h
    obtain ⟨q, hq, he⟩ := subst_go_param_mem hl h
    simp only [Level.subst, he, Level.allParamsDefined, List.contains_iff_mem]
    exact hq

theorem expr_defined_ren {ks ps : List Name} (hl : ks.length = ps.length) :
    ∀ e : Expr, e.allLevelParamsDefined ks = true →
      (e.instantiateLevelParams ks (ps.map Level.param)).allLevelParamsDefined ps = true := by
  intro e
  induction e with
  | bvar i => intro _; rfl
  | fvar i t ih => intro h; exact ih h
  | sort u => intro h; exact level_defined_ren hl u h
  | const n vs =>
    intro h
    simp only [Expr.allLevelParamsDefined, List.all_eq_true] at h
    simp only [Expr.instantiateLevelParams, Expr.allLevelParamsDefined, List.all_eq_true,
      List.mem_map]
    rintro _ ⟨v, hv, rfl⟩
    exact level_defined_ren hl v (h v hv)
  | app f a ihf iha =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨ihf h.1, iha h.2⟩
  | lam t b iht ihb =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨iht h.1, ihb h.2⟩
  | forallE t b iht ihb =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨iht h.1, ihb h.2⟩
  | letE t v b iht ihv ihb =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨iht h.1.1, ihv h.1.2⟩, ihb h.2⟩
  | lit l => intro _; rfl
  | proj s i e ih => intro h; exact ih h

/-- **The valuation-level renaming**, at the list's names: reading the
parameter `ks[i]` at `ps[i]`, in an assignment that gives `ps[i]` the
instantiation's `us[i]`, is the instantiation at `ks[i]`. -/
theorem substFn_ren :
    ∀ {ks ps : List Name} {us : List Level} {ψ X : Name → Nat}, ps.Nodup →
      ks.length = ps.length → us.length = ps.length →
      (∀ q ∈ ps, X q = Level.substFn ψ ps us q) →
      ∀ p ∈ ks, Level.substFn X ks (ps.map Level.param) p = Level.substFn ψ ks us p
  | k :: ks, p' :: ps, u :: us, ψ, X, hnd, hl, hu, hX, p, hp => by
    simp only [List.map_cons, Level.substFn]
    by_cases h : k = p
    · rw [if_pos h, if_pos h]
      show X p' = _
      rw [hX p' List.mem_cons_self]
      simp [Level.substFn]
    · rw [if_neg h, if_neg h]
      have hp' : p ∈ ks := by
        rcases List.mem_cons.mp hp with rfl | h'
        · exact absurd rfl h
        · exact h'
      obtain ⟨hne, hnd'⟩ := List.nodup_cons.mp hnd
      refine substFn_ren hnd' (Nat.succ.inj hl) (Nat.succ.inj hu) (fun q hq => ?_) p hp'
      rw [hX q (List.mem_cons_of_mem _ hq)]
      have hq' : p' ≠ q := fun h' => hne (h' ▸ hq)
      simp only [Level.substFn]
      rw [if_neg hq']
  | [], _, _, _, _, _, _, _, _, _, hp => absurd hp List.not_mem_nil
  | _ :: _, [], _, _, _, _, hl, _, _, _, _ => nomatch hl
  | _ :: _, _ :: _, [], _, _, _, _, hu, _, _, _ => nomatch hu

/-! ## The relation -/

/-- **One constant, on both sides**: the same, or two copies of its pin. -/
@[expose] def ConstRen (c c' : ConstantInfo) : Prop :=
  c' = c ∨
    (reservedBasisNames.contains c.name = true ∧
      PinCopy c (pinnedInfo c.name) ∧ PinCopy c' (pinnedInfo c.name))

/-- `ConstRen`, position by position. -/
inductive ConstsRen : List ConstantInfo → List ConstantInfo → Prop where
  | nil : ConstsRen [] []
  | cons {c c' : ConstantInfo} {cs cs' : List ConstantInfo} :
      ConstRen c c' → ConstsRen cs cs' → ConstsRen (c :: cs) (c' :: cs')

/-- **The two environments' relation.** -/
structure RenEnv (env env' : Env) : Prop where
  consts : ConstsRen env.consts env'.consts
  tables : env'.tables = env.tables

/-- A copy's name is its pin's. -/
theorem atLps_name (ci : ConstantInfo) (ps : List Name) : (ci.atLps ps).name = ci.name := by
  cases ci <;> rfl

/-- A copy's common data is the pin's at the names. -/
theorem atLps_cv (ci : ConstantInfo) (ps : List Name) :
    (ci.atLps ps).toConstantVal = ci.toConstantVal.atLps ps := by
  cases ci <;> rfl

theorem pinnedInfo_name {n : Name} (h : reservedBasisNames.contains n = true) :
    (pinnedInfo n).name = n := by
  have hmem : n ∈ reservedBasisNames := by simpa using h
  simp only [reservedBasisNames, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> rfl

/-- What the pins are made of: no definition, and every rule plain, at
the pin's own parameters. -/
@[expose] def pinShapeOk : ConstantInfo → Bool
  | .recInfo cv _ _ _ rules => rules.all fun r =>
    (RecRule.rhs r).allLevelParamsDefined cv.levelParams &&
      (match RecRule.fire r with | .plain => true | _ => false)
  | .defnInfo .. => false
  | _ => true

theorem pinnedInfo_wf {n : Name} (h : reservedBasisNames.contains n = true) :
    (pinnedInfo n).toConstantVal.type.allLevelParamsDefined
        (pinnedInfo n).toConstantVal.levelParams = true ∧ pinShapeOk (pinnedInfo n) = true := by
  have hmem : n ∈ reservedBasisNames := by simpa using h
  simp only [reservedBasisNames, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩

theorem PinCopy.name {c pin : ConstantInfo} (h : PinCopy c pin) : c.name = pin.name := by
  rw [h.1, atLps_name]

/-- Both sides of the relation name the same constant. -/
theorem ConstRen.name {c c' : ConstantInfo} (h : ConstRen c c') : c'.name = c.name := by
  rcases h with rfl | ⟨hr, -, h'⟩
  · rfl
  · rw [h'.name, pinnedInfo_name hr]

theorem ConstRen.symm {c c' : ConstantInfo} (h : ConstRen c c') : ConstRen c' c := by
  have hn := h.name
  rcases h with rfl | ⟨hr, h1, h2⟩
  · exact .inl rfl
  · exact .inr ⟨by rw [hn]; exact hr, by rw [hn]; exact h2, by rw [hn]; exact h1⟩

theorem ConstsRen.symm {cs cs' : List ConstantInfo} (h : ConstsRen cs cs') : ConstsRen cs' cs := by
  induction h with
  | nil => exact .nil
  | cons hc _ ih => exact .cons hc.symm ih

theorem RenEnv.symm {env env' : Env} (h : RenEnv env env') : RenEnv env' env :=
  ⟨h.consts.symm, h.tables.symm⟩

/-- **The lookups correspond.** -/
theorem find_ren : ∀ {cs cs' : List ConstantInfo}, ConstsRen cs cs' → ∀ n,
    (cs.find? (·.name == n) = none ∧ cs'.find? (·.name == n) = none) ∨
    ∃ c c', cs.find? (·.name == n) = some c ∧ cs'.find? (·.name == n) = some c' ∧ ConstRen c c'
  | [], [], .nil, _ => .inl ⟨rfl, rfl⟩
  | c :: cs, c' :: cs', .cons hc ht, n => by
    simp only [List.find?_cons, ← hc.name]
    cases hb : (c'.name == n) with
    | true => exact .inr ⟨c, c', rfl, rfl, hc⟩
    | false => exact find_ren ht n

theorem RenEnv.find {env env' : Env} (h : RenEnv env env') (n : Name) :
    (env.find? n = none ∧ env'.find? n = none) ∨
    ∃ c c', env.find? n = some c ∧ env'.find? n = some c' ∧ ConstRen c c' :=
  find_ren h.consts n

theorem RenEnv.mem {env env' : Env} (h : RenEnv env env') {c' : ConstantInfo}
    (hc : c' ∈ env'.consts) : ∃ c ∈ env.consts, ConstRen c c' := by
  have := h.consts
  generalize env.consts = cs at this
  generalize env'.consts = cs' at this hc
  induction this with
  | nil => exact absurd hc List.not_mem_nil
  | cons h0 _ ih =>
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact ⟨_, List.mem_cons_self, h0⟩
    · obtain ⟨c, hm, hr⟩ := ih hc'
      exact ⟨c, List.mem_cons_of_mem _ hm, hr⟩

/-- A name no pin holds keeps its lookup. -/
theorem RenEnv.find_nonres {env env' : Env} (h : RenEnv env env') {n : Name}
    (hn : reservedBasisNames.contains n = false) : env'.find? n = env.find? n := by
  rcases h.find n with ⟨h1, h2⟩ | ⟨c, c', h1, h2, hr⟩
  · rw [h1, h2]
  · rw [h1, h2]
    rcases hr with rfl | ⟨hres, -, -⟩
    · rfl
    · have hnm : c.name = n := by simpa using Env.find?_name h1
      rw [hnm, hn] at hres
      exact nomatch hres

/-- A level-free pin keeps its lookup. -/
theorem RenEnv.find_noLps {env env' : Env} (h : RenEnv env env') {n : Name}
    (hl : (pinnedInfo n).toConstantVal.levelParams = []) : env'.find? n = env.find? n := by
  rcases h.find n with ⟨h1, h2⟩ | ⟨c, c', h1, h2, hr⟩
  · rw [h1, h2]
  · rw [h1, h2]
    rcases hr with rfl | ⟨-, h3, h4⟩
    · rfl
    · have hnm : c.name = n := by simpa using Env.find?_name h1
      rw [hnm] at h3 h4
      have e3 : c.toConstantVal.levelParams = [] := List.eq_nil_of_length_eq_zero (by
        rw [h3.2.2, hl]; rfl)
      have e4 : c'.toConstantVal.levelParams = [] := List.eq_nil_of_length_eq_zero (by
        rw [h4.2.2, hl]; rfl)
      rw [h3.1, h4.1, e3, e4]

/-- Which names are stored is the same on both sides. -/
theorem RenEnv.isSome {env env' : Env} (h : RenEnv env env') (n : Name) :
    (env'.find? n).isSome = (env.find? n).isSome := by
  rcases h.find n with ⟨h1, h2⟩ | ⟨c, c', h1, h2, -⟩
  · rw [h1, h2]
  · rw [h1, h2]; rfl

theorem RenEnv.constsResolve {env env' : Env} (h : RenEnv env env') :
    ∀ e : Expr, e.constsResolve env' = e.constsResolve env := by
  intro e
  induction e with
  | lit l => cases l <;> simp [Expr.constsResolve, h.isSome]
  | bvar _ => rfl
  | sort _ => rfl
  | const n _ => simp [Expr.constsResolve, h.isSome]
  | fvar _ t ih => simpa [Expr.constsResolve] using ih
  | app f a ihf iha => simp [Expr.constsResolve, ihf, iha]
  | lam t b iht ihb => simp [Expr.constsResolve, iht, ihb]
  | forallE t b iht ihb => simp [Expr.constsResolve, iht, ihb]
  | letE t v b iht ihv ihb => simp [Expr.constsResolve, iht, ihv, ihb]
  | proj s i e ih => simp [Expr.constsResolve, h.isSome, ih]

theorem RenEnv.natLit {env env' : Env} (h : RenEnv env env') :
    natLitSupported env' = natLitSupported env := by
  simp only [natLitSupported, h.find_noLps (n := natName) rfl,
    h.find_noLps (n := natZeroName) rfl, h.find_noLps (n := natSuccName) rfl]

theorem RenEnv.strLit {env env' : Env} (h : RenEnv env env') :
    strLitSupported env' = strLitSupported env := by
  simp only [strLitSupported, h.natLit, h.find_nonres (n := stringName) (by decide),
    h.find_nonres (n := stringOfListName) (by decide), h.find_nonres (n := listName) (by decide),
    h.find_nonres (n := listNilName) (by decide), h.find_nonres (n := listConsName) (by decide),
    h.find_nonres (n := charName) (by decide), h.find_nonres (n := charOfNatName) (by decide)]

theorem RenEnv.findTable {env env' : Env} (h : RenEnv env env') (T : Name) :
    env'.findTable? T = env.findTable? T := by
  simp only [Env.findTable?, h.isSome, h.tables]

theorem RenEnv.findProj {env env' : Env} (h : RenEnv env env') (T : Name) (i : Nat) :
    env'.findProj? T i = env.findProj? T i := by
  simp only [Env.findProj?, h.findTable]

end ConLeche.Verify

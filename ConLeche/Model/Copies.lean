module

public import ConLeche.Model.BasisRename
public import ConLeche.Model.Denotes
import ConLeche.Model.Levels
import ConLeche.Verify.InstLevels

public section

/-!
# A model across copies of constants (task #607)

`CopiesEnv env env'` says `env'` holds `env`'s constants, position by position, each the same or
`env`'s at other level-parameter names (`ConstantInfo.atLps`, as many names, distinct), with the
same tables.  A compared challenge's environment is such a copy of what it stands for in its
solution's.  `Model.ofCopies` reads a model of `env'` off the invariant of `env`: a constant of
`env'` is valued as `env`'s at the assignment that gives `env`'s `i`-th parameter the copy's
`i`-th parameter's value (`renAcval`), so every term reads alike on both sides (`denote_ren`
over `CopyEnv`), and every type of `env'` reads as `env`'s at that assignment
(`denote_instLevels`).
-/

namespace ConLeche.Model

open ConLeche.Semantics ConLeche.Term ConLeche.Verify SetTheory
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal)

universe w

variable {V : Type w} [SetTheory V]

/-- **One constant, copied**: the same, or the first at other level-parameter names, as many
as its own, distinct. -/
@[expose] def ConstCopy (c c' : ConstantInfo) : Prop :=
  c' = c ∨ ∃ ps, c' = c.atLps ps ∧ ps.Nodup ∧ c.toConstantVal.levelParams.length = ps.length

/-- `ConstCopy`, position by position. -/
inductive ConstsCopy : List ConstantInfo → List ConstantInfo → Prop where
  | nil : ConstsCopy [] []
  | cons {c c' : ConstantInfo} {cs cs' : List ConstantInfo} :
      ConstCopy c c' → ConstsCopy cs cs' → ConstsCopy (c :: cs) (c' :: cs')

/-- **An environment copied** (see the module docstring); `env`'s names are distinct. -/
structure CopiesEnv (env env' : Env) : Prop where
  consts : ConstsCopy env.consts env'.consts
  tables : env'.tables = env.tables
  nodup : (env.consts.map (·.toConstantVal.name)).Nodup

theorem ConstCopy.name {c c' : ConstantInfo} (h : ConstCopy c c') : c'.name = c.name := by
  rcases h with rfl | ⟨ps, rfl, -⟩
  · rfl
  · exact atLps_name c ps

theorem ConstCopy.lpsCopy {c c' : ConstantInfo} (h : ConstCopy c c') : LpsCopy c c' := by
  rcases h with rfl | ⟨ps, rfl, hnd, hl⟩
  · exact .inl rfl
  · right
    rw [atLps_cv]
    exact ⟨hnd, hl⟩

theorem Level.subst_nil (l : Level) : Level.subst [] [] l = l := by
  induction l <;> simp_all [Level.subst, Level.subst.go]

theorem Level.subst_nil_fun : Level.subst [] [] = id := funext Level.subst_nil

theorem Expr.instantiateLevelParams_nil (e : Expr) : e.instantiateLevelParams [] [] = e := by
  induction e <;> simp_all [Expr.instantiateLevelParams, Level.subst_nil, Level.subst_nil_fun]

/-- A copy with no level parameters is the constant. -/
theorem ConstCopy.eq_of_nil {c c' : ConstantInfo} (h : ConstCopy c c')
    (h0 : c.toConstantVal.levelParams = []) : c' = c := by
  rcases h with rfl | ⟨ps, rfl, -, hl⟩
  · rfl
  · rw [h0] at hl
    obtain rfl : ps = [] := List.eq_nil_of_length_eq_zero hl.symm
    cases c with
    | recInfo cv mI rP isK rules =>
      simp only [ConstantInfo.toConstantVal] at h0
      simp only [ConstantInfo.atLps, ConstantVal.atLps, ConstantInfo.toConstantVal, h0,
        List.map_nil, Expr.instantiateLevelParams_nil]
      congr 1
      · cases cv; simp_all
      · conv => rhs; rw [← List.map_id rules]
        refine List.map_congr_left fun rl _ => ?_
        cases rl with
        | mk ctor nf fire rhs =>
          cases fire <;> simp [RecRuleFire.atLps, Level.subst_nil_fun]
    | _ =>
      simp only [ConstantInfo.toConstantVal] at h0
      simp only [ConstantInfo.atLps, ConstantVal.atLps, ConstantInfo.toConstantVal, h0,
        List.map_nil, Expr.instantiateLevelParams_nil]
      all_goals (cases ‹ConstantVal›; simp_all)

/-! ## The lookups -/

theorem find_copies : ∀ {cs cs' : List ConstantInfo}, ConstsCopy cs cs' → ∀ n,
    (cs.find? (·.name == n) = none ∧ cs'.find? (·.name == n) = none) ∨
    ∃ c c', cs.find? (·.name == n) = some c ∧ cs'.find? (·.name == n) = some c' ∧ ConstCopy c c'
  | [], [], .nil, _ => .inl ⟨rfl, rfl⟩
  | c :: cs, c' :: cs', .cons hc ht, n => by
    simp only [List.find?_cons, hc.name]
    cases hb : (c.name == n) with
    | true => exact .inr ⟨c, c', rfl, rfl, hc⟩
    | false => exact find_copies ht n

theorem mem_copies : ∀ {cs cs' : List ConstantInfo}, ConstsCopy cs cs' →
    (cs.map (·.toConstantVal.name)).Nodup → ∀ c' ∈ cs', ∃ c ∈ cs,
      cs.find? (·.name == c'.name) = some c ∧ cs'.find? (·.name == c'.name) = some c' ∧
      ConstCopy c c'
  | [], [], .nil, _, _, h => absurd h List.not_mem_nil
  | c :: cs, c₁ :: cs', .cons hc ht, hnd, c', h => by
    have hn : c₁.name = c.name := hc.name
    rcases List.mem_cons.mp h with rfl | h
    · refine ⟨c, List.mem_cons_self, ?_, ?_, hc⟩ <;> simp [hn]
    · obtain ⟨hnot, hnd'⟩ := List.nodup_cons.mp hnd
      obtain ⟨d, hd, h1, h2, hr⟩ := mem_copies ht hnd' c' h
      have hdn : d.name = c'.name := by simpa using List.find?_some h1
      have hne : c.name ≠ c'.name := fun e => hnot (List.mem_map.mpr ⟨d, hd, by
        rw [← e] at hdn; exact hdn⟩)
      refine ⟨d, List.mem_cons_of_mem _ hd, ?_, ?_, hr⟩
      · simp [hne, h1]
      · simp [hn, hne, h2]

theorem CopiesEnv.find {env env' : Env} (h : CopiesEnv env env') (n : Name) :
    (env.find? n = none ∧ env'.find? n = none) ∨
    ∃ c c', env.find? n = some c ∧ env'.find? n = some c' ∧ ConstCopy c c' :=
  find_copies h.consts n

/-! ## The literals -/

theorem natIndOk_len {o : Option ConstantInfo} (h : natIndOk o = true) :
    ∃ c, o = some c ∧ c.toConstantVal.levelParams.length = 0 := by
  match o, h with
  | some (.indInfo cv _), h =>
    simp only [natIndOk, Bool.and_eq_true, List.isEmpty_iff] at h
    exact ⟨_, rfl, by simp [ConstantInfo.toConstantVal, h.1]⟩

theorem stringTyOk_len {o : Option ConstantInfo} (h : stringTyOk o = true) :
    ∃ c, o = some c ∧ c.toConstantVal.levelParams.length = 0 := by
  match o, h with
  | some c, h =>
    simp only [stringTyOk, Bool.and_eq_true, List.isEmpty_iff] at h
    exact ⟨_, rfl, by simp [h.1]⟩

/-- **A level-free shape reads the same of a copy.** -/
theorem pred_copy0 {P : Option ConstantInfo → Bool}
    (hP : ∀ {o}, P o = true → ∃ c, o = some c ∧ c.toConstantVal.levelParams.length = 0)
    {c c' : ConstantInfo} (hc : ConstCopy c c') : P (some c') = P (some c) := by
  have hl : c.toConstantVal.levelParams.length = c'.toConstantVal.levelParams.length := by
    rcases hc.lpsCopy with rfl | ⟨-, hl⟩
    · rfl
    · exact hl
  cases h1 : P (some c) with
  | true =>
    obtain ⟨_, he, h0⟩ := hP h1
    obtain rfl := Option.some.inj he
    rw [hc.eq_of_nil (List.eq_nil_of_length_eq_zero h0), h1]
  | false =>
    cases h2 : P (some c') with
    | false => rfl
    | true =>
      obtain ⟨_, he, h0⟩ := hP h2
      obtain rfl := Option.some.inj he
      rw [hc.eq_of_nil (List.eq_nil_of_length_eq_zero (hl.trans h0)), h1] at h2
      exact nomatch h2

/-- A shape that reads only the common data. -/
theorem shape_cv {P : Option ConstantInfo → Bool} (hP : ∀ x y : ConstantInfo,
    x.toConstantVal = y.toConstantVal → P (some x) = P (some y)) {c : ConstantInfo}
    {ps : List Name} : P (some (c.atLps ps)) = P (some (.axiomInfo (c.toConstantVal.atLps ps))) :=
  hP _ _ (by rw [atLps_cv]; rfl)

theorem listTyOk_copy {c c' : ConstantInfo} (hc : ConstCopy c c')
    (h : listTyOk (some c) = true) : listTyOk (some c') = true := by
  rcases hc with rfl | ⟨ps, rfl, -, hl⟩
  · exact h
  have hP : ∀ x y : ConstantInfo, x.toConstantVal = y.toConstantVal →
      listTyOk (some x) = listTyOk (some y) := fun x y e => by simp only [listTyOk, e]
  rw [shape_cv hP]
  rw [hP c (.axiomInfo c.toConstantVal) rfl] at h
  generalize c.toConstantVal = cv at h hl
  obtain ⟨nm, lps, ty⟩ := cv
  simp only [listTyOk, ConstantInfo.toConstantVal] at h hl ⊢
  match lps, ty, ps, hl, h with
  | [p], .forallE (.sort u1) (.sort u2), [p'], _, h =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [ConstantVal.atLps, Expr.instantiateLevelParams, Level.subst, Level.subst.go]

theorem listNilTyOk_copy {c c' : ConstantInfo} (hc : ConstCopy c c')
    (h : listNilTyOk (some c) = true) : listNilTyOk (some c') = true := by
  rcases hc with rfl | ⟨ps, rfl, -, hl⟩
  · exact h
  have hP : ∀ x y : ConstantInfo, x.toConstantVal = y.toConstantVal →
      listNilTyOk (some x) = listNilTyOk (some y) := fun x y e => by simp only [listNilTyOk, e]
  rw [shape_cv hP]
  rw [hP c (.axiomInfo c.toConstantVal) rfl] at h
  generalize c.toConstantVal = cv at h hl
  obtain ⟨nm, lps, ty⟩ := cv
  simp only [listNilTyOk, ConstantInfo.toConstantVal] at h hl ⊢
  match lps, ty, ps, hl, h with
  | [p], .forallE (.sort u1) (.app (.const l1 us1) (.bvar 0)), [p'], _, h =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    simp [ConstantVal.atLps, Expr.instantiateLevelParams, Level.subst, Level.subst.go]

theorem listConsTyOk_copy {c c' : ConstantInfo} (hc : ConstCopy c c')
    (h : listConsTyOk (some c) = true) : listConsTyOk (some c') = true := by
  rcases hc with rfl | ⟨ps, rfl, -, hl⟩
  · exact h
  have hP : ∀ x y : ConstantInfo, x.toConstantVal = y.toConstantVal →
      listConsTyOk (some x) = listConsTyOk (some y) := fun x y e => by
    simp only [listConsTyOk, e]
  rw [shape_cv hP]
  rw [hP c (.axiomInfo c.toConstantVal) rfl] at h
  generalize c.toConstantVal = cv at h hl
  obtain ⟨nm, lps, ty⟩ := cv
  simp only [listConsTyOk, ConstantInfo.toConstantVal] at h hl ⊢
  match lps, ty, ps, hl, h with
  | [p], .forallE (.sort u1) (.forallE (.bvar 0) (.forallE (.app (.const l1 us1) (.bvar 1))
      (.app (.const l2 us2) (.bvar 2)))), [p'], _, h =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h
    simp [ConstantVal.atLps, Expr.instantiateLevelParams, Level.subst, Level.subst.go]

/-- **A literal name's stored constant has its shape**, off `EnvWF`. -/
theorem shape_of_wf {env : Env} (hwf : EnvWF env) {n : Name} {c : ConstantInfo}
    (hf : env.find? n = some c) :
    (n = listName → listTyOk (some c) = true) ∧ (n = listNilName → listNilTyOk (some c) = true) ∧
    (n = listConsName → listConsTyOk (some c) = true) := by
  have hs := hwf.shapes c (Env.find?_mem hf)
  have hn : c.name = n := Env.find?_name hf
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩ <;> subst e <;>
    simpa (config := { decide := true }) [litShapeOk, hn] using hs

theorem list_copy {env env' : Env} (h : CopiesEnv env env') {n : Name}
    {P : Option ConstantInfo → Bool}
    (hsh : ∀ c, env.find? n = some c → P (some c) = true)
    (hcp : ∀ {c c'}, ConstCopy c c' → P (some c) = true → P (some c') = true) :
    P (env'.find? n) = P (env.find? n) := by
  rcases h.find n with ⟨h1, h2⟩ | ⟨c, c', h1, h2, hr⟩
  · rw [h1, h2]
  · rw [h1, h2, hcp hr (hsh c h1), hsh c h1]

theorem copy0 {env env' : Env} (h : CopiesEnv env env') {n : Name}
    {P : Option ConstantInfo → Bool}
    (hP : ∀ {o}, P o = true → ∃ c, o = some c ∧ c.toConstantVal.levelParams.length = 0) :
    P (env'.find? n) = P (env.find? n) := by
  rcases h.find n with ⟨h1, h2⟩ | ⟨c, c', h1, h2, hr⟩
  · rw [h1, h2]
  · rw [h1, h2]; exact pred_copy0 hP hr

/-- **A copied environment is a copy in the reading's sense.** -/
theorem CopiesEnv.copy {env env' : Env} (hwf : EnvWF env) (h : CopiesEnv env env') :
    CopyEnv env env' := by
  have hnat : ConLeche.natLitSupported env' = ConLeche.natLitSupported env := by
    simp only [ConLeche.natLitSupported, copy0 h natIndOk_len, copy0 h natZeroOk_len,
      copy0 h natSuccOk_len]
  refine ⟨fun n => ?_, hnat, ?_, fun T i => ?_⟩
  · rcases h.find n with h1 | ⟨c, c', h1, h2, hr⟩
    · exact .inl h1
    · exact .inr ⟨c, c', h1, h2, hr.lpsCopy⟩
  · simp only [ConLeche.strLitSupported, hnat, copy0 h stringTyOk_len,
      copy0 h stringOfListTyOk_len, copy0 h charTyOk_len, copy0 h charOfNatTyOk_len,
      list_copy h (fun c hc => (shape_of_wf hwf hc).1 rfl) listTyOk_copy,
      list_copy h (fun c hc => (shape_of_wf hwf hc).2.1 rfl) listNilTyOk_copy,
      list_copy h (fun c hc => (shape_of_wf hwf hc).2.2 rfl) listConsTyOk_copy]
  · have hs : ∀ n, (env'.find? n).isSome = (env.find? n).isSome := fun n => by
      rcases h.find n with ⟨h1, h2⟩ | ⟨c, c', h1, h2, -⟩
      · rw [h1, h2]
      · rw [h1, h2]; rfl
    simp only [Env.findProj?, Env.findTable?, hs, h.tables]

/-! ## The model -/

/-- **A copy's type reads as the constant's**, at the assignment the copy's leaf reads. -/
theorem denote_copy {env env' : Env} (m : EnvModelM V env) (h : CopiesEnv env env')
    {n : Name} {c c' : ConstantInfo} (hf : env.find? n = some c) (hf' : env'.find? n = some c')
    (hr : ConstCopy c c') (φ : Name → Nat) :
    denote (renAcval m.base2.acval env env') env' φ 0 c'.toConstantVal.type
      = denote m.base2.acval env (renTr env env' n φ) 0 c.toConstantVal.type := by
  rw [denote_ren (h.copy m.base2.wf) m.base2.acval_params φ 0]
  unfold renTr
  rw [hf, hf']
  dsimp only
  rcases hr with rfl | ⟨ps, rfl, -, -⟩
  · rw [Level.substFn_param_self]
  · rw [atLps_cv]
    exact denote_instLevels m.base2.acval_params φ 0 _

/-- **The model of a copied environment**, read off the invariant of the original. -/
noncomputable def Model.ofCopies {env env' : Env} (m : EnvModelM V env)
    (h : CopiesEnv env env') : ConLeche.Model V env' where
  cval := cvalOf (renAcval m.base2.acval env env')
  mem := by
    intro c' hc' φ ρ
    obtain ⟨c, hc, hf, hf', hr⟩ := mem_copies h.consts h.nodup c' hc'
    have hn : c.name = c'.name := hr.name.symm
    obtain ⟨ta, hta⟩ := m.type_reads c hc (renTr env env' c'.name φ)
    have hta' := (denote_copy m h hf hf' hr φ).trans hta
    have hwf := m.base2.wf.consts c hc
    have hnf' : c'.toConstantVal.type.hasFvar = false := by
      rcases hr with rfl | ⟨ps, rfl, -, -⟩
      · exact hwf.1
      · rw [atLps_cv]; simpa [ConstantVal.atLps, Expr.hasFvar_instantiateLevelParams] using hwf.1
    have hlb' : c'.toConstantVal.type.looseBVarsBounded 0 = true := by
      rcases hr with rfl | ⟨ps, rfl, -, -⟩
      · exact hwf.2.2.2.1
      · rw [atLps_cv]
        simpa [ConstantVal.atLps, Expr.looseBVarsBounded_instantiateLevelParams] using hwf.2.2.2.1
    have hcl : ∀ n ψ, Term.Closed (renAcval m.base2.acval env env' n ψ) :=
      fun n ψ => m.base2.cval_closed n _
    have hbr := Denotes_of_denote (V := V) hcl 0 c'.toConstantVal.type hta'
      (fvarsBelow_zero_of_not_hasFvar hnf') hlb' ρ
    rw [Expr.closeN_of_hasFvar _ 0 0 hnf'] at hbr
    refine ⟨interp V ρ ta, hbr, ?_⟩
    rw [← interp_cvalOf hcl]
    show interp V ρ (m.base2.acval c'.name (renTr env env' c'.name φ)) ∈ˢ _
    rw [← hn]
    exact m.mem_type c hc _ ta (hn ▸ hta) ρ
  false_empty := by
    intro φ ρ F hd
    cases hd with
    | const hf' hlen =>
      rename_i ci'
      rcases h.find ConLeche.falseName with ⟨-, h2⟩ | ⟨c, c', h1, -, -⟩
      · rw [h2] at hf'; exact nomatch hf'
      · have hpd : ∀ ψ' : Name → Nat, ConLeche.Verify.pinnedStructT ConLeche.falseName ψ'
            = some (Term.const .empty [0]) := fun _ => by
          simp +decide [ConLeche.Verify.pinnedStructT]
        have he : renAcval m.base2.acval env env' ConLeche.falseName
            (Level.substFn φ ci'.toConstantVal.levelParams []) = Term.const .empty [0] :=
          m.base2.acval_pinned_free h1 (by decide) hpd
        rw [cvalOf, he, interp_const]
        rfl
  eq_equality := by
    intro u φ ρ E A a b hd hA ha hb
    cases hd with
    | const hf' hlen =>
      rename_i x
      rcases h.find ConLeche.eqName with ⟨-, h2⟩ | ⟨ci, ci', h1, h2, hr⟩
      · rw [h2] at hf'; exact nomatch hf'
      · have e : ci' = x := Option.some.inj (h2.symm.trans hf')
        subst e
        obtain ⟨-, -, hl⟩ := (m.base2.basis_pinned _ _ h1 (by decide)).1
        have hl1 : ci.toConstantVal.levelParams.length = 1 := hl
        have hl' : ci'.toConstantVal.levelParams.length = 1 := by
          rcases hr.lpsCopy with rfl | ⟨-, e⟩
          · exact hl1
          · rw [← e]; exact hl1
        match hq : ci.toConstantVal.levelParams, hl1, hq' : ci'.toConstantVal.levelParams, hl' with
        | [p], _, [p'], _ =>
        have hψ : renTr env env' ConLeche.eqName (Level.substFn φ [p'] [u]) p = Level.eval φ u := by
          simp [renTr, h1, h2, hq, hq', Level.substFn, Level.eval]
        have hlaw := (m.eq_law ci p h1 hq
          (renTr env env' ConLeche.eqName (Level.substFn φ [p'] [u]))).1 ρ A a b
          (by rw [hψ]; exact hA) ha hb
        rw [interp_cvalOf m.base2.cval_closed] at hlaw
        rw [hq'] at *
        exact hlaw

/-- The copied model's values are the original's leaves', read at the renamed assignment. -/
theorem Model.ofCopies_cval {env env' : Env} (m : EnvModelM V env) (h : CopiesEnv env env')
    {n : Name} {c c' : ConstantInfo} (hf : env.find? n = some c) (hf' : env'.find? n = some c')
    (φ : Name → Nat) :
    (Model.ofCopies m h).cval n φ = cvalOf m.base2.acval n
      (Level.substFn φ c.toConstantVal.levelParams
        (c'.toConstantVal.levelParams.map Level.param)) := by
  show cvalOf (renAcval m.base2.acval env env') n φ = _
  simp only [cvalOf, renAcval, renTr, hf, hf']

end ConLeche.Model

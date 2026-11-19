module

public import ConLeche.Model.Copies
public import ConLeche.Model.Inductives.RunEnv
public import ConLeche.Model.Modular.Proofs
import ConLeche.Model.BasisAtBlock
import ConLeche.Model.Reading.Levels

public section

/-!
# The invariant across copies of statements (task #619)

`EnvModelM.copyStmt` carries the model invariant from `env` to a copy `env'` (`CopiesEnv`) in
which only definitions, theorems and axioms at unreserved names differ (`StmtCopies`), each at
other level-parameter names.  The new valuation is `renAcval`: a renamed constant is read at
the assignment that gives its original's `i`-th parameter the copy's `i`-th parameter's value,
so every term reads alike on both sides (`denote_ren`).  Every inductive former, constructor,
recursor, quotient constant and reserved name keeps its entry, so every law keyed on one of
those keeps its leaf (`renAcval_same`); the `Nat` operations and the compiler-trust opaques
are pinned at no level parameter, so they keep theirs too (`ConstCopy.eq_of_nil`).
-/

namespace ConLeche.Model

open ConLeche.Semantics ConLeche.SetModel ConLeche.Term ConLeche.Verify SetTheory
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecRule IndCaps reservedBasisNames)

universe w

variable {V : Type w} [SetTheory V]

/-- **Only statements differ**: where a copy's constant is not the original's, the original is
a definition, a theorem or an axiom, at an unreserved name. -/
@[expose] def StmtCopies (env env' : Env) : Prop :=
  ∀ n c c', env.find? n = some c → env'.find? n = some c' → c' ≠ c →
    c.isStmtKind = true ∧ reservedBasisNames.contains n = false

theorem atLps_isStmtKind (c : ConstantInfo) (ps : List Name) :
    (c.atLps ps).isStmtKind = c.isStmtKind := by
  cases c <;> rfl

theorem ConstCopy.isStmtKind {c c' : ConstantInfo} (h : ConstCopy c c') :
    c'.isStmtKind = c.isStmtKind := by
  rcases h with rfl | ⟨ps, rfl, -⟩
  · rfl
  · exact atLps_isStmtKind c ps

theorem ConstCopy.len {c c' : ConstantInfo} (h : ConstCopy c c') :
    c'.toConstantVal.levelParams.length = c.toConstantVal.levelParams.length := by
  rcases h.lpsCopy with rfl | ⟨-, hl⟩
  · rfl
  · exact hl.symm

/-- A copy is the constant, or both are at some level parameter. -/
theorem ConstCopy.nil_cases {c c' : ConstantInfo} (h : ConstCopy c c') :
    c' = c ∨ (c.toConstantVal.levelParams.isEmpty = false ∧
      c'.toConstantVal.levelParams.isEmpty = false) := by
  cases h0 : c.toConstantVal.levelParams with
  | nil => exact .inl (h.eq_of_nil h0)
  | cons p ps =>
    right
    refine ⟨rfl, ?_⟩
    have hl := h.len
    rw [h0] at hl
    cases h1 : c'.toConstantVal.levelParams with
    | nil => rw [h1] at hl; exact nomatch hl
    | cons => rfl

section Find

variable {env env' : Env} (h : CopiesEnv env env')

include h

theorem CopiesEnv.isSome_eq (n : Name) : (env'.find? n).isSome = (env.find? n).isSome := by
  rcases h.find n with ⟨h1, h2⟩ | ⟨c, c', h1, h2, -⟩
  · rw [h1, h2]
  · rw [h1, h2]; rfl

theorem CopiesEnv.findTable_eq (T : Name) : env'.findTable? T = env.findTable? T := by
  simp only [Env.findTable?, h.isSome_eq, h.tables]

/-- **A lookup is kept, or both sides hold a constant at some level parameter.** -/
theorem CopiesEnv.find_cases (n : Name) :
    env'.find? n = env.find? n ∨ ∃ c c', env.find? n = some c ∧ env'.find? n = some c' ∧
      c.toConstantVal.levelParams.isEmpty = false ∧
      c'.toConstantVal.levelParams.isEmpty = false := by
  rcases h.find n with ⟨h1, h2⟩ | ⟨c, c', h1, h2, hr⟩
  · exact .inl (h2.trans h1.symm)
  · rcases hr.nil_cases with rfl | hl
    · exact .inl (h2.trans h1.symm)
    · exact .inr ⟨c, c', h1, h2, hl⟩

/-- A constant at no level parameter is kept. -/
theorem CopiesEnv.keep_nil {n : Name} {c : ConstantInfo} (hf : env.find? n = some c)
    (h0 : c.toConstantVal.levelParams = []) : env'.find? n = env.find? n := by
  rcases h.find n with ⟨h1, -⟩ | ⟨c₁, c', h1, h2, hr⟩
  · rw [h1] at hf; exact nomatch hf
  · rw [h1] at hf
    obtain rfl := Option.some.inj hf
    rw [h2, h1, hr.eq_of_nil h0]

theorem CopiesEnv.keep_nil' {n : Name} {c' : ConstantInfo} (hf : env'.find? n = some c')
    (h0 : c'.toConstantVal.levelParams = []) : env'.find? n = env.find? n := by
  rcases h.find n with ⟨-, h2⟩ | ⟨c, c₁, h1, h2, hr⟩
  · rw [h2] at hf; exact nomatch hf
  · rw [h2] at hf
    obtain rfl := Option.some.inj hf
    have hl := hr.len
    rw [h0] at hl
    rw [h2, h1, hr.eq_of_nil (List.eq_nil_of_length_eq_zero hl.symm)]

/-- `natOpCod` reads `Bool` only at no level parameter. -/
theorem CopiesEnv.natOpCod_eq (c : Name) (e : Expr) :
    ConLeche.natOpCod env' c e = ConLeche.natOpCod env c e := by
  unfold ConLeche.natOpCod
  rcases h.find_cases ConLeche.boolName with he | ⟨b, b', h1, h2, l1, l2⟩
  · rw [he]
  · rw [h1, h2]; simp [l1, l2]

theorem CopiesEnv.natOpTyPinned_eq (c : Name) (e : Expr) :
    ConLeche.natOpTyPinned env' c e = ConLeche.natOpTyPinned env c e := by
  unfold ConLeche.natOpTyPinned
  simp only [h.natOpCod_eq]

theorem CopiesEnv.natOpPinnedOk_eq (n : Name) :
    ConLeche.natOpPinnedOk env' n = ConLeche.natOpPinnedOk env n := by
  unfold ConLeche.natOpPinnedOk
  rcases h.find_cases n with he | ⟨b, b', h1, h2, l1, l2⟩
  · rw [he]; simp only [h.natOpTyPinned_eq]
  · rw [h1, h2]; simp [l1, l2]

theorem CopiesEnv.natOpGuard_eq (hwf : EnvWF env) (c : Name) :
    ConLeche.natOpGuard env' c = ConLeche.natOpGuard env c := by
  unfold ConLeche.natOpGuard
  simp only [(h.copy hwf).natLit, h.isSome_eq]
  rcases h.find_cases ConLeche.boolTrueName with e1 | ⟨b, b', h1, h2, l1, l2⟩ <;>
  rcases h.find_cases ConLeche.boolFalseName with e2 | ⟨d, d', g1, g2, k1, k2⟩ <;>
  (try rw [e1]) <;> (try rw [e2]) <;> (try rw [h1, h2]) <;> (try rw [g1, g2]) <;>
  first | rfl | simp [l1, l2, k1, k2] | simp [l1, l2] | simp [k1, k2]

end Find

section Stmt

variable {env env' : Env} (h : CopiesEnv env env') (hk : StmtCopies env env')

include h hk

/-- **A constant that is no statement, or at a reserved name, is kept.** -/
theorem CopiesEnv.keep {n : Name} {c : ConstantInfo} (hf : env.find? n = some c)
    (hc : c.isStmtKind = false ∨ reservedBasisNames.contains n = true) :
    env'.find? n = env.find? n := by
  rcases h.find n with ⟨h1, -⟩ | ⟨c₁, c', h1, h2, hr⟩
  · rw [h1] at hf; exact nomatch hf
  · rw [h1] at hf
    obtain rfl := Option.some.inj hf
    by_cases he : c' = c₁
    · rw [h2, h1, he]
    · obtain ⟨hs, hres⟩ := hk n c₁ c' h1 h2 he
      rcases hc with hc | hc
      · rw [hs] at hc; exact nomatch hc
      · rw [hres] at hc; exact nomatch hc

theorem CopiesEnv.keep' {n : Name} {c' : ConstantInfo} (hf : env'.find? n = some c')
    (hc : c'.isStmtKind = false ∨ reservedBasisNames.contains n = true) :
    env'.find? n = env.find? n := by
  rcases h.find n with ⟨-, h2⟩ | ⟨c, c₁, h1, h2, hr⟩
  · rw [h2] at hf; exact nomatch hf
  · rw [h2] at hf
    obtain rfl := Option.some.inj hf
    by_cases he : c₁ = c
    · rw [h2, h1, he]
    · obtain ⟨hs, hres⟩ := hk n c c₁ h1 h2 he
      rcases hc with hc | hc
      · rw [hr.isStmtKind, hs] at hc; exact nomatch hc
      · rw [hres] at hc; exact nomatch hc

/-- **A stored constant of the copy, against the original's.** -/
theorem CopiesEnv.mem_stmt {c' : ConstantInfo} (hc' : c' ∈ env'.consts) :
    ∃ c ∈ env.consts, env.find? c'.name = some c ∧ env'.find? c'.name = some c' ∧
      ConstCopy c c' ∧ (c' = c ∨ ∃ ps, c' = c.atLps ps ∧ ps.Nodup ∧
        c.toConstantVal.levelParams.length = ps.length ∧ c.isStmtKind = true ∧
        reservedBasisNames.contains c'.name = false) := by
  obtain ⟨c, hc, h1, h2, hr⟩ := mem_copies h.consts h.nodup c' hc'
  refine ⟨c, hc, h1, h2, hr, ?_⟩
  by_cases he : c' = c
  · exact .inl he
  · obtain ⟨hs, hres⟩ := hk c'.name c c' h1 h2 he
    rcases hr with he' | ⟨ps, rfl, hnd, hl, -⟩
    · exact absurd he' he
    · exact .inr ⟨ps, rfl, hnd, hl, hs, hres⟩

/-- A reserved name's lookup is kept. -/
theorem CopiesEnv.keep_res {n : Name} (hres : reservedBasisNames.contains n = true) :
    env'.find? n = env.find? n := by
  rcases h.find n with ⟨h1, h2⟩ | ⟨c, -, h1, -, -⟩
  · rw [h1, h2]
  · exact h.keep hk h1 (.inr hres)

end Stmt

/-! ## Well-formedness -/

section WF

variable {env env' : Env}

theorem litShapeOk_copy {c c' : ConstantInfo} (hr : ConstCopy c c')
    (hres : reservedBasisNames.contains c.name = false) (hs : ConLeche.litShapeOk c = true) :
    ConLeche.litShapeOk c' = true := by
  unfold ConLeche.litShapeOk at hs ⊢
  rw [hr.name]
  by_cases h1 : c.name = ConLeche.natName
  · rw [h1] at hres; exact absurd hres (by decide)
  by_cases h2 : c.name = ConLeche.natZeroName
  · rw [h2] at hres; exact absurd hres (by decide)
  by_cases h3 : c.name = ConLeche.natSuccName
  · rw [h3] at hres; exact absurd hres (by decide)
  simp only [h1, h2, h3, ↓reduceIte] at hs ⊢
  by_cases h4 : c.name = ConLeche.stringName
  · simp only [h4, ↓reduceIte] at hs ⊢; rw [pred_copy0 stringTyOk_len hr]; exact hs
  simp only [h4, ↓reduceIte] at hs ⊢
  by_cases h5 : c.name = ConLeche.stringOfListName
  · simp only [h5, ↓reduceIte] at hs ⊢; rw [pred_copy0 stringOfListTyOk_len hr]; exact hs
  simp only [h5, ↓reduceIte] at hs ⊢
  by_cases h6 : c.name = ConLeche.listName
  · simp only [h6, ↓reduceIte] at hs ⊢; exact listTyOk_copy hr hs
  simp only [h6, ↓reduceIte] at hs ⊢
  by_cases h7 : c.name = ConLeche.listNilName
  · simp only [h7, ↓reduceIte] at hs ⊢; exact listNilTyOk_copy hr hs
  simp only [h7, ↓reduceIte] at hs ⊢
  by_cases h8 : c.name = ConLeche.listConsName
  · simp only [h8, ↓reduceIte] at hs ⊢; exact listConsTyOk_copy hr hs
  simp only [h8, ↓reduceIte] at hs ⊢
  by_cases h9 : c.name = ConLeche.charName
  · simp only [h9, ↓reduceIte] at hs ⊢; rw [pred_copy0 charTyOk_len hr]; exact hs
  simp only [h9, ↓reduceIte] at hs ⊢
  by_cases h10 : c.name = ConLeche.charOfNatName
  · simp only [h10, ↓reduceIte] at hs ⊢; rw [pred_copy0 charOfNatTyOk_len hr]; exact hs
  simp only [h10, ↓reduceIte] at hs ⊢

/-- **A statement at other level-parameter names keeps its well-formedness.** -/
theorem constWF_stmt_atLps
    (hs : ∀ n, (env'.find? n).isSome = (env.find? n).isSome)
    {c : ConstantInfo} {ps : List Name} (hl : c.toConstantVal.levelParams.length = ps.length)
    (hk : c.isStmtKind = true) (hwf : ConstWF env c) : ConstWF env' (c.atLps ps) := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hwf
  have htype : (c.atLps ps).toConstantVal.type = c.toConstantVal.type.instantiateLevelParams
      c.toConstantVal.levelParams (ps.map Level.param) := by rw [atLps_cv]; rfl
  have hlps : (c.atLps ps).toConstantVal.levelParams = ps := by rw [atLps_cv]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [htype, Expr.hasFvar_instantiateLevelParams]; exact h1
  · rw [htype, hlps]; exact expr_defined_ren hl _ h2
  · rw [htype, Expr.constsResolve_instantiateLevelParams, Expr.constsResolve_eq_of_isSome hs]
    exact h3
  · rw [htype, Expr.looseBVarsBounded_instantiateLevelParams]; exact h4
  · intro cv v hint heq
    cases c with
    | defnInfo cv₀ v₀ hint₀ =>
      simp only [ConstantInfo.atLps, ConstantInfo.defnInfo.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      obtain ⟨g1, g2, g3, g4⟩ := h5 cv₀ v₀ hint₀ rfl
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [Expr.hasFvar_instantiateLevelParams]; exact g1
      · exact expr_defined_ren hl _ g2
      · rw [Expr.constsResolve_instantiateLevelParams, Expr.constsResolve_eq_of_isSome hs]
        exact g3
      · rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact g4
    | _ => simp [ConstantInfo.atLps] at heq
  · intro cv mI rP isK rules heq
    cases c with
    | recInfo => exact nomatch hk
    | _ => simp [ConstantInfo.atLps] at heq

/-- **The copy is well formed.** -/
theorem CopiesEnv.envWF (h : CopiesEnv env env') (hk : StmtCopies env env') (hwf : EnvWF env) :
    EnvWF env' := by
  have hs := h.isSome_eq
  refine ⟨fun c' hc' => ?_, fun c' hc' => ?_, fun t ht => ?_, fun c' hc' => ?_, fun c' hc' => ?_,
    fun c' hc' => ?_⟩
  · obtain ⟨c, hc, -, -, -, hor⟩ := h.mem_stmt hk hc'
    rcases hor with rfl | ⟨ps, rfl, -, hl, hst, -⟩
    · exact (hwf.consts _ hc).of_isSome hs
    · exact constWF_stmt_atLps hs hl hst (hwf.consts _ hc)
  · obtain ⟨c, hc, -, -, hr, hor⟩ := h.mem_stmt hk hc'
    rcases hor with rfl | ⟨ps, rfl, -, -, -, hres⟩
    · exact hwf.shapes _ hc
    · exact litShapeOk_copy hr (by rw [← atLps_name c ps]; exact hres) (hwf.shapes _ hc)
  · rw [h.tables] at ht
    exact (hwf.tables t ht).of_isSome hs
  · obtain ⟨c, hc, -, -, -, hor⟩ := h.mem_stmt hk hc'
    rcases hor with rfl | ⟨ps, rfl, -, -, hst, -⟩
    · exact hwf.inds _ hc
    · refine IndWF.of_not_ind fun cv caps he => ?_
      have := atLps_isStmtKind c ps
      rw [he, hst] at this
      exact nomatch this
  · obtain ⟨c, hc, -, -, -, hor⟩ := h.mem_stmt hk hc'
    rcases hor with rfl | ⟨ps, rfl, -, -, hst, -⟩
    · exact hwf.ctors _ hc
    · refine CtorWF.of_not_ctor fun cv nP nF T he => ?_
      have := atLps_isStmtKind c ps
      rw [he, hst] at this
      exact nomatch this
  · obtain ⟨c, hc, -, -, -, hor⟩ := h.mem_stmt hk hc'
    rcases hor with rfl | ⟨ps, rfl, -, -, hst, -⟩
    · exact hwf.rules _ hc
    · refine RuleWF.of_not_rec fun cv mI rP isK rules he => ?_
      have := atLps_isStmtKind c ps
      rw [he, hst] at this
      exact nomatch this

end WF

/-! ## The carrier -/

section Base

variable {env env' : Env}

theorem acvalParams_copies (m : EnvModel V env) (h : CopiesEnv env env') :
    ∀ (n : Name) (ci : ConstantInfo), env'.find? n = some ci →
      ∀ ψ₁ ψ₂ : Name → Nat, (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
        renAcval m.acval env env' n ψ₁ = renAcval m.acval env env' n ψ₂ := by
  intro n ci hf' ψ₁ ψ₂ hag
  rcases h.find n with ⟨-, h2⟩ | ⟨c, c', h1, h2, hr⟩
  · rw [h2] at hf'; exact nomatch hf'
  · rw [h2] at hf'
    obtain rfl := Option.some.inj hf'
    unfold renAcval
    refine m.acval_params n c h1 _ _ fun p hp => ?_
    rw [renTr_pair h1 h2, renTr_pair h1 h2]
    rcases hr.lpsCopy with rfl | ⟨-, hl⟩
    · rw [Level.substFn_param_self, Level.substFn_param_self]
      exact hag p hp
    · exact substFn_map_param_agree hl hag p hp

theorem basisPinned_copies (m : EnvModel V env) (h : CopiesEnv env env')
    (hk : StmtCopies env env') : BasisPinnedTT env' (renAcval m.acval env env') := by
  intro n ci hf' hres
  have he := h.keep' hk hf' (.inr hres)
  obtain ⟨hcp, hlk, hleaf⟩ := m.basis_pinned n ci (he.symm.trans hf') hres
  refine ⟨hcp, hlk.mono fun x cvj cnP cnF T hx => (h.keep' hk hx (.inl rfl)).symm.trans hx,
    fun t ψ ht => ?_⟩
  rw [renAcval_same he]
  exact hleaf t ψ ht

theorem projOk_copies (m : EnvModel V env) (h : CopiesEnv env env') (hk : StmtCopies env env') :
    ProjOkT env' := by
  intro T tbl hf
  rw [h.findTable_eq] at hf
  obtain ⟨h2, h3, h4, ⟨cvT, caps, hT, hlT⟩, ⟨cvC, iT, hC, hlC, hs⟩⟩ := m.proj_ok T tbl hf
  exact ⟨h2, h3, h4, ⟨cvT, caps, (h.keep hk hT (.inl rfl)).trans hT, hlT⟩,
    ⟨cvC, iT, (h.keep hk hC (.inl rfl)).trans hC, hlC, hs⟩⟩

theorem recCtors_copies (m : EnvModel V env) (h : CopiesEnv env env')
    (hk : StmtCopies env env') : RecCtorsStored env' := by
  intro n cv mI rP isK rules hf' r hr
  obtain ⟨cvj, a, b, iT, hj⟩ :=
    m.rec_ctors n cv mI rP isK rules ((h.keep' hk hf' (.inl rfl)).symm.trans hf') r hr
  exact ⟨cvj, a, b, iT, (h.keep hk hj (.inl rfl)).trans hj⟩

/-- **The carrier of the copy.** -/
@[expose] def EnvModel.copyStmt (m : EnvModel V env) (h : CopiesEnv env env')
    (hk : StmtCopies env env') : EnvModel V env' where
  wf := h.envWF hk m.wf
  acval := renAcval m.acval env env'
  cval_closed := fun n _ => m.cval_closed n _
  basis_pinned := basisPinned_copies m h hk
  proj_ok := projOk_copies m h hk
  rec_ctors := recCtors_copies m h hk
  acval_params := acvalParams_copies m h
  acval_wellDenoted := fun n _ ρ => m.acval_wellDenoted n _ ρ

end Base

/-! ## The invariant -/

section Core

variable {env env' : Env}

/-- A statement is no constructor. -/
theorem ctorEntry_stmt {C : Name} {c : ConstantInfo} (hs : c.isStmtKind = true) :
    ctorEntry C c = none := by
  cases c <;> first | rfl | exact nomatch hs

/-- **A recorded block's names are kept**: formers and constructors. -/
theorem CopiesEnv.lfp_names (h : CopiesEnv env env') (hk : StmtCopies env env')
    (mp : EnvModelM V env) {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) :
    (∀ mm, mm < D.k → env'.find? (D.member mm) = env.find? (D.member mm)) ∧
    (∀ c, c < D.N → ∀ j, j < D.nctors c →
      env'.find? (D.ctorName c j) = env.find? (D.ctorName c j)) := by
  obtain ⟨-, ⟨hst, hstC⟩, -⟩ := mp.lfp_ok D hD
  refine ⟨fun mm hmm => ?_, fun c hc j hj => ?_⟩
  · obtain ⟨cv, caps, hf⟩ := hst mm hmm
    exact h.keep hk hf (.inl rfl)
  · obtain ⟨cv, a, b, iT, hf⟩ := hstC c hc j hj
    exact h.keep hk hf (.inl rfl)

/-- **The transport**, keeping the recorded blocks. -/
theorem EnvModelM.copyStmtCore (mp : EnvModelM V env) (h : CopiesEnv env env')
    (hk : StmtCopies env env') :
    ∃ mp' : EnvModelM V env', mp'.base2.acval = renAcval mp.base2.acval env env' ∧
      mp'.lfpBlocks = mp.lfpBlocks := by
  have hcopy := h.copy mp.base2.wf
  have hde : ∀ (φ : Name → Nat) (d : Nat) (e : Expr),
      denote (renAcval mp.base2.acval env env') env' φ d e = denote mp.base2.acval env φ d e :=
    fun φ d e => denote_ren hcopy mp.base2.acval_params φ d e
  let m' := mp.base2.copyStmt h hk
  have hsame : ∀ {n : Name}, env'.find? n = env.find? n → m'.acval n = mp.base2.acval n :=
    fun he => renAcval_same he
  have hde' : ∀ (φ : Name → Nat) (d : Nat) (e : Expr),
      denote m'.acval env' φ d e = denote mp.base2.acval env φ d e := hde
  have hres : ∀ {n : Name}, reservedBasisNames.contains n = true →
      m'.acval n = mp.base2.acval n := fun hr => hsame (h.keep_res hk hr)
  -- a stored recursor's rules: the recursor, its constructors and their families are kept
  have hrec : ∀ φ : Name → Nat, RecRules m' φ := by
    intro φ n cv mI rP isK rules hf' rl hrl
    have he := h.keep' hk hf' (.inl rfl)
    have h1 := he.symm.trans hf'
    refine recRuleLaw_ren ?_ (mp.rec_rules φ n cv mI rP isK rules h1 rl hrl)
    obtain ⟨cvj0, a0, b0, iT0, hc0⟩ := mp.base2.rec_ctors n cv mI rP isK rules h1 rl hrl
    have hct : env'.find? (RecRule.ctor rl) = env.find? (RecRule.ctor rl) :=
      h.keep hk hc0 (.inl rfl)
    have hfam : ∀ cvj, ctorTypeFamily env'.find? cvj = ctorTypeFamily env.find? cvj :=
      fun _ => ctorFamily_ind_congr fun T _ _ cv caps =>
        ⟨fun hT => (h.keep' hk hT (.inl rfl)).symm.trans hT,
          fun hT => (h.keep hk hT (.inl rfl)).trans hT⟩
    refine ⟨fun d e => hde φ d e, rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl,
      fun _ _ => Iff.rfl, Iff.rfl, fun _ _ _ => rfl, fun us _ => congrFun (hsame he) _,
      fun cvj' cnP cnF iT hfc => ?_⟩
    have hfc0 := hct ▸ hfc
    exact ⟨cvj', hfc0, rfl, fun _ _ => rfl, fun _ _ => congrFun (hsame hct) _, rfl,
      fun _ _ => rfl, fun _ _ _ _ => Iff.rfl,
      fun _ us => famNZ_of_ctorFamily (hfam cvj') (fun d e => hde φ d e)⟩
  refine ⟨{ base2 := m'
            type_reads := ?_
            type_wellDenotedTy := ?_
            mem_type := ?_
            defn_reads := ?_
            nat_heads := ?_
            nat_ops := ?_
            div_mod := ?_
            eq_law := ?_
            rec_rules := hrec
            reduce_ops := ?_
            tower_ok := ?_
            lfpBlocks := mp.lfpBlocks
            lfp_ok := fun D hD => lfp_keep mp hcopy hD (h.lfp_names hk mp hD).1
              (h.lfp_names hk mp hD).2 }, rfl, rfl⟩
  · -- `type_reads`
    intro c' hc' ψ
    obtain ⟨c, hc, hf, hf', hr⟩ := mem_copies h.consts h.nodup c' hc'
    obtain ⟨ta, hta⟩ := mp.type_reads c hc (renTr env env' c'.name ψ)
    exact ⟨ta, (denote_copy mp h (n := c'.name) hf hf' hr ψ).trans hta⟩
  · -- `type_wellDenotedTy`
    intro c' hc' ψ ta hta ρ
    obtain ⟨c, hc, hf, hf', hr⟩ := mem_copies h.consts h.nodup c' hc'
    exact mp.type_wellDenotedTy c hc _ ta
      ((denote_copy mp h (n := c'.name) hf hf' hr ψ).symm.trans hta) ρ
  · -- `mem_type`
    intro c' hc' ψ ta hta ρ
    obtain ⟨c, hc, hf, hf', hr⟩ := mem_copies h.consts h.nodup c' hc'
    have hm := mp.mem_type c hc _ ta
      ((denote_copy mp h (n := c'.name) hf hf' hr ψ).symm.trans hta) ρ
    show interp V ρ (mp.base2.acval c'.name (renTr env env' c'.name ψ)) ∈ˢ _
    rwa [show mp.base2.acval c'.name = mp.base2.acval c.name by rw [hr.name]]
  · -- `defn_reads`
    intro ψ cv' v' ⟨hint, hd⟩
    obtain ⟨cv, v, hc, hn, hden, -, -⟩ := denote_copy_value mp h hd ψ
    obtain ⟨t, ht, hlr⟩ := mp.defn_reads (renTr env env' cv'.name ψ) cv v ⟨hint, hc⟩
    refine ⟨t, hden.trans ht, ?_⟩
    show LeafReads V (mp.base2.acval cv'.name (renTr env env' cv'.name ψ)) t
    rwa [show mp.base2.acval cv'.name = mp.base2.acval cv.name by rw [hn]]
  · -- `nat_heads`
    intro φ hsup ρ
    rw [hres (n := ConLeche.natZeroName) (by decide), hres (n := ConLeche.natSuccName) (by decide),
      hres (n := ConLeche.natName) (by decide)]
    exact mp.nat_heads φ (hcopy.natLit ▸ hsup) ρ
  · -- `nat_ops`
    intro φ c hc ci hf
    obtain ⟨ci0, hf0⟩ : ∃ ci0, env.find? c = some ci0 := by
      rcases h.find c with ⟨-, h2⟩ | ⟨c0, -, h1, -, -⟩
      · rw [h2] at hf; exact nomatch hf
      · exact ⟨c0, h1⟩
    obtain ⟨hgu, hpin, hlaw⟩ := mp.nat_ops φ c hc ci0 hf0
    have hpk : ConLeche.natOpPinnedOk env' = ConLeche.natOpPinnedOk env :=
      funext h.natOpPinnedOk_eq
    refine ⟨by rw [h.natOpGuard_eq mp.base2.wf]; exact hgu, by rw [hpk]; exact hpin,
      fun eq heq => ?_⟩
    obtain ⟨L, R, hL, hR, hval⟩ := hlaw eq heq
    exact ⟨L, R, by rw [hde']; exact hL, by rw [hde']; exact hR,
      by rw [hres (n := ConLeche.natName) (by decide)]; exact hval⟩
  · -- `div_mod`: every name the clauses read is kept
    intro φ c hc ci hf
    obtain ⟨ci0, hf0⟩ : ∃ ci0, env.find? c = some ci0 := by
      rcases h.find c with ⟨-, h2⟩ | ⟨c0, -, h1, -, -⟩
      · rw [h2] at hf; exact nomatch hf
      · exact ⟨c0, h1⟩
    obtain ⟨hgu, hpin, hlaw⟩ := mp.div_mod φ c hc ci0 hf0
    have hpk : ConLeche.natOpPinnedOk env' = ConLeche.natOpPinnedOk env :=
      funext h.natOpPinnedOk_eq
    refine ⟨by rw [h.natOpGuard_eq mp.base2.wf]; exact hgu, by rw [hpk]; exact hpin,
      fun ρ x y hx hy => ?_⟩
    rw [hres (n := ConLeche.natName) (by decide)] at hx hy
    have hdep : ∀ n ∈ ConLeche.natOpDeps c, env'.find? n = env.find? n := fun n hn => by
      obtain ⟨ci, hci, hl, -⟩ := ConLeche.natOpPinnedOk_inv (List.all_eq_true.mp hpin n hn)
      exact h.keep_nil hci hl
    obtain ⟨⟨ciT, hT, hlT⟩, ⟨ciF, hF, hlF⟩⟩ :=
      (ConLeche.natOpGuard_inv hgu).2.2 (.inr (.inr hc))
    have hble : ConLeche.natBleName ∈ ConLeche.natOpDeps c :=
      (by decide : ∀ c ∈ ConLeche.natDivModNames, ConLeche.natBleName ∈ ConLeche.natOpDeps c) c hc
    have hself := ConLeche.mem_natOpDeps_self (.inr hc)
    have hkeepN : ∀ n ∈ dmValNames c, env'.find? n = env.find? n := by
      intro n hn
      simp only [dmValNames, List.mem_cons] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hn
      · exact h.keep_res hk (by decide)
      · exact h.keep_nil hT hlT
      · exact h.keep_nil hF hlF
      · exact h.keep_res hk (by decide)
      · exact h.keep_res hk (by decide)
      · exact hdep _ hble
      · exact hdep _ hself
      · exact hdep _ hn
    exact (divModClausesV_congr hc fun n hn => by
      show interp V ρ (mp.base2.acval n φ) = interp V ρ (m'.acval n φ)
      rw [hsame (hkeepN n hn)]).mp (hlaw ρ x y hx hy)
  · -- `eq_law`
    intro ci p hf' hp ψ
    have he := h.keep_res hk (n := ConLeche.eqName) (by decide)
    rw [hsame he]
    exact mp.eq_law ci p (he.symm.trans hf') hp ψ
  · -- `reduce_ops`: the opaques are at no level parameter
    intro c hc cv' hf' hpin
    have hl : cv'.levelParams = [] := by
      simp only [ConstantVal.matchesPin, Bool.and_eq_true, decide_eq_true_eq] at hpin
      rw [hpin.1.2]
      exact (by decide : ∀ c ∈ ConLeche.reduceOpNames,
        (ConLeche.reduceOpCvA c).levelParams = []) c hc
    have he := h.keep_nil' (c' := .axiomInfo cv') hf' hl
    have hf := he.symm.trans hf'
    obtain ⟨hs, hlaw⟩ := mp.reduce_ops c hc cv' hf hpin
    refine ⟨by rw [h.isSome_eq]; exact hs, fun ψ ρ x hx => ?_⟩
    rw [hsame he]
    have hlx := hlaw (renTr env env' (ConLeche.reduceElemName c) ψ) ρ x hx
    rwa [mp.base2.acval_params c _ hf (renTr env env' (ConLeche.reduceElemName c) ψ) ψ
      (fun p hp => by simp [ConstantInfo.toConstantVal, hl] at hp)] at hlx
  · -- `tower_ok`: a table's former and constructor are kept
    intro φ
    refine ⟨fun T tbl hf => ?_, fun T i entry hf => ?_⟩
    · rw [h.findTable_eq] at hf
      obtain ⟨-, -, -, -, ⟨cvC, iTC, hC, -⟩⟩ := mp.base2.proj_ok T tbl hf
      obtain ⟨⟨cvT, capsT, hfT, hlpsT⟩, hetaL⟩ := (mp.tower_ok φ).table T tbl hf
      have heT := h.keep hk hfT (.inl rfl)
      have heC := h.keep hk hC (.inl rfl)
      refine ⟨⟨cvT, capsT, heT.trans hfT, hlpsT⟩, ?_⟩
      intro cvT' capsT' hfT' us hus
      rw [heT] at hfT'
      obtain ⟨hlaw', hcoh⟩ := hetaL cvT' capsT' hfT' us hus
      refine ⟨?_, fun he => ?_⟩
      · rw [hsame heT, hsame heC]; exact hlaw'
      · exact (hcoh he).transport (m₂ := m')
          (fun _ _ _ _ hf₂ => by rw [heC] at hf₂; exact hf₂)
          (fun _ _ _ _ _ _ hTCa => by rw [hde']; exact hTCa)
          (congrFun (hsame heT) _) (fun _ _ _ => rfl)
    · rw [hcopy.findProj] at hf
      obtain ⟨hsn, hidx, hlt, ⟨cvT, capsT, hfT, hlpsT⟩, cvC, iT, hfC, hlpsC, hlaw⟩ :=
        (mp.tower_ok φ).entry T i entry hf
      have heT := h.keep hk hfT (.inl rfl)
      have heC := h.keep hk hfC (.inl rfl)
      refine ⟨hsn, hidx, hlt, ⟨cvT, capsT, heT.trans hfT, hlpsT⟩,
        cvC, iT, heC.trans hfC, hlpsC, fun us hus => ?_⟩
      obtain ⟨⟨Ta, hTa, hA⟩, ⟨TCa, hTCa, hB⟩⟩ := hlaw us hus
      refine ⟨⟨Ta, by rw [hde']; exact hTa, ?_⟩, ⟨TCa, by rw [hde']; exact hTCa, ?_⟩⟩
      · rw [hsame heT]
        exact fun ρ vs x rest h₁ h₂ h₃ h₄ h₅ h₆ hg =>
          hA ρ vs x rest h₁ h₂ h₃ h₄ h₅ h₆ (hg.imp_left (TowerGuardAt.mono
            (by rw [hsn]; exact heT)
            (fun _ _ _ _ ht => by rw [hde']; exact ht) fun _ ht => by rw [hde']; exact ht))
      · rw [hsame heC]
        exact hB

/-- **The invariant across copies of statements**: an invariant of `env` is one of `env'`, at
the renamed valuation, and its coverage carries over. -/
theorem EnvModelM.copyStmt (mp : EnvModelM V env) (hcov : LfpCover mp [])
    (h : CopiesEnv env env')
    (hk : ∀ n c c', env.find? n = some c → env'.find? n = some c' → c' ≠ c →
      c.isStmtKind = true ∧ reservedBasisNames.contains n = false) :
    ∃ mp' : EnvModelM V env', mp'.base2.acval = renAcval mp.base2.acval env env' ∧
      LfpCover mp' [] := by
  obtain ⟨mp', hac, hbl⟩ := mp.copyStmtCore h hk
  refine ⟨mp', hac, ?_⟩
  have hind : ∀ T cv caps, env'.find? T = some (.indInfo cv caps) →
      env.find? T = some (.indInfo cv caps) :=
    fun _ _ _ hf => (h.keep' hk hf (.inl rfl)).symm.trans hf
  have hlook : ∀ C n, ctorLook env'.find? C n = ctorLook env.find? C n := by
    intro C n
    refine ctorLook_congr (fun x => ?_) n
    rcases h.find x with ⟨g1, g2⟩ | ⟨d, d', g1, g2, hrd⟩
    · exact ⟨default, default, .inl ⟨g1, g2⟩⟩
    · refine ⟨d, d', .inr ⟨g1, g2, ?_⟩⟩
      by_cases he : d' = d
      · rw [he]
      · obtain ⟨hs, -⟩ := hk x d d' g1 g2 he
        rw [ctorEntry_stmt hs, ctorEntry_stmt (hrd.isStmtKind.trans hs)]
  have hkeepD := fun {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) => h.lfp_names hk mp hD
  exact {
    cover := fun n cv caps hf hn hq => by
      rw [hbl]
      exact hcov.cover n cv caps (hind _ _ _ hf) hn hq
    nodup := fun D hD => hcov.nodup D (hbl ▸ hD)
    len := fun D hD => hcov.len D (hbl ▸ hD)
    all := fun D hD mm hmm cv caps hf => by
      rw [hbl] at hD
      rw [(hkeepD hD).1 mm hmm] at hf
      exact hcov.all D hD mm hmm cv caps hf
    fresh := fun _ _ _ _ hin => absurd hin List.not_mem_nil
    own := fun D hD => by
      rw [hbl] at hD
      have hkk := hcov.wid D hD
      exact (hcov.own D hD).monoOn (hkeepD hD).1
        (fun c hc' j hj => (hkeepD hD).2 c (hkk ▸ hc') j hj)
        fun c hc' => nestContainer_congr ((hkeepD hD).1 c hc') (hlook _)
    wid := fun D hD => hcov.wid D (hbl ▸ hD) }

/-- **`NatFacts` across a copy**: the same names are stored. -/
theorem NatFacts.copies (h : CopiesEnv env env') (hN : NatFacts env) : NatFacts env' := by
  refine ⟨?_⟩
  simp only [h.isSome_eq]
  exact hN.trio

/-- **Every proof's leaf is the canonical proof, in the copy**: a renamed statement's type reads
as the original's at some assignment, and every assignment of the original is reached. -/
theorem ProofLeaves.copies (mp : EnvModelM V env) (h : CopiesEnv env env')
    (hpl : ConLeche.Model.Modular.ProofLeaves V env mp.base2.acval) :
    ConLeche.Model.Modular.ProofLeaves V env' (renAcval mp.base2.acval env env') := by
  intro n ci' hf' hks
  rcases h.find n with ⟨-, h2⟩ | ⟨c, c', h1, h2, hr⟩
  · rw [h2] at hf'; exact nomatch hf'
  rw [h2] at hf'
  obtain rfl := Option.some.inj hf'
  obtain ⟨p1, p2⟩ := hpl n c h1 (hr.isStmtKind ▸ hks)
  have hden := denote_copy mp h h1 h2 hr
  refine ⟨fun ⟨cv, hcv⟩ => ?_, fun hs => ?_⟩
  · have hthm : ∃ cv, c = .thmInfo cv := by
      rcases hr with rfl | ⟨ps, rfl, -⟩
      · exact ⟨cv, hcv⟩
      · cases c with
        | thmInfo cv₀ => exact ⟨cv₀, rfl⟩
        | _ => simp [ConstantInfo.atLps] at hcv
    intro ψ Ta hTa ρ
    exact p1 hthm _ Ta ((hden ψ).symm.trans hTa) ρ
  · have hsc : SemPropType V mp.base2.acval env c.toConstantVal.type := by
      intro ψ Ta hTa ρ
      -- an assignment of the copy reading as `ψ` at the original's parameters
      have hdef := (mp.base2.wf.consts c (ConLeche.Env.find?_mem h1)).2.1
      let ψ' := Level.substFn ψ c'.toConstantVal.levelParams
        (c.toConstantVal.levelParams.map Level.param)
      have hag : ∀ p ∈ c.toConstantVal.levelParams, renTr env env' n ψ' p = ψ p := by
        intro p hp
        rw [renTr_pair h1 h2]
        rcases hr.lpsCopy with rfl | ⟨hnd, hl⟩
        · simp only [ψ', Level.substFn_param_self]
        · rw [substFn_ren (us := c.toConstantVal.levelParams.map Level.param) hnd hl
            (by rw [List.length_map]; exact hl) (fun _ _ => rfl) p hp, Level.substFn_param_self]
      refine hs ψ' Ta ?_ ρ
      rw [hden ψ', denote_params_ext mp.base2 hag 0 _ hdef]
      exact hTa
    funext ψ
    show mp.base2.acval n (renTr env env' n ψ) = .prf
    rw [p2 hsc]

end Core

end ConLeche.Model

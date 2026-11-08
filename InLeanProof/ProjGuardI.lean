module

public import InLeanProof.WalksInferBody
import ConLeche.Verify.LooseBVar
import ConLeche.Verify.ProjGuard
import ConLeche.Verify.Denote.IndFrame

/-!
# The projection guard's field loop against master's (task #451, lane follow-master)

InLean's guard (`InLean.checkProjGuardI`) is the twin of master's
`checkProjGuard`: the structure's sort (`projGuardSortI`), the constructor's
type at the use's levels with its parameters opened (`constTyAtM`,
`openPisAtFvarsM`), its fields stepped as official `infer_proj` does
(`projGuardRowsGoM`, twin of `projGuardRowsGo`), and the rows' sorts
(`checkGuardRowsI`).  This file has the parameters' opener
(`openPisAtFvarsI_run`, master's pure `openPisAtFvars` at the translation,
read at the final state) and the loop: `projGuardRowsGoI_run`, an answer's
rows read at the final state as master's on the translated telescope.  A field the rest of the telescope does not use is stepped over in
both (`hasLooseBVarI_TrS`: InLean's occurrence test is master's on the
reading), unopened.  Then the rows' sorts (`checkGuardRowsI_run`), the sort
they answer to (`projGuardSortI_run`), the rows at a sort
(`checkProjRowsI_run`, master's `projGuardRows` on the translated entry, whose
rows' scoping is master's `projGuardRows_ws`), and the guard:
**`projGuardSpecI_of`**, `ProjGuardSpecI` from the knot's specs and what the
bodies read of the environment (`EnvWF`, `EnvRelI`, `EnvViewI`), so the knot's
bodies discharge it themselves (`bodiesI_of`).

The proofs are functional (`bind_run`, `pure_run`), as O7's.
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached
open scoped Lean.Order

variable {mode : ConLeche.CheckMode} {eager : Bool} {env : ConLeche.Env}

/-! ## The telescope opener -/

/-- **Opening a telescope at interned variables** (master's `openPisAtFvars` at
the translation): an answer reads, at the final state, as master's on the
translated term. -/
theorem openPisAtFvarsI_run :
    ∀ (n i : Nat) {e : Lean.Expr} {s₀ : InLean.CState} {r : Option (List Lean.Expr × Lean.Expr)}
      {s' : InLean.CState},
      CSOKI mode eager env s₀ → OkS s₀ e = true → (TrS s₀ e).looseBVarsBounded 0 = true →
      InLean.openPisAtFvarsM n e i s₀ = .ok (r, s') →
      CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
        ∀ fvs b, r = some (fvs, b) → OkSL s' fvs = true ∧ OkS s' b = true ∧
          ConLeche.openPisAtFvars n (TrS s₀ e) i = some (TrSL s' fvs, TrS s' b)
  | 0, i, e, s₀, r, s', hs, hok, _, h => by
    rw [InLean.openPisAtFvarsM] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    refine ⟨hs, TabLe.refl _, ?_⟩
    rintro fvs b ⟨⟩
    exact ⟨rfl, hok, rfl⟩
  | n + 1, i, .mdata _ e, s₀, r, s', hs, hok, hc, h => by
    rw [InLean.openPisAtFvarsM] at h
    rw [OkS_mdata] at hok
    rw [TrS_mdata] at hc ⊢
    exact openPisAtFvarsI_run (n + 1) i hs hok hc h
  | n + 1, i, .forallE nm dom body bi, s₀, r, s', hs, hok, hc, h => by
    rw [InLean.openPisAtFvarsM] at h
    simp only [OkS_forallE, Bool.and_eq_true] at hok
    rw [TrS_forallE, lbb_forallE, Bool.and_eq_true] at hc
    obtain ⟨x, s₂, hx, h⟩ := bind_run h
    obtain ⟨hs₂, ht₂, hokx, htx⟩ := tripleI_iff_run.1 (mkFVarM_specI hs i hok.1 hc.1) x s₂ hx
    obtain ⟨r', s₃, hr, h⟩ := bind_run h
    have hb₂ : OkS s₂ body = true := okS_of_tabLe ht₂ hok.2
    have hcx : (TrS s₂ x).looseBVarsBounded 0 = true := by rw [htx]; rfl
    have hokI : OkS s₂ (body.inst1I x) = true := OkS_inst1 hb₂ hokx hcx
    have hTI : TrS s₂ (body.inst1I x) =
        (TrS s₀ body).instantiate1 (.fvar i (TrS s₀ dom)) 0 := by
      rw [inst1I_eq, TrS_inst1_eq hb₂ hokx hcx, htx, TrS_of_tabLe ht₂ hok.2]
    obtain ⟨hs₃, ht₃, hR⟩ := openPisAtFvarsI_run n (i + 1) hs₂ hokI
      (by rw [hTI]; exact lbb_instantiate1 rfl hc.2) hr
    have ht23 : TabLe s₀ s₃ := ht₂.trans ht₃
    cases r' with
    | none =>
      obtain ⟨rfl, rfl⟩ := pure_run h
      exact ⟨hs₃, ht23, by rintro _ _ ⟨⟩⟩
    | some q =>
      obtain ⟨fvs', b'⟩ := q
      obtain ⟨rfl, rfl⟩ := pure_run h
      refine ⟨hs₃, ht23, ?_⟩
      rintro fvs b ⟨⟩
      obtain ⟨hokf, hokb, hm⟩ := hR fvs' b' rfl
      refine ⟨?_, hokb, ?_⟩
      · simp only [OkSL, List.all_cons, Bool.and_eq_true]
        exact ⟨okS_of_tabLe ht₃ hokx, hokf⟩
      · rw [TrS_forallE]
        simp only [ConLeche.openPisAtFvars]
        rw [← hTI, hm]
        simp only [TrSL, List.map_cons, TrS_of_tabLe ht₃ hokx, htx]
  | _ + 1, _, .bvar _, _, _, _, hs, _, _, h | _ + 1, _, .fvar _, _, _, _, hs, _, _, h
  | _ + 1, _, .mvar _, _, _, _, hs, _, _, h | _ + 1, _, .sort _, _, _, _, hs, _, _, h
  | _ + 1, _, .const _ _, _, _, _, hs, _, _, h | _ + 1, _, .app _ _, _, _, _, hs, _, _, h
  | _ + 1, _, .lam _ _ _ _, _, _, _, hs, _, _, h | _ + 1, _, .letE _ _ _ _ _, _, _, _, hs, _, _, h
  | _ + 1, _, .lit _, _, _, _, hs, _, _, h | _ + 1, _, .proj _ _ _, _, _, _, hs, _, _, h => by
    simp only [InLean.openPisAtFvarsM] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, by rintro _ _ ⟨⟩⟩

/-- InLean's occurrence test on a term with a reading is master's on the
reading. -/
theorem hasLooseBVarI_TrS {s : InLean.CState} {e : Lean.Expr} (h : OkS s e = true) (i : Nat) :
    e.hasLooseBVarI i = (TrS s e).hasLooseBVarB i := by
  rw [ConLeche.Expr.hasLooseBVarB_eq]
  exact toExpr_hasLooseBVar (FVarTable.trans_fvarsOnly _) (RangeOk_of_OkS h) (TransS_of_ok h) i

/-- **The guard's field loop at interned variables** (master's
`projGuardRowsGo` at the translation): an answer's rows read, at the final
state, as master's on the translated telescope. -/
theorem projGuardRowsGoI_run :
    ∀ (k d : Nat) {e : Lean.Expr} {s₀ : InLean.CState}
      {r : Option (List (Nat × Lean.Expr))} {s' : InLean.CState},
      CSOKI mode eager env s₀ → OkS s₀ e = true → (TrS s₀ e).looseBVarsBounded 0 = true →
      InLean.projGuardRowsGoM k d e s₀ = .ok (r, s') →
      CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
        ∀ rows, r = some rows →
          (∀ p ∈ rows, OkS s' p.2 = true ∧ (TrS s' p.2).looseBVarsBounded 0 = true) ∧
          ConLeche.projGuardRowsGo k d (TrS s₀ e) = some (rows.map fun p => (p.1, TrS s' p.2))
  | k, d, .mdata _ e, s₀, r, s', hs, hok, hc, h => by
    rw [InLean.projGuardRowsGoM] at h
    rw [OkS_mdata] at hok
    rw [TrS_mdata] at hc ⊢
    exact projGuardRowsGoI_run k d hs hok hc h
  | 0, d, .forallE nm dom body bi, s₀, r, s', hs, hok, hc, h => by
    rw [InLean.projGuardRowsGoM] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    simp only [OkS_forallE, Bool.and_eq_true] at hok
    rw [TrS_forallE, lbb_forallE, Bool.and_eq_true] at hc
    refine ⟨hs, TabLe.refl _, ?_⟩
    rintro rows ⟨⟩
    refine ⟨by simp [hok.1, hc.1], ?_⟩
    rw [TrS_forallE]
    rfl
  | k + 1, d, .forallE nm dom body bi, s₀, r, s', hs, hok, hc, h => by
    rw [InLean.projGuardRowsGoM] at h
    simp only [OkS_forallE, Bool.and_eq_true] at hok
    rw [TrS_forallE, lbb_forallE, Bool.and_eq_true] at hc
    have hlb := hasLooseBVarI_TrS hok.2 0
    rw [TrS_forallE]
    cases hb : body.hasLooseBVarI 0
    · -- stepped over, unopened
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
      have hc0 : (TrS s₀ body).looseBVarsBounded 0 = true :=
        ConLeche.Expr.looseBVarsBounded_of_not_hasLooseBVar _ hc.2
          (by rw [← ConLeche.Expr.hasLooseBVarB_eq, ← hlb, hb])
      obtain ⟨hs', ht', hR⟩ := projGuardRowsGoI_run k (d + 1) hs hok.2 hc0 h
      refine ⟨hs', ht', fun rows hr => ?_⟩
      obtain ⟨hokr, hm⟩ := hR rows hr
      refine ⟨hokr, ?_⟩
      simp only [ConLeche.projGuardRowsGo, ← hlb, hb, Bool.false_eq_true, ↓reduceIte]
      exact hm
    · -- a row, opened at its variable
      simp only [hb, ↓reduceIte] at h
      obtain ⟨x, s₂, hx, h⟩ := bind_run h
      obtain ⟨hs₂, ht₂, hokx, htx⟩ := tripleI_iff_run.1 (mkFVarM_specI hs d hok.1 hc.1) x s₂ hx
      obtain ⟨r', s₃, hr, h⟩ := bind_run h
      have hb₂ : OkS s₂ body = true := okS_of_tabLe ht₂ hok.2
      have hcx : (TrS s₂ x).looseBVarsBounded 0 = true := by rw [htx]; rfl
      have hokI : OkS s₂ (body.inst1I x) = true := OkS_inst1 hb₂ hokx hcx
      have hTI : TrS s₂ (body.inst1I x) =
          (TrS s₀ body).instantiate1 (.fvar d (TrS s₀ dom)) 0 := by
        rw [inst1I_eq, TrS_inst1_eq hb₂ hokx hcx, htx, TrS_of_tabLe ht₂ hok.2]
      obtain ⟨hs₃, ht₃, hR⟩ := projGuardRowsGoI_run k (d + 1) hs₂ hokI
        (by rw [hTI]; exact lbb_instantiate1 rfl hc.2) hr
      have ht23 : TabLe s₀ s₃ := ht₂.trans ht₃
      cases r' with
      | none =>
        obtain ⟨rfl, rfl⟩ := pure_run h
        exact ⟨hs₃, ht23, by rintro _ ⟨⟩⟩
      | some rows' =>
        obtain ⟨rfl, rfl⟩ := pure_run h
        refine ⟨hs₃, ht23, ?_⟩
        rintro rows ⟨⟩
        obtain ⟨hokr, hm⟩ := hR rows' rfl
        refine ⟨?_, ?_⟩
        · intro p hp
          rcases List.mem_cons.1 hp with rfl | hp
          · exact ⟨okS_of_tabLe ht23 hok.1, by rw [TrS_of_tabLe ht23 hok.1]; exact hc.1⟩
          · exact hokr p hp
        · simp only [ConLeche.projGuardRowsGo, ← hlb, hb, ↓reduceIte]
          rw [← hTI, hm]
          simp only [List.map_cons, TrS_of_tabLe ht23 hok.1]
  | 0, _, .bvar _, _, _, _, hs, _, _, h | 0, _, .fvar _, _, _, _, hs, _, _, h
  | 0, _, .mvar _, _, _, _, hs, _, _, h | 0, _, .sort _, _, _, _, hs, _, _, h
  | 0, _, .const _ _, _, _, _, hs, _, _, h | 0, _, .app _ _, _, _, _, hs, _, _, h
  | 0, _, .lam _ _ _ _, _, _, _, hs, _, _, h | 0, _, .letE _ _ _ _ _, _, _, _, hs, _, _, h
  | 0, _, .lit _, _, _, _, hs, _, _, h | 0, _, .proj _ _ _, _, _, _, hs, _, _, h
  | _ + 1, _, .bvar _, _, _, _, hs, _, _, h | _ + 1, _, .fvar _, _, _, _, hs, _, _, h
  | _ + 1, _, .mvar _, _, _, _, hs, _, _, h | _ + 1, _, .sort _, _, _, _, hs, _, _, h
  | _ + 1, _, .const _ _, _, _, _, hs, _, _, h | _ + 1, _, .app _ _, _, _, _, hs, _, _, h
  | _ + 1, _, .lam _ _ _ _, _, _, _, hs, _, _, h | _ + 1, _, .letE _ _ _ _ _, _, _, _, hs, _, _, h
  | _ + 1, _, .lit _, _, _, _, hs, _, _, h | _ + 1, _, .proj _ _ _, _, _, _, hs, _, _, h => by
    simp only [InLean.projGuardRowsGoM] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, by rintro _ ⟨⟩⟩

/-! ## The rows' sorts -/

variable {r : InLean.CoreFnsI}

/-- **The rows of a projection's guard** (`checkGuardRowsC_spec`'s twin): each
row's domain read at the starting state, master's rows on the readings. -/
theorem checkGuardRowsI_run (ih : KnotSpecI mode eager env r) {g : Level} (hg : okL g = true) :
    ∀ (rows : List (Nat × Lean.Expr)) {s₀ s' : InLean.CState} {v : Unit},
      CSOKI mode eager env s₀ →
      (∀ p ∈ rows, OkS s₀ p.2 = true ∧ ConLeche.Expr.WScoped p.1 (TrS s₀ p.2) ∧
        (TrS s₀ p.2).looseBVarsBounded 0 = true) →
      InLean.checkGuardRowsI r.inferIO r.whnf g rows s₀ = .ok (v, s') →
      CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
        Runs (ConLeche.checkGuardRows (ConLeche.fueledFns mode eager env).inferIO
          (ConLeche.fueledFns mode eager env).whnf (trL g)
          (rows.map fun p => (p.1, TrS s₀ p.2))) ()
  | [], s₀, s', v, hs, _, h => by
    rw [InLean.checkGuardRowsI] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, Runs.pure _⟩
  | (d, dom) :: rest, s₀, s', v, hs, hrows, h => by
    obtain ⟨hok, hw, hc⟩ := hrows _ List.mem_cons_self
    rw [InLean.checkGuardRowsI] at h
    obtain ⟨t, s₁, hti, h⟩ := bind_run h
    obtain ⟨hs₁, ht₁, hokt, hRt, hwt, hct⟩ := tripleI_iff_run.1 (ih.inferIO hs hok hw hc) t s₁ hti
    obtain ⟨w, s₂, hwi, h⟩ := bind_run h
    obtain ⟨hs₂, ht₂, hokw, hRw, -, -⟩ := tripleI_iff_run.1 (ih.whnf hs₁ hokt hwt hct) w s₂ hwi
    have ht12 : TabLe s₀ s₂ := ht₁.trans ht₂
    generalize hx : EO.stripTop w = x at h
    have hT : TrS s₂ w = TrS s₂ x := by rw [← hx, TrS_stripTop]
    have hokx : OkS s₂ x = true := by rw [← hx, OkS_stripTop]; exact hokw
    cases x with
    | sort u =>
      simp only at h
      have hu : okL u = true := by
        simp only [OkS_sort, okLv, Bool.and_eq_true] at hokx; exact hokx.1
      cases hz : InLean.Lvl.zeroWhereZero g u
      · simp only [hz] at h
        obtain ⟨_, _, h1, _⟩ := bind_run h
        exact (throw_run h1).elim
      · simp only [hz] at h
        have hrest : ∀ p ∈ rest, OkS s₂ p.2 = true ∧ ConLeche.Expr.WScoped p.1 (TrS s₂ p.2) ∧
            (TrS s₂ p.2).looseBVarsBounded 0 = true := by
          intro p hp
          obtain ⟨h1, h2, h3⟩ := hrows p (List.mem_cons_of_mem _ hp)
          rw [TrS_of_tabLe ht12 h1]
          exact ⟨okS_of_tabLe ht12 h1, h2, h3⟩
        obtain ⟨hs', ht', hR⟩ := checkGuardRowsI_run ih hg rest hs₂ hrest h
        have hmap : (rest.map fun p => (p.1, TrS s₂ p.2)) = rest.map fun p => (p.1, TrS s₀ p.2) := by
          apply List.map_congr_left
          intro p hp
          rw [TrS_of_tabLe ht12 (hrows p (List.mem_cons_of_mem _ hp)).1]
        rw [hmap] at hR
        refine ⟨hs', ht12.trans ht', ?_⟩
        simp only [List.map_cons]
        rw [ConLeche.checkGuardRows]
        refine Runs.bind hRt (Runs.bind hRw ?_)
        rw [hT, TrS_sort]
        simp only [zeroWhereZero_trL hg hu, hz]
        first | exact hR | exact Runs.bind (Runs.pure ()) hR
    | mdata _ _ => exact (stripTop_ne_mdata hx).elim
    | _ => exact (throw_run h).elim

/-! ## The sort the rows answer to -/

theorem isAlwaysZero_trL (u : Level) :
    ConLeche.Level.isAlwaysZero (trL u) = InLean.Lvl.isAlwaysZero u := by
  unfold ConLeche.Level.isAlwaysZero InLean.Lvl.isAlwaysZero
  rw [← trPW_zeronessOf]
  cases InLean.Lvl.zeronessOf u with
  | never => rfl
  | ifAllZero ps => cases ps <;> rfl

/-- **The sort a projection's rows answer to** (`projGuardSortC_spec`'s twin):
the structure is a stored record, closed. -/
theorem projGuardSortI_run (ih : KnotSpecI mode eager env r) {cvT : Lean.ConstantVal}
    {ccvT : ConLeche.ConstantVal} (hcv : CVRel cvT ccvT) (hcl : ccvT.type.hasFvar = false)
    (hlbb : ccvT.type.looseBVarsBounded 0 = true) (caps : InLean.IndCaps) {us : List Level}
    (hus : us.all okLv = true) {s₀ s' : InLean.CState} {o : Option Level}
    (hs : CSOKI mode eager env s₀)
    (hr : InLean.projGuardSortI r.whnf cvT caps us s₀ = .ok (o, s')) :
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ (∀ g, o = some g → okL g = true) ∧
      Runs (ConLeche.projGuardSort (ConLeche.fueledFns mode eager env).whnf ccvT (toCaps caps)
        (us.map trL)) (o.map trL) := by
  have hty : TrS s₀ cvT.type = ccvT.type := hcv.2.2.trS s₀
  have hrs : ConLeche.formerResSort ccvT.type = (InLean.formerResSort cvT.type).map trL := by
    rw [← hty, formerResSort_TrS]
  unfold ConLeche.projGuardSort
  unfold InLean.projGuardSortI at hr
  rw [hrs]
  cases hf : InLean.formerResSort cvT.type with
  | some u =>
    simp only [hf] at hr
    obtain ⟨rfl, rfl⟩ := pure_run hr
    refine ⟨hs, TabLe.refl _, ?_, ?_⟩
    · intro g hg
      cases hz : InLean.Lvl.isAlwaysZero u <;> simp [hz] at hg; subst hg; rfl
    · simp only [Option.map_some, isAlwaysZero_trL]
      cases InLean.Lvl.isAlwaysZero u <;> exact Runs.pure _
  | none =>
    simp only [hf] at hr
    obtain ⟨ty, s₁, hty1, hr⟩ := bind_run hr
    obtain ⟨hs₁, ht₁, hok₁, htr₁⟩ := tripleI_iff_run.1
      (instLevelParamsM_specI hs (hcv.2.2.okS s₀) hcv.2.2.1 hus) ty s₁ hty1
    rw [hty, ← hcv.2.1] at htr₁
    have hw : ConLeche.Expr.WScoped 0 (TrS s₁ ty) := by
      rw [htr₁]; exact ConLeche.Expr.WScoped.of_not_hasFvar
        (by rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hcl)
    have hc : (TrS s₁ ty).looseBVarsBounded 0 = true := by
      rw [htr₁, ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]; exact hlbb
    obtain ⟨o', s₂, ho, hr⟩ := bind_run hr
    obtain ⟨hs₂, ht₂, hoko, hruno⟩ := tripleI_iff_run.1
      (formerSortLoopI_specI ih (n := caps.nparams + caps.nIdx) hs₁ hok₁ hw hc) o' s₂ ho
    rw [htr₁] at hruno
    simp only [Option.map_none]
    cases o' with
    | none => exact (throw_run hr).elim
    | some u =>
      obtain ⟨rfl, rfl⟩ := pure_run hr
      have hu : okL u = true := by
        simp only [Option.all_some, okLv, Bool.and_eq_true] at hoko; exact hoko.1
      refine ⟨hs₂, ht₁.trans ht₂, ?_, Runs.bind hruno ?_⟩
      · intro g hg
        cases hn : (InLean.Lvl.zeronessOf u).isNever <;> simp [hn] at hg; subst hg; exact hu
      · simp only [Option.map_some]
        rw [← trPW_zeronessOf, trPW_isNever]
        cases (InLean.Lvl.zeronessOf u).isNever <;> exact Runs.pure _

/-! ## The rows, and the guard -/

variable {fe : InLean.FEnv}

/-- **The rows at a sort** (`projRowsC_spec`'s twin): the constructor's type at
the use's levels, its parameters opened, its fields stepped; master's
`projGuardRows` on the translated entry, then its rows' check. -/
theorem checkProjRowsI_run (ih : KnotSpecI mode eager env r) (henv : ConLeche.EnvWF env)
    (hfe : EnvRelI fe env) {e : InLean.ProjEntry} {ce : ConLeche.ProjEntry}
    (hrel : ProjEntryRel e ce) {us : List Level} (hus : us.all okLv = true) {g : Level}
    (hg : okL g = true) {s₀ s' : InLean.CState} {v : Unit} (hs : CSOKI mode eager env s₀)
    (h : InLean.checkProjRowsI r.inferIO r.whnf fe e us g s₀ = .ok (v, s')) :
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (match ConLeche.projGuardRows env.find? ce (us.map trL) with
        | some rows => ConLeche.checkGuardRows (ConLeche.fueledFns mode eager env).inferIO
            (ConLeche.fueledFns mode eager env).whnf (trL g) rows
        | none => throw (.invalid "projection from a propositional structure must be a proposition"))
        () := by
  obtain ⟨-, hidx, hctor, hnP, -⟩ := hrel
  unfold InLean.checkProjRowsI at h
  cases hf : fe.find? e.ctor with
  | none => rw [hf] at h; exact (throw_run h).elim
  | some ci =>
    rw [hf] at h
    simp only at h
    obtain ⟨cci, cty, hL, -, -, -, -, -⟩ := hfe.ty e.ctor ci hf
    have hwf := henv.consts _ (ConLeche.Env.find?_mem hL)
    have hct : ConLeche.Cached.constTyOf env (toName e.ctor) (us.map trL) =
        cci.toConstantVal.type.instantiateLevelParams cci.toConstantVal.levelParams
          (us.map trL) := by
      simp only [ConLeche.Cached.constTyOf, hL]
    obtain ⟨t, s₁, htc, h⟩ := bind_run h
    obtain ⟨hs₁, ht₁, hokt, htrt⟩ :=
      tripleI_iff_run.1 (constTyAtM_specI hfe hs e.ctor hus) t s₁ htc
    rw [hct] at htrt
    have hlbt : (TrS s₁ t).looseBVarsBounded 0 = true := by
      rw [htrt, ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]; exact hwf.2.2.2.1
    obtain ⟨o, s₂, ho, h⟩ := bind_run h
    obtain ⟨hs₂, ht₂, hR⟩ := openPisAtFvarsI_run e.numParams 0 hs₁ hokt hlbt ho
    cases o with
    | none => exact (throw_run h).elim
    | some q =>
      obtain ⟨fvs, b⟩ := q
      obtain ⟨-, hokb, hm⟩ := hR fvs b rfl
      have hlbb : (TrS s₂ b).looseBVarsBounded 0 = true :=
        (ConLeche.Verify.openPisAtFvars_bounded e.numParams hm hlbt).1
      simp only at h
      obtain ⟨o2, s₃, ho2, h⟩ := bind_run h
      obtain ⟨hs₃, ht₃, hR2⟩ := projGuardRowsGoI_run e.idx e.numParams hs₂ hokb hlbb ho2
      cases o2 with
      | none => exact (throw_run h).elim
      | some rows =>
        obtain ⟨hrowsOk, hm2⟩ := hR2 rows rfl
        have hpg : ConLeche.projGuardRows env.find? ce (us.map trL) =
            some (rows.map fun p => (p.1, TrS s₃ p.2)) := by
          unfold ConLeche.projGuardRows
          rw [hctor, hL]
          simp only
          rw [← htrt, hnP, hm, hidx]
          exact hm2
        have hws := ConLeche.projGuardRows_ws
          (fun ci' hc' => (henv.consts _ (ConLeche.Env.find?_mem hc')).1) hpg
        have hfacts : ∀ p ∈ rows, OkS s₃ p.2 = true ∧ ConLeche.Expr.WScoped p.1 (TrS s₃ p.2) ∧
            (TrS s₃ p.2).looseBVarsBounded 0 = true := by
          intro p hp
          exact ⟨(hrowsOk p hp).1, hws _ (List.mem_map_of_mem hp), (hrowsOk p hp).2⟩
        obtain ⟨hs', ht', hRr⟩ := checkGuardRowsI_run ih hg rows hs₃ hfacts h
        refine ⟨hs', ht₁.trans (ht₂.trans (ht₃.trans ht')), ?_⟩
        rw [hpg]
        exact hRr

/-- **The projection guard's spec, proved** (`checkProjGuardC_spec`'s twin):
from the knot's specs, the environment's well-formedness, the relation and
the former view. -/
theorem projGuardSpecI_of (ih : KnotSpecI .verified eager env r) (henv : ConLeche.EnvWF env)
    (hfe : EnvRelI fe env) (hview : EnvViewI fe env) : ProjGuardSpecI eager env r fe := by
  intro e ce us s₀ hs hrel hus
  refine tripleI_iff_run.2 fun v s' h => ?_
  unfold InLean.checkProjGuardI at h
  unfold ConLeche.checkProjGuard
  rw [hrel.1]
  cases hv : fe.indView? e.structName with
  | none => rw [hv] at h; exact (throw_run h).elim
  | some p =>
    obtain ⟨cvT, caps⟩ := p
    rw [hv] at h
    simp only at h
    obtain ⟨ccv, hcv, hL⟩ := hview.ind _ _ _ hv
    rw [hL]
    simp only
    have hwf := henv.consts _ (ConLeche.Env.find?_mem hL)
    obtain ⟨o, s₁, ho, h⟩ := bind_run h
    obtain ⟨hs₁, ht₁, hog, hRo⟩ := projGuardSortI_run ih hcv hwf.1 hwf.2.2.2.1 caps hus hs ho
    cases o with
    | none =>
      obtain ⟨rfl, rfl⟩ := pure_run h
      exact ⟨hs₁, ht₁, Runs.bind hRo (Runs.pure ())⟩
    | some g =>
      simp only at h
      obtain ⟨hs', ht', hR⟩ := checkProjRowsI_run ih henv hfe hrel hus (hog g rfl) hs₁ h
      exact ⟨hs', ht₁.trans ht', Runs.bind hRo hR⟩

end InLeanProof

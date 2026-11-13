module

public import InLeanProof.WalksInfer
public import InLeanProof.WalksWhnf
public import InLeanProof.LeafGuardI
public import ConLeche.Verify.Cached.BinderLoopC
import ConLeche.Verify.Leaves

/-!
# The inference bodies (task #451, lane P2-close)

`inferBodyI` and `inferBodyIOI` as `BodySpecI` (`inferBodyC_spec`'s and
`inferBodyIOC_spec`'s twins), with what they need: the binder loops against
`inferBody`'s own chained λ/∀ tails (`inferLams_sound`/`inferPis_sound`, as
master's `inferLamsC_tail_sim`/`inferPisC_tail_sim`), `ensureSortI` at the io
view, a free variable's interned type.

What the bodies read of the environment beyond `EnvRelI`/`EnvDomI` is a named
hypothesis, P3a's to establish: `EnvProjI` (a projection entry against
con-leche's, its body a stored open term).  The projection guard
(`checkProjGuardI` with `projGuardSortI`/`checkProjRowsI`) is a named callee
spec, `ProjGuardSpecI`, proved from the knot's specs in the next file
(`InLeanProof.projGuardSpecI_of`, `ProjGuardI.lean`).
-/

set_option experimental.vcgen true

public section

/-! ## The chained tails (pure) -/

namespace InLeanProof.Pure

open ConLeche ConLeche.Cached

variable {mode : CheckMode} {eager : Bool} {env : Env}

theorem inferLamTail_atF (d : Nat) (tyx bodyx : Expr) (F : Nat) :
    ((do
      let bt ← (fueledFns mode eager env).infer (d + 1)
        (bodyx.instantiate1 (.fvar d tyx))
      pure (Expr.forallE tyx (bt.abstract1 d))) : FueledM Expr).val F
    = (inferTypeCore mode eager env F (d + 1) (bodyx.instantiate1 (.fvar d tyx))
        >>= fun bt => pure (Expr.forallE tyx (bt.abstract1 d))) := by
  rw [FueledM.atF_bind]
  rfl

theorem inferPiTail_atF (d : Nat) (tyx bodyx : Expr) (lu : Level) (F : Nat) :
    ((do
      let v ← ensureSort (fueledFns mode eager env) env (d + 1)
        (← (fueledFns mode eager env).infer (d + 1)
          (bodyx.instantiate1 (.fvar d tyx)))
      pure (Expr.sort (.imax lu v))) : FueledM Expr).val F
    = (inferTypeCore mode eager env F (d + 1) (bodyx.instantiate1 (.fvar d tyx))
        >>= fun bt => ensureSortCore mode eager env F (d + 1) bt >>= fun v =>
        pure (Expr.sort (.imax lu v))) := by
  rw [FueledM.atF_bind]
  congr 1
  funext bt
  rw [FueledM.atF_bind, ensureSort_atF]
  rfl

/-- **The λ-loop's answer is `inferBody`'s λ tail's** (`inferLams_sound`). -/
theorem runs_inferLams_tail {d fuel : Nat} {b ty r : Expr}
    (h : Runs (inferLams (fueledFns mode eager env) d fuel b 1 [Expr.fvar d ty] [ty]) r) :
    Runs (do
      let bt ← (fueledFns mode eager env).infer (d + 1) (b.instantiate1 (.fvar d ty))
      pure (Expr.forallE ty (bt.abstract1 d))) r := by
  obtain ⟨F, hF⟩ := h
  rw [inferLams_atF] at hF
  obtain ⟨F', hchain⟩ := inferLams_sound fuel b 1 [Expr.fvar d ty] [ty] F r rfl hF
  refine ⟨F', ?_⟩
  rw [inferLamTail_atF]
  obtain ⟨bt, hbt, htail⟩ := bind_okB hchain
  have hbt' : inferTypeCore mode eager env F' (d + 1) (b.instantiate1 (.fvar d ty)) = .ok bt := by
    rw [← instList_single b (Expr.fvar d ty)]
    exact hbt
  rw [hbt', okB_bind]
  exact htail

/-- The λ tail's answer is scoped. -/
theorem wscoped_lamTail (henv : EnvWF env) {d : Nat} {b ty r : Expr} (hwty : Expr.WScoped d ty)
    (hwb : Expr.WScoped d b)
    (h : Runs (do
      let bt ← (fueledFns mode eager env).infer (d + 1) (b.instantiate1 (.fvar d ty))
      pure (Expr.forallE ty (bt.abstract1 d))) r) : Expr.WScoped d r := by
  obtain ⟨F, hF⟩ := h
  rw [inferLamTail_atF] at hF
  obtain ⟨bt, hbt, hF⟩ := bind_okB hF
  have hwbt : Expr.WScoped (d + 1) bt :=
    inferTypeCore_WScoped henv F hbt (Expr.WScoped.instantiate1 hwty 0 hwb)
  injection hF with hres
  subst hres
  simp only [Expr.WScoped]
  exact ⟨hwty, ConLeche.WScoped.abstract1 0 hwbt⟩

/-- The λ tail's answer is closed, at a body whose free variables' types
are closed (`inferTypeCore_looseBVars`). -/
theorem closed_lamTail (henv : EnvWF env) {d : Nat} {b ty r : Expr} (hwty : Expr.WScoped d ty)
    (hwb : Expr.WScoped d b) (hcty : ty.looseBVarsBounded 0 = true)
    (hcb : b.looseBVarsBounded 1 = true) (hL : Expr.LeavesBounded (.lam ty b))
    (h : Runs (do
      let bt ← (fueledFns mode eager env).infer (d + 1) (b.instantiate1 (.fvar d ty))
      pure (Expr.forallE ty (bt.abstract1 d))) r) : r.looseBVarsBounded 0 = true := by
  obtain ⟨F, hF⟩ := h
  rw [inferLamTail_atF] at hF
  obtain ⟨bt, hbt, hF⟩ := bind_okB hF
  have hLo : Expr.LeavesBounded (b.instantiate1 (.fvar d ty)) := by
    intro l hl
    rcases Expr.fvarLeaves_instantiate1 b 0 hl with hl | hl
    · exact hL l (by simp [Expr.fvarLeaves, hl])
    · simp only [Expr.fvarLeaves, List.mem_cons] at hl
      rcases hl with rfl | hl
      · exact hcty
      · exact hL l (by simp [Expr.fvarLeaves, hl])
  have hcbt := inferTypeCore_looseBVars henv F hbt (Expr.WScoped.instantiate1 hwty 0 hwb)
    (looseBVarsBounded_instantiate1 _ 0 hcb) hLo
  injection hF with hres
  subst hres
  simp only [Expr.looseBVarsBounded, hcty, looseBVarsBounded_abstract1 bt 0 hcbt, Bool.and_self]

/-- **The ∀-loop's answer is `inferBody`'s ∀ tail's** (`inferPis_sound`). -/
theorem runs_inferPis_tail {d fuel : Nat} {b ty r : Expr} {u : Level}
    (h : Runs (inferPis (fueledFns mode eager env) d fuel b 1 [Expr.fvar d ty] [u]) r) :
    Runs (do
      let v ← ensureSort (fueledFns mode eager env) env (d + 1)
        (← (fueledFns mode eager env).infer (d + 1) (b.instantiate1 (.fvar d ty)))
      pure (Expr.sort (.imax u v))) r := by
  obtain ⟨F, hF⟩ := h
  rw [inferPis_atF] at hF
  obtain ⟨F', hchain⟩ := inferPis_sound fuel b 1 [Expr.fvar d ty] [u] F r rfl (Nat.le_refl 1) hF
  refine ⟨F', ?_⟩
  rw [inferPiTail_atF]
  obtain ⟨bt, hbt, hwrap⟩ := bind_okB hchain
  have hbt' : inferTypeCore mode eager env F' (d + 1) (b.instantiate1 (.fvar d ty)) = .ok bt := by
    rw [← instList_single b (Expr.fvar d ty)]
    exact hbt
  rw [hbt', okB_bind]
  unfold inferPisWrap at hwrap
  obtain ⟨v, hv, hwrap⟩ := bind_okB hwrap
  rw [ensureSort_def] at hv
  have hv' : ensureSortCore mode eager env F' (d + 1) bt = .ok v := hv
  rw [hv', okB_bind]
  unfold inferPisWrap at hwrap
  exact hwrap

theorem instList_single' (b a : Expr) : b.instantiateList [a] = b.instantiate1 a :=
  instList_single b a

/-- The ∀ tail answers a sort. -/
theorem piTail_sort {d : Nat} {b ty r : Expr} {u : Level}
    (h : Runs (do
      let v ← ensureSort (fueledFns mode eager env) env (d + 1)
        (← (fueledFns mode eager env).infer (d + 1) (b.instantiate1 (.fvar d ty)))
      pure (Expr.sort (.imax u v))) r) : ∃ l, r = .sort l := by
  obtain ⟨F, hF⟩ := h
  rw [inferPiTail_atF] at hF
  obtain ⟨bt, -, hF⟩ := bind_okB hF
  obtain ⟨v, -, hF⟩ := bind_okB hF
  injection hF with hres
  exact ⟨_, hres.symm⟩

end InLeanProof.Pure

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached
open scoped Lean.Order

variable {mode : ConLeche.CheckMode} {mi : InLean.CheckMode} {eager : Bool} {env : ConLeche.Env}

/-! ## The binder loops against the chained tails -/

/-- **A reading's free variables carry closed types** (`CSOKI.fvClosed`,
through the leaves of a translation, `term_leaves`). -/
theorem leavesBounded_TrS {s : InLean.CState} (hs : CSOKI mode eager env s) {e : Expr}
    (h : OkS s e = true) : ConLeche.Expr.LeavesBounded (TrS s e) := by
  intro p hp
  have htf : toExpr (fvT s) e = some (TrS s e) := TransS_of_ok h
  have hL := term_leaves (s := s) (fun _ _ h => h) htf (fun x _ => idLeaves hs.fv x)
  obtain ⟨y, -, hy⟩ := (hL p).1 hp
  have hT : TransS s (.fvar y) = some (.fvar p.1 p.2) := by simpa [TransS, toExpr] using hy
  obtain ⟨n, ty, -, hty, htr⟩ := TransS_fvar hT
  exact hs.fvClosed n ty _ hty htr

/-- The λ-loop from one opened binder answers `inferBody`'s λ tail. -/
theorem inferLamsI_tail_spec {fe : InLean.FEnv} {lv : Nat} (ih : KnotSpecI mode mi eager env fe lv)
    (henv : ConLeche.EnvWF env) {d fuel : Nat} {b ty fv : Expr} {s₀ : InLean.CState}
    (hs : CSOKI mode eager env s₀) (hb : OkS s₀ b = true) (hty : OkS s₀ ty = true)
    (hfv : OkS s₀ fv = true) (hfvT : TrS s₀ fv = .fvar d (TrS s₀ ty))
    (hwty : ConLeche.Expr.WScoped d (TrS s₀ ty)) (hwb : ConLeche.Expr.WScoped d (TrS s₀ b))
    (hcty : (TrS s₀ ty).looseBVarsBounded 0 = true) (hcb : (TrS s₀ b).looseBVarsBounded 1 = true) :
    ⦃fun s => s = s₀⦄ inferLamsI mi fe eager lv false d fuel b 1 #[fv] [ty]
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
      Runs (do
        let bt ← (ConLeche.fueledFns mode eager env).infer (d + 1)
          ((TrS s₀ b).instantiate1 (.fvar d (TrS s₀ ty)))
        pure (ConLeche.Expr.forallE (TrS s₀ ty) (bt.abstract1 d))) (TrS s' v) ∧
      ConLeche.Expr.WScoped d (TrS s' v) ∧ (TrS s' v).looseBVarsBounded 0 = true; ⊤⦄ := by
  have hopen : (TrS s₀ b).instantiateList [ConLeche.Expr.fvar d (TrS s₀ ty)] =
      (TrS s₀ b).instantiate1 (.fvar d (TrS s₀ ty)) := Pure.instList_single' _ _
  have hw1 : ConLeche.Expr.WScoped (d + 1)
      ((TrS s₀ b).instantiateList (TrSL s₀ (#[fv] : Array Expr).toList).reverse) := by
    simp only [TrSL, List.map, List.reverse_cons, List.reverse_nil, List.nil_append,
      hfvT, hopen]
    exact ConLeche.Expr.WScoped.instantiate1 hwty 0 hwb
  have hc1 : ((TrS s₀ b).instantiateList (TrSL s₀ (#[fv] : Array Expr).toList).reverse).looseBVarsBounded 0
      = true := by
    simp only [TrSL, List.map, List.reverse_cons, List.reverse_nil, List.nil_append,
      hfvT, hopen]
    exact ConLeche.looseBVarsBounded_instantiate1 _ 0 hcb
  have hT := inferLamsI_spec ih (d := d) fuel (t := b) (k := 1) (fvs := #[fv]) (stk := [ty]) hs hb
    (by simp [OkSL, hfv]) (by simp [AllClosed, TrSL, hfvT, ConLeche.Expr.looseBVarsBounded])
    (by simp [OkSL, hty]) hw1 hc1
  refine tripleI_iff_run.2 fun v s' hr => ?_
  obtain ⟨h1, h2, h3, h4⟩ := tripleI_iff_run.1 hT v s' hr
  have h4' : Runs (ConLeche.inferLams (ConLeche.fueledFns mode eager env) d fuel (TrS s₀ b) 1
      [ConLeche.Expr.fvar d (TrS s₀ ty)] [TrS s₀ ty]) (TrS s' v) := by
    simpa [TrSL, hfvT] using h4
  have ht := Pure.runs_inferLams_tail h4'
  have hL : ConLeche.Expr.LeavesBounded (ConLeche.Expr.lam (TrS s₀ ty) (TrS s₀ b)) := by
    have := leavesBounded_TrS hs (e := .lam .anonymous ty b .default) (by simp [OkS_lam, hty, hb])
    simpa [TrS_lam] using this
  exact ⟨h1, h2, h3, ht, Pure.wscoped_lamTail henv hwty hwb ht,
    Pure.closed_lamTail henv hwty hwb hcty hcb hL ht⟩

/-- The type annotation of a term's translation, where it is a free
variable (total; `.bvar 0` elsewhere): names the opened binder's domain
where only the variable is in the program. -/
@[expose] def fvTyE (s : InLean.CState) (e : Expr) : ConLeche.Expr :=
  match TrS s e with
  | .fvar _ c => c
  | _ => .bvar 0

theorem fvTyE_of {s : InLean.CState} {e : Expr} {d : Nat} {c : ConLeche.Expr}
    (h : TrS s e = .fvar d c) : fvTyE s e = c := by
  simp [fvTyE, h]
grind_pattern [conleche_grind] fvTyE_of => fvTyE s e, ConLeche.Expr.fvar d c

/-- The ∀-loop from one opened binder answers `inferBody`'s ∀ tail. -/
theorem inferPisI_tail_spec {fe : InLean.FEnv} {lv : Nat} (ih : KnotSpecI mode mi eager env fe lv)
    {d fuel : Nat} {b fv : Expr} {u : Level} {s₀ : InLean.CState}
    (hs : CSOKI mode eager env s₀) (hb : OkS s₀ b = true) (hu : okLv u = true)
    (hfv : OkS s₀ fv = true) (hfvT : TrS s₀ fv = .fvar d (fvTyE s₀ fv))
    (hwty : ConLeche.Expr.WScoped d (fvTyE s₀ fv)) (hwb : ConLeche.Expr.WScoped d (TrS s₀ b))
    (hcb : (TrS s₀ b).looseBVarsBounded 1 = true) :
    ⦃fun s => s = s₀⦄ inferPisI mi fe eager lv false d fuel b 1 #[fv] [u]
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
      Runs (do
        let v ← ConLeche.ensureSort (ConLeche.fueledFns mode eager env) env (d + 1)
          (← (ConLeche.fueledFns mode eager env).infer (d + 1)
            ((TrS s₀ b).instantiate1 (.fvar d (fvTyE s₀ fv))))
        pure (ConLeche.Expr.sort (.imax (trL u) v))) (TrS s' v) ∧
      ConLeche.Expr.WScoped d (TrS s' v) ∧ (TrS s' v).looseBVarsBounded 0 = true; ⊤⦄ := by
  have hopen : (TrS s₀ b).instantiateList [ConLeche.Expr.fvar d (fvTyE s₀ fv)] =
      (TrS s₀ b).instantiate1 (.fvar d (fvTyE s₀ fv)) := Pure.instList_single' _ _
  have hw1 : ConLeche.Expr.WScoped (d + 1)
      ((TrS s₀ b).instantiateList (TrSL s₀ (#[fv] : Array Expr).toList).reverse) := by
    simp only [TrSL, List.map, List.reverse_cons, List.reverse_nil, List.nil_append,
      hfvT, hopen]
    exact ConLeche.Expr.WScoped.instantiate1 hwty 0 hwb
  have hc1 : ((TrS s₀ b).instantiateList (TrSL s₀ (#[fv] : Array Expr).toList).reverse).looseBVarsBounded 0
      = true := by
    simp only [TrSL, List.map, List.reverse_cons, List.reverse_nil, List.nil_append,
      hfvT, hopen]
    exact ConLeche.looseBVarsBounded_instantiate1 _ 0 hcb
  have hT := inferPisI_spec ih (d := d) fuel (t := b) (k := 1) (fvs := #[fv]) (stk := [u]) hs hb
    (by simp [OkSL, hfv]) (by simp [AllClosed, TrSL, hfvT, ConLeche.Expr.looseBVarsBounded])
    (by simp [hu]) hw1 hc1
  refine tripleI_iff_run.2 fun v s' hr => ?_
  obtain ⟨h1, h2, h3, h4⟩ := tripleI_iff_run.1 hT v s' hr
  have h4' : Runs (ConLeche.inferPis (ConLeche.fueledFns mode eager env) d fuel (TrS s₀ b) 1
      [ConLeche.Expr.fvar d (fvTyE s₀ fv)] [trL u]) (TrS s' v) := by
    simpa [TrSL, hfvT] using h4
  have ht := Pure.runs_inferPis_tail h4'
  obtain ⟨l, hl⟩ := Pure.piTail_sort ht
  exact ⟨h1, h2, h3, ht, by rw [hl]; simp [ConLeche.Expr.WScoped], by rw [hl]; rfl⟩

/-! ## `ensureSortI` at the io view -/

/-- **`ensureSortI` at the io view simulates the io `ensureSort`**
(`ensureSortIOC_spec`'s twin). -/
theorem ensureSortIOI_spec {fe : InLean.FEnv} {lv : Nat} (ih : KnotSpecI mode mi eager env fe lv) {d : Nat}
    {i : Expr} {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) (hok : OkS s₀ i = true)
    (hw : ConLeche.Expr.WScoped d (TrS s₀ i)) (hc : (TrS s₀ i).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ ensureSortI mi fe eager lv d i
    ⦃fun u s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ okLv u = true ∧
      Runs (ConLeche.ensureSort (ConLeche.CoreFns.ioView (ConLeche.fueledFns mode eager env)) env d
        (TrS s₀ i)) (trL u); ⊤⦄ := by
  sym only [conleche_grind, ConLeche.ensureSort, CoreFns.ioView_whnf] =>
    vcgen [InLean.ensureSortI.eq_def, ih.whnf hs hok hw hc] <;> finish

/-! ## A free variable's interned type -/

/-- A free variable with a reading carries its depth in its id. -/
theorem fvarDepth_of_ok {s : InLean.CState} {id : FVarId} (h : OkS s (.fvar id) = true) :
    fvarDepth? id = some (fvIdxS s id) := by
  simp only [OkS, okE, Option.isSome_iff_exists] at h
  obtain ⟨c, hc⟩ := h
  obtain ⟨d, n, rfl, hn⟩ := FVarTable.trans_some hc
  obtain ⟨-, -, cty, -, -, rfl⟩ := FVarTable.transNum_some hn
  simp only [fvIdxS, TrS, trE, hc]
  exact fvDepth_fvId d n

/-- **The type `fvarTypeM?` reads** is the translation's annotation, with a
reading, closed. -/
theorem fvarTypeM_specI {s₀ : InLean.CState} {id : FVarId} (hs : CSOKI mode eager env s₀)
    (h : OkS s₀ (.fvar id) = true) :
    ⦃fun s => s = s₀⦄ fvarTypeM? id
    ⦃fun o s' => s' = s₀ ∧ OkO s₀ o = true ∧ TrO s₀ o = some (fvTyS s₀ id) ∧
      OptClosed (TrO s₀ o) = true; ⊤⦄ := by
  have hT := TrS_fvar h
  have hTr : TransS s₀ (.fvar id) = some (.fvar (fvIdxS s₀ id) (fvTyS s₀ id)) := by
    rw [← hT]; exact TransS_of_ok h
  obtain ⟨n, ty, hp, hty, htr⟩ := TransS_fvar hTr
  have hr : Expr.RangeOk ty := hs.fv.range n ty hty
  obtain ⟨hok, htrS⟩ := ok_of_TransS hr htr
  have hcl := hs.fvClosed n ty _ hty htr
  refine tripleI_iff_run.2 fun o s' hr' => ?_
  simp only [fvarTypeM?, hp, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind,
    pure, StateT.pure, Except.pure, Except.bind, Except.ok.injEq, Prod.mk.injEq] at hr'
  obtain ⟨rfl, rfl⟩ := hr'
  rw [hty]
  exact ⟨rfl, hok, by simp [TrO, htrS], by simp [TrO, OptClosed, htrS, hcl]⟩

/-! ## What the bodies read of the environment, and the projection guard

Named hypotheses, P3a's to establish (O4).  A projection entry is
con-leche's at the translated name, its body read off the constructor type
(`InLean.projBodyAt`) a stored open term translating to con-leche's stored
body.  The guard's spec is `ProjGuardSpecI`. -/

/-- A projection entry against con-leche's. -/
@[expose] def ProjEntryRel (e : InLean.ProjEntry) (ce : ConLeche.ProjEntry) : Prop :=
  ce.structName = toName e.structName ∧ ce.idx = e.idx ∧ ce.ctor = toName e.ctor ∧
  ce.numParams = e.numParams ∧ ce.numFields = e.numFields ∧
  ce.levelParams = e.levelParams.map toName ∧
  ∀ body, InLean.projBodyAt e.structName e.numParams e.idx e.ctorType = some body →
    StoredT body ce.body

/-- **The projection entries** (O4, P3a's): InLean's entry of `T`'s field
`i` is con-leche's at the translated name. -/
structure EnvProjI (fe : InLean.FEnv) (env : ConLeche.Env) : Prop where
  find : ∀ T i e, fe.findProj? T i = some e →
    ∃ ce, env.findProj? (toName T) i = some ce ∧ ProjEntryRel e ce

/-- **The projection guard's spec** (P3a's; proved as `projGuardSpecI_of`),
at the knot's level; the full and the io inference run the same guard (it
infers at the io grade). -/
@[expose] def ProjGuardSpecI (eager : Bool) (env : ConLeche.Env) (fe : InLean.FEnv) (lv : Nat)
    : Prop :=
  ∀ {e : InLean.ProjEntry} {ce : ConLeche.ProjEntry} {us : List Level} {s₀ : InLean.CState},
    CSOKI .verified eager env s₀ → ProjEntryRel e ce → us.all okLv = true →
    ⦃fun s => s = s₀⦄ checkProjGuardI .verified fe eager lv e us
    ⦃fun _ s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.checkProjGuard (ConLeche.fueledFns .verified eager env).inferIO
        (ConLeche.fueledFns .verified eager env).whnf env ce (us.map trL)) (); ⊤⦄

/-- **A projection's type through the translation**: the entry's body at
the subject type's levels, arguments and the subject. -/
theorem typeAtI_TrS {s : InLean.CState} {e : InLean.ProjEntry} {ce : ConLeche.ProjEntry}
    (hrel : ProjEntryRel e ce) {us : List Level} {targs : List Expr} {pe ty : Expr}
    (h : e.typeAtI us targs pe = some ty) (hus : us.all okLv = true) (hpe : OkS s pe = true)
    (hargs : OkSL s targs = true) (hcpe : (TrS s pe).looseBVarsBounded 0 = true)
    (hcargs : AllClosed (TrSL s targs) = true) :
    OkS s ty = true ∧ TrS s ty = ce.typeAt (us.map trL) (TrSL s targs) (TrS s pe) := by
  obtain ⟨-, -, -, -, -, hlp, hbody⟩ := hrel
  simp only [InLean.ProjEntry.typeAtI, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨body, hb, q, hq, rfl⟩ := h
  have hp := hbody body hb
  have hus' : ∀ u ∈ us, depthS u ≤ maxLevelDepth := by
    intro u hu
    simp only [List.all_eq_true, okLv, Bool.and_eq_true, decide_eq_true_eq] at hus
    exact (hus u hu).2
  have hl : toLevels us = some (us.map trL) := toLevels_of_okLv hus
  obtain ⟨rfl, hrr, hm⟩ := instLevelParamsChecked_ok hp.2.1 hus' hq
  have htp : TransS s body = some ce.body := by
    unfold TransS; rw [toExpr_noFVar body hp.1]; exact hp.2.2
  have h1 := toExpr_instantiateLevelParams (fv := FVarTable.trans (tableOf s))
    hp.2.1 hp.1 htp e.levelParams hl hm
  obtain ⟨hokq, htrq⟩ := ok_of_TransS hrr h1
  have hvs : OkSL s (pe :: targs.reverse) = true := by
    simp only [OkSL, List.all_cons, List.all_reverse, Bool.and_eq_true] at hargs ⊢
    exact ⟨hpe, hargs⟩
  have hcvs : AllClosed (TrSL s (pe :: targs.reverse)) = true := by
    simp only [TrSL, AllClosed, List.map_cons, List.map_reverse, List.all_cons, List.all_reverse,
      Bool.and_eq_true] at hcargs ⊢
    exact ⟨hcpe, hcargs⟩
  have harr : (#[pe] ++ targs.toArray.reverse) = (pe :: targs.reverse).toArray := by simp
  rw [harr]
  obtain ⟨hok, htr⟩ := TrS_instI hokq hvs hcvs
  refine ⟨hok, ?_⟩
  rw [htr, htrq, ConLeche.ProjEntry.typeAt, hlp]
  simp [TrSL, List.map_reverse]

/-- A throwing program has no successful run. -/
theorem throw_run {α : Type} {x : InLean.CheckError} {s₀ : InLean.CState} {p : α × InLean.CState}
    (h : (throw x : InLean.CheckCM α) s₀ = .ok p) : False := by
  simp [throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, Except.bind] at h

theorem toName_natName : toName InLean.natName = ConLeche.natName := rfl
theorem toName_stringName : toName InLean.stringName = ConLeche.stringName := rfl

@[conleche_grind =] theorem trL_succ (u : Level) : trL (.succ u) = .succ (trL u) := rfl
@[conleche_grind =] theorem trL_imax (u v : Level) : trL (.imax u v) = .imax (trL u) (trL v) := rfl

/-! ## The inference body -/

section Body

variable {fe : InLean.FEnv} {lv : Nat}

/-- The shapes `inferBodyI` answers without a binder or a spine (and where
`inferBodyIOI` falls back to it). -/
@[expose] def inferLeafI : Expr → Bool
  | .sort _ | .fvar _ | .const .. | .lit _ | .proj .. | .bvar _ | .mvar _ => true
  | _ => false

/-- **`inferBodyI`'s leaf arms**, at any record whose `infer` and `whnf`
slots simulate the pure record `R`'s (the knot's, or its io view's). -/
theorem inferBodyI_leaf {R : ConLeche.CoreFns ConLeche.FueledM} {io : Bool}
    (hinf : BodySpecI .verified eager env (InLean.inferI .verified fe eager lv io) R.infer)
    (hwh : BodySpecI .verified eager env (InLean.whnfI .verified fe eager lv) R.whnf)
    (hguard : ∀ {e : InLean.ProjEntry} {ce : ConLeche.ProjEntry} {us : List Level}
      {s₀ : InLean.CState}, CSOKI .verified eager env s₀ → ProjEntryRel e ce → us.all okLv = true →
      ⦃fun s => s = s₀⦄ checkProjGuardI .verified fe eager lv e us
      ⦃fun _ s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧
        Runs (ConLeche.checkProjGuard R.inferIO R.whnf env ce (us.map trL)) (); ⊤⦄)
    (henv : ConLeche.EnvWF env) (hfe : EnvRelI fe env) (hdom : EnvDomI fe env)
    (hproj : EnvProjI fe env) {s₀ : InLean.CState} {d : Nat} {i : Expr}
    (hs : CSOKI .verified eager env s₀) (hok : OkS s₀ i = true)
    (hw : ConLeche.Expr.WScoped d (TrS s₀ i)) (hc : (TrS s₀ i).looseBVarsBounded 0 = true)
    (hl : inferLeafI (EO.stripTop i) = true) :
    ⦃fun s => s = s₀⦄ inferBodyI .verified fe eager lv io d i
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
      Runs (ConLeche.inferBody R env d (TrS s₀ i)) (TrS s' v) ∧
      ConLeche.Expr.WScoped d (TrS s' v) ∧ (TrS s' v).looseBVarsBounded 0 = true; ⊤⦄ := by
  have hT : TrS s₀ i = TrS s₀ (EO.stripTop i) := (TrS_stripTop s₀ i).symm
  have hO : OkS s₀ (EO.stripTop i) = true := by rw [OkS_stripTop]; exact hok
  rw [hT] at hw hc ⊢
  unfold InLean.inferBodyI
  generalize hx : EO.stripTop i = x at hO hw hc hT hl ⊢
  cases x with
  | sort u =>
    sym only [conleche_grind, ConLeche.inferBody] => vcgen <;> finish
  | fvar id =>
    sym only [conleche_grind, ConLeche.inferBody, fvarDepth_of_ok hO] =>
      vcgen [fvarTypeM_specI hs hO] <;> finish
  | lit l =>
    cases l <;>
    sym only [conleche_grind, ConLeche.inferBody, natLit_I hdom, strLit_I hdom,
        List.all_nil, List.map_nil, toName_natName, toName_stringName] =>
      vcgen <;> finish
  | bvar _ => sym only [conleche_grind] => vcgen <;> finish
  | mvar _ => sym only [conleche_grind] => vcgen <;> finish
  | const n us =>
    have hus : us.all okLv = true := hO
    cases hf : fe.find? n with
    | none =>
      have hn : env.find? (toName n) = none := by
        have := hdom.dom n; rw [hf] at this; simpa using this
      sym only [conleche_grind, ConLeche.inferBody, List.all_nil] => vcgen <;> finish
    | some ci =>
      obtain ⟨cci, cty, hcf, -, -, hlp, -, -⟩ := hfe.ty n ci hf
      have hwf := henv.consts _ (ConLeche.Env.find?_mem hcf)
      have hcl : (cci.toConstantVal.type.instantiateLevelParams cci.toConstantVal.levelParams
          (us.map trL)).looseBVarsBounded 0 = true := by
        rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]; exact hwf.2.2.2.1
      have hws : ConLeche.Expr.WScoped d (cci.toConstantVal.type.instantiateLevelParams
          cci.toConstantVal.levelParams (us.map trL)) :=
        ConLeche.Expr.WScoped.of_not_hasFvar (by
          rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hwf.1)
      have hlen : (us.map trL).length = cci.toConstantVal.levelParams.length ↔
          us.length = ci.levelParams.length := by simp [hlp]
      sym only [conleche_grind, ConLeche.inferBody, constTyOf] =>
        vcgen [checkConstSafety, constTyAtM_specI hfe hs n hus] <;> finish
  | proj sn idx pe =>
    have hpe : OkS s₀ pe = true := hO
    have hwpe : ConLeche.Expr.WScoped d (TrS s₀ pe) := by
      simpa [TrS_proj, ConLeche.Expr.WScoped] using hw
    have hcpe : (TrS s₀ pe).looseBVarsBounded 0 = true := by
      simpa [TrS_proj, ConLeche.Expr.looseBVarsBounded] using hc
    refine tripleI_iff_run.2 fun v s' hr => ?_
    obtain ⟨tpe, s₁, h1, hr⟩ := bind_run hr
    obtain ⟨hs1, hle1, hok1, hrun1, hw1, hc1⟩ :=
      tripleI_iff_run.1 (hinf hs hpe hwpe hcpe) tpe s₁ h1
    obtain ⟨te, s₂, h2, hr⟩ := bind_run hr
    obtain ⟨hs2, hle2, hok2, hrun2, hw2, hc2⟩ :=
      tripleI_iff_run.1 (hwh hs1 hok1 hw1 hc1) te s₂ h2
    cases hh : Expr.getAppFnT te with
    | const T us =>
      simp only [hh] at hr
      cases hfp : fe.findProj? T idx with
      | none => simp only [hfp] at hr; exact (throw_run hr).elim
      | some e =>
        simp only [hfp] at hr
        obtain ⟨ce, hcf, hrel⟩ := hproj.find T idx e hfp
        by_cases hTs : (T == sn) = true
        · simp only [hTs, ↓reduceIte] at hr
          by_cases hlen : (appArgs te).length = e.numParams
          · simp only [hlen, ↓reduceIte] at hr
            by_cases hlp : us.length = e.levelParams.length
            · simp only [hlp, ↓reduceIte] at hr
              obtain ⟨u3, s₅, hu3, hr⟩ := bind_run hr
              have hus : us.all okLv = true := by
                have := OkS_getAppFnT (s := s₂) hok2; rw [hh] at this; exact this
              obtain ⟨hs5, hle5, hguard⟩ := tripleI_iff_run.1 (hguard hs2 hrel hus) u3 s₅ hu3
              cases hty : e.typeAtI us (appArgs te) pe with
              | some ty =>
                simp only [hty] at hr
                obtain ⟨rfl, rfl⟩ := pure_run hr
                have hle05 : TabLe s₀ s₅ := hle1.trans (hle2.trans hle5)
                have hpe5 : OkS s₅ pe = true := okS_of_tabLe hle05 hpe
                have hargs2 : OkSL s₂ (appArgs te) = true := OkSL_appArgs (s := s₂) hok2
                have hargs5 : OkSL s₅ (appArgs te) = true := okSL_of_tabLe hle5 hargs2
                have hTargs : TrSL s₅ (appArgs te) = (TrS s₂ te).getAppArgs := by
                  rw [TrSL_of_tabLe hle5 hargs2, TrSL_appArgs]
                have hTpe : TrS s₅ pe = TrS s₀ pe := TrS_of_tabLe hle05 hpe
                obtain ⟨hokty, htrty⟩ := typeAtI_TrS hrel hty hus hpe5 hargs5
                  (by rw [hTpe]; exact hcpe)
                  (by rw [hTargs]; exact allClosed_getAppArgs hc2)
                rw [hTargs, hTpe] at htrty
                have hhd := TrS_getAppFn_const s₂ hh
                obtain ⟨hsn, -, -, hnp, -, hlps, -⟩ := hrel
                have hTsn : T = sn := by simpa using hTs
                subst hTsn
                have hlenC : (TrS s₂ te).getAppArgs.length = ce.numParams := by
                  rw [← TrSL_appArgs, hnp, ← hlen]; simp [TrSL]
                have hlpC : (us.map trL).length = ce.levelParams.length := by
                  rw [hlps]; simpa using hlp
                refine ⟨hs5, hle05, hokty, ?_, ?_, ?_⟩
                · rw [htrty, TrS_proj]
                  simp only [ConLeche.inferBody]
                  refine Runs.bind hrun1 (Runs.bind hrun2 ?_)
                  rw [hhd]
                  simp only [hcf, hlenC, hlpC, and_self, ↓reduceIte]
                  exact Runs.bind hguard (Runs.pure _)
                · rw [htrty]
                  exact ConLeche.projEntry_typeAt_WScoped henv hcf _ hlenC
                    (allWS_getAppArgs hw2) hwpe
                · rw [htrty]
                  exact ConLeche.projEntry_typeAt_looseBVars henv hcf _ hlenC
                    (fun a ha => by
                      have := allClosed_getAppArgs hc2
                      simp only [AllClosed, List.all_eq_true] at this
                      exact this a ha) hcpe
              | none => simp only [hty] at hr; exact (throw_run hr).elim
            · simp only [hlp, ↓reduceIte] at hr; exact (throw_run hr).elim
          · simp only [hlen, ↓reduceIte] at hr
            obtain ⟨_, _, h, _⟩ := bind_run hr
            exact (throw_run h).elim
        · simp only [hTs, Bool.false_eq_true, ↓reduceIte] at hr
          obtain ⟨_, _, h, _⟩ := bind_run hr
          exact (throw_run h).elim
    | _ => simp only [hh] at hr; exact (throw_run hr).elim

  | _ => simp [inferLeafI] at hl

/-- **`inferBodyI` simulates the pure `inferBody`** (`inferBodyC_spec`'s
twin): the leaf arms by `inferBodyI_leaf`, the binder arms through the
loops' tails, the application arm through the spine loop. -/
theorem inferBodyI_spec (ih : KnotSpecI .verified .verified eager env fe lv)
    (harg : DefeqArgSpecI .verified .verified eager env fe lv) (hpg : ProjGuardSpecI eager env fe lv)
    (henv : ConLeche.EnvWF env) (hfe : EnvRelI fe env) (hdom : EnvDomI fe env)
    (hproj : EnvProjI fe env) :
    BodySpecI .verified eager env (inferBodyI .verified fe eager lv false)
      (ConLeche.inferBody (ConLeche.fueledFns .verified eager env) env) := by
  intro s₀ d i hs hok hw hc
  cases hl : inferLeafI (EO.stripTop i)
  case true =>
    exact inferBodyI_leaf (fun hs hok hw hc => ih.infer hs hok hw hc)
      (fun hs hok hw hc => ih.whnf hs hok hw hc) hpg henv hfe hdom hproj hs hok hw hc hl
  have hT : TrS s₀ i = TrS s₀ (EO.stripTop i) := (TrS_stripTop s₀ i).symm
  have hO : OkS s₀ (EO.stripTop i) = true := by rw [OkS_stripTop]; exact hok
  rw [hT] at hw hc ⊢
  unfold InLean.inferBodyI
  generalize hx : EO.stripTop i = x at hO hw hc hT hl ⊢
  cases x with
  | mdata _ _ => exact (stripTop_ne_mdata hx).elim
  | letE _ ty v b _ =>
    sym only [conleche_grind, ConLeche.inferBody] =>
      vcgen [ih.infer, ih.defeq, ensureSortI_spec ih] <;> finish
  | app f a =>
    have hTa : TrS s₀ i = .app (TrS s₀ f) (TrS s₀ a) := hT
    sym only [conleche_grind] =>
      vcgen [ih.infer, SpineSpecI.triple (inferSpineI_spec ih harg _)] <;> finish
  | forallE _ ty b _ =>
    sym only [conleche_grind, ConLeche.inferBody] =>
      vcgen [ih.infer, ih.whnf, InLean.peelFuelM, mkFVarM_specI (mode := .verified) (eager := eager) (env := env),
        inferPisI_tail_spec ih] <;> finish
  | lam _ ty b _ =>
    sym only [conleche_grind, ConLeche.inferBody] =>
      vcgen [ih.infer, ih.whnf, InLean.peelFuelM, mkFVarM_specI (mode := .verified) (eager := eager) (env := env),
        inferLamsI_tail_spec ih henv] <;> finish
  | _ => simp [inferLeafI] at hl

/-! ## The io inference body -/

/-- Bulk abstraction of one variable is `abstract1`. -/
@[conleche_grind =] theorem abstractRange_one (e : ConLeche.Expr) (d c : Nat) :
    e.abstractRange d 1 c = e.abstract1 d c := by
  rw [ConLeche.abstractRange_succ, Nat.add_zero, ConLeche.abstractRange_zero]

/-- On a leaf shape, the io body is the full one (at the io view). -/
theorem inferBodyIO_leaf_eq (R : ConLeche.CoreFns ConLeche.FueledM) {s : InLean.CState} {x : Expr}
    (hl : inferLeafI x = true) (hok : OkS s x = true) (d : Nat) :
    ConLeche.inferBodyIO (ConLeche.CoreFns.ioView R) env d (TrS s x) =
      ConLeche.inferBody (ConLeche.CoreFns.ioView R) env d (TrS s x) := by
  cases x with
  | fvar id => rw [TrS_fvar hok]; rfl
  | mvar _ => simp [OkS, okE] at hok
  | lit l => cases l <;> rfl
  | _ => first | rfl | simp [inferLeafI] at hl

/-- **`inferBodyIOI` simulates the pure io body** (`inferBodyIOC_spec`'s
twin): its own application, binder and `let` arms, and `inferBodyI`'s leaf
arms at the io view. -/
theorem inferBodyIOI_spec (ih : KnotSpecI .verified .verified eager env fe lv)
    (hpg : ProjGuardSpecI eager env fe lv)
    (henv : ConLeche.EnvWF env) (hfe : EnvRelI fe env) (hdom : EnvDomI fe env)
    (hproj : EnvProjI fe env) :
    BodySpecI .verified eager env (inferBodyIOI .verified fe eager lv)
      (ConLeche.inferBodyIO (ConLeche.CoreFns.ioView (ConLeche.fueledFns .verified eager env)) env) := by
  intro s₀ d i hs hok hw hc
  have hO : OkS s₀ (EO.stripTop i) = true := by rw [OkS_stripTop]; exact hok
  cases hl : inferLeafI (EO.stripTop i)
  case true =>
    have hfb : inferBodyIOI .verified fe eager lv d i = inferBodyI .verified fe eager lv true d i := by
      rw [InLean.inferBodyIOI.eq_def]
      generalize hx : EO.stripTop i = x at hl
      cases x <;> simp [inferLeafI] at hl <;> rfl
    rw [hfb]
    have hio := inferBodyIO_leaf_eq (env := env) (ConLeche.fueledFns .verified eager env) hl hO d
    rw [TrS_stripTop] at hio
    rw [hio]
    exact inferBodyI_leaf (R := ConLeche.CoreFns.ioView (ConLeche.fueledFns .verified eager env))
      (fun hs hok hw hc => ih.inferIO hs hok hw hc) (fun hs hok hw hc => ih.whnf hs hok hw hc)
      (fun hs hrel hus => hpg hs hrel hus) henv hfe hdom hproj hs hok hw hc hl
  have hT : TrS s₀ i = TrS s₀ (EO.stripTop i) := (TrS_stripTop s₀ i).symm
  rw [hT] at hw hc ⊢
  unfold InLean.inferBodyIOI
  generalize hx : EO.stripTop i = x at hO hw hc hT hl ⊢
  cases x with
  | mdata _ _ => exact (stripTop_ne_mdata hx).elim
  | app f a =>
    have hTa : TrS s₀ i = .app (TrS s₀ f) (TrS s₀ a) := hT
    sym only [conleche_grind, CoreFns.ioView_infer, CoreFns.ioView_whnf] =>
      vcgen [ih.inferIO, SpineIOSpecI.triple (inferSpineIOI_spec ih _)] <;> finish
  | forallE _ ty b _ =>
    sym only [conleche_grind, ConLeche.inferBodyIO, CoreFns.ioView_infer, CoreFns.ioView_whnf] =>
      vcgen [ih.inferIO, ih.whnf, mkFVarM_specI (mode := .verified) (eager := eager) (env := env),
        ensureSortIOI_spec ih] <;> finish
  | lam _ ty b _ =>
    sym only [conleche_grind, ConLeche.inferBodyIO, CoreFns.ioView_infer] =>
      vcgen [ih.inferIO, mkFVarM_specI (mode := .verified) (eager := eager) (env := env), InLean.abstract1M,
        abstractRangeM_specI (mode := .verified) (eager := eager) (env := env)] <;> finish
  | letE _ ty v b _ =>
    sym only [conleche_grind, ConLeche.inferBodyIO, CoreFns.ioView_infer] =>
      vcgen [ih.inferIO] <;> finish
  | _ => simp [inferLeafI] at hl

end Body

end InLeanProof

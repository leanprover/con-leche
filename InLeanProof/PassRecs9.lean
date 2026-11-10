module

public import InLeanProof.PassRecs8
import ConLeche.Verify.Cached.IndWalksC

/-!
# O7-recursors: the stored recursors' firing data (task #451, round 7)

* `streamNestedOk_tr`: InLean's guard on a stored recursor type at the
  generated firing data (`generatedFire`) gives master's on its reading:
  the pins (`abstractPrefix` of the class's parameters, lifted past the
  index binders) read as master's where InLean's comparison (`clEq`)
  found them equal to the domain's arguments, which have readings.
-/

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached

/-! ## Metavariables through a `mapSpec` pass -/

/-- A `mapSpec` pass whose callback writes metavariables only where it read
one keeps a metavariable-free result's input metavariable-free. -/
theorem emvarS_of_mapSpec (f : Lean.Expr → Nat → Option Lean.Expr)
    (hf : ∀ x k y, f x k = some y → emvarS y = false → emvarS x = false) :
    ∀ (e : Lean.Expr) (c : Nat), emvarS (mapSpec f e c) = false → emvarS e = false := by
  intro e
  induction e with
  | app g a ihg iha =>
    intro c h
    cases hc : f (.app g a) c with
    | some y => simp only [mapSpec, hc, Option.getD_some] at h; exact hf _ _ _ hc h
    | none =>
      simp only [mapSpec, hc, Option.getD_none, emvarS, Bool.or_eq_false_iff] at h ⊢
      exact ⟨ihg c h.1, iha c h.2⟩
  | lam n t b bi iht ihb =>
    intro c h
    cases hc : f (.lam n t b bi) c with
    | some y => simp only [mapSpec, hc, Option.getD_some] at h; exact hf _ _ _ hc h
    | none =>
      simp only [mapSpec, hc, Option.getD_none, emvarS, Bool.or_eq_false_iff] at h ⊢
      exact ⟨iht c h.1, ihb (c + 1) h.2⟩
  | forallE n t b bi iht ihb =>
    intro c h
    cases hc : f (.forallE n t b bi) c with
    | some y => simp only [mapSpec, hc, Option.getD_some] at h; exact hf _ _ _ hc h
    | none =>
      simp only [mapSpec, hc, Option.getD_none, emvarS, Bool.or_eq_false_iff] at h ⊢
      exact ⟨iht c h.1, ihb (c + 1) h.2⟩
  | letE n t v b nd iht ihv ihb =>
    intro c h
    cases hc : f (.letE n t v b nd) c with
    | some y => simp only [mapSpec, hc, Option.getD_some] at h; exact hf _ _ _ hc h
    | none =>
      simp only [mapSpec, hc, Option.getD_none, emvarS, Bool.or_eq_false_iff] at h ⊢
      exact ⟨⟨iht c h.1.1, ihv c h.1.2⟩, ihb (c + 1) h.2⟩
  | mdata m x ih =>
    intro c h
    cases hc : f (.mdata m x) c with
    | some y => simp only [mapSpec, hc, Option.getD_some] at h; exact hf _ _ _ hc h
    | none =>
      simp only [mapSpec, hc, Option.getD_none, emvarS] at h ⊢
      exact ih c h
  | proj s i x ih =>
    intro c h
    cases hc : f (.proj s i x) c with
    | some y => simp only [mapSpec, hc, Option.getD_some] at h; exact hf _ _ _ hc h
    | none =>
      simp only [mapSpec, hc, Option.getD_none, emvarS] at h ⊢
      exact ih c h
  | bvar _ | fvar _ | sort _ | const _ _ | lit _ => intro _ _; rfl
  | mvar m =>
    intro c h
    cases hc : f (.mvar m) c with
    | some y => simp only [mapSpec, hc, Option.getD_some] at h; exact hf _ _ _ hc h
    | none => simp only [mapSpec, hc, Option.getD_none] at h; exact h

/-- Lifting writes no metavariable. -/
theorem emvarS_of_liftLooseBVars {e : Lean.Expr} {s d : Nat}
    (h : emvarS (EO.liftLooseBVars e s d) = false) : emvarS e = false := by
  rw [liftLooseBVars_eq] at h
  split at h
  · exact h
  · refine emvarS_of_mapSpec (liftF s d) ?_ e 0 h
    intro x k y hy hm
    unfold liftF at hy
    split at hy
    · cases hy; exact hm
    · split at hy
      · rfl
      · cases hy

theorem emvarS_of_abstractPrefix {k c : Nat} {e : Lean.Expr}
    (h : emvarS (InLean.abstractPrefix k c e) = false) : emvarS e = false :=
  emvarS_of_abstractDepthsFrom h

/-- **InLean's prefix abstraction reads as master's** where it wrote no
marker. -/
theorem toExpr_abstractPrefix {fv : FVarId → Option ConLeche.Expr} (hfd : FvDepthOK fv)
    (k c : Nat) {e : Lean.Expr} {ce : ConLeche.Expr} (hr : Expr.RangeOk e) (h : toExpr fv e = some ce)
    (hm : emvarS (InLean.abstractPrefix k c e) = false) :
    Expr.RangeOk (InLean.abstractPrefix k c e) ∧
      toExpr fv (InLean.abstractPrefix k c e) = some (ConLeche.Expr.abstractPrefixC k c ce) := by
  unfold InLean.abstractPrefix at hm ⊢
  rw [ConLeche.Expr.abstractPrefixC, ConLeche.Expr.abstractRangeC_spec]
  exact ⟨RangeOk_abstractDepthsFrom hr 0 k c, toExpr_abstractDepthsFrom hfd hr h 0 k c hm⟩

/-! ## The guard -/

theorem okC_stripPis : ∀ {n : Nat} {e : Lean.Expr} {ds : List Lean.Expr} {r : Lean.Expr},
    okC e = true → InLean.stripPis n e = some (ds, r) → okC r = true
  | 0, e, ds, r, h, hs => by
    simp only [InLean.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨-, rfl⟩ := hs; exact h
  | n + 1, .forallE _ d b _, ds, r, h, hs => by
    simp only [InLean.stripPis, Option.map_eq_some_iff, Prod.mk.injEq] at hs
    obtain ⟨⟨ds', r'⟩, h1, -, rfl⟩ := hs
    simp only [okC, okE, Bool.and_eq_true] at h
    exact okC_stripPis h.2 h1
  | n + 1, .mdata _ e, ds, r, h, hs => by
    simp only [InLean.stripPis] at hs
    exact okC_stripPis (e := e) h hs
  | _ + 1, .bvar _, _, _, _, hs | _ + 1, .fvar _, _, _, _, hs | _ + 1, .mvar _, _, _, _, hs
  | _ + 1, .sort _, _, _, _, hs | _ + 1, .const _ _, _, _, _, hs | _ + 1, .app _ _, _, _, _, hs
  | _ + 1, .lam _ _ _ _, _, _, _, hs | _ + 1, .letE _ _ _ _ _, _, _, _, hs
  | _ + 1, .lit _, _, _, _, hs | _ + 1, .proj _ _ _, _, _, _, hs => by
    simp [InLean.stripPis] at hs

/-- Equal under the checker's comparison, element by element: the right
side reads as the left one's readings. -/
theorem mapM_toExpr_of_beq {fv : FVarId → Option ConLeche.Expr} :
    ∀ {l₁ l₂ : List Lean.Expr} {c : List ConLeche.Expr},
      l₁.mapM (toExpr fv) = some c → (l₁ == l₂) = true → l₂.mapM (toExpr fv) = some c
  | [], [], _, h, _ => h
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: l₁, b :: l₂, c, h₁, h => by
    simp only [List.cons_beq_cons, Bool.and_eq_true] at h
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h₁ ⊢
    obtain ⟨ca, ha, cl, hl, rfl⟩ := h₁
    exact ⟨ca, by rw [← toExpr_of_clEq fv h.1]; exact ha, cl, mapM_toExpr_of_beq hl h.2, rfl⟩

theorem mapM_toExpr_TrSL {s : InLean.CState} :
    ∀ {l : List Lean.Expr}, OkSL s l = true →
      l.mapM (toExpr (FVarTable.trans (tableOf s))) = some (TrSL s l)
  | [], _ => rfl
  | a :: l, h => by
    simp only [OkSL_cons, Bool.and_eq_true] at h
    have ha : toExpr (FVarTable.trans (tableOf s)) a = some (TrS s a) := TransS_of_ok h.1
    simp only [List.mapM_cons, ha, mapM_toExpr_TrSL h.2, TrSL_cons, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]

theorem mapM_toExpr_bvars {fv : FVarId → Option ConLeche.Expr} (f : Nat → Nat) :
    ∀ l : List Nat, (l.map fun i => Lean.Expr.bvar (f i)).mapM (toExpr fv) =
      some (l.map fun i => ConLeche.Expr.bvar (f i))
  | [] => rfl
  | i :: l => by
    simp only [List.map_cons, List.mapM_cons, toExpr, mapM_toExpr_bvars f l, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]

/-- The pins, read: each one's reading is master's pin at the reading of its
parameter, where the InLean pin has a reading. -/
theorem mapM_pins {s : InLean.CState} (rP n : Nat) :
    ∀ {ds : List Lean.Expr} {c : List ConLeche.Expr}, OkSL s ds = true →
      ((ds.map (InLean.abstractPrefix rP 0)).map (EO.liftLooseBVars · 0 n)).mapM
        (toExpr (FVarTable.trans (tableOf s))) = some c →
      c = ((TrSL s ds).map (ConLeche.Expr.abstractPrefix rP 0)).map
        (ConLeche.Expr.liftLooseBVars n 0)
  | [], c, _, h => by simp at h; subst h; rfl
  | a :: ds, c, hok, h => by
    simp only [OkSL_cons, Bool.and_eq_true] at hok
    simp only [List.map_cons, List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨ca, ha, cl, hl, rfl⟩ := h
    have hfv := FVarTable.trans_fvarsOnly (tableOf s)
    have hm := emvarS_of_liftLooseBVars (emvarS_of_toExpr ha)
    obtain ⟨hr1, h1⟩ := toExpr_abstractPrefix (FVarTable.trans_depthOK _) rP 0 (RangeOk_of_OkS hok.1)
      (TransS_of_ok hok.1) hm
    rw [ConLeche.Expr.abstractPrefixC_eq] at h1
    rw [toExpr_liftLooseBVars hfv hr1 h1 0 n] at ha
    cases ha
    rw [mapM_pins rP n hok.2 hl]
    rfl

/-- **The firing data's guard, read**: InLean's `streamNestedOk` on a stored
type at the generated firing data gives master's on the reading. -/
theorem streamNestedOk_tr {s : InLean.CState} {ty : Lean.Expr} {mI rP : Nat}
    {M : InLean.TargetMajor} (hty : okC ty = true) (hds : OkSL s M.ds = true)
    (h : InLean.streamNestedOk ty mI rP (InLean.generatedFire M rP) = true) :
    ConLeche.streamNestedOk (trC ty) mI rP (ConLeche.generatedFire (trTM s M) rP) = true := by
  unfold InLean.generatedFire at h
  unfold ConLeche.generatedFire
  simp only [trTM]
  cases hM : M.member with
  | some _ => rfl
  | none =>
    simp only [hM] at h
    simp only [InLean.auxRuleFire, InLean.streamNestedOk] at h
    simp only [ConLeche.auxRuleFire, ConLeche.streamNestedOk]
    rw [stripPis_tr]
    cases hsp : InLean.stripPis mI ty with
    | none => simp [hsp] at h
    | some pr =>
      obtain ⟨ds, r⟩ := pr
      simp only [hsp, Option.map_some] at h
      have hokr : okC (EO.stripTop r) = true := by rw [okC_stripTop]; exact okC_stripPis hty hsp
      simp only [Option.map_some]
      rw [← trC_stripTop r]
      split at h
      rotate_left
      · simp at h
      rename_i n0 dom b bi hst
      have hst' : EO.stripTop r = .forallE n0 dom b bi := Option.some.inj hst
      rw [hst'] at hokr ⊢
      simp only [okC, okE, Bool.and_eq_true] at hokr
      simp only [trC, trE]
      rw [show trE (fun _ => none) dom = trC dom from rfl]
      simp only [Bool.and_eq_true] at h ⊢
      obtain ⟨h1, h2⟩ := h
      refine ⟨?_, ?_⟩
      · rw [← TrS_of_okC s hokr.1, ← TrS_getAppFnT]
        split at h1
        · rename_i n us hfn
          rw [hfn, TrS_const]
          simp only [beq_iff_eq] at h1 ⊢
          rw [h1]
        · simp at h1
      · have hl := mapM_toExpr_TrSL (s := s) (OkSL_appArgs s (OkS_of_okC s hokr.1))
        have hr := mapM_toExpr_of_beq hl h2
        rw [TrSL_appArgs, TrS_of_okC s hokr.1] at hr
        simp only [List.mapM_append, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.pure_def, Option.some.injEq] at hr
        obtain ⟨a, ha, b, hb, he⟩ := hr
        rw [← he, mapM_pins rP (mI - rP) hds ha]
        simp only [mkBvar_eq] at hb
        rw [mapM_toExpr_bvars, Option.some.injEq] at hb
        rw [← hb]
        exact beq_self_eq_true _

/-! ## One recursor, then the family -/

/-- **One stored recursor against the generated one** (`streamRecCheck`): the
rules' shape, the firing-data guard (`streamNestedOk_tr`), the comparison
(`streamRecCompareI_run`). -/
theorem streamRecCheckI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    {rc : InLean.RecShape} {g : Lean.ConstantVal × InLean.TargetMajor × List Lean.Expr}
    (sx : InLean.CState) {s₀ s' : InLean.CState} (hs : CSOKI .verified false L s₀)
    (hokS : okC rc.cvR.type = true) (hrl : ∀ r ∈ rc.rules, okC r.rhs = true)
    (hokG : okC g.1.type = true) (hlbbG : (trC g.1.type).looseBVarsBounded 0 = true)
    (hgr : ∀ r ∈ g.2.2, okC r = true ∧ (trC r).looseBVarsBounded 0 = true)
    (hds : OkSL sx g.2.1.ds = true)
    (h : InLean.streamRecCheck .verified fe rc g s₀ = .ok ((), s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.streamRecCheck (ConLeche.fueledOpsM .verified) (ConLeche.mkFEnv L)
        (trRec rc) (trOut sx g)) () := by
  unfold InLean.streamRecCheck at h
  obtain ⟨_, s₁, h1, hA⟩ := bind_run h
  obtain ⟨e1, hR1⟩ := streamRulesShapeI_run rc.rules g.2.1.ctors h1
  subst e1
  cases hn : InLean.streamNestedOk rc.cvR.type rc.mI rc.rP (InLean.generatedFire g.2.1 rc.rP) <;>
    simp only [hn, Bool.false_eq_true, ↓reduceIte] at hA
  · obtain ⟨_, _, h2, -⟩ := bind_run hA; exact (throw_run h2).elim
  obtain ⟨hs₃, ht₃, hR3⟩ := streamRecCompareI_run hJ sx hs hokS hrl hokG hlbbG hgr hA
  refine ⟨hs₃, ht₃, ?_⟩
  have hn' := streamNestedOk_tr (s := sx) hokS hds hn
  unfold ConLeche.streamRecCheck
  simp only [trRec, trCV] at hn' hR3 ⊢
  refine Runs.bind hR1 ?_
  simp only [trOut, trTM, trCV] at hn' ⊢
  simp only [hn', ↓reduceIte]
  simpa only [trOut, trTM, trCV] using hR3

/-- **The family's stored recursors against the generated ones**
(`streamRecsCheck`), record by record. -/
theorem streamRecsCheckI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    (sx : InLean.CState) :
    ∀ (rcs : List InLean.RecShape) (gs : List (Lean.ConstantVal × InLean.TargetMajor × List Lean.Expr))
      {s₀ s' : InLean.CState}, CSOKI .verified false L s₀ →
      (∀ rc ∈ rcs, okC rc.cvR.type = true ∧ ∀ r ∈ rc.rules, okC r.rhs = true) →
      (∀ g ∈ gs, okC g.1.type = true ∧ (trC g.1.type).looseBVarsBounded 0 = true ∧
        (∀ r ∈ g.2.2, okC r = true ∧ (trC r).looseBVarsBounded 0 = true) ∧
        OkSL sx g.2.1.ds = true) →
      InLean.streamRecsCheck .verified fe rcs gs s₀ = .ok ((), s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
        Runs (ConLeche.streamRecsCheck (ConLeche.fueledOpsM .verified) (ConLeche.mkFEnv L)
          (rcs.map trRec) (gs.map (trOut sx))) ()
  | rc :: rcs, g :: gs, s₀, s', hs, hrc, hg, h => by
    unfold InLean.streamRecsCheck at h
    obtain ⟨_, s₁, h1, h⟩ := bind_run h
    obtain ⟨g1, g2, g3, g4⟩ := hg g List.mem_cons_self
    obtain ⟨hs₁, ht₁, hR1⟩ := streamRecCheckI_run hJ sx hs (hrc rc List.mem_cons_self).1
      (hrc rc List.mem_cons_self).2 g1 g2 g3 g4 h1
    obtain ⟨hs₂, ht₂, hR2⟩ := streamRecsCheckI_run hJ sx rcs gs hs₁
      (fun r hr => hrc r (List.mem_cons_of_mem _ hr)) (fun x hx => hg x (List.mem_cons_of_mem _ hx)) h
    refine ⟨hs₂, ht₁.trans ht₂, ?_⟩
    simp only [List.map_cons]
    unfold ConLeche.streamRecsCheck
    exact Runs.bind hR1 hR2
  | [], [], s₀, s', hs, _, _, h => by
    unfold InLean.streamRecsCheck at h
    obtain ⟨-, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, by unfold ConLeche.streamRecsCheck; exact Runs.pure _⟩
  | [], _ :: _, s₀, s', _, _, _, h | _ :: _, [], s₀, s', _, _, _, h => by
    unfold InLean.streamRecsCheck at h; exact (throw_run h).elim

/-! ## The generated recursors' environment, master's side -/

/-- **Master's generated install is well formed** (`genRecCheck_recsWF`) at
a run of the stage at `fueledOpsM .verified`, the run
`genRecCheckI_run` gives: the well-formedness part of `JobEnvI` at the
stored recursors' check (`fe₂.pushAll (blockRecInfosTF p 0 out)`). -/
theorem envWF_genRecs {L₂ : ConLeche.Env} (hwf : ConLeche.EnvWF L₂) {p : ConLeche.BlockShape}
    {nestedBit : Bool} {params : List ConLeche.Expr} {tbl : List ConLeche.NestCtorNf}
    {rd : ConLeche.ClassRead} {Ms : List ConLeche.TargetMajor} {block : List ConLeche.ConstantInfo}
    {out : List (ConLeche.ConstantVal × ConLeche.TargetMajor × List ConLeche.Expr)}
    (hR : Runs (ConLeche.genRecCheck (ConLeche.fueledOpsM .verified)
      (ConLeche.mkFEnv L₂) p nestedBit params tbl rd Ms block) out)
    (hpl : params.length = p.nP) (hMs : ∀ M ∈ Ms, ConLeche.ClassOutParams p.nP M) :
    ConLeche.EnvWF (ConLeche.consBlockRecsT p 0 out L₂) := by
  obtain ⟨F, hF⟩ := hR
  rw [ConLeche.genRecCheck_datF] at hF
  exact ConLeche.Cached.genRecCheck_recsWF hwf hF hpl hMs

end InLeanProof

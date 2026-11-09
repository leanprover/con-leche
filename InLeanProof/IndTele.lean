module

public import InLeanProof.IndMembers
public import ConLeche.Verify.Cached.NestPosC
import ConLeche.Verify.Cached.IndWalksC

/-!
# O7: the former's whnf telescope and its reduct (task #451, lane O7)

`whnfTelescopeI_run` (`whnfTelescopeS_spec`'s twin): InLean's telescope loop at
the job's operations answers master's fueled loop at the translation, the
domains read at the final state.  `closeTelescope_tr`: InLean's closing (by
depth, `EO.abstractDepthsFrom`) reads as master's `closeTelescopeC` when it
wrote no out-of-range marker, which `reducedFormer` checks
(`reducedFormer_emvar`).  `reducedFormerSimI` discharges `ReducedFormerSimI`.
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached
open scoped Lean.Order

/-! ## The telescope loop -/

/-- **The whnf telescope** (`whnfTelescopeS_spec`'s twin), functional form. -/
theorem whnfTelescopeI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hO : OpsSimI fe L) :
    ∀ (n i : Nat) {e : Lean.Expr} {s₀ : InLean.CState} {bs : List Lean.Expr} {u : Lean.Level}
      {s' : InLean.CState},
      CSOKI .verified false L s₀ → OkS s₀ e = true → ConLeche.Expr.WScoped i (TrS s₀ e) →
      (TrS s₀ e).looseBVarsBounded 0 = true →
      InLean.whnfTelescope (sharedOpsC .verified fe) fe i n e s₀ = .ok ((bs, u), s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ OkSL s' bs = true ∧ okLv u = true ∧
        AllClosed (TrSL s' bs) = true ∧
        Runs (ConLeche.whnfTelescope (ConLeche.fueledOpsM .verified) L i n (TrS s₀ e))
          (TrSL s' bs, trL u)
  | 0, i, e, s₀, bs, u, s', hs, hok, hw, hc, h => by
    unfold InLean.whnfTelescope at h
    obtain ⟨v, s₁, hv, h⟩ := bindI_ok h
    obtain ⟨hs₁, ht₁, hok₁, hR, -, -⟩ := tripleI_iff_run.1 (hO.whnf hs hok hw hc) v s₁ hv
    have hT : TrS s₁ v = TrS s₁ (EO.stripTop v) := (TrS_stripTop s₁ v).symm
    have hOk : OkS s₁ (EO.stripTop v) = true := by rw [OkS_stripTop]; exact hok₁
    generalize EO.stripTop v = x at h hT hOk
    cases x with
    | sort w =>
      obtain ⟨hp, rfl⟩ := pureI_ok h
      simp only [Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      refine ⟨hs₁, ht₁, rfl, hOk, rfl, ?_⟩
      unfold ConLeche.whnfTelescope
      rw [hT] at hR
      exact Runs.bind hR (Runs.pure _)
    | _ => exact (throwI_ok h).elim
  | n + 1, i, e, s₀, bs, u, s', hs, hok, hw, hc, h => by
    unfold InLean.whnfTelescope at h
    obtain ⟨v, s₁, hv, h⟩ := bindI_ok h
    obtain ⟨hs₁, ht₁, hok₁, hR, hw₁, hc₁⟩ := tripleI_iff_run.1 (hO.whnf hs hok hw hc) v s₁ hv
    have hT : TrS s₁ v = TrS s₁ (EO.stripTop v) := (TrS_stripTop s₁ v).symm
    have hOk : OkS s₁ (EO.stripTop v) = true := by rw [OkS_stripTop]; exact hok₁
    generalize EO.stripTop v = x at h hT hOk
    cases x with
    | forallE nm dom body bi =>
      rw [TrS_forallE] at hT
      rw [hT] at hw₁ hc₁ hR
      simp only [OkS_forallE, Bool.and_eq_true] at hOk
      simp only [ConLeche.Expr.WScoped] at hw₁
      simp only [ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true] at hc₁
      obtain ⟨x, s₂, hx, h⟩ := bindI_ok h
      obtain ⟨hs₂, ht₂, hokx, htx⟩ := tripleI_iff_run.1
        (mkFVarM_specI hs₁ i hOk.1 hc₁.1) x s₂ hx
      obtain ⟨r, s₃, hr, h⟩ := bindI_ok h
      obtain ⟨bs', u'⟩ := r
      have hb₂ : OkS s₂ body = true := okS_of_tabLe ht₂ hOk.2
      have hcx : (TrS s₂ x).looseBVarsBounded 0 = true := by rw [htx]; rfl
      have hinst := TrS_inst1_eq hb₂ hokx hcx
      have hokI : OkS s₂ (body.inst1I x) = true := OkS_inst1 hb₂ hokx hcx
      have hTI : TrS s₂ (body.inst1I x) =
          (TrS s₁ body).instantiate1 (.fvar i (TrS s₁ dom)) 0 := by
        rw [inst1I_eq, hinst, htx, TrS_of_tabLe ht₂ hOk.2]
      obtain ⟨hs₃, ht₃, hokbs, hoku, hcl, hR'⟩ := whnfTelescopeI_run hO n (i + 1) hs₂ hokI
        (by rw [hTI]; exact ConLeche.Expr.WScoped.instantiate1 hw₁.1 0 hw₁.2)
        (by rw [hTI]; exact lbb_instantiate1 rfl hc₁.2) hr
      obtain ⟨hp, rfl⟩ := pureI_ok h
      simp only [Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      have ht13 : TabLe s₁ s₃ := ht₂.trans ht₃
      have hdom : TrS s₃ dom = TrS s₁ dom := TrS_of_tabLe ht13 hOk.1
      refine ⟨hs₃, ht₁.trans ht13, ?_, hoku, ?_, ?_⟩
      · simp only [OkSL, List.all_cons, Bool.and_eq_true]
        exact ⟨okS_of_tabLe ht13 hOk.1, hokbs⟩
      · simp only [TrSL, AllClosed, List.map_cons, List.all_cons, Bool.and_eq_true] at hcl ⊢
        exact ⟨by rw [hdom]; exact hc₁.1, hcl⟩
      · unfold ConLeche.whnfTelescope
        refine Runs.bind hR ?_
        rw [hTI] at hR'
        refine Runs.bind hR' ?_
        simp only [TrSL, List.map_cons, hdom]
        exact Runs.pure _
    | _ => exact (throwI_ok h).elim

/-! ## The closing -/

/-- Abstraction writes metavariables only as its marker: a marker-free result
comes from a metavariable-free term. -/
theorem emvarS_of_mapSpec_absF (d k : Nat) :
    ∀ (e : Lean.Expr) (c : Nat), emvarS (mapSpec (absF d k) e c) = false → emvarS e = false := by
  intro e
  induction e with
  | mvar m =>
    intro c h
    exfalso
    have : mapSpec (absF d k) (.mvar m) c = .mvar m := by
      unfold mapSpec absF
      cases (Lean.Expr.mvar m).hasFVar <;> rfl
    rw [this] at h; simp [emvarS] at h
  | app f a ihf iha =>
    intro c h
    cases hf : (Lean.Expr.app f a).hasFVar
    · have : mapSpec (absF d k) (.app f a) c = .app f a := by
        exact mapSpec_eq_of_some (by simp [absF, hf])
      rwa [this] at h
    · have : mapSpec (absF d k) (.app f a) c = .app (mapSpec (absF d k) f c) (mapSpec (absF d k) a c) := by
        simp [mapSpec, absF, hf]
      rw [this] at h; simp only [emvarS, Bool.or_eq_false_iff] at h ⊢
      exact ⟨ihf c h.1, iha c h.2⟩
  | lam n t b bi iht ihb =>
    intro c h
    cases hf : (Lean.Expr.lam n t b bi).hasFVar
    · have : mapSpec (absF d k) (.lam n t b bi) c = .lam n t b bi := by
        exact mapSpec_eq_of_some (by simp [absF, hf])
      rwa [this] at h
    · have : mapSpec (absF d k) (.lam n t b bi) c =
          .lam n (mapSpec (absF d k) t c) (mapSpec (absF d k) b (c + 1)) bi := by
        simp [mapSpec, absF, hf]
      rw [this] at h; simp only [emvarS, Bool.or_eq_false_iff] at h ⊢
      exact ⟨iht c h.1, ihb (c + 1) h.2⟩
  | forallE n t b bi iht ihb =>
    intro c h
    cases hf : (Lean.Expr.forallE n t b bi).hasFVar
    · have : mapSpec (absF d k) (.forallE n t b bi) c = .forallE n t b bi := by
        exact mapSpec_eq_of_some (by simp [absF, hf])
      rwa [this] at h
    · have : mapSpec (absF d k) (.forallE n t b bi) c =
          .forallE n (mapSpec (absF d k) t c) (mapSpec (absF d k) b (c + 1)) bi := by
        simp [mapSpec, absF, hf]
      rw [this] at h; simp only [emvarS, Bool.or_eq_false_iff] at h ⊢
      exact ⟨iht c h.1, ihb (c + 1) h.2⟩
  | letE n t v b nd iht ihv ihb =>
    intro c h
    cases hf : (Lean.Expr.letE n t v b nd).hasFVar
    · have : mapSpec (absF d k) (.letE n t v b nd) c = .letE n t v b nd := by
        exact mapSpec_eq_of_some (by simp [absF, hf])
      rwa [this] at h
    · have : mapSpec (absF d k) (.letE n t v b nd) c =
          .letE n (mapSpec (absF d k) t c) (mapSpec (absF d k) v c) (mapSpec (absF d k) b (c + 1)) nd := by
        simp [mapSpec, absF, hf]
      rw [this] at h; simp only [emvarS, Bool.or_eq_false_iff] at h ⊢
      exact ⟨⟨iht c h.1.1, ihv c h.1.2⟩, ihb (c + 1) h.2⟩
  | mdata m x ih =>
    intro c h
    cases hf : (Lean.Expr.mdata m x).hasFVar
    · have : mapSpec (absF d k) (.mdata m x) c = .mdata m x := by
        exact mapSpec_eq_of_some (by simp [absF, hf])
      rwa [this] at h
    · have : mapSpec (absF d k) (.mdata m x) c = .mdata m (mapSpec (absF d k) x c) := by
        simp [mapSpec, absF, hf]
      rw [this] at h; simp only [emvarS] at h ⊢
      exact ih c h
  | proj s i x ih =>
    intro c h
    cases hf : (Lean.Expr.proj s i x).hasFVar
    · have : mapSpec (absF d k) (.proj s i x) c = .proj s i x := by
        exact mapSpec_eq_of_some (by simp [absF, hf])
      rwa [this] at h
    · have : mapSpec (absF d k) (.proj s i x) c = .proj s i (mapSpec (absF d k) x c) := by
        simp [mapSpec, absF, hf]
      rw [this] at h; simp only [emvarS] at h ⊢
      exact ih c h
  | bvar _ | fvar _ | sort _ | const _ _ | lit _ => intro _ _; rfl

theorem emvarS_of_abstractDepthsFrom {e : Lean.Expr} {d k c : Nat}
    (h : emvarS (EO.abstractDepthsFrom e d k c) = false) : emvarS e = false := by
  rw [abstractDepthsFrom_eq] at h
  split at h
  · exact h
  · exact emvarS_of_mapSpec_absF d k e c h

theorem emvarS_of_abstract1 {e : Lean.Expr} {i c : Nat}
    (h : emvarS (InLean.abstract1 e i c) = false) : emvarS e = false :=
  emvarS_of_abstractDepthsFrom h

/-- A closed term's translation, abstracted in bulk (`closeTelescopeFrom`'s
reading). -/
theorem tr_abstractDepthsFrom {s : InLean.CState} {e : Lean.Expr} (he : OkS s e = true) (d k c : Nat)
    (hm : emvarS (EO.abstractDepthsFrom e d k c) = false) :
    OkS s (EO.abstractDepthsFrom e d k c) = true ∧
      TrS s (EO.abstractDepthsFrom e d k c) = (TrS s e).abstractRange d k c :=
  ok_of_TransS (RangeOk_abstractDepthsFrom (RangeOk_of_OkS he) d k c)
    (toExpr_abstractDepthsFrom (FVarTable.trans_depthOK _) (RangeOk_of_OkS he) (TransS_of_ok he)
      d k c hm)

/-- **InLean's closing reads as master's one-pass closing**
(`closeTelescopeGoC`) where it wrote no out-of-range marker. -/
theorem closeTelescopeFrom_tr (s : InLean.CState) :
    ∀ (bs : List Lean.Expr) (i j : Nat) (body : Lean.Expr), OkSL s bs = true → OkS s body = true →
      emvarS (InLean.closeTelescopeFrom bs i j body) = false →
      OkS s (InLean.closeTelescopeFrom bs i j body) = true ∧
        TrS s (InLean.closeTelescopeFrom bs i j body) =
          ConLeche.Expr.closeTelescopeGoC i j (TrSL s bs) (TrS s body)
  | [], i, j, body, _, hb, hm => by
    simp only [TrSL, List.map_nil, ConLeche.Expr.closeTelescopeGoC, ConLeche.Expr.abstractRangeC_spec]
    exact tr_abstractDepthsFrom hb i j 0 hm
  | dom :: bs, i, j, body, hbs, hb, hm => by
    simp only [OkSL, List.all_cons, Bool.and_eq_true] at hbs
    simp only [InLean.closeTelescopeFrom, emvarS, Bool.or_eq_false_iff] at hm
    obtain ⟨hC, hTC⟩ := closeTelescopeFrom_tr s bs i (j + 1) body hbs.2 hb hm.2
    obtain ⟨hokA, htrA⟩ := tr_abstractDepthsFrom hbs.1 i j 0 hm.1
    refine ⟨?_, ?_⟩
    · simp only [InLean.closeTelescopeFrom, OkS_forallE, Bool.and_eq_true]
      exact ⟨hokA, hC⟩
    · simp only [InLean.closeTelescopeFrom, TrS_forallE, TrSL, List.map_cons,
        ConLeche.Expr.closeTelescopeGoC, ConLeche.Expr.mkForallE_eq, ConLeche.Expr.abstractRangeC_spec]
      rw [htrA, hTC]
      rfl

/-- **InLean's closing reads as master's `closeTelescopeC`** where it wrote
no out-of-range marker. -/
theorem closeTelescope_tr (s : InLean.CState) (bs : List Lean.Expr) (i : Nat) (body : Lean.Expr)
    (hbs : OkSL s bs = true) (hb : OkS s body = true)
    (hm : emvarS (InLean.closeTelescope bs i body) = false) :
    OkS s (InLean.closeTelescope bs i body) = true ∧
      TrS s (InLean.closeTelescope bs i body) =
        ConLeche.Expr.closeTelescopeC (TrSL s bs) i (TrS s body) :=
  closeTelescopeFrom_tr s bs i 0 body hbs hb hm

/-! ## The reduct -/

/-- **The reduct is marker-free**: InLean's `closeTelescope` abstracts by depth
through `EO.abstractDepthsFrom`, which writes `EO.rangePoison` where the bound
index would pass C's bound (`maxBVarIdx`); `reducedFormer` refuses a reduct
`EO.inRange` refuses. -/
theorem reducedFormer_emvar {ops : InLean.CheckerOps} {fe : InLean.FEnv}
    {cv cvR : Lean.ConstantVal} {n : Nat} {s₀ s' : InLean.CState}
    (h : InLean.reducedFormer ops fe cv n s₀ = .ok (cvR, s')) :
    emvarS cvR.type = false := by
  unfold InLean.reducedFormer at h
  obtain ⟨⟨bs, u⟩, s₁, _, h⟩ := bindI_ok h
  dsimp only at h
  split at h
  · obtain ⟨rfl, -⟩ := pureI_ok h
    exact (RangeOk_of_inRange ‹_›).2
  · exact (throwI_ok h).elim

theorem lbb_closeTelescope : ∀ (bs : List ConLeche.Expr) (i : Nat) (body : ConLeche.Expr),
    AllClosed bs = true → body.looseBVarsBounded 0 = true →
    (ConLeche.closeTelescope bs i body).looseBVarsBounded 0 = true
  | [], _, _, _, hb => hb
  | dom :: bs, i, body, hbs, hb => by
    simp only [AllClosed, List.all_cons, Bool.and_eq_true] at hbs
    simp only [ConLeche.closeTelescope, ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨hbs.1, lbb_abstract1 (lbb_closeTelescope bs (i + 1) body hbs.2 hb)⟩

/-- A term with a reading whose translation has no free variable has a closed
reading. -/
theorem okC_of_OkS {s : InLean.CState} :
    ∀ {e : Lean.Expr}, OkS s e = true → (TrS s e).hasFvar = false → okC e = true ∧ TrS s e = trC e := by
  intro e
  induction e with
  | fvar id =>
    intro h hf
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (show (FVarTable.trans (tableOf s) id).isSome = true from h)
    obtain ⟨d, ty, rfl⟩ := FVarTable.trans_fvarsOnly _ id _ hc
    simp [TrS, trE, hc, ConLeche.Expr.hasFvar] at hf
  | app f a ihf iha =>
    intro h hf
    simp only [OkS_app, Bool.and_eq_true] at h
    simp only [TrS_app, ConLeche.Expr.hasFvar, Bool.or_eq_false_iff] at hf
    obtain ⟨h1, h2⟩ := ihf h.1 hf.1; obtain ⟨h3, h4⟩ := iha h.2 hf.2
    exact ⟨by simp [okC, okE] at h1 h3 ⊢; exact ⟨h1, h3⟩, by rw [TrS_app, h2, h4]; rfl⟩
  | lam n t b bi iht ihb =>
    intro h hf
    simp only [OkS_lam, Bool.and_eq_true] at h
    simp only [TrS_lam, ConLeche.Expr.hasFvar, Bool.or_eq_false_iff] at hf
    obtain ⟨h1, h2⟩ := iht h.1 hf.1; obtain ⟨h3, h4⟩ := ihb h.2 hf.2
    exact ⟨by simp [okC, okE] at h1 h3 ⊢; exact ⟨h1, h3⟩, by rw [TrS_lam, h2, h4]; rfl⟩
  | forallE n t b bi iht ihb =>
    intro h hf
    simp only [OkS_forallE, Bool.and_eq_true] at h
    simp only [TrS_forallE, ConLeche.Expr.hasFvar, Bool.or_eq_false_iff] at hf
    obtain ⟨h1, h2⟩ := iht h.1 hf.1; obtain ⟨h3, h4⟩ := ihb h.2 hf.2
    exact ⟨by simp [okC, okE] at h1 h3 ⊢; exact ⟨h1, h3⟩, by rw [TrS_forallE, h2, h4]; rfl⟩
  | letE n t v b nd iht ihv ihb =>
    intro h hf
    simp only [OkS_letE, Bool.and_eq_true] at h
    simp only [TrS_letE, ConLeche.Expr.hasFvar, Bool.or_eq_false_iff] at hf
    obtain ⟨h1, h2⟩ := iht h.1.1 hf.1.1; obtain ⟨h3, h4⟩ := ihv h.1.2 hf.1.2
    obtain ⟨h5, h6⟩ := ihb h.2 hf.2
    exact ⟨by simp [okC, okE] at h1 h3 h5 ⊢; exact ⟨⟨h1, h3⟩, h5⟩,
      by rw [TrS_letE, h2, h4, h6]; rfl⟩
  | mdata m x ih =>
    intro h hf
    rw [OkS_mdata] at h; rw [TrS_mdata] at hf ⊢
    obtain ⟨h1, h2⟩ := ih h hf
    exact ⟨h1, h2⟩
  | proj sn i x ih =>
    intro h hf
    rw [OkS_proj] at h; rw [TrS_proj] at hf ⊢
    simp only [ConLeche.Expr.hasFvar] at hf
    obtain ⟨h1, h2⟩ := ih h hf
    exact ⟨h1, by rw [h2]; rfl⟩
  | bvar _ | mvar _ | sort _ | const _ _ | lit _ => intro h _; exact ⟨h, rfl⟩

/-- **`ReducedFormerSimI` discharged.** -/
theorem reducedFormerSimI : ReducedFormerSimI := by
  intro fe L cv cvR n s₀ s' hJ hs hok hcl h
  have hpoison := reducedFormer_emvar h
  unfold InLean.reducedFormer at h
  obtain ⟨r, s₁, h1, h⟩ := bindI_ok h
  obtain ⟨bs, u⟩ := r
  dsimp only at h
  split at h
  case isFalse => exact (throwI_ok h).elim
  obtain ⟨rfl, rfl⟩ := pureI_ok h
  obtain ⟨hs₁, ht₁, hokbs, hoku, hclbs, hR⟩ := whnfTelescopeI_run hJ.ops n 0 hs (OkS_of_okC _ hok)
    (by rw [TrS_of_okC _ hok]; exact trC_wscoped 0 _) (by rw [TrS_of_okC _ hok]; exact hcl) h1
  obtain ⟨hokC, htC⟩ := closeTelescope_tr s₁ bs 0 (.sort u) hokbs (by simpa [OkS_sort] using hoku)
    hpoison
  rw [ConLeche.Expr.closeTelescopeC_eq] at htC
  rw [TrS_of_okC _ hok] at hR
  -- the master reduct: closed and free of free variables
  have hRun : Runs (ConLeche.reducedFormer (ConLeche.fueledOpsM .verified) L (trCV cv) n)
      { trCV cv with type := TrS s₁ (InLean.closeTelescope bs 0 (.sort u)) } := by
    unfold ConLeche.reducedFormer
    refine Runs.bind (by rw [trCV_type]; exact hR) ?_
    rw [htC]
    exact Runs.pure _
  have hnf : (TrS s₁ (InLean.closeTelescope bs 0 (.sort u))).hasFvar = false := by
    have := Runs.reducedFormer_hasFvar hJ.wf (cv := trCV cv) (trC_hasFvar cv.type) hRun
    simpa using this
  obtain ⟨hokR, htR⟩ := okC_of_OkS hokC hnf
  refine ⟨hs₁, ht₁, hokR, ?_, ?_⟩
  · rw [← htR, htC]
    exact lbb_closeTelescope _ 0 _ hclbs rfl
  · rw [htR] at hRun
    exact hRun

end InLeanProof

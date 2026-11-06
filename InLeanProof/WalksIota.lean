module

public import InLeanProof.WalksWhnf
import ConLeche.Verify.Cached.DiscC3

/-!
# InLean's body walks, part 2: the ι step's walks (task #451, lane P2-whnf)

The twins of `Verify/Cached/DiscC3.lean`'s walks.  InLean reads a stored
constant's record off Lean's entry (`FEnv.indView?`, `FEnv.ctorView?`, …);
con-leche off its environment.  What relates the two is O4 (lane P3's), here
the named hypothesis `EnvViewI fe env`: every view InLean reads is the
translation of con-leche's record at the translated name.  A record's terms
are closed and translate as such (`CVRel`), so they read the same at every
state.

The walks whose pure side matches on the answer of a knot call (the family
sort's walk) are proved run by run, as `defeqSpineI_specI`: InLean's match
is on `EO.stripTop` of its answer, the pure one on the answer's translation.
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached
open scoped Lean.Order

variable {mode : ConLeche.CheckMode} {eager : Bool} {env : ConLeche.Env}

/-! ## Runs of binds -/

/-- A successful run of a bind is a successful run of each half. -/
theorem bind_run {α β : Type} {x : InLean.CheckCM α} {f : α → InLean.CheckCM β}
    {s₀ s' : InLean.CState} {v : β} (h : (x >>= f) s₀ = .ok (v, s')) :
    ∃ a s₁, x s₀ = .ok (a, s₁) ∧ f a s₁ = .ok (v, s') := by
  simp only [bind, StateT.bind, Except.bind] at h
  cases hx : x s₀ with
  | error e => rw [hx] at h; cases h
  | ok p => obtain ⟨a, s₁⟩ := p; rw [hx] at h; exact ⟨a, s₁, rfl, h⟩

theorem pure_run {α : Type} {a v : α} {s₀ s' : InLean.CState}
    (h : (pure a : InLean.CheckCM α) s₀ = .ok (v, s')) : a = v ∧ s₀ = s' := by
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  exact h

/-! ## Shapes through the translation -/

section Shapes
variable (s : InLean.CState)

/-- A top that is no sort translates to none. -/
theorem TrS_ne_sort {e : Expr} (h : ∀ u, EO.stripTop e ≠ .sort u) :
    ∀ u, TrS s e ≠ .sort u := by
  intro u ht
  rw [← TrS_stripTop s e] at ht
  generalize hx : EO.stripTop e = x at h ht
  cases x with
  | sort v => exact h v rfl
  | fvar id =>
    simp only [TrS, trE] at ht
    cases hf : FVarTable.trans (tableOf s) id with
    | none => simp [hf] at ht
    | some c =>
      obtain ⟨d, ty, rfl⟩ := FVarTable.trans_fvarsOnly _ id c hf
      simp [hf] at ht
  | mdata _ y => exact (stripTop_ne_mdata hx).elim
  | _ => simp [TrS, trE] at ht

/-- A top that is no `∀` translates to none. -/
theorem TrS_ne_forallE {e : Expr} (h : ∀ n t b bi, EO.stripTop e ≠ .forallE n t b bi) :
    ∀ t b, TrS s e ≠ .forallE t b := by
  intro t b ht
  rw [← TrS_stripTop s e] at ht
  generalize hx : EO.stripTop e = x at h ht
  cases x with
  | forallE n t' b' bi => exact h n t' b' bi rfl
  | fvar id =>
    simp only [TrS, trE] at ht
    cases hf : FVarTable.trans (tableOf s) id with
    | none => simp [hf] at ht
    | some c =>
      obtain ⟨d, ty, rfl⟩ := FVarTable.trans_fvarsOnly _ id c hf
      simp [hf] at ht
  | mdata _ y => exact (stripTop_ne_mdata hx).elim
  | _ => simp [TrS, trE] at ht

/-- The spine's head below the `∀`s, through `mdata`, is the translation's. -/
theorem TrS_piResult : ∀ e : Expr, TrS s (InLean.piResult e) = (TrS s e).piResult
  | .mdata _ e => by rw [InLean.piResult, TrS_mdata, TrS_piResult e]
  | .forallE _ t b _ => by
    rw [InLean.piResult, TrS_forallE, TrS_piResult b]; rfl
  | .fvar id => by
    simp only [InLean.piResult, TrS, trE]
    cases hf : FVarTable.trans (tableOf s) id with
    | none => rfl
    | some c => obtain ⟨d, ty, rfl⟩ := FVarTable.trans_fvarsOnly _ id c hf; rfl
  | .bvar _ | .mvar _ | .sort _ | .const .. | .app .. | .lam .. | .letE .. | .lit _ | .proj .. => rfl

theorem stripTop_getAppFnT (e : Expr) : EO.stripTop (Expr.getAppFnT e) = Expr.getAppFnT e := by
  generalize hx : Expr.getAppFnT e = x
  cases x with
  | mdata _ y => exact (getAppFnT_ne_mdata hx).elim
  | _ => rfl

end Shapes

/-! ## Zero-ness data through the translation -/

section PropWhenI

/-- The zero-ness datum's translation. -/
@[expose] def trPW : InLean.PropWhen → ConLeche.PropWhen
  | .never => .never
  | .ifAllZero ps => .ifAllZero (ps.map toName)

theorem trPW_isNever (p : InLean.PropWhen) : (trPW p).isNever = p.isNever := by
  cases p <;> rfl

theorem trPW_inter (p q : InLean.PropWhen) : trPW (p.inter q) = (trPW p).inter (trPW q) := by
  cases p <;> cases q <;> simp [trPW, InLean.PropWhen.inter, ConLeche.PropWhen.inter]

theorem trPW_zeronessOf : ∀ u : Level, trPW (InLean.Lvl.zeronessOf u) =
    ConLeche.Level.zeronessOf (trL u)
  | .zero => rfl
  | .succ _ => rfl
  | .param _ => rfl
  | .mvar _ => rfl
  | .max a b => by
    rw [InLean.Lvl.zeronessOf, trPW_inter, trPW_zeronessOf a, trPW_zeronessOf b]; rfl
  | .imax _ b => by rw [InLean.Lvl.zeronessOf, trPW_zeronessOf b]; rfl

theorem trL_substGo_gen : ∀ (ks : List Name) (vs : List Level) (n : Name),
    trL (Lvl.substGo ks vs n) = ConLeche.Level.subst.go (ks.map toName) (vs.map trL) (toName n)
  | k :: ks, v :: vs, n => by
    simp only [Lvl.substGo, List.map_cons, ConLeche.Level.subst.go, toName_eq_iff]
    by_cases h : k = n
    · simp [h]
    · simp only [beq_iff_eq, h, ↓reduceIte]; exact trL_substGo_gen ks vs n
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl

theorem trPW_bindZ_go (f : Name → InLean.PropWhen) (g : ConLeche.Name → ConLeche.PropWhen)
    (hfg : ∀ n, trPW (f n) = g (toName n)) :
    ∀ ps : List Name, trPW (InLean.PropWhen.bindZ.go f ps) = ConLeche.PropWhen.bindZ.go g (ps.map toName)
  | [] => rfl
  | n :: ps => by
    rw [InLean.PropWhen.bindZ.go, trPW_inter, hfg, trPW_bindZ_go f g hfg ps]; rfl

theorem trPW_substPW (ks : List Name) (us : List Level) (p : InLean.PropWhen) :
    trPW (InLean.Lvl.substPW ks us p) =
      ConLeche.Level.substPW (ks.map toName) (us.map trL) (trPW p) := by
  cases p with
  | never => rfl
  | ifAllZero ps =>
    simp only [InLean.Lvl.substPW, InLean.PropWhen.bindZ, ConLeche.Level.substPW, trPW,
      ConLeche.PropWhen.bindZ]
    exact trPW_bindZ_go _ _ (fun n => by rw [trPW_zeronessOf, trL_substGo_gen]) ps

end PropWhenI

/-! ## Stored records and the environment's views (O4, P3's) -/

section Views

/-- A stored term: no free variable, in range, with a closed reading. -/
@[expose] def StoredT (t : Expr) (c : ConLeche.Expr) : Prop :=
  fvarS t = false ∧ Expr.RangeOk t ∧ toExprC t = some c

/-- A stored constant's name, levels and type, against con-leche's. -/
@[expose] def CVRel (cv : Lean.ConstantVal) (ccv : ConLeche.ConstantVal) : Prop :=
  ccv.name = toName cv.name ∧ ccv.levelParams = cv.levelParams.map toName ∧ StoredT cv.type ccv.type

theorem StoredT.okS {t : Expr} {c : ConLeche.Expr} (h : StoredT t c) (s : InLean.CState) :
    OkS s t = true := (okS_of_toExprC h.1 h.2.1 h.2.2).1

theorem StoredT.trS {t : Expr} {c : ConLeche.Expr} (h : StoredT t c) (s : InLean.CState) :
    TrS s t = c := (okS_of_toExprC h.1 h.2.1 h.2.2).2

/-- An inductive family's capabilities, as con-leche records them. -/
@[expose] def toCaps (c : InLean.IndCaps) : ConLeche.IndCaps :=
  { eta := c.eta, etaCtor := toName c.etaCtor, etaParams := c.etaParams, etaFields := c.etaFields,
    unitlike := c.unitlike, unitParams := c.unitParams, all := c.all.map toName,
    nparams := c.nparams, nIdx := c.nIdx, ctors := c.ctors.map toName }

/-- **The environment's views** (O4 with `EnvRelI`/`EnvDomI`/`EnvDefnI`, P3's):
InLean's view of an inductive family or a constructor is the translation of
con-leche's record at the translated name, and InLean has none exactly where
con-leche records none. -/
structure EnvViewI (fe : InLean.FEnv) (env : ConLeche.Env) : Prop where
  ind : ∀ n cv caps, fe.indView? n = some (cv, caps) →
    ∃ ccv, CVRel cv ccv ∧ env.find? (toName n) = some (.indInfo ccv (toCaps caps))
  indNone : ∀ n, fe.indView? n = none → ∀ ccv caps, env.find? (toName n) ≠ some (.indInfo ccv caps)
  ctor : ∀ n cv nP nF, fe.ctorView? n = some (cv, nP, nF) →
    ∃ ccv, CVRel cv ccv ∧ env.find? (toName n) = some (.ctorInfo ccv nP nF)
  ctorNone : ∀ n, fe.ctorView? n = none →
    ∀ ccv nP nF, env.find? (toName n) ≠ some (.ctorInfo ccv nP nF)

/-- A family's result sort through the translation. -/
theorem formerResSort_TrS (s : InLean.CState) (t : Expr) :
    ConLeche.formerResSort (TrS s t) = (InLean.formerResSort t).map trL := by
  unfold ConLeche.formerResSort InLean.formerResSort
  rw [← TrS_piResult, ← TrS_stripTop s (InLean.piResult t)]
  generalize hx : EO.stripTop (InLean.piResult t) = x
  cases x with
  | sort u => rfl
  | mdata _ y => exact (stripTop_ne_mdata hx).elim
  | fvar id =>
    simp only [TrS, trE]
    cases hf : FVarTable.trans (tableOf s) id with
    | none => rfl
    | some c => obtain ⟨d, ty, rfl⟩ := FVarTable.trans_fvarsOnly _ id c hf; rfl
  | _ => rfl

theorem formerNeverZero_CV {cv : Lean.ConstantVal} {ccv : ConLeche.ConstantVal} (h : CVRel cv ccv)
    (us : List Level) :
    ConLeche.formerNeverZero ccv (us.map trL) = InLean.formerNeverZero cv us := by
  have hty : ccv.type = TrS default cv.type := (h.2.2.trS default).symm
  have hz : ConLeche.formerZ ccv = trPW (InLean.formerZ cv) := by
    unfold ConLeche.formerZ InLean.formerZ
    rw [hty, formerResSort_TrS]
    cases InLean.formerResSort cv.type with
    | none => rfl
    | some u => exact (trPW_zeronessOf u).symm
  unfold ConLeche.formerNeverZero InLean.formerNeverZero
  rw [hz, h.2.1, ← trPW_substPW, trPW_isNever]

/-- The family a constructor's type concludes in, through the views. -/
theorem ctorFamily_CV {fe : InLean.FEnv} (hv : EnvViewI fe env) {cvj : Lean.ConstantVal}
    {ccvj : ConLeche.ConstantVal} (h : CVRel cvj ccvj) :
    match InLean.ctorFamily fe cvj with
    | some (cvT, caps) => ∃ ccvT, CVRel cvT ccvT ∧
        ConLeche.ctorFamily env.find? ccvj = some (ccvT, toCaps caps)
    | none => ConLeche.ctorFamily env.find? ccvj = none := by
  have hty : ccvj.type = TrS default cvj.type := (h.2.2.trS default).symm
  unfold InLean.ctorFamily ConLeche.ctorFamily
  rw [hty, ← TrS_piResult, ← TrS_getAppFnT, stripTop_getAppFnT]
  generalize hx : Expr.getAppFnT (InLean.piResult cvj.type) = x
  cases x with
  | mdata _ y => exact (getAppFnT_ne_mdata hx).elim
  | const T us =>
    simp only [TrS_const]
    cases hi : fe.indView? T with
    | none =>
      simp only
      split
      · rename_i cv caps hf; exact absurd hf (hv.indNone T hi cv caps)
      · rfl
    | some p =>
      obtain ⟨cvT, caps⟩ := p
      obtain ⟨ccvT, hrel, hf⟩ := hv.ind T cvT caps hi
      exact ⟨ccvT, hrel, by simp [hf]⟩
  | fvar id =>
    simp only [TrS, trE]
    cases hf : FVarTable.trans (tableOf default) id with
    | none => rfl
    | some c => obtain ⟨d, ty, rfl⟩ := FVarTable.trans_fvarsOnly _ id c hf; rfl
  | _ => rfl

end Views

/-! ## The family sort's walks -/

section FamilySort

variable {r : InLean.CoreFnsI}

/-- **The walk to a family's sort** (`formerSortLoopC_spec`'s twin): the
binders are opened at interned free variables, con-leche's `.fvar d dom`. -/
theorem formerSortLoopI_specI (ih : KnotSpecI mode eager env r) :
    ∀ {n d : Nat} {e : Expr} {s₀ : InLean.CState}, CSOKI mode eager env s₀ → OkS s₀ e = true →
      ConLeche.Expr.WScoped d (TrS s₀ e) → (TrS s₀ e).looseBVarsBounded 0 = true →
      ⦃fun s => s = s₀⦄ InLean.formerSortLoopI r.whnf d n e
      ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ v.all okLv = true ∧
        Runs (ConLeche.formerSortLoop (ConLeche.fueledFns mode eager env).whnf d n (TrS s₀ e))
          (v.map trL); ⊤⦄ := by
  intro n
  induction n with
  | zero =>
    intro d e s₀ hs he hw hc
    refine tripleI_iff_run.2 fun v s' hr => ?_
    rw [InLean.formerSortLoopI] at hr
    obtain ⟨w, s₁, hw1, hr⟩ := bind_run hr
    obtain ⟨hs₁, ht₁, hokw, hrun, -, -⟩ := tripleI_iff_run.1 (ih.whnf hs he hw hc) w s₁ hw1
    rw [ConLeche.formerSortLoop]
    by_cases hsrt : ∃ u, EO.stripTop w = .sort u
    · obtain ⟨u, hu⟩ := hsrt
      simp only [hu] at hr
      obtain ⟨rfl, rfl⟩ := pure_run hr
      have hT : TrS s₁ w = .sort (trL u) := by rw [← TrS_stripTop, hu]; rfl
      have hok : okLv u = true := by
        have := hokw; rw [← OkS_stripTop, hu] at this; exact this
      refine ⟨hs₁, ht₁, by simpa using hok, ?_⟩
      exact Runs.bind hrun (by rw [hT]; exact Runs.pure _)
    · have hu : ∀ u, EO.stripTop w ≠ .sort u := fun u h => hsrt ⟨u, h⟩
      have hr' : (pure none : InLean.CheckCM (Option Level)) s₁ = .ok (v, s') := by
        rw [← hr]
        generalize hx : EO.stripTop w = x at hu
        cases x with
        | sort u => exact absurd rfl (hu u)
        | _ => rfl
      obtain ⟨rfl, rfl⟩ := pure_run hr'
      refine ⟨hs₁, ht₁, rfl, Runs.bind hrun ?_⟩
      generalize hx : TrS s₁ w = x
      have hx' := TrS_ne_sort s₁ hu
      rw [hx] at hx'
      cases x with
      | sort u => exact absurd rfl (hx' u)
      | _ => exact Runs.pure _
  | succ n ihn =>
    intro d e s₀ hs he hw hc
    refine tripleI_iff_run.2 fun v s' hr => ?_
    rw [InLean.formerSortLoopI] at hr
    obtain ⟨w, s₁, hw1, hr⟩ := bind_run hr
    obtain ⟨hs₁, ht₁, hokw, hrun, hww, hcw⟩ := tripleI_iff_run.1 (ih.whnf hs he hw hc) w s₁ hw1
    rw [ConLeche.formerSortLoop]
    by_cases hpi : ∃ nm dom b bi, EO.stripTop w = .forallE nm dom b bi
    · obtain ⟨nm, dom, b, bi, hpi⟩ := hpi
      simp only [hpi] at hr
      have hT : TrS s₁ w = .forallE (TrS s₁ dom) (TrS s₁ b) := by
        rw [← TrS_stripTop, hpi]; rfl
      have hokpi : OkS s₁ dom = true ∧ OkS s₁ b = true := by
        have := hokw; rw [← OkS_stripTop, hpi, OkS_forallE, Bool.and_eq_true] at this; exact this
      obtain ⟨fv, s₂, hfv, hr⟩ := bind_run hr
      obtain ⟨hs₂, ht₂, hokfv, htrfv⟩ :=
        tripleI_iff_run.1 (mkFVarM_specI hs₁ d hokpi.1) fv s₂ hfv
      have hb₂ : OkS s₂ b = true := okS_of_tabLe ht₂ hokpi.2
      have hcfv : (TrS s₂ fv).looseBVarsBounded 0 = true := by rw [htrfv]; rfl
      obtain ⟨hokI, htrI⟩ := TrS_inst1 hb₂ hokfv hcfv
      have heq : TrS s₂ (EO.instantiate1 b fv) =
          (TrS s₁ b).instantiate1 (.fvar d (TrS s₁ dom)) 0 := by
        rw [htrI, htrfv, TrS_of_tabLe ht₂ hokpi.2]
      rw [hT] at hww hcw
      simp only [ConLeche.Expr.WScoped] at hww
      have hwI : ConLeche.Expr.WScoped (d + 1) (TrS s₂ (EO.instantiate1 b fv)) := by
        rw [heq]; exact wscoped_open 0 hww.1 hww.2
      have hcI : (TrS s₂ (EO.instantiate1 b fv)).looseBVarsBounded 0 = true := by
        rw [heq]
        rw [ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true] at hcw
        exact lbb_instantiate1 rfl hcw.2
      obtain ⟨hs₃, ht₃, hok₃, hrun₃⟩ :=
        tripleI_iff_run.1 (ihn hs₂ hokI hwI hcI) v s' (by rw [← inst1I_eq]; exact hr)
      refine ⟨hs₃, ht₁.trans (ht₂.trans ht₃), hok₃, Runs.bind hrun ?_⟩
      rw [hT]; rw [heq] at hrun₃; exact hrun₃
    · have hu : ∀ nm dom b bi, EO.stripTop w ≠ .forallE nm dom b bi :=
        fun nm dom b bi h => hpi ⟨nm, dom, b, bi, h⟩
      have hr' : (pure none : InLean.CheckCM (Option Level)) s₁ = .ok (v, s') := by
        rw [← hr]
        generalize hx : EO.stripTop w = x at hu
        cases x with
        | forallE nm dom b bi => exact absurd rfl (hu nm dom b bi)
        | _ => rfl
      obtain ⟨rfl, rfl⟩ := pure_run hr'
      refine ⟨hs₁, ht₁, rfl, Runs.bind hrun ?_⟩
      generalize hx : TrS s₁ w = x
      have hx' := TrS_ne_forallE s₁ hu
      rw [hx] at hx'
      cases x with
      | forallE t b => exact absurd rfl (hx' t b)
      | _ => exact Runs.pure _

/-- **A family's sort at a use** (`formerNeverZeroC_spec`'s twin): the former
is a stored record, closed. -/
theorem formerNeverZeroI_specI (ih : KnotSpecI mode eager env r) {cvT : Lean.ConstantVal}
    {ccvT : ConLeche.ConstantVal} (hcv : CVRel cvT ccvT) (hcl : ccvT.type.hasFvar = false)
    (hlbb : ccvT.type.looseBVarsBounded 0 = true) (caps : InLean.IndCaps) {us : List Level}
    (hus : us.all okLv = true) {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) :
    ⦃fun s => s = s₀⦄ InLean.formerNeverZeroI r.whnf cvT caps us
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.formerNeverZeroAt (ConLeche.fueledFns mode eager env).whnf ccvT (toCaps caps)
        (us.map trL)) v; ⊤⦄ := by
  refine tripleI_iff_run.2 fun v s' hr => ?_
  have hty : TrS s₀ cvT.type = ccvT.type := hcv.2.2.trS s₀
  have hrs : ConLeche.formerResSort ccvT.type = (InLean.formerResSort cvT.type).map trL := by
    rw [← hty, formerResSort_TrS]
  unfold ConLeche.formerNeverZeroAt
  unfold InLean.formerNeverZeroI at hr
  rw [hrs]
  cases hf : InLean.formerResSort cvT.type with
  | some u =>
    simp only [hf] at hr
    obtain ⟨rfl, rfl⟩ := pure_run hr
    refine ⟨hs, TabLe.refl _, ?_⟩
    simp only [Option.map_some]
    rw [formerNeverZero_CV hcv]; exact Runs.pure _
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
    obtain ⟨o, s₂, ho, hr⟩ := bind_run hr
    obtain ⟨hs₂, ht₂, hoko, hruno⟩ := tripleI_iff_run.1
      (formerSortLoopI_specI ih (n := caps.nparams + caps.nIdx) hs₁ hok₁ hw hc) o s₂ ho
    rw [htr₁] at hruno
    simp only [Option.map_none]
    refine ⟨?_, ?_, Runs.bind hruno ?_⟩
    · cases o <;> (obtain ⟨rfl, rfl⟩ := pure_run hr; exact hs₂)
    · cases o <;> (obtain ⟨rfl, rfl⟩ := pure_run hr; exact ht₁.trans ht₂)
    · cases o with
      | none => obtain ⟨rfl, rfl⟩ := pure_run hr; exact Runs.pure _
      | some u =>
        obtain ⟨rfl, rfl⟩ := pure_run hr
        simp only [Option.map_some]
        rw [← trPW_zeronessOf, trPW_isNever]; exact Runs.pure _

/-- A family a constructor concludes in is a stored record: closed. -/
theorem ctorFamily_closed (henv : ConLeche.EnvWF env) {ccvj ccvT : ConLeche.ConstantVal}
    {caps : ConLeche.IndCaps} (h : ConLeche.ctorFamily env.find? ccvj = some (ccvT, caps)) :
    ccvT.type.hasFvar = false ∧ ccvT.type.looseBVarsBounded 0 = true := by
  unfold ConLeche.ctorFamily at h
  split at h
  · split at h
    · rename_i hf
      cases Option.some.inj h
      have hw := henv.consts _ (ConLeche.Env.find?_mem hf)
      exact ⟨hw.1, hw.2.2.2.1⟩
    · exact nomatch h
  · exact nomatch h

/-- **The ι case split** (`iotaCase3C_spec`'s twin). -/
theorem iotaCase3I_specI (ih : KnotSpecI mode eager env r) (henv : ConLeche.EnvWF env)
    {fe : InLean.FEnv} (hv : EnvViewI fe env) {isK : Bool} {cvj : Lean.ConstantVal}
    {ccvj : ConLeche.ConstantVal} (hcvj : CVRel cvj ccvj) {us : List Level}
    (hus : us.all okLv = true) {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) :
    ⦃fun s => s = s₀⦄ InLean.iotaCase3I r.whnf fe isK cvj us
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.iotaCase3At (ConLeche.fueledFns mode eager env).whnf env.find? isK ccvj
        (us.map trL)) v; ⊤⦄ := by
  refine tripleI_iff_run.2 fun v s' hr => ?_
  unfold InLean.iotaCase3I at hr
  unfold ConLeche.iotaCase3At
  cases isK with
  | true =>
    simp only [↓reduceIte] at hr
    obtain ⟨rfl, rfl⟩ := pure_run hr
    exact ⟨hs, TabLe.refl _, Runs.pure _⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hr ⊢
    have hfam := ctorFamily_CV hv hcvj
    revert hr hfam
    cases InLean.ctorFamily fe cvj with
    | none =>
      intro hr hfam
      obtain ⟨rfl, rfl⟩ := pure_run hr
      rw [hfam]; exact ⟨hs, TabLe.refl _, Runs.pure _⟩
    | some p =>
      obtain ⟨cvT, caps⟩ := p
      intro hr hfam
      obtain ⟨ccvT, hrel, hf⟩ := hfam
      rw [hf]
      simp only
      have hlen : (ccvT.levelParams.length == (us.map trL).length) =
          (cvT.levelParams.length == us.length) := by
        rw [hrel.2.1]; simp
      rw [hlen]
      by_cases hl : (cvT.levelParams.length == us.length) = true
      · simp only [hl, ↓reduceIte] at hr ⊢
        obtain ⟨nz, s₁, hnz, hr⟩ := bind_run hr
        obtain ⟨hcl, hlbb⟩ := ctorFamily_closed henv hf
        obtain ⟨hs₁, ht₁, hrun⟩ := tripleI_iff_run.1
          (formerNeverZeroI_specI ih hrel hcl hlbb caps hus hs) nz s₁ hnz
        obtain ⟨rfl, rfl⟩ := pure_run hr
        exact ⟨hs₁, ht₁, Runs.bind hrun (Runs.pure _)⟩
      · simp only [hl, Bool.false_eq_true, ↓reduceIte] at hr ⊢
        obtain ⟨rfl, rfl⟩ := pure_run hr
        exact ⟨hs, TabLe.refl _, Runs.pure _⟩

end FamilySort

/-! ## The canonical-index comparison -/

section IndexOk

variable {r : InLean.CoreFnsI}

/-- Bulk instantiation by an array of closed values read at a state
(`instListM_specI`'s computation). -/
theorem TrS_instI {s : InLean.CState} {e : Expr} {vs : List Expr} (he : OkS s e = true)
    (hv : OkSL s vs = true) (hcl : AllClosed (TrSL s vs) = true) :
    OkS s (e.instI vs.toArray) = true ∧
      TrS s (e.instI vs.toArray) = (TrS s e).instantiateList (TrSL s vs) 0 := by
  have hmem := closed_entries hv hcl
  have hsr : SubstReads (FVarTable.trans (tableOf s)) vs.toArray (TrSL s vs) := by
    have := substReads_of_ok (s := s) (vs := vs.toArray) (by simpa using hv) (by simpa using hcl)
    simpa using this
  have h := toExpr_instantiate (FVarTable.trans_fvarsOnly _) hsr (RangeOk_of_OkS he)
    (TransS_of_ok he)
  have hr' : Expr.RangeOk (EO.instantiate e vs.toArray) :=
    RangeOk_instantiate (RangeOk_of_OkS he)
      (fun j hj => (hmem _ (by simp)).1) (fun j hj => (hmem _ (by simp)).2)
  exact ok_of_TransS hr' h

/-- The pure residual of a closed telescope along closed arguments is closed. -/
theorem lbb_piResidual : ∀ {args : List ConLeche.Expr} {e r : ConLeche.Expr},
    e.looseBVarsBounded 0 = true → AllClosed args = true →
    ConLeche.piResidual e args = some r → r.looseBVarsBounded 0 = true
  | [], e, r, he, _, h => by
    rw [ConLeche.piResidual] at h; cases h; exact he
  | a :: as, e, r, he, ha, h => by
    simp only [AllClosed_cons, Bool.and_eq_true] at ha
    cases e with
    | forallE ty b =>
      rw [ConLeche.piResidual] at h
      rw [ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true] at he
      exact lbb_piResidual (lbb_instantiate1 ha.1 he.2) ha.2 h
    | _ => simp [ConLeche.piResidual] at h

/-- InLean's accumulating residual is the pure one at the translation. -/
theorem piResidual_go_TrS (s : InLean.CState) :
    ∀ (as acc : List Expr) (e : Expr), OkS s e = true → OkSL s acc = true →
      AllClosed (TrSL s acc) = true → OkSL s as = true → AllClosed (TrSL s as) = true →
      OkO s (InLean.piResidual.go acc e as) = true ∧
      TrO s (InLean.piResidual.go acc e as) =
        ConLeche.piResidual ((TrS s e).instantiateList (TrSL s acc)) (TrSL s as)
  | [], acc, e, he, hacc, hcl, _, _ => by
    rw [InLean.piResidual.go.eq_def]
    obtain ⟨h1, h2⟩ := TrS_instI he hacc hcl
    exact ⟨h1, by rw [TrO_some, h2, TrSL_nil, ConLeche.piResidual]⟩
  | a :: as, acc, e, he, hacc, hcl, has, hcas => by
    simp only [OkSL_cons, Bool.and_eq_true] at has
    simp only [TrSL_cons, AllClosed_cons, Bool.and_eq_true] at hcas
    rw [InLean.piResidual.go.eq_def]
    dsimp only
    have hT := TrS_stripTop s e
    have hO := OkS_stripTop s e
    generalize hx : EO.stripTop e = x at hT hO ⊢
    cases x with
    | forallE nm dom b bi =>
      rw [← hO, OkS_forallE, Bool.and_eq_true] at he
      have ih := piResidual_go_TrS s as (a :: acc) b he.2
        (by rw [OkSL_cons, has.1, hacc]; rfl)
        (by rw [TrSL_cons, AllClosed_cons, hcas.1, hcl]; rfl) has.2 hcas.2
      refine ⟨ih.1, ?_⟩
      rw [ih.2, ← hT, TrS_forallE, TrSL_cons, TrSL_cons, ConLeche.Expr.instantiateList_cons]
      simp only [ConLeche.Expr.instantiateList, ConLeche.piResidual]
    | bvar k =>
      match hm : acc with
      | [] =>
        refine ⟨rfl, ?_⟩
        rw [TrO_none, ← hT, TrS_bvar, TrSL_nil, TrSL_cons]
        simp [ConLeche.Expr.instantiateList, ConLeche.piResidual]
      | c :: cs =>
        obtain ⟨h1, h2⟩ := TrS_instI he hacc hcl
        have ih := piResidual_go_TrS s (a :: as) [] (e.instI (c :: cs).toArray) h1 rfl rfl
          (by rw [OkSL_cons, has.1, has.2]; rfl)
          (by rw [TrSL_cons, AllClosed_cons, hcas.1, hcas.2]; rfl)
        refine ⟨ih.1, ?_⟩
        rw [ih.2, h2, TrSL_nil, ConLeche.Expr.instantiateList_nil, TrSL_cons]
    | fvar id =>
      refine ⟨rfl, ?_⟩
      rw [← hO] at he
      rw [TrO_none, ← hT, TrS_fvar he, TrSL_cons]
      simp [ConLeche.Expr.instantiateList, ConLeche.piResidual]
    | mvar _ => rw [← hO, OkS_mvar] at he; cases he
    | mdata _ y => exact (stripTop_ne_mdata hx).elim
    | _ =>
      refine ⟨rfl, ?_⟩
      rw [TrO_none, ← hT, TrSL_cons]
      simp [TrS, trE, ConLeche.Expr.instantiateList, ConLeche.piResidual]
termination_by as acc => (as.length, acc.length)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.right; simp +arith +decide)
    | (apply Prod.Lex.left; simp +arith +decide)

/-- **The canonical-index comparison** (`iotaIndexOkC_spec`'s twin). -/
theorem iotaIndexOkI_specI (ih : KnotSpecI mode eager env r) {d : Nat} {mI rP cnP : Nat}
    {ty : Expr} {margs idx : List Expr} {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀)
    (hty : OkS s₀ ty = true) (hwty : ConLeche.Expr.WScoped d (TrS s₀ ty))
    (hcty : (TrS s₀ ty).looseBVarsBounded 0 = true)
    (hm : OkSL s₀ margs = true) (hwm : AllWS d (TrSL s₀ margs))
    (hcm : AllClosed (TrSL s₀ margs) = true)
    (hi : OkSL s₀ idx = true) (hwi : AllWS d (TrSL s₀ idx))
    (hci : AllClosed (TrSL s₀ idx) = true) :
    ⦃fun s => s = s₀⦄ InLean.iotaIndexOkI r d mI rP cnP ty margs idx
    ⦃fun b s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.iotaIndexOk (ConLeche.fueledFns mode eager env) env d mI rP cnP (TrS s₀ ty)
        (TrSL s₀ margs) (TrSL s₀ idx)) b; ⊤⦄ := by
  refine tripleI_iff_run.2 fun b s' hr => ?_
  unfold InLean.iotaIndexOkI at hr
  unfold ConLeche.iotaIndexOk
  by_cases hmr : mI = rP
  · simp only [hmr, ↓reduceIte] at hr ⊢
    obtain ⟨rfl, rfl⟩ := pure_run hr
    exact ⟨hs, TabLe.refl _, Runs.pure _⟩
  · simp only [hmr, ↓reduceIte] at hr ⊢
    obtain ⟨hok, htr⟩ := piResidual_go_TrS s₀ margs [] ty hty rfl rfl hm hcm
    rw [TrSL_nil, ConLeche.Expr.instantiateList_nil] at htr
    unfold InLean.piResidual at hr
    revert hr hok htr
    cases InLean.piResidual.go [] ty margs with
    | none =>
      intro hr _ htr
      rw [TrO_none] at htr; rw [← htr]
      obtain ⟨rfl, rfl⟩ := pure_run hr
      exact ⟨hs, TabLe.refl _, Runs.pure _⟩
    | some res =>
      intro hr hok htr
      rw [TrO_some] at htr; rw [← htr]
      rw [OkO_some] at hok
      simp only
      have hpr : ConLeche.piResidual (TrS s₀ ty) (TrSL s₀ margs) = some (TrS s₀ res) := htr.symm
      have hwres : ConLeche.Expr.WScoped d (TrS s₀ res) :=
        ConLeche.piResidual_WScoped hpr hwty hwm
      have hcres : (TrS s₀ res).looseBVarsBounded 0 = true := lbb_piResidual hcty hcm hpr
      have hargs : OkSL s₀ ((appArgs res).drop cnP) = true := by
        have := OkSL_appArgs s₀ hok
        simp only [OkSL, List.all_eq_true] at this ⊢
        exact fun x hx => this x (List.mem_of_mem_drop hx)
      have heq : TrSL s₀ ((appArgs res).drop cnP) = (TrS s₀ res).getAppArgs.drop cnP := by
        rw [TrSL, List.map_drop, ← TrSL, TrSL_appArgs]
      have hwa : AllWS d (TrSL s₀ ((appArgs res).drop cnP)) := by
        rw [heq]; intro x hx; exact allWS_getAppArgs hwres x (List.mem_of_mem_drop hx)
      have hca : AllClosed (TrSL s₀ ((appArgs res).drop cnP)) = true := by
        rw [heq]; have := allClosed_getAppArgs hcres
        simp only [AllClosed, List.all_eq_true] at this ⊢
        exact fun x hx => this x (List.mem_of_mem_drop hx)
      obtain ⟨hs₁, ht₁, hrun⟩ := tripleI_iff_run.1
        (defEqListI_spec ih hs hargs hi hwa hwi hca hci) b s' hr
      rw [heq] at hrun
      exact ⟨hs₁, ht₁, hrun⟩

end IndexOk

end InLeanProof

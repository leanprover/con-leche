module

public import InLeanProof.PassUniform
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Verify.Cached.IndWalksC

/-!
# O7-stages: a container instantiation's type against master's (task #451, lane O7-stages)

The positivity walk's environment-reading steps below the frames, each
master's on the reading:

* `familyTelescopeI_run`: a stored family's telescope (its stored type, or
  its reduct, `ReducedFormerSimI`), closed.
* `checkSpineAtI_run`: arguments against a telescope (`inferType`, `isDefEq`
  through `OpsSimI`; InLean also reads through `mdata`, which the reading
  drops).
* `familyKeyCheckI_run`: a family at a key, typed.
* `nestInstTypeI_run`: a container instantiation's type (`nestInstType`): the
  container's telescope at the key's levels, instantiated at its parameters,
  its index telescope free of the block, at the block's sort.

The key translates as `trKey`: its name, levels and parameters read at a
state.  The proofs are functional (`bind_run`, `pure_run`), as O7's.
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached

/-- A stored constant's record is the closed translation of InLean's. -/
theorem CVRel.eq_trCV {cv : Lean.ConstantVal} {ccv : ConLeche.ConstantVal} (h : CVRel cv ccv) :
    ccv = trCV cv := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨-, h4⟩ := trC_of_toExprC h3.2.2 h3.2.1
  cases ccv
  simp only at h1 h2
  simp [trCV, h1, h2, h4]

/-- A container lookup through the relation: master's record is the closed
translation, closed and in range. -/
theorem indView_trCV {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L) {n : Lean.Name}
    {cv : Lean.ConstantVal} {caps : InLean.IndCaps} (h : fe.indView? n = some (cv, caps)) :
    L.find? (toName n) = some (.indInfo (trCV cv) (toCaps caps)) ∧ okC cv.type = true ∧
      (trC cv.type).looseBVarsBounded 0 = true := by
  obtain ⟨ccv, hcv, hL⟩ := indView_rel hJ.pres h
  have he := hcv.eq_trCV
  subst he
  have hwf := hJ.wf.consts _ (ConLeche.Env.find?_mem hL)
  exact ⟨hL, (trC_of_toExprC hcv.2.2.2.2 hcv.2.2.2.1).1, hwf.2.2.2.1⟩

theorem indView_none_tr {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L) {n : Lean.Name}
    (h : fe.indView? n = none) : ∀ ccv caps, L.find? (toName n) ≠ some (.indInfo ccv caps) :=
  indView_none hJ.pres h

/-! ## A family's telescope -/

/-- **A stored family's telescope** (`familyTelescope`): its stored type, or
its reduct, closed, master's at the translated record. -/
theorem familyTelescopeI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    (hRF : ReducedFormerSimI) {cv : Lean.ConstantVal} {caps : InLean.IndCaps}
    (hok : okC cv.type = true) (hcl : (trC cv.type).looseBVarsBounded 0 = true)
    {s₀ s' : InLean.CState} {ty : Lean.Expr} (hs : CSOKI .verified false L s₀)
    (h : InLean.familyTelescope .verified fe cv caps s₀ = .ok (ty, s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ okC ty = true ∧
      (trC ty).looseBVarsBounded 0 = true ∧
      Runs (ConLeche.familyTelescope (ConLeche.fueledOpsM .verified) L (trCV cv) (toCaps caps))
        (trC ty) := by
  unfold InLean.familyTelescope at h
  unfold ConLeche.familyTelescope
  rw [formerDefHeaded_tr]
  by_cases hd : InLean.formerDefHeaded cv = true
  · simp only [hd, ↓reduceIte] at h ⊢
    obtain ⟨cvR, s₁, h1, h⟩ := bind_run h
    obtain ⟨rfl, rfl⟩ := pure_run h
    obtain ⟨hs₁, ht₁, hokR, hclR, hR⟩ := hRF fe L cv cvR _ s₀ s₁ hJ hs hok hcl h1
    exact ⟨hs₁, ht₁, hokR, hclR, Runs.bind hR (Runs.pure _)⟩
  · simp only [hd, Bool.false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, hok, hcl, Runs.pure _⟩

/-! ## Arguments against a telescope -/

/-- **Arguments against a telescope** (`checkSpineAt`): InLean's check
passing means master's passes on the readings. -/
theorem checkSpineAtI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hO : OpsSimI fe L) {d : Nat} :
    ∀ (ds : List Lean.Expr) (T : Lean.Expr) {s₀ s' : InLean.CState} {v : Unit},
      CSOKI .verified false L s₀ → OkS s₀ T = true → OkSL s₀ ds = true →
      ConLeche.Expr.WScoped d (TrS s₀ T) → (TrS s₀ T).looseBVarsBounded 0 = true →
      (∀ a ∈ ds, ConLeche.Expr.WScoped d (TrS s₀ a) ∧ (TrS s₀ a).looseBVarsBounded 0 = true) →
      InLean.checkSpineAt .verified fe d T ds s₀ = .ok (v, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
        Runs (ConLeche.checkSpineAt (ConLeche.fueledOpsM .verified) L d (TrS s₀ T) (TrSL s₀ ds)) ()
  | [], T, s₀, s', v, hs, _, _, _, _, _, h => by
    unfold InLean.checkSpineAt at h
    obtain ⟨-, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, by unfold ConLeche.checkSpineAt; exact Runs.pure _⟩
  | a :: as, T, s₀, s', v, hs, hokT, hokds, hwT, hcT, hds, h => by
    unfold InLean.checkSpineAt at h
    simp only [OkSL_cons, Bool.and_eq_true] at hokds
    obtain ⟨hwa, hca⟩ := hds a List.mem_cons_self
    have hT : TrS s₀ T = TrS s₀ (EO.stripTop T) := (TrS_stripTop s₀ T).symm
    have hOk : OkS s₀ (EO.stripTop T) = true := by rw [OkS_stripTop]; exact hokT
    have hnm : ∀ m b, EO.stripTop T ≠ .mdata m b := fun m b he => stripTop_ne_mdata he
    rw [hT] at hwT hcT ⊢
    generalize EO.stripTop T = x at h hOk hnm hwT hcT
    cases x with
    | forallE nm ty body bi =>
      simp only at h
      simp only [OkS_forallE, Bool.and_eq_true] at hOk
      rw [TrS_forallE] at hwT hcT ⊢
      rw [lbb_forallE, Bool.and_eq_true] at hcT
      simp only [ConLeche.Expr.WScoped] at hwT
      obtain ⟨ta, s₁, h1, h⟩ := bind_run h
      obtain ⟨hs₁, ht₁, hokt, hRt, hwt, hct⟩ :=
        tripleI_iff_run.1 (hO.infer hs hokds.1 hwa hca) ta s₁ h1
      obtain ⟨b, s₂, h2, h⟩ := bind_run h
      have hoky₁ := okS_of_tabLe ht₁ hOk.1
      have hty₁ := TrS_of_tabLe ht₁ hOk.1
      obtain ⟨hs₂, ht₂, hRd⟩ := tripleI_iff_run.1 (hO.defeq hs₁ hokt hoky₁ hwt
        (by rw [hty₁]; exact hwT.1) hct (by rw [hty₁]; exact hcT.1)) b s₂ h2
      rw [hty₁] at hRd
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨_, _, h3, -⟩ := bind_run h
        exact (throw_run h3).elim
      | true =>
        simp only [↓reduceIte] at h
        have ht12 := ht₁.trans ht₂
        have hokb := okS_of_tabLe ht12 hOk.2
        have hoka := okS_of_tabLe ht12 hokds.1
        have hcaa : (TrS s₂ a).looseBVarsBounded 0 = true := by
          rw [TrS_of_tabLe ht12 hokds.1]; exact hca
        have hokI : OkS s₂ (body.inst1I a) = true := OkS_inst1 hokb hoka hcaa
        have hTI : TrS s₂ (body.inst1I a) = (TrS s₀ body).instantiate1 (TrS s₀ a) 0 := by
          rw [inst1I_eq, TrS_inst1_eq hokb hoka hcaa, TrS_of_tabLe ht12 hOk.2,
            TrS_of_tabLe ht12 hokds.1]
        have hrest : ∀ x ∈ as, ConLeche.Expr.WScoped d (TrS s₂ x) ∧
            (TrS s₂ x).looseBVarsBounded 0 = true := by
          intro x hx
          rw [TrS_of_tabLe ht12 (by simp only [OkSL, List.all_eq_true] at hokds; exact hokds.2 x hx)]
          exact hds x (List.mem_cons_of_mem _ hx)
        obtain ⟨hs', ht', hR⟩ := checkSpineAtI_run hO as (body.inst1I a) hs₂ hokI
          (okSL_of_tabLe ht12 hokds.2)
          (by rw [hTI]; exact ConLeche.Expr.WScoped.instantiate1_gen hwa 0 hwT.2)
          (by rw [hTI]; exact lbb_instantiate1 hca hcT.2) hrest h
        refine ⟨hs', ht12.trans ht', ?_⟩
        rw [TrSL_cons]
        unfold ConLeche.checkSpineAt
        refine Runs.bind hRt (Runs.bind hRd ?_)
        simp only [↓reduceIte]
        rw [hTI, TrSL_of_tabLe ht12 hokds.2] at hR
        first | exact hR | exact Runs.bind (Runs.pure _) hR
    | mdata m b => exact (hnm m b rfl).elim
    | fvar id =>
      simp only at h
      exact (throw_run h).elim
    | _ => simp only at h; exact (throw_run h).elim

/-! ## A family at a key -/

/-- **A family at a key, typed** (`familyKeyCheck`): InLean's check passing
means master's passes on the readings, at master's lookup. -/
theorem familyKeyCheckI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    (hRF : ReducedFormerSimI) {d : Nat} {c : Lean.Name} {us : List Lean.Level}
    {ds : List Lean.Expr} {s₀ s' : InLean.CState} {v : Unit} (hs : CSOKI .verified false L s₀)
    (hus : us.all okLv = true) (hokds : OkSL s₀ ds = true)
    (hds : ∀ a ∈ ds, ConLeche.Expr.WScoped d (TrS s₀ a) ∧ (TrS s₀ a).looseBVarsBounded 0 = true)
    (h : InLean.familyKeyCheck .verified fe d c us ds s₀ = .ok (v, s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.familyKeyCheck (ConLeche.fueledOpsM .verified) L L.find? d (toName c)
        (us.map trL) (TrSL s₀ ds)) () := by
  unfold InLean.familyKeyCheck at h
  cases hv : fe.indView? c with
  | none =>
    rw [hv] at h
    exact (throw_run h).elim
  | some p =>
    obtain ⟨cv, caps⟩ := p
    rw [hv] at h
    simp only at h
    obtain ⟨hL, hok, hcl⟩ := indView_trCV hJ hv
    unfold ConLeche.familyKeyCheck
    rw [hL]
    simp only
    by_cases hlen : us.length = cv.levelParams.length
    · simp only [hlen, ↓reduceIte] at h
      obtain ⟨ty, s₂, h2, h⟩ := bind_run h
      obtain ⟨hs₂, ht₂, hokty, hclty, hRty⟩ := familyTelescopeI_run hJ hRF hok hcl hs h2
      obtain ⟨r, s₃, h3, h⟩ := bind_run h
      obtain ⟨hs₃, ht₃, hokr, htrr⟩ := tripleI_iff_run.1
        (instLevelParamsM_specI hs₂ (OkS_of_okC s₂ hokty) (fvarS_of_okC hokty) hus) r s₃ h3
      rw [TrS_of_okC _ hokty] at htrr
      have ht23 := ht₂.trans ht₃
      have hds₃ : ∀ a ∈ ds, ConLeche.Expr.WScoped d (TrS s₃ a) ∧
          (TrS s₃ a).looseBVarsBounded 0 = true := by
        intro a ha
        rw [TrS_of_tabLe ht23 (by simp only [OkSL, List.all_eq_true] at hokds; exact hokds a ha)]
        exact hds a ha
      have hclr : (trC ty).hasFvar = false := trC_hasFvar ty
      have hwr : ConLeche.Expr.WScoped d (TrS s₃ r) := by
        rw [htrr]
        refine ConLeche.Expr.WScoped.of_not_hasFvar ?_
        rw [ConLeche.Expr.hasFvar_instantiateLevelParams]
        exact hclr
      have hcr : (TrS s₃ r).looseBVarsBounded 0 = true := by
        rw [htrr, ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]
        exact hclty
      obtain ⟨hs', ht', hR⟩ := checkSpineAtI_run (d := d) hJ.ops ds r hs₃ hokr
        (okSL_of_tabLe ht23 hokds) hwr hcr hds₃ h
      refine ⟨hs', ht23.trans ht', ?_⟩
      simp only [List.length_map, trCV, hlen, ↓reduceIte]
      refine Runs.bind hRty ?_
      rw [htrr, TrSL_of_tabLe ht23 hokds] at hR
      exact hR
    · simp only [hlen, ↓reduceIte] at h
      obtain ⟨_, _, h1, -⟩ := bind_run h
      exact (throw_run h1).elim

/-! ## A container instantiation's type -/

/-- InLean's `piBinders`, read: master's on the reading; its end is no
`mdata`. -/
theorem piBinders_TrS {s : InLean.CState} : ∀ (e : Lean.Expr), OkS s e = true →
    ConLeche.Expr.piBinders (TrS s e) =
        ((InLean.piBinders e).1.map (TrS s), TrS s (InLean.piBinders e).2) ∧
      OkSL s (InLean.piBinders e).1 = true ∧ OkS s (InLean.piBinders e).2 = true ∧
      ∀ m b, (InLean.piBinders e).2 ≠ .mdata m b
  | .forallE _ d b _, h => by
    simp only [OkS_forallE, Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3, h4⟩ := piBinders_TrS b h.2
    simp only [InLean.piBinders, TrS_forallE, ConLeche.Expr.piBinders, h1, List.map_cons,
      OkSL_cons, h.1, h2, Bool.and_self]
    refine ⟨?_, ?_, h3, h4⟩ <;> first | trivial | rfl | simp
  | .mdata _ e, h => by
    rw [OkS_mdata] at h
    simp only [InLean.piBinders, TrS_mdata]
    exact piBinders_TrS e h
  | .fvar id, h => by
    rw [TrS_fvar h]
    simp only [InLean.piBinders, ConLeche.Expr.piBinders, List.map_nil]
    exact ⟨by rw [TrS_fvar h], rfl, h, fun _ _ he => nomatch he⟩
  | .mvar _, h => by simp [OkS, okE] at h
  | .bvar _, h | .sort _, h | .const _ _, h | .app _ _, h | .lam _ _ _ _, h
  | .letE _ _ _ _ _, h | .lit _, h | .proj _ _ _, h => by
    simp only [InLean.piBinders, List.map_nil]
    refine ⟨?_, rfl, h, fun _ _ he => nomatch he⟩
    simp [TrS_bvar, TrS_sort, TrS_const, TrS_app, TrS_lam, TrS_letE, TrS_lit, TrS_proj,
      ConLeche.Expr.piBinders]

/-- A sort end, read. -/
theorem sortOf_TrS {s : InLean.CState} {x : Lean.Expr} (h : OkS s x = true)
    (hm : ∀ m b, x ≠ .mdata m b) :
    (match TrS s x with
      | .sort u => some u
      | _ => none) = (match x with
      | .sort u => some u
      | _ => none).map trL := by
  cases x with
  | sort u => rfl
  | fvar id => rw [TrS_fvar h]; rfl
  | mvar _ => simp [OkS, okE] at h
  | mdata m b => exact (hm m b rfl).elim
  | _ => rfl

/-- A container key, read at a state. -/
@[expose] def trKey (s : InLean.CState) (k : InLean.NestKey) : ConLeche.NestKey :=
  ⟨toName k.cname, k.lvls.map trL, TrSL s k.ds⟩

/-- A bind on the pure side, under five facts. -/
theorem runs5_bind {A B C D E : Prop} {α β : Type} {x : ConLeche.FueledM α}
    {f : α → ConLeche.FueledM β} {a : α} {b : β} (hx : Runs x a)
    (h : A ∧ B ∧ C ∧ D ∧ E ∧ Runs (f a) b) : A ∧ B ∧ C ∧ D ∧ E ∧ Runs (x >>= f) b :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, Runs.bind hx h.2.2.2.2.2⟩

/-- **A container instantiation's type** (`nestInstType`): InLean's answer
reads, at the final state, as master's at the translated key and the
relation's lookup; closed where the key's parameters are. -/
theorem nestInstTypeI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    (hRF : ReducedFormerSimI) {ctx : InLean.NestCtx} {cctx : ConLeche.NestCtx}
    (hR : CanonRel ctx cctx) (hfe : ctx.fe = fe) (hfind : cctx.find? = L.find?)
    (hsort : cctx.sort = trL ctx.sort) (hsok : okL ctx.sort = true) {hi : Nat}
    {key : InLean.NestKey} {s₀ s' : InLean.CState} {k : Nat} {ty : Lean.Expr}
    (hs : CSOKI .verified false L s₀) (hlv : key.lvls.all okLv = true)
    (hokds : OkSL s₀ key.ds = true) (hcds : ∀ a ∈ key.ds, (TrS s₀ a).looseBVarsBounded 0 = true)
    (h : InLean.nestInstType .verified ctx fe hi key s₀ = .ok ((k, ty), s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ OkS s' ty = true ∧
      (TrS s' ty).looseBVarsBounded 0 = true ∧
      (∀ d, (∀ a ∈ key.ds, ConLeche.Expr.WScoped d (TrS s₀ a)) →
        ConLeche.Expr.WScoped d (TrS s' ty)) ∧
      Runs (ConLeche.nestInstType cctx (ConLeche.fueledOpsM .verified) L hi (trKey s₀ key))
        (k, TrS s' ty) := by
  unfold InLean.nestInstType at h
  subst hfe
  obtain ⟨p, s₁, h1, h⟩ := bind_run h
  cases hv : ctx.fe.indView? key.cname with
  | none => rw [hv] at h1; exact (throw_run h1).elim
  | some p' =>
  rw [hv] at h1
  obtain ⟨rfl, rfl⟩ := pure_run h1
  obtain ⟨cv, caps⟩ := p'
  obtain ⟨hL, hok, hcl⟩ := indView_trCV hJ hv
  simp only at h
  unfold ConLeche.nestInstType
  simp only [trKey, hfind, hL, ConLeche.unwrapOr]
  refine runs5_bind (Runs.pure _) ?_
  by_cases hlen : key.lvls.length = cv.levelParams.length
  · simp only [hlen, ↓reduceIte] at h
    simp only [List.length_map, trCV, hlen, ↓reduceIte]
    obtain ⟨tyC, s₂, h2, h⟩ := bind_run h
    obtain ⟨hs₂, ht₂, hokC, hclC, hRC⟩ := familyTelescopeI_run hJ hRF hok hcl hs h2
    refine runs5_bind hRC ?_
    have hsp : (ConLeche.Expr.stripPis (TrSL s₀ key.ds).length (trC tyC)).isSome =
        (InLean.stripPis key.ds.length tyC).isSome := by
      rw [stripPis_tr]; simp [TrSL]
    rw [hsp]
    by_cases hst : (InLean.stripPis key.ds.length tyC).isSome = true
    · simp only [hst, ↓reduceIte] at h ⊢
      obtain ⟨r, s₃, h3, h⟩ := bind_run h
      obtain ⟨hs₃, ht₃, hokr, htrr⟩ := tripleI_iff_run.1
        (instLevelParamsM_specI hs₂ (OkS_of_okC s₂ hokC) (fvarS_of_okC hokC) hlv) r s₃ h3
      rw [TrS_of_okC _ hokC] at htrr
      have ht13 := ht₂.trans ht₃
      have hokds₃ := okSL_of_tabLe ht13 hokds
      have hcds₃ : ∀ a ∈ key.ds, (TrS s₃ a).looseBVarsBounded 0 = true := by
        intro a ha
        rw [TrS_of_tabLe ht13 (by simp only [OkSL, List.all_eq_true] at hokds; exact hokds a ha)]
        exact hcds a ha
      have hmap := instPisWithI_map key.ds r hokr hokds₃ hcds₃
      rw [ConLeche.Expr.instPisWithC_eq] at hmap
      rw [htrr, TrSL_of_tabLe ht13 hokds] at hmap
      obtain ⟨ty', s₄, h4, h⟩ := bind_run h
      cases hi' : InLean.instPisWith key.ds r with
      | none => rw [hi'] at h4; exact (throw_run h4).elim
      | some ty0 =>
      rw [hi'] at h4
      obtain ⟨rfl, rfl⟩ := pure_run h4
      rw [hi', Option.map_some] at hmap
      have hws : ∀ d, (∀ a ∈ key.ds, ConLeche.Expr.WScoped d (TrS s₀ a)) →
          ConLeche.Expr.WScoped d (TrS s₃ ty0) := by
        intro d hd
        refine ConLeche.wscoped_instPisWith (as := TrSL s₀ key.ds) ?_ ?_ hmap.symm
        · intro a ha
          obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
          exact hd b hb
        · refine ConLeche.Expr.WScoped.of_not_hasFvar ?_
          rw [ConLeche.Expr.hasFvar_instantiateLevelParams]
          exact trC_hasFvar tyC
      rw [← hmap]
      refine runs5_bind (Runs.pure _) ?_
      obtain ⟨hokty, -⟩ := instPisWithI_tr key.ds r hokr hokds₃ hcds₃ hi'
      have hclty : (TrS s₃ ty0).looseBVarsBounded 0 = true := by
        refine ConLeche.looseBVarsBounded_instPisWith (as := TrSL s₃ key.ds) (e := TrS s₃ r)
          ?_ ?_ ?_
        · intro a ha
          obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
          exact hcds₃ b hb
        · rw [htrr, ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]; exact hclC
        · rw [← ConLeche.Expr.instPisWithC_eq, ← (instPisWithI_tr key.ds r hokr hokds₃ hcds₃ hi').2]
      obtain ⟨hpb, hokbs, hokend, hnm⟩ := piBinders_TrS ty0 hokty
      rw [hpb]
      simp only
      obtain ⟨u, s₅, h5, h⟩ := bind_run h
      generalize hx : (InLean.piBinders ty0).2 = x at h5 hokend hnm ⊢
      cases x with
      | sort u0 =>
      simp only [InLean.unwrapOr] at h5
      obtain ⟨rfl, rfl⟩ := pure_run h5
      rw [TrS_sort]
      simp only
      refine runs5_bind (Runs.pure _) ?_
      have hu0 : okL u0 = true := by
        simp only [OkS_sort, okLv, Bool.and_eq_true] at hokend
        exact hokend.1
      have hokbs' : ∀ b ∈ (InLean.piBinders ty0).1, OkS s₃ b = true := by
        simp only [OkSL, List.all_eq_true] at hokbs; exact hokbs
      have hany : ((InLean.piBinders ty0).1.map (TrS s₃)).any
          (fun b => b.nestOcc cctx.names cctx.nP hi) =
          (InLean.piBinders ty0).1.any (fun b => InLean.nestOcc ctx.names ctx.nP hi b) := by
        generalize (InLean.piBinders ty0).1 = l at hokbs'
        induction l with
        | nil => rfl
        | cons b l ih =>
          simp only [List.map_cons, List.any_cons]
          rw [ih (fun x hx => hokbs' x (List.mem_cons_of_mem _ hx)), hR.names, hR.nP,
            nestOccI_tr ctx.names ctx.nP hi (hokbs' b List.mem_cons_self)]
      rw [hany]
      by_cases ho : (InLean.piBinders ty0).1.any (fun b => InLean.nestOcc ctx.names ctx.nP hi b) = true
      · simp only [ho, ↓reduceIte] at h
        obtain ⟨_, _, h6, -⟩ := bind_run h
        exact (throw_run h6).elim
      · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
        obtain ⟨b, s₆, h6, h⟩ := bind_run h
        obtain ⟨hs₆, ht₆, hb⟩ := tripleI_iff_run.1 (liftFueled_specI hs₃ "level comparison" _) b s₆ h6
        rw [hsort, ← isEquiv_trL hu0 hsok, hb]
        refine runs5_bind (Runs.pure _) ?_
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          obtain ⟨_, _, h7, -⟩ := bind_run h
          exact (throw_run h7).elim
        | true =>
          simp only [↓reduceIte] at h ⊢
          obtain ⟨hkt, rfl⟩ := pure_run h
          simp only [Prod.mk.injEq] at hkt
          obtain ⟨rfl, rfl⟩ := hkt
          refine ⟨hs₆, ht13.trans ht₆, okS_of_tabLe ht₆ hokty, ?_, ?_, ?_⟩
          · rw [TrS_of_tabLe ht₆ hokty]; exact hclty
          · intro d hd; rw [TrS_of_tabLe ht₆ hokty]; exact hws d hd
          · rw [TrS_of_tabLe ht₆ hokty, List.length_map]
            first | exact Runs.pure _ | exact Runs.bind (Runs.pure _) (Runs.pure _)
      | mdata m b => exact (hnm m b rfl).elim
      | _ =>
        simp only [InLean.unwrapOr] at h5
        exact (throw_run h5).elim
    · simp only [hst] at h
      obtain ⟨_, _, h3, -⟩ := bind_run h
      exact (throw_run h3).elim
  · simp only [hlen, ↓reduceIte] at h
    obtain ⟨_, _, h2, -⟩ := bind_run h
    exact (throw_run h2).elim

end InLeanProof

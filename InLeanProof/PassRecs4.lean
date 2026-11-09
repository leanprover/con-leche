module

public import InLeanProof.PassRecs3
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.Cached.IndWalksC
import ConLeche.Verify.Inductives.NestCallSyn
import ConLeche.Verify.Inductives.ClassGenScope
/- `Lean.mkAppN`'s body is not exposed by `Lean.Expr`; the marker-freeness of
an application's arguments (`emvarS_mkAppN_args`) unfolds it. -/
import all Lean.Expr

/-!
# O7-recursors: the generator and the recursor checks (task #451, lane O7-recursors)

The recursor stage (`genRecCheck`) against master's, continued bottom-up from
`PassRecs3`:

* the generator's remaining steps, `ClassGen.minorTy`, `ClassGen.prefixBinders`,
  `classGenRecTy` and `classGenRule`, read as master's where the closed result
  holds no out-of-range marker (`emvarS = false`), which the checks provide:
  `classConstOk` and `classRuleCheck` refuse a generated term `EO.inRange`
  refuses.
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached

variable {mode : ConLeche.CheckMode} {eager : Bool} {env : ConLeche.Env}

/-! ## Closings: the marker-freeness of the pieces -/

theorem emvarS_closeTelescopeFrom_all : ∀ (bs : List Lean.Expr) (i j : Nat) (body : Lean.Expr),
    emvarS (InLean.closeTelescopeFrom bs i j body) = false →
      (∀ b ∈ bs, emvarS b = false) ∧ emvarS body = false
  | [], _, _, _, h => ⟨fun _ hb => (nomatch hb), emvarS_of_abstractDepthsFrom h⟩
  | dom :: bs, i, j, body, h => by
    simp only [InLean.closeTelescopeFrom, emvarS, Bool.or_eq_false_iff] at h
    obtain ⟨h1, h2⟩ := emvarS_closeTelescopeFrom_all bs i (j + 1) body h.2
    refine ⟨fun b hb => ?_, h2⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact emvarS_of_abstractDepthsFrom h.1
    · exact h1 b hb

/-- A marker-free closed telescope has marker-free binders and body. -/
theorem emvarS_closeTelescope_all (bs : List Lean.Expr) (i : Nat) (body : Lean.Expr)
    (h : emvarS (InLean.closeTelescope bs i body) = false) :
    (∀ b ∈ bs, emvarS b = false) ∧ emvarS body = false :=
  emvarS_closeTelescopeFrom_all bs i 0 body h

theorem emvarS_closeLamsFrom : ∀ (bs : List Lean.Expr) (i j : Nat) (body : Lean.Expr),
    emvarS (InLean.closeLamsFrom bs i j body) = false →
      (∀ b ∈ bs, emvarS b = false) ∧ emvarS body = false
  | [], _, _, _, h => ⟨fun _ hb => (nomatch hb), emvarS_of_abstractDepthsFrom h⟩
  | dom :: bs, i, j, body, h => by
    simp only [InLean.closeLamsFrom, emvarS, Bool.or_eq_false_iff] at h
    obtain ⟨h1, h2⟩ := emvarS_closeLamsFrom bs i (j + 1) body h.2
    refine ⟨fun b hb => ?_, h2⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact emvarS_of_abstractDepthsFrom h.1
    · exact h1 b hb

/-- A marker-free closed λ-telescope has marker-free binders and body. -/
theorem emvarS_closeLams (bs : List Lean.Expr) (i : Nat) (body : Lean.Expr)
    (h : emvarS (InLean.closeLams bs i body) = false) :
    (∀ b ∈ bs, emvarS b = false) ∧ emvarS body = false :=
  emvarS_closeLamsFrom bs i 0 body h

theorem closeLamsFrom_tr (s : InLean.CState) :
    ∀ (bs : List Lean.Expr) (i j : Nat) (body : Lean.Expr), OkSL s bs = true → OkS s body = true →
      emvarS (InLean.closeLamsFrom bs i j body) = false →
      OkS s (InLean.closeLamsFrom bs i j body) = true ∧
        TrS s (InLean.closeLamsFrom bs i j body) =
          ConLeche.Expr.closeLamsGoC i j (TrSL s bs) (TrS s body)
  | [], i, j, body, _, hb, hm => by
    simp only [TrSL, List.map_nil, ConLeche.Expr.closeLamsGoC, ConLeche.Expr.abstractRangeC_spec]
    exact tr_abstractDepthsFrom hb i j 0 hm
  | dom :: bs, i, j, body, hbs, hb, hm => by
    simp only [OkSL, List.all_cons, Bool.and_eq_true] at hbs
    simp only [InLean.closeLamsFrom, emvarS, Bool.or_eq_false_iff] at hm
    obtain ⟨hC, hTC⟩ := closeLamsFrom_tr s bs i (j + 1) body hbs.2 hb hm.2
    obtain ⟨hokA, htrA⟩ := tr_abstractDepthsFrom hbs.1 i j 0 hm.1
    refine ⟨?_, ?_⟩
    · simp only [InLean.closeLamsFrom, OkS_lam, Bool.and_eq_true]
      exact ⟨hokA, hC⟩
    · simp only [InLean.closeLamsFrom, TrS_lam, TrSL, List.map_cons,
        ConLeche.Expr.closeLamsGoC, ConLeche.Expr.mkLam_eq, ConLeche.Expr.abstractRangeC_spec]
      rw [htrA, hTC]
      rfl

/-- **InLean's λ-closing reads as master's `closeLamsC`** where it wrote no
out-of-range marker (`closeTelescope_tr`'s twin). -/
theorem closeLams_tr (s : InLean.CState) (bs : List Lean.Expr) (i : Nat) (body : Lean.Expr)
    (hbs : OkSL s bs = true) (hb : OkS s body = true)
    (hm : emvarS (InLean.closeLams bs i body) = false) :
    OkS s (InLean.closeLams bs i body) = true ∧
      TrS s (InLean.closeLams bs i body) = ConLeche.Expr.closeLamsC (TrSL s bs) i (TrS s body) :=
  closeLamsFrom_tr s bs i 0 body hbs hb hm

/-! ## Lists -/

theorem TrSL_getD (s : InLean.CState) {l : List Lean.Expr} {i : Nat} (hi : i < l.length) :
    (TrSL s l).getD i default = TrS s (l.getD i default) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, TrSL, List.getElem?_map,
    List.getElem?_eq_getElem hi]
  rfl

theorem okS_getD {s : InLean.CState} {l : List Lean.Expr} (h : OkSL s l = true) {i : Nat}
    (hi : i < l.length) : OkS s (l.getD i default) = true := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  simp only [OkSL, List.all_eq_true] at h
  exact h _ (List.getElem_mem hi)

/-- The domains `targetPiDomsWith` instantiates at closed arguments in a closed
telescope are closed. -/
theorem lbb_targetPiDomsWith :
    ∀ {as : List ConLeche.Expr} {t : ConLeche.Expr} {ws : List ConLeche.Expr},
      ConLeche.targetPiDomsWith as t = some ws → t.looseBVarsBounded 0 = true →
      (∀ a ∈ as, a.looseBVarsBounded 0 = true) → ∀ w ∈ ws, w.looseBVarsBounded 0 = true
  | [], t, ws, h, _, _ => by
    simp only [ConLeche.targetPiDomsWith, Option.some.injEq] at h
    subst h; intro w hw; exact nomatch hw
  | a :: as, t, ws, h, ht, ha => by
    match t, ht, h with
    | .forallE dom body, ht, h =>
      simp only [ConLeche.targetPiDomsWith] at h
      obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true] at ht
      intro w hw'
      rcases List.mem_cons.mp hw' with rfl | hw'
      · exact ht.1
      · exact lbb_targetPiDomsWith hr (lbb_instantiate1 (ha a List.mem_cons_self) ht.2)
          (fun x hx => ha x (List.mem_cons_of_mem _ hx)) w hw'

/-! ## The slot variables -/

theorem motiveSlot_trSlot (s : InLean.CState) (slots : List InLean.ClassSlot) (c : Nat) :
    ConLeche.ClassRead.motiveSlot ⟨slots.map (trSlot s), []⟩ c =
      InLean.ClassRead.motiveSlot ⟨slots, []⟩ c := by
  unfold ConLeche.ClassRead.motiveSlot InLean.ClassRead.motiveSlot
  simp only [List.length_map, List.getElem?_map]
  congr 1
  apply List.filter_congr
  intro x _
  cases slots[x]? with
  | none => rfl
  | some sl => cases sl <;> rfl

/-- **A slot's variable** (`ClassGen.slotVar`), read. -/
theorem slotVarI_run {s₀ s' : InLean.CState} {g : InLean.ClassGen} {sg : InLean.CState} {n : Nat}
    {v : Lean.Expr} (hs : CSOKI mode eager env s₀) (h : g.slotVar n s₀ = .ok (v, s')) :
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
      TrS s' v = (trCG sg g).slotVar n := by
  unfold InLean.ClassGen.slotVar at h
  obtain ⟨hs', ht, ho, htr⟩ := tripleI_iff_run.1 (mkFVarM_specI hs _ (by rfl) (by rfl)) v s' h
  exact ⟨hs', ht, ho, by rw [htr]; rfl⟩

/-- **A class's motive variable** (`ClassGen.motVar`), read. -/
theorem motVarI_run {s₀ s' : InLean.CState} {g : InLean.ClassGen} {sg : InLean.CState} {c : Nat}
    {v : Lean.Expr} (hs : CSOKI mode eager env s₀) (h : g.motVar c s₀ = .ok (v, s')) :
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
      TrS s' v = (trCG sg g).motVar c := by
  unfold InLean.ClassGen.motVar at h
  obtain ⟨hs', ht, ho, htr⟩ := slotVarI_run (sg := sg) hs h
  refine ⟨hs', ht, ho, ?_⟩
  rw [htr]
  unfold ConLeche.ClassGen.motVar
  simp only [trCG, motiveSlot_trSlot]

/-! ## `mapM` in `OptionT` against master's `Option` -/

/-- One step of a generated list: InLean's `some` is master's `some` on the
reading, where the term holds no marker. -/
@[expose] def StepOk (mode : ConLeche.CheckMode) (eager : Bool) (env : ConLeche.Env)
    (sb : InLean.CState) (F : OptionT InLean.CheckCM Lean.Expr) (G : Option ConLeche.Expr) : Prop :=
  ∀ s₀ s' r, CSOKI mode eager env s₀ → TabLe sb s₀ → F.run s₀ = .ok (r, s') →
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ ∀ e, r = some e → emvarS e = false →
      OkS s' e = true ∧ G = some (TrS s' e)

/-- **A generated list** (`mapM` in `OptionT CheckCM`), read. -/
theorem mapM_optT_run {sb : InLean.CState} {F : Nat → OptionT InLean.CheckCM Lean.Expr}
    {G : Nat → Option ConLeche.Expr} :
    ∀ (ls : List Nat), (∀ l ∈ ls, StepOk mode eager env sb (F l) (G l)) →
      ∀ {s₀ s' : InLean.CState} {r : Option (List Lean.Expr)}, CSOKI mode eager env s₀ →
        TabLe sb s₀ → (ls.mapM F).run s₀ = .ok (r, s') →
        CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ ∀ es, r = some es → (∀ e ∈ es, emvarS e = false) →
          OkSL s' es = true ∧ ls.mapM G = some (TrSL s' es)
  | [], _, s₀, s', r, hs, _, h => by
    rw [List.mapM_nil] at h
    obtain ⟨rfl, rfl⟩ := optT_pure_run h
    exact ⟨hs, TabLe.refl _, fun es he _ => by cases he; exact ⟨rfl, rfl⟩⟩
  | l :: ls, hF, s₀, s', r, hs, hb, h => by
    rw [List.mapM_cons] at h
    obtain ⟨o, s₁, h1, h⟩ := optT_bind_run h
    obtain ⟨hs₁, ht₁, hR1⟩ := hF l List.mem_cons_self s₀ s₁ o hs hb h1
    cases o with
    | none =>
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hs₁, ht₁, fun _ h => by cases h⟩
    | some e =>
      simp only at h
      obtain ⟨o', s₂, h2, h⟩ := optT_bind_run h
      obtain ⟨hs₂, ht₂, hR2⟩ := mapM_optT_run ls (fun l' hl' => hF l' (List.mem_cons_of_mem _ hl'))
        hs₁ (hb.trans ht₁) h2
      cases o' with
      | none =>
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hs₂, ht₁.trans ht₂, fun _ h => by cases h⟩
      | some es =>
        simp only at h
        obtain ⟨rfl, rfl⟩ := optT_pure_run h
        refine ⟨hs₂, ht₁.trans ht₂, fun es' hes hem => ?_⟩
        simp only [Option.some.injEq] at hes
        subst hes
        obtain ⟨he1, hG⟩ := hR1 e rfl (hem e List.mem_cons_self)
        obtain ⟨hes1, hGs⟩ := hR2 es rfl (fun e' he' => hem e' (List.mem_cons_of_mem _ he'))
        refine ⟨by rw [OkSL_cons, okS_of_tabLe ht₂ he1, hes1]; rfl, ?_⟩
        rw [List.mapM_cons, hG, hGs, TrSL_cons, TrS_of_tabLe ht₂ he1]
        rfl

/-! ## A minor premise's type -/

theorem getD_map_trCF (ks : List InLean.ClassField) (i : Nat) :
    (ks.map trCF).getD i .ordinary = trCF (ks.getD i .ordinary) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ks[i]? <;> rfl

/-- An entry of a `filterMap` over `range n` that keeps the index is below `n`. -/
theorem getD_filterMap_range_lt {α : Type} [Inhabited α] {f : Nat → Option (Nat × α)}
    (hf : ∀ i q, f i = some q → q.1 = i) {n l : Nat}
    (hl : l < ((List.range n).filterMap f).length) :
    (((List.range n).filterMap f).getD l default).1 < n := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
  have hm := List.getElem_mem hl
  generalize (List.filterMap _ _)[l] = q at hm
  obtain ⟨i, hi, hq⟩ := List.mem_filterMap.1 hm
  rw [List.mem_range] at hi
  rw [hf i q hq]
  exact hi

/-- **A minor premise's inductive hypotheses, one step** (the body of
`ClassGen.minorTy`'s `mapM`), read. -/
theorem minorIhStepOk {sb sg : InLean.CState} {g : InLean.ClassGen} {fvs ws : List Lean.Expr}
    {recs : List (Nat × Nat × Nat)} {d nF : Nat} (hfv : FvsOk sb fvs) (hwo : OkSL sb ws = true)
    (hwc : ∀ w ∈ TrSL sb ws, w.looseBVarsBounded 0 = true)
    (hrecs : ∀ l < recs.length, (recs.getD l default).1 < ws.length ∧
      (recs.getD l default).1 < fvs.length) :
    ∀ l ∈ List.range recs.length, StepOk mode eager env sb
      (do
        let (i, t, tele) := recs.getD l default
        let e := d + nF + l
        let (xs, idx) ← g.ihParts t tele (ws.getD i default) e
        pure (InLean.closeTelescope (← xs.mapM fun x => liftM (g.binder x)) e
          (InLean.mkAppL (← g.motVar t) (idx ++ [InLean.mkAppL (fvs.getD i default) xs]))) :
        OptionT InLean.CheckCM Lean.Expr)
      (do
        let (i, t, tele) := recs.getD l default
        let e := d + nF + l
        let (xs, idx) ← (trCG sg g).ihParts t tele ((TrSL sb ws).getD i default) e
        pure (ConLeche.closeTelescope (xs.map (trCG sg g).binder) e
          (ConLeche.Expr.mkAppN ((trCG sg g).motVar t)
            (idx ++ [ConLeche.Expr.mkAppN ((TrSL sb fvs).getD i default) xs])))) := by
  intro l hl s₀ s' r hs hb h
  rw [List.mem_range] at hl
  obtain ⟨hiw, hif⟩ := hrecs l hl
  obtain ⟨⟨i, t, tele⟩, hq⟩ : ∃ q, recs.getD l default = q := ⟨_, rfl⟩
  rw [hq] at hiw hif h ⊢
  simp only at hiw hif h ⊢
  have hw₀ : OkS s₀ (ws.getD i default) = true := okS_getD (okSL_of_tabLe hb hwo) hiw
  have hwb : OkS sb (ws.getD i default) = true := okS_getD hwo hiw
  have hwC : (TrS s₀ (ws.getD i default)).looseBVarsBounded 0 = true := by
    rw [TrS_of_tabLe hb hwb, ← TrSL_getD sb hiw]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [TrSL_length]; exact hiw),
      Option.getD_some]
    exact hwc _ (List.getElem_mem _)
  rw [TrSL_getD sb hiw, ← TrS_of_tabLe hb hwb]
  obtain ⟨o, s₁, h1, h⟩ := optT_bind_run h
  obtain ⟨hs₁, ht₁, hip⟩ := ihPartsI_run (sg := sg) hs hw₀ hwC h1
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hs₁, ht₁, fun _ h => by cases h⟩
  | some q =>
    obtain ⟨xs, idx⟩ := q
    obtain ⟨hxs, hidx, hipC⟩ := hip xs idx rfl
    rw [hipC]
    simp only [InLean.ClassGen.binder] at h
    obtain ⟨o, s₂, h2, h⟩ := optT_bind_run h
    obtain ⟨rfl, bs, rfl, hbso, hbst⟩ := mapM_binder_run hs₁ xs hxs h2
    simp only at h
    obtain ⟨o, s₃, h3, h⟩ := optT_bind_run h
    obtain ⟨v, rfl, hv⟩ := liftM_run h3
    obtain ⟨hs₃, ht₃, hvo, hvt⟩ := motVarI_run (sg := sg) hs₁ hv
    simp only at h
    obtain ⟨rfl, rfl⟩ := optT_pure_run h
    refine ⟨hs₃, ht₁.trans ht₃, fun e he hem => ?_⟩
    simp only [Option.some.injEq] at he
    subst he
    have hf₀ : OkS sb (fvs.getD i default) = true := okS_getD hfv.okSL hif
    have hf₃ : OkS s' (fvs.getD i default) = true :=
      okS_of_tabLe ((hb.trans ht₁).trans ht₃) hf₀
    have hxs' := okSL_of_tabLe ht₃ hxs.okSL
    have hbody : OkS s' (InLean.mkAppL v (idx ++ [InLean.mkAppL (fvs.getD i default) xs])) = true := by
      unfold InLean.mkAppL
      rw [OkS_mkAppN, hvo, OkSL_append (h := okSL_of_tabLe ht₃ hidx)]
      · rfl
      · rw [OkSL_cons, OkS_mkAppN, hf₃, hxs']; rfl
    obtain ⟨ho, ht⟩ := closeTelescope_tr s' bs _ _ (okSL_of_tabLe ht₃ hbso) hbody hem
    rw [ConLeche.Expr.closeTelescopeC_eq] at ht
    refine ⟨ho, ?_⟩
    rw [ht, TrSL_of_tabLe ht₃ hbso, hbst]
    unfold InLean.mkAppL
    rw [TrS_mkAppN, hvt, TrSL_append, TrSL_cons, TrSL_nil, TrS_mkAppN,
      TrSL_of_tabLe ht₃ hidx, TrSL_of_tabLe ht₃ hxs.okSL,
      TrS_of_tabLe ((hb.trans ht₁).trans ht₃) hf₀, ← TrSL_getD sb hif]
    rfl

/-- **A constructor's minor premise type** (`ClassGen.minorTy`), read where
InLean's closing wrote no out-of-range marker. -/
theorem minorTyI_run {s₀ s' : InLean.CState} {g : InLean.ClassGen} {c d : Nat}
    {x : InLean.ClassCtor} {r : Option Lean.Expr} (hs : CSOKI mode eager env s₀)
    (hM : ClassOk s₀ (g.cls.getD c default)) (hx : OkCC s₀ x)
    (hxD : (TrS s₀ x.tyD).looseBVarsBounded 0 = true)
    (hxN : (TrS s₀ x.tyN).looseBVarsBounded 0 = true)
    (h : (g.minorTy c x d).run s₀ = .ok (r, s')) :
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ ∀ e, r = some e → emvarS e = false →
      OkS s' e = true ∧ (trCG s₀ g).minorTy c (trCC s₀ x) d = some (TrS s' e) := by
  obtain ⟨hMn, -, -, -⟩ := hM
  obtain ⟨-, hxDo, hxNo⟩ := hx
  unfold InLean.ClassGen.minorTy at h
  unfold ConLeche.ClassGen.minorTy
  obtain ⟨o, s₁, h1, h⟩ := optT_bind_run h
  simp only [InLean.openPisO, OptionT.run, OptionT.mk] at h1
  unfold InLean.openPisAtFvars at h1
  obtain ⟨hs₁, ht₁, hop⟩ := openPisAtFvarsI_run _ d hs hxDo hxD h1
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hs₁, ht₁, fun _ h => by cases h⟩
  | some q =>
  obtain ⟨fvs, res⟩ := q
  obtain ⟨hfo, hro, hopC⟩ := hop fvs res rfl
  rw [ConLeche.Cached.openPisAtFvarsC_eq] at hopC
  have hfv : FvsOk s₁ fvs := fvsOk_of_open hfo hopC
  have hfl : fvs.length = x.nF := by
    have := ConLeche.Verify.openPisAtFvars_length _ hopC
    rwa [TrSL_length] at this
  have hxN₁ := okS_of_tabLe ht₁ hxNo
  obtain ⟨hwo, hwC⟩ := targetPiDomsWith_tr fvs x.tyN hfo hfv.lbb hxN₁
  rw [ConLeche.Expr.targetPiDomsWithC_eq] at hwC
  rw [TrS_of_tabLe ht₁ hxNo] at hwC
  simp only [trCC]
  rw [hopC]
  simp only [Option.bind_eq_bind, Option.bind_some]
  simp only at h
  obtain ⟨o, s₂, h2, h⟩ := optT_bind_run h
  obtain ⟨rfl, hs21⟩ := liftOpt_run h2
  rw [hs21] at h
  cases hw : InLean.targetPiDomsWith fvs x.tyN with
  | none =>
    rw [hw] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hs₁, ht₁, fun _ h => by cases h⟩
  | some ws =>
  rw [hw] at h hwC
  simp only [Option.map_some] at hwC
  rw [hwC]
  simp only [Option.bind_some]
  try simp only at h
  have hws := hwo ws hw
  have hwl : ws.length = fvs.length := by
    have := ConLeche.targetPiDomsWith_length _ _ _ hwC
    rwa [TrSL_length, TrSL_length] at this
  have hwc : ∀ w ∈ TrSL s₁ ws, w.looseBVarsBounded 0 = true := by
    exact lbb_targetPiDomsWith hwC hxN (fun a ha => by
        simp only [TrSL, List.mem_map] at ha
        obtain ⟨a', ha', rfl⟩ := ha
        exact hfv.lbb a' ha')
  generalize hRM : List.filterMap _ (List.range x.nF) = recsM
  generalize hRI : List.filterMap _ (List.range x.nF) = recs at h
  have hrl : ∀ l < recs.length, (recs.getD l default).1 < x.nF := by
    intro l hl
    rw [← hRI] at hl ⊢
    exact getD_filterMap_range_lt (fun i q hq => by
      try dsimp only at hq
      split at hq <;> cases hq <;> rfl) hl
  have hRR : recsM = recs := by
    rw [← hRM, ← hRI]
    congr 1
    funext i
    rw [getD_map_trCF]
    cases x.kinds.getD i .ordinary <;> rfl
  subst hRR
  obtain ⟨o, s₃, h3, h⟩ := optT_bind_run h
  obtain ⟨hs₃, ht₃, hR3⟩ := mapM_optT_run (List.range _)
    (minorIhStepOk (sg := s₀) (d := d) (nF := x.nF) hfv hws hwc (fun l hl => by
      have := hrl l hl
      exact ⟨by omega, by omega⟩)) hs₁ (TabLe.refl _) h3
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hs₃, ht₁.trans ht₃, fun _ h => by cases h⟩
  | some ihs =>
  simp only at h
  obtain ⟨o, s₄, h4, h⟩ := optT_bind_run h
  obtain ⟨v, rfl, hv⟩ := liftM_run h4
  obtain ⟨hs₄, ht₄, hvo, hvt⟩ := motVarI_run (sg := s₀) hs₃ hv
  simp only [InLean.ClassGen.binder] at h
  obtain ⟨o, s₅, h5, h⟩ := optT_bind_run h
  obtain ⟨rfl, bs, rfl, hbso, hbst⟩ := mapM_binder_run hs₄ fvs
    ((hfv.mono (ht₃.trans ht₄)).1) h5
  simp only at h
  obtain ⟨rfl, rfl⟩ := optT_pure_run h
  refine ⟨hs₄, (ht₁.trans ht₃).trans ht₄, fun e he hem => ?_⟩
  simp only [Option.some.injEq] at he
  subst he
  obtain ⟨hemb, -⟩ := emvarS_closeTelescope_all _ _ _ hem
  obtain ⟨hihso, hihsC⟩ := hR3 ihs rfl (fun e he => hemb e (List.mem_append_right _ he))
  have ht₁₄ := ht₃.trans ht₄
  have hds₄ := okSL_of_tabLe ((ht₁.trans ht₃).trans ht₄) hMn.2.1
  have hfo₄ := okSL_of_tabLe ht₁₄ hfo
  have hro₄ := okS_of_tabLe ht₁₄ hro
  have hbody : OkS s' (InLean.mkAppL v ((appArgs res).drop (g.cls.getD c default).nPc ++
      [InLean.mkAppL (.const x.cv.name (g.cls.getD c default).lvls)
        ((g.cls.getD c default).ds ++ fvs)])) = true := by
    unfold InLean.mkAppL
    rw [OkS_mkAppN, hvo, OkSL_append (h := OkSL_drop s' (OkSL_appArgs s' hro₄) _)]
    · rfl
    · rw [OkSL_cons, OkS_mkAppN, OkS_const, hMn.1, OkSL_append (h := hds₄) (h' := hfo₄)]; rfl
  obtain ⟨ho, ht⟩ := closeTelescope_tr s' (bs ++ ihs) d _
    (OkSL_append (h := hbso) (h' := okSL_of_tabLe ht₄ hihso)) hbody hem
  rw [ConLeche.Expr.closeTelescopeC_eq] at ht
  refine ⟨ho, ?_⟩
  simp only [Option.bind_eq_bind] at hihsC
  rw [hihsC]
  simp only [Option.bind_some, Option.pure_def, Option.some.injEq]
  rw [ht, TrSL_append, hbst, TrSL_of_tabLe ht₄ hihso, TrSL_of_tabLe ht₁₄ hfo]
  unfold InLean.mkAppL
  rw [TrS_mkAppN, hvt, TrSL_append, TrSL_drop, TrSL_appArgs, TrS_of_tabLe ht₁₄ hro, TrSL_cons,
    TrSL_nil, TrS_mkAppN, TrS_const, TrSL_append, TrSL_of_tabLe ((ht₁.trans ht₃).trans ht₄) hMn.2.1,
    TrSL_of_tabLe ht₁₄ hfo]
  simp only [trCG, getD_map_trTM, trTM, trCV_name]
  rfl

/-! ## The generator's record at a later state -/

/-- The generator's record has a reading. -/
@[expose] def CGOk (s : InLean.CState) (g : InLean.ClassGen) : Prop :=
  OkSL s g.params = true ∧ (∀ M ∈ g.cls, OkTMN s M) ∧ OkSL s g.formerTys = true ∧
    (∀ sl ∈ g.slots, OkSlot s sl) ∧ (∀ xs ∈ g.ctors, ∀ x ∈ xs, OkCC s x) ∧ OkSL s g.pre = true

theorem CGOk.mono {s₀ s₁ : InLean.CState} (h : TabLe s₀ s₁) {g : InLean.ClassGen}
    (hg : CGOk s₀ g) : CGOk s₁ g ∧ trCG s₁ g = trCG s₀ g := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hg
  refine ⟨⟨okSL_of_tabLe h h1, fun M hM => (OkTMN.mono h (h2 M hM)).1, okSL_of_tabLe h h3,
    fun sl hsl => OkSlot.mono h (h4 sl hsl), fun xs hxs x hx => (OkCC.mono h (h5 xs hxs x hx)).1,
    okSL_of_tabLe h h6⟩, ?_⟩
  unfold trCG
  rw [TrSL_of_tabLe h h1, map_trTM_mono h h2, TrSL_of_tabLe h h3, TrSL_of_tabLe h h6,
    List.map_congr_left fun sl hsl => trSlot_mono h (h4 sl hsl),
    List.map_congr_left fun xs hxs => map_trCC_mono h (h5 xs hxs)]

theorem getD_map_trSlot (s : InLean.CState) {slots : List InLean.ClassSlot} {i : Nat}
    (hi : i < slots.length) : (slots.map (trSlot s)).getD i default = trSlot s (slots.getD i default) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hi]
  rfl

theorem getD_map_trCCs (s : InLean.CState) (xss : List (List InLean.ClassCtor)) (c : Nat) :
    (xss.map (·.map (trCC s))).getD c [] = (xss.getD c []).map (trCC s) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases xss[c]? <;> rfl

theorem find?_trCC (s : InLean.CState) (xs : List InLean.ClassCtor) (C : Lean.Name) :
    (xs.map (trCC s)).find? (·.cv.name == toName C) = (xs.find? (·.cv.name == C)).map (trCC s) := by
  rw [List.find?_map]
  congr 2
  funext x
  simp only [Function.comp, trCC, trCV_name, toName_beq]

theorem closed_getD {s : InLean.CState} {l : List Lean.Expr}
    (h : ∀ f ∈ l, (TrS s f).looseBVarsBounded 0 = true) {i : Nat} (hi : i < l.length) :
    (TrS s (l.getD i default)).looseBVarsBounded 0 = true := by
  apply h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

/-! ## The prefix -/

/-- **One slot's binder** (the body of `ClassGen.prefixBinders`' `mapM`), read. -/
theorem prefixSlotStepOk {sb : InLean.CState} {g : InLean.ClassGen} (hg : CGOk sb g)
    (hcls : ∀ c, ClassOk sb (g.cls.getD c default))
    (hft : ∀ f ∈ g.formerTys, (TrS sb f).looseBVarsBounded 0 = true) (hel : okLv g.elim = true)
    (hmc : ∀ s < g.slots.length, ∀ k, g.slots.getD s default = .motive k →
      ((List.range s).filter fun s' =>
        match g.slots.getD s' default with | .motive _ => true | _ => false).length <
        g.formerTys.length)
    (hct : ∀ xs ∈ g.ctors, ∀ x ∈ xs, (TrS sb x.tyD).looseBVarsBounded 0 = true ∧
      (TrS sb x.tyN).looseBVarsBounded 0 = true) :
    ∀ s ∈ List.range g.slots.length, StepOk mode eager env sb
      (do
        let d := g.nP + s
        match g.slots.getD s default with
        | .motive _ =>
          let c := ((List.range s).filter fun s' =>
            match g.slots.getD s' default with | .motive _ => true | _ => false).length
          g.motiveTy c d
        | .minor c C _ =>
          let x ← liftOpt ((g.ctors.getD c []).find? (·.cv.name == C))
          g.minorTy c x d : OptionT InLean.CheckCM Lean.Expr)
      (do
        let d := g.nP + s
        match (trCG sb g).slots.getD s default with
        | .motive _ =>
          let c := ((List.range s).filter fun s' =>
            match (trCG sb g).slots.getD s' default with | .motive _ => true | _ => false).length
          (trCG sb g).motiveTy c d
        | .minor c C _ =>
          let x ← ((trCG sb g).ctors.getD c []).find? (·.cv.name == C)
          (trCG sb g).minorTy c x d) := by
  intro s hsr s₀ s' r hs hb h
  rw [List.mem_range] at hsr
  obtain ⟨hg₀, htg⟩ := hg.mono hb
  have hsl : (trCG sb g).slots.getD s default = trSlot sb (g.slots.getD s default) :=
    getD_map_trSlot sb hsr
  rw [hsl]
  cases hk : g.slots.getD s default with
  | motive k =>
    rw [hk] at h
    simp only at h
    simp only [trSlot]
    have hfilt : ((List.range s).filter fun s' =>
        match (trCG sb g).slots.getD s' default with | .motive _ => true | _ => false) =
        ((List.range s).filter fun s' =>
          match g.slots.getD s' default with | .motive _ => true | _ => false) := by
      apply List.filter_congr
      intro s' hs'
      rw [List.mem_range] at hs'
      rw [show (trCG sb g).slots = g.slots.map (trSlot sb) from rfl,
        getD_map_trSlot sb (by omega)]
      cases g.slots.getD s' default <;> rfl
    erw [hfilt]
    have hc := hmc s hsr k hk
    have hfc := closed_getD hft hc
    rw [← TrS_of_tabLe hb (okS_getD hg.2.2.1 hc)] at hfc
    obtain ⟨hs', ht', hR⟩ := motiveTyI_run hs ((hcls _).mono hb) (okS_getD hg₀.2.2.1 hc) hfc hc
      hel h
    refine ⟨hs', ht', fun e he hem => ?_⟩
    obtain ⟨ho, hC⟩ := hR e he hem
    exact ⟨ho, by rw [← htg]; exact hC⟩
  | minor c C ihs =>
    rw [hk] at h
    simp only at h
    simp only [trSlot]
    obtain ⟨o, s₁, h1, h⟩ := optT_bind_run h
    obtain ⟨rfl, hs10⟩ := liftOpt_run h1
    subst hs10
    rw [show (trCG sb g).ctors = g.ctors.map (·.map (trCC sb)) from rfl, getD_map_trCCs,
      find?_trCC]
    cases hx : (g.ctors.getD c []).find? (·.cv.name == C) with
    | none =>
      rw [hx] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hs, TabLe.refl _, fun _ h => by cases h⟩
    | some x =>
      rw [hx] at h
      try simp only at h
      have hxm : x ∈ g.ctors.getD c [] := List.mem_of_find?_eq_some hx
      have hxs : g.ctors.getD c [] ∈ g.ctors ∨ g.ctors.getD c [] = [] := by
        rw [List.getD_eq_getElem?_getD]
        cases hc : g.ctors[c]? with
        | none => exact .inr rfl
        | some xs => exact .inl (List.mem_of_getElem? hc)
      have hxs : g.ctors.getD c [] ∈ g.ctors := by
        rcases hxs with h' | h'
        · exact h'
        · rw [h'] at hxm; cases hxm
      have hxo := hg.2.2.2.2.1 _ hxs x hxm
      obtain ⟨hxD, hxN⟩ := hct _ hxs x hxm
      obtain ⟨hxo₀, htx⟩ := OkCC.mono hb hxo
      obtain ⟨hs', ht', hR⟩ := minorTyI_run hs ((hcls c).mono hb) hxo₀
        (by rw [TrS_of_tabLe hb hxo.2.1]; exact hxD) (by rw [TrS_of_tabLe hb hxo.2.2]; exact hxN) h
      refine ⟨hs', ht', fun e he hem => ?_⟩
      obtain ⟨ho, hC⟩ := hR e he hem
      refine ⟨ho, ?_⟩
      simp only [Option.bind_eq_bind, Option.map_some, Option.bind_some]
      rw [← htg, ← htx]
      exact hC

/-- **The prefix binders** (`ClassGen.prefixBinders`), read where InLean's
closings wrote no out-of-range marker. -/
theorem prefixBindersI_run {s₀ s' : InLean.CState} {g : InLean.ClassGen}
    {r : Option (List Lean.Expr)} (hs : CSOKI mode eager env s₀) (hg : CGOk s₀ g)
    (hcls : ∀ c, ClassOk s₀ (g.cls.getD c default))
    (hft : ∀ f ∈ g.formerTys, (TrS s₀ f).looseBVarsBounded 0 = true) (hel : okLv g.elim = true)
    (hmc : ∀ s < g.slots.length, ∀ k, g.slots.getD s default = .motive k →
      ((List.range s).filter fun s' =>
        match g.slots.getD s' default with | .motive _ => true | _ => false).length <
        g.formerTys.length)
    (hct : ∀ xs ∈ g.ctors, ∀ x ∈ xs, (TrS s₀ x.tyD).looseBVarsBounded 0 = true ∧
      (TrS s₀ x.tyN).looseBVarsBounded 0 = true)
    (hpar : FvsOk s₀ g.params) (h : g.prefixBinders.run s₀ = .ok (r, s')) :
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ ∀ pre, r = some pre → (∀ b ∈ pre, emvarS b = false) →
      OkSL s' pre = true ∧ (trCG s₀ g).prefixBinders = some (TrSL s' pre) := by
  unfold InLean.ClassGen.prefixBinders at h
  unfold ConLeche.ClassGen.prefixBinders
  obtain ⟨o, s₁, h1, h⟩ := optT_bind_run h
  obtain ⟨hs₁, ht₁, hR1⟩ := mapM_optT_run _ (prefixSlotStepOk hg hcls hft hel hmc hct) hs
    (TabLe.refl _) h1
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hs₁, ht₁, fun _ h => by cases h⟩
  | some slotBs =>
  simp only [InLean.ClassGen.binder] at h
  obtain ⟨o, s₂, h2, h3⟩ := optT_bind_run h
  obtain ⟨hst, bs, rfl, hbso, hbst⟩ := mapM_binder_run hs₁ g.params (hpar.mono ht₁).1 h2
  subst hst
  try simp only at h3
  obtain ⟨rfl, rfl⟩ := optT_pure_run h3
  refine ⟨hs₁, ht₁, fun pre he hem => ?_⟩
  simp only [Option.some.injEq] at he
  subst he
  obtain ⟨hso, hsC⟩ := hR1 slotBs rfl (fun e he => hem e (List.mem_append_right _ he))
  refine ⟨OkSL_append (h := hbso) (h' := hso), ?_⟩
  have hlen : (trCG s₀ g).slots.length = g.slots.length := by simp [trCG]
  rw [hlen]
  erw [hsC]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq]
  rw [TrSL_append, hbst, (hpar.mono ht₁).2]
  rfl

/-! ## The recursor type -/

/-- A class's major domain, read, is closed. -/
theorem major_closed {s sg : InLean.CState} {g : InLean.ClassGen} {c d : Nat}
    {ifs : List Lean.Expr} {maj : Lean.Expr} (hM : ClassOk sg (g.cls.getD c default))
    (hfv : FvsOk s ifs) (h : (trCG sg g).major c d = some (TrSL s ifs, TrS s maj)) :
    (TrS s maj).looseBVarsBounded 0 = true := by
  obtain ⟨-, -, -, -, hmaj⟩ := ConLeche.ClassGen.major_inv h
  rw [hmaj]
  apply lbb_mkAppN_closed rfl
  simp only [AllClosed, List.all_append, Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · simp only [trCG, getD_map_trTM, trTM, TrSL, List.mem_map] at ha
    obtain ⟨a', ha', rfl⟩ := ha
    exact hM.2.2.1 a' ha'
  · simp only [TrSL, List.mem_map] at ha
    obtain ⟨a', ha', rfl⟩ := ha
    exact hfv.lbb a' ha'

/-- **The generated recursor type** (`classGenRecTy`), read where InLean's
closing wrote no out-of-range marker. -/
theorem classGenRecTyI_run {s₀ s' : InLean.CState} {g : InLean.ClassGen} {c : Nat}
    {r : Option Lean.Expr} (hs : CSOKI mode eager env s₀)
    (hM : ClassOk s₀ (g.cls.getD c default)) (hft : OkS s₀ (g.formerTys.getD c default) = true)
    (hftc : (TrS s₀ (g.formerTys.getD c default)).looseBVarsBounded 0 = true)
    (hc : c < g.formerTys.length) (hpre : OkSL s₀ g.pre = true)
    (h : (InLean.classGenRecTy g c).run s₀ = .ok (r, s')) :
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ ∀ e, r = some e → emvarS e = false →
      OkS s' e = true ∧ ConLeche.classGenRecTy (trCG s₀ g) c = some (TrS s' e) := by
  unfold InLean.classGenRecTy at h
  unfold ConLeche.classGenRecTy
  have hpl : (trCG s₀ g).pre.length = g.pre.length := by simp [trCG, TrSL_length]
  dsimp only
  rw [hpl]
  obtain ⟨o, s₁, h1, h⟩ := optT_bind_run h
  obtain ⟨hs₁, ht₁, hmj⟩ := majorI_run hs hM hft hftc hc h1
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hs₁, ht₁, fun _ h => by cases h⟩
  | some q =>
  obtain ⟨ifs, maj⟩ := q
  obtain ⟨hfv, hmo, hmC⟩ := hmj ifs maj rfl
  have hmc := major_closed hM hfv hmC
  erw [hmC]
  simp only [Option.bind_eq_bind, Option.bind_some]
  try simp only at h
  obtain ⟨o, s₂, h2, hk⟩ := optT_bind_run h
  obtain ⟨t, rfl, ht⟩ := liftM_run h2
  obtain ⟨hs₂, ht₂, hto, htt⟩ := tripleI_iff_run.1 (mkFVarM_specI hs₁ _ hmo hmc) t s₂ ht
  try simp only [InLean.ClassGen.binder] at hk
  obtain ⟨o, s₃, h3, hk3⟩ := optT_bind_run hk
  obtain ⟨hst, bs, rfl, hbso, hbst⟩ := mapM_binder_run hs₂ ifs (hfv.mono ht₂).1 h3
  subst hst
  try simp only at hk3
  obtain ⟨o, s₄, h4, hk4⟩ := optT_bind_run hk3
  obtain ⟨v, rfl, hv⟩ := liftM_run h4
  obtain ⟨hs₄, ht₄, hvo, hvt⟩ := motVarI_run (sg := s₀) hs₂ hv
  try simp only at hk4
  obtain ⟨rfl, rfl⟩ := optT_pure_run hk4
  refine ⟨hs₄, (ht₁.trans ht₂).trans ht₄, fun e he hem => ?_⟩
  simp only [Option.some.injEq] at he
  subst he
  have ht14 := ht₂.trans ht₄
  have hifs := okSL_of_tabLe ht14 hfv.okSL
  have hbody : OkS s' (InLean.mkAppL v (ifs ++ [t])) = true := by
    unfold InLean.mkAppL
    rw [OkS_mkAppN, hvo, OkSL_append (h := hifs) (h' := by rw [OkSL_cons, okS_of_tabLe ht₄ hto]; rfl)]
    rfl
  have hbs : OkSL s' (g.pre ++ bs ++ [maj]) = true := by
    refine OkSL_append (h := OkSL_append (h := okSL_of_tabLe ((ht₁.trans ht₂).trans ht₄) hpre)
      (h' := okSL_of_tabLe ht₄ hbso)) (h' := ?_)
    rw [OkSL_cons, okS_of_tabLe ht14 hmo]; rfl
  obtain ⟨ho, htr⟩ := closeTelescope_tr s' _ 0 _ hbs hbody hem
  rw [ConLeche.Expr.closeTelescopeC_eq] at htr
  refine ⟨ho, ?_⟩
  rw [htr, TrSL_append, TrSL_append, TrSL_of_tabLe ((ht₁.trans ht₂).trans ht₄) hpre,
    TrSL_of_tabLe ht₄ hbso, hbst, TrSL_of_tabLe ht₂ hfv.okSL, TrSL_cons, TrSL_nil,
    TrS_of_tabLe ht14 hmo]
  unfold InLean.mkAppL
  rw [TrS_mkAppN, hvt, TrSL_append, TrSL_cons, TrSL_nil, TrS_of_tabLe ht₄ hto, htt,
    TrSL_of_tabLe ht14 hfv.okSL, TrSL_length]
  rfl

/-! ## `filterMapM` in `OptionT` against master's `Option` -/

/-- One step of a generated, filtered list. -/
@[expose] def StepOkO (mode : ConLeche.CheckMode) (eager : Bool) (env : ConLeche.Env)
    (sb : InLean.CState) (F : OptionT InLean.CheckCM (Option Lean.Expr))
    (G : Option (Option ConLeche.Expr)) : Prop :=
  ∀ s₀ s' r, CSOKI mode eager env s₀ → TabLe sb s₀ → F.run s₀ = .ok (r, s') →
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ ∀ o, r = some o → (∀ e, o = some e → emvarS e = false) →
      (∀ e, o = some e → OkS s' e = true) ∧ G = some (o.map (TrS s'))

/-- **A generated, filtered list** (`filterMapM` in `OptionT CheckCM`), read. -/
theorem filterMapM_optT_run {sb : InLean.CState}
    {F : Nat → OptionT InLean.CheckCM (Option Lean.Expr)} {G : Nat → Option (Option ConLeche.Expr)} :
    ∀ (ls : List Nat), (∀ l ∈ ls, StepOkO mode eager env sb (F l) (G l)) →
      ∀ {s₀ s' : InLean.CState} {r : Option (List Lean.Expr)}, CSOKI mode eager env s₀ →
        TabLe sb s₀ → (ls.filterMapM F).run s₀ = .ok (r, s') →
        CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ ∀ es, r = some es → (∀ e ∈ es, emvarS e = false) →
          OkSL s' es = true ∧ ls.filterMapM G = some (TrSL s' es)
  | [], _, s₀, s', r, hs, _, h => by
    rw [List.filterMapM_nil] at h
    obtain ⟨rfl, rfl⟩ := optT_pure_run h
    exact ⟨hs, TabLe.refl _, fun es he _ => by cases he; exact ⟨rfl, rfl⟩⟩
  | l :: ls, hF, s₀, s', r, hs, hb, h => by
    rw [List.filterMapM_cons] at h
    rw [List.filterMapM_cons]
    obtain ⟨o, s₁, h1, hk⟩ := optT_bind_run h
    obtain ⟨hs₁, ht₁, hR1⟩ := hF l List.mem_cons_self s₀ s₁ o hs hb h1
    cases o with
    | none =>
      obtain ⟨rfl, rfl⟩ := hk
      exact ⟨hs₁, ht₁, fun _ h => by cases h⟩
    | some ob =>
      try simp only at hk
      cases ob with
      | none =>
        obtain ⟨hs₂, ht₂, hR2⟩ := filterMapM_optT_run ls
          (fun l' hl' => hF l' (List.mem_cons_of_mem _ hl')) hs₁ (hb.trans ht₁) hk
        refine ⟨hs₂, ht₁.trans ht₂, fun es hes hem => ?_⟩
        obtain ⟨hes1, hGs⟩ := hR2 es hes hem
        obtain ⟨-, hG⟩ := hR1 none rfl (fun _ h => by cases h)
        refine ⟨hes1, ?_⟩
        rw [hG]
        simp only [Option.map_none, Option.bind_eq_bind, Option.bind_some, hGs]
      | some b =>
        obtain ⟨o', s₂, h2, hk2⟩ := optT_bind_run hk
        obtain ⟨hs₂, ht₂, hR2⟩ := filterMapM_optT_run ls
          (fun l' hl' => hF l' (List.mem_cons_of_mem _ hl')) hs₁ (hb.trans ht₁) h2
        cases o' with
        | none =>
          obtain ⟨rfl, rfl⟩ := hk2
          exact ⟨hs₂, ht₁.trans ht₂, fun _ h => by cases h⟩
        | some es =>
          try simp only at hk2
          obtain ⟨rfl, rfl⟩ := optT_pure_run hk2
          refine ⟨hs₂, ht₁.trans ht₂, fun es' hes hem => ?_⟩
          simp only [Option.some.injEq] at hes
          subst hes
          obtain ⟨hb1, hG⟩ := hR1 (some b) rfl (fun e he => by
            cases he; exact hem b List.mem_cons_self)
          obtain ⟨hes1, hGs⟩ := hR2 es rfl (fun e' he' => hem e' (List.mem_cons_of_mem _ he'))
          have hbo := hb1 b rfl
          refine ⟨by rw [OkSL_cons, okS_of_tabLe ht₂ hbo, hes1]; rfl, ?_⟩
          rw [hG]
          simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, hGs, TrSL_cons,
            TrS_of_tabLe ht₂ hbo]
          rfl

/-! ## The rule's pieces -/

/-- **The prefix variables** of a rule (`pvars`, a `mapM` in `OptionT`), read. -/
theorem pvarsI_run {sg : InLean.CState} {g : InLean.ClassGen} (hpl : g.params.length = g.nP) :
    ∀ (ls : List Nat) {s₀ s' : InLean.CState} {r : Option (List Lean.Expr)},
      CSOKI mode eager env s₀ → OkSL s₀ g.params = true →
      (ls.mapM fun i => if i < g.nP then pure (g.params.getD i default)
          else (liftM (g.slotVar (i - g.nP)) : OptionT InLean.CheckCM Lean.Expr)).run
        s₀ = .ok (r, s') →
      CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ ∃ pv, r = some pv ∧ OkSL s' pv = true ∧
        TrSL s' pv = ls.map fun i => if i < (trCG sg g).nP then (TrSL s₀ g.params).getD i default
          else (trCG sg g).slotVar (i - (trCG sg g).nP)
  | [], s₀, s', r, hs, _, h => by
    rw [List.mapM_nil] at h
    obtain ⟨rfl, rfl⟩ := optT_pure_run h
    exact ⟨hs, TabLe.refl _, [], rfl, rfl, rfl⟩
  | i :: ls, s₀, s', r, hs, hpo, h => by
    rw [List.mapM_cons] at h
    obtain ⟨o, s₁, h1, hk⟩ := optT_bind_run h
    have hA : CSOKI mode eager env s₁ ∧ TabLe s₀ s₁ ∧ ∃ a, o = some a ∧ OkS s₁ a = true ∧
        TrS s₁ a = if i < (trCG sg g).nP then (TrSL s₀ g.params).getD i default
          else (trCG sg g).slotVar (i - (trCG sg g).nP) := by
      by_cases hi : i < g.nP
      · simp only [hi, ↓reduceIte] at h1
        obtain ⟨rfl, hst⟩ := optT_pure_run h1
        rw [hst]
        have hi' : i < (trCG sg g).nP := hi
        simp only [hi', ↓reduceIte]; rw [TrSL_getD s₀ (by omega)]
        exact ⟨hs, TabLe.refl _, _, rfl, okS_getD hpo (by omega), rfl⟩
      · simp only [hi, ↓reduceIte] at h1
        have hi' : ¬ i < (trCG sg g).nP := hi
        simp only [hi', ↓reduceIte]
        obtain ⟨a, rfl, ha⟩ := liftM_run h1
        obtain ⟨hs₁, ht₁, hao, hat⟩ := slotVarI_run (sg := sg) hs ha
        exact ⟨hs₁, ht₁, a, rfl, hao, hat⟩
    obtain ⟨hs₁, ht₁, a, rfl, hao, hat⟩ := hA
    try simp only at hk
    obtain ⟨o', s₂, h2, hk2⟩ := optT_bind_run hk
    obtain ⟨hs₂, ht₂, as, rfl, haso, hast⟩ := pvarsI_run hpl ls hs₁ (okSL_of_tabLe ht₁ hpo) h2
    try simp only at hk2
    obtain ⟨rfl, rfl⟩ := optT_pure_run hk2
    refine ⟨hs₂, ht₁.trans ht₂, _, rfl, by rw [OkSL_cons, okS_of_tabLe ht₂ hao, haso]; rfl, ?_⟩
    rw [TrSL_cons, TrS_of_tabLe ht₂ hao, hat, hast, TrSL_of_tabLe ht₁ hpo, List.map_cons]

/-- The minor slot a rule applies, as master finds it. -/
theorem find?_slot_tr (s : InLean.CState) (slots : List InLean.ClassSlot) (c : Nat)
    (C : Lean.Name) :
    ((List.range (slots.map (trSlot s)).length).zip (slots.map (trSlot s))).find?
        (fun (_, sl) => match sl with
          | .minor c' C' _ => c' == c && C' == toName C | _ => false) =
      (((List.range slots.length).zip slots).find? (fun (_, sl) => match sl with
          | .minor c' C' _ => c' == c && C' == C | _ => false)).map
        (fun q => (q.1, trSlot s q.2)) := by
  rw [List.length_map]
  generalize List.range slots.length = ns
  induction slots generalizing ns with
  | nil => cases ns <;> rfl
  | cons sl slots ih =>
    cases ns with
    | nil => rfl
    | cons n ns =>
      simp only [List.map_cons, List.zip_cons_cons, List.find?_cons]
      cases sl with
      | motive k => simp only [trSlot]; exact ih ns
      | minor c' C' ihs =>
        simp only [trSlot, toName_beq]
        cases c' == c && C' == C
        · exact ih ns
        · rfl

/-- **A rule's recursive call, one field** (the body of `classGenRule`'s
`filterMapM`), read. -/
theorem ruleIhStepOk {sb sg : InLean.CState} {g : InLean.ClassGen} {ks : List InLean.ClassField}
    {fvs ws pvars : List Lean.Expr} {pvM : List ConLeche.Expr} {rP nF : Nat}
    {recOf : Nat → Option Lean.Name} {recOfM : Nat → Option ConLeche.Name}
    {rlvls : List Lean.Level} (hfv : FvsOk sb fvs) (hwo : OkSL sb ws = true)
    (hwc : ∀ w ∈ TrSL sb ws, w.looseBVarsBounded 0 = true) (hfl : fvs.length = nF)
    (hwl : ws.length = nF) (hpv : OkSL sb pvars = true) (hpvM : TrSL sb pvars = pvM)
    (hrec : ∀ t, recOfM t = (recOf t).map toName) (hrl : rlvls.all okLv = true) :
    ∀ i ∈ List.range nF, StepOkO mode eager env sb
      (do
        match ks.getD i .ordinary with
        | .ordinary => pure none
        | .recursive t tele =>
          let f := fvs.getD i default
          let (xs, idx) ← g.ihParts t tele (ws.getD i default) (rP + nF)
          let r ← liftOpt (recOf t)
          pure (some (InLean.closeLams (← xs.mapM fun x => liftM (g.binder x)) (rP + nF)
            (InLean.mkAppL (.const r rlvls) (pvars ++ idx ++ [InLean.mkAppL f xs])))) :
        OptionT InLean.CheckCM (Option Lean.Expr))
      (match (ks.map trCF).getD i .ordinary with
        | .ordinary => some none
        | .recursive t tele => do
          let f := (TrSL sb fvs).getD i default
          let (xs, idx) ← (trCG sg g).ihParts t tele ((TrSL sb ws).getD i default) (rP + nF)
          let r ← recOfM t
          pure (some (ConLeche.closeLams (xs.map (trCG sg g).binder) (rP + nF)
            (ConLeche.Expr.mkAppN (.const r (rlvls.map trL)) (pvM ++ idx ++
              [ConLeche.Expr.mkAppN f xs]))))) := by
  intro i hi s₀ s' r hs hb h
  rw [List.mem_range] at hi
  rw [getD_map_trCF]
  cases hk : ks.getD i .ordinary with
  | ordinary =>
    rw [hk] at h
    try simp only at h
    obtain ⟨rfl, rfl⟩ := optT_pure_run h
    refine ⟨hs, TabLe.refl _, fun o ho _ => ?_⟩
    simp only [Option.some.injEq] at ho
    subst ho
    exact ⟨fun e h => (by cases h), rfl⟩
  | recursive t tele =>
    rw [hk] at h
    try simp only at h
    simp only [trCF]
    have hiw : i < ws.length := by omega
    have hif : i < fvs.length := by omega
    have hw₀ : OkS s₀ (ws.getD i default) = true := okS_getD (okSL_of_tabLe hb hwo) hiw
    have hwb : OkS sb (ws.getD i default) = true := okS_getD hwo hiw
    have hwC : (TrS s₀ (ws.getD i default)).looseBVarsBounded 0 = true := by
      rw [TrS_of_tabLe hb hwb, ← TrSL_getD sb hiw]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [TrSL_length]; exact hiw),
        Option.getD_some]
      exact hwc _ (List.getElem_mem _)
    rw [TrSL_getD sb hiw, ← TrS_of_tabLe hb hwb]
    obtain ⟨o, s₁, h1, hk1⟩ := optT_bind_run h
    obtain ⟨hs₁, ht₁, hip⟩ := ihPartsI_run (sg := sg) hs hw₀ hwC h1
    cases o with
    | none =>
      obtain ⟨rfl, rfl⟩ := hk1
      exact ⟨hs₁, ht₁, fun _ h => by cases h⟩
    | some q =>
    obtain ⟨xs, idx⟩ := q
    obtain ⟨hxs, hidx, hipC⟩ := hip xs idx rfl
    erw [hipC]
    simp only [Option.bind_eq_bind, Option.bind_some]
    try simp only at hk1
    obtain ⟨o, s₂, h2, hk2⟩ := optT_bind_run hk1
    obtain ⟨rfl, hs21⟩ := liftOpt_run h2
    subst hs21
    rw [hrec t]
    cases hr : recOf t with
    | none =>
      rw [hr] at hk2
      obtain ⟨rfl, rfl⟩ := hk2
      exact ⟨hs₁, ht₁, fun _ h => by cases h⟩
    | some rn =>
    rw [hr] at hk2
    try simp only at hk2
    simp only [Option.map_some, Option.bind_some]
    simp only [InLean.ClassGen.binder] at hk2
    obtain ⟨o, s₃, h3, hk3⟩ := optT_bind_run hk2
    obtain ⟨hst, bs, rfl, hbso, hbst⟩ := mapM_binder_run hs₁ xs hxs h3
    subst hst
    try simp only at hk3
    obtain ⟨rfl, rfl⟩ := optT_pure_run hk3
    refine ⟨hs₁, ht₁, fun o ho hem => ?_⟩
    simp only [Option.some.injEq] at ho
    subst ho
    have hem' := hem _ rfl
    have hf₀ : OkS sb (fvs.getD i default) = true := okS_getD hfv.okSL hif
    have hbt := hb.trans ht₁
    have hbody : OkS s' (InLean.mkAppL (.const rn rlvls)
        (pvars ++ idx ++ [InLean.mkAppL (fvs.getD i default) xs])) = true := by
      unfold InLean.mkAppL
      rw [OkS_mkAppN, OkS_const, hrl, OkSL_append (h := OkSL_append (h := okSL_of_tabLe hbt hpv)
        (h' := hidx)) (h' := by rw [OkSL_cons, OkS_mkAppN, okS_of_tabLe hbt hf₀, hxs.okSL]; rfl)]
      rfl
    obtain ⟨ho, htr⟩ := closeLams_tr s' bs _ _ hbso hbody hem'
    rw [ConLeche.Expr.closeLamsC_eq] at htr
    refine ⟨fun e he => (by cases he; exact ho), ?_⟩
    simp only [Option.map_some, Option.pure_def, Option.some.injEq]
    rw [htr, hbst]
    unfold InLean.mkAppL
    rw [TrS_mkAppN, TrS_const, TrSL_append, TrSL_append, TrSL_of_tabLe hbt hpv, hpvM, TrSL_cons,
      TrSL_nil, TrS_mkAppN, TrS_of_tabLe hbt hf₀, ← TrSL_getD sb hif]
    rfl

/-- A marker-free application has a marker-free head and arguments. -/
theorem emvarS_mkAppN_args : ∀ (args : List Lean.Expr) (f : Lean.Expr),
    emvarS (mkAppN f args.toArray) = false → emvarS f = false ∧ ∀ a ∈ args, emvarS a = false
  | [], f, h => ⟨h, fun _ h => nomatch h⟩
  | a :: as, f, h => by
    have key := emvarS_mkAppN_args as (.app f a)
    simp only [Lean.mkAppN, List.foldl_toArray', List.foldl_cons, Lean.mkApp] at key h
    obtain ⟨h1, h2⟩ := key h
    simp only [emvarS, Bool.or_eq_false_iff] at h1
    refine ⟨h1.1, fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h1.2
    · exact h2 x hx

/-- **A generated rule** (`classGenRule`), read where InLean's closing wrote no
out-of-range marker. -/
theorem classGenRuleI_run {s₀ s' : InLean.CState} {g : InLean.ClassGen}
    {recOf : Nat → Option Lean.Name} {recOfM : Nat → Option ConLeche.Name}
    {rlvls : List Lean.Level} {c : Nat} {x : InLean.ClassCtor} {r : Option Lean.Expr}
    (hs : CSOKI mode eager env s₀) (hx : OkCC s₀ x)
    (hxD : (TrS s₀ x.tyD).looseBVarsBounded 0 = true)
    (hxN : (TrS s₀ x.tyN).looseBVarsBounded 0 = true)
    (hpre : OkSL s₀ g.pre = true) (hpar : OkSL s₀ g.params = true)
    (hpl : g.params.length = g.nP) (hrec : ∀ t, recOfM t = (recOf t).map toName)
    (hrl : rlvls.all okLv = true)
    (h : (InLean.classGenRule g recOf rlvls c x).run s₀ = .ok (r, s')) :
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ ∀ e, r = some e → emvarS e = false →
      OkS s' e = true ∧
        ConLeche.classGenRule (trCG s₀ g) recOfM (rlvls.map trL) c (trCC s₀ x) = some (TrS s' e) := by
  obtain ⟨-, hxDo, hxNo⟩ := hx
  unfold InLean.classGenRule at h
  unfold ConLeche.classGenRule
  have hprl : (trCG s₀ g).pre.length = g.pre.length := by simp [trCG, TrSL_length]
  dsimp only
  rw [hprl]
  -- the minor slot
  obtain ⟨o, s₁, h1, hk1⟩ := optT_bind_run h
  obtain ⟨rfl, hs10⟩ := liftOpt_run h1
  rw [hs10] at hk1
  erw [find?_slot_tr]
  cases hf : ((List.range g.slots.length).zip g.slots).find? (fun (_, sl) => match sl with
      | .minor c' C _ => c' == c && C == x.cv.name | _ => false) with
  | none =>
    erw [hf] at hk1
    obtain ⟨rfl, rfl⟩ := hk1
    exact ⟨hs, TabLe.refl _, fun _ h => by cases h⟩
  | some q =>
  obtain ⟨sl, slot⟩ := q
  erw [hf] at hk1 ⊢
  simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
  try simp only at hk1
  -- the fields
  obtain ⟨o, sA, h2, hk2⟩ := optT_bind_run hk1
  simp only [InLean.openPisO, OptionT.run, OptionT.mk] at h2
  unfold InLean.openPisAtFvars at h2
  obtain ⟨hs₁, ht₁, hop⟩ := openPisAtFvarsI_run _ _ hs hxDo hxD h2
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := hk2
    exact ⟨hs₁, ht₁, fun _ h => by cases h⟩
  | some q =>
  obtain ⟨fvs, res⟩ := q
  obtain ⟨hfo, hro, hopC⟩ := hop fvs res rfl
  rw [ConLeche.Cached.openPisAtFvarsC_eq] at hopC
  have hfv : FvsOk sA fvs := fvsOk_of_open hfo hopC
  have hfl : fvs.length = x.nF := by
    have := ConLeche.Verify.openPisAtFvars_length _ hopC
    rwa [TrSL_length] at this
  have hxN₁ := okS_of_tabLe ht₁ hxNo
  obtain ⟨hwo, hwC⟩ := targetPiDomsWith_tr fvs x.tyN hfo hfv.lbb hxN₁
  rw [ConLeche.Expr.targetPiDomsWithC_eq] at hwC
  rw [TrS_of_tabLe ht₁ hxNo] at hwC
  simp only [trCC]
  rw [hopC]
  simp only [Option.bind_some]
  try simp only at hk2
  -- the domains
  obtain ⟨o, s₂, h3, hk3⟩ := optT_bind_run hk2
  obtain ⟨rfl, hs21⟩ := liftOpt_run h3
  rw [hs21] at hk3
  cases hw : InLean.targetPiDomsWith fvs x.tyN with
  | none =>
    rw [hw] at hk3
    obtain ⟨rfl, rfl⟩ := hk3
    exact ⟨hs₁, ht₁, fun _ h => by cases h⟩
  | some ws =>
  rw [hw] at hk3 hwC
  simp only [Option.map_some] at hwC
  rw [hwC]
  simp only [Option.bind_some]
  try simp only at hk3
  have hws := hwo ws hw
  have hwl : ws.length = fvs.length := by
    have := ConLeche.targetPiDomsWith_length _ _ _ hwC
    rwa [TrSL_length, TrSL_length] at this
  have hwc : ∀ w ∈ TrSL sA ws, w.looseBVarsBounded 0 = true :=
    lbb_targetPiDomsWith hwC hxN (fun a ha => by
      simp only [TrSL, List.mem_map] at ha
      obtain ⟨a', ha', rfl⟩ := ha
      exact hfv.lbb a' ha')
  -- the prefix variables
  obtain ⟨o, s₃, h4, hk4⟩ := optT_bind_run hk3
  obtain ⟨hs₃, ht₃, pv, rfl, hpvo, hpvt⟩ := pvarsI_run (sg := s₀) hpl _ hs₁ (okSL_of_tabLe ht₁ hpar) h4
  rw [TrSL_of_tabLe ht₁ hpar] at hpvt
  try simp only at hk4
  -- the recursive calls
  obtain ⟨o, s₄, h5, hk5⟩ := optT_bind_run hk4
  obtain ⟨hs₄, ht₄, hR5⟩ := filterMapM_optT_run (List.range _)
    (ruleIhStepOk (sg := s₀) (ks := x.kinds) (rP := g.pre.length) (nF := x.nF)
      (recOfM := recOfM) (hfv.mono ht₃).1 (okSL_of_tabLe ht₃ hws)
      (by rw [TrSL_of_tabLe ht₃ hws]; exact hwc) (by omega) (by omega) hpvo hpvt hrec hrl)
    hs₃ (TabLe.refl _) h5
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := hk5
    exact ⟨hs₄, (ht₁.trans ht₃).trans ht₄, fun _ h => by cases h⟩
  | some ihs =>
  try simp only at hk5
  -- the binders and the minor's variable
  simp only [InLean.ClassGen.binder] at hk5
  obtain ⟨o, s₅, h6, hk6⟩ := optT_bind_run hk5
  obtain ⟨hst, bs, rfl, hbso, hbst⟩ := mapM_binder_run hs₄ fvs ((hfv.mono (ht₃.trans ht₄)).1) h6
  subst hst
  try simp only at hk6
  obtain ⟨o, s₆, h7, hk7⟩ := optT_bind_run hk6
  obtain ⟨v, rfl, hv⟩ := liftM_run h7
  obtain ⟨hs₆, ht₆, hvo, hvt⟩ := slotVarI_run (sg := s₀) hs₄ hv
  try simp only at hk7
  obtain ⟨rfl, rfl⟩ := optT_pure_run hk7
  refine ⟨hs₆, ((ht₁.trans ht₃).trans ht₄).trans ht₆, fun e he hem => ?_⟩
  simp only [Option.some.injEq] at he
  subst he
  have hemi : ∀ e ∈ ihs, emvarS e = false := fun e he =>
    (emvarS_mkAppN_args _ _ (emvarS_closeLams _ _ _ hem).2).2 e (List.mem_append_right _ he)
  obtain ⟨hihso, hihsC⟩ := hR5 ihs rfl hemi
  have ht₁₆ := (ht₃.trans ht₄).trans ht₆
  have hfo₆ := okSL_of_tabLe ht₁₆ hfo
  have hbody : OkS s' (InLean.mkAppL v (fvs ++ ihs)) = true := by
    unfold InLean.mkAppL
    rw [OkS_mkAppN, hvo, OkSL_append (h := hfo₆) (h' := okSL_of_tabLe ht₆ hihso)]
    rfl
  obtain ⟨ho, htr⟩ := closeLams_tr s' (g.pre ++ bs) 0 _
    (OkSL_append (h := okSL_of_tabLe (((ht₁.trans ht₃).trans ht₄).trans ht₆) hpre)
      (h' := okSL_of_tabLe ht₆ hbso)) hbody hem
  rw [ConLeche.Expr.closeLamsC_eq] at htr
  refine ⟨ho, ?_⟩
  rw [(hfv.mono ht₃).2, TrSL_of_tabLe ht₃ hws] at hihsC
  erw [hihsC]
  simp only [Option.bind_some, Option.pure_def, Option.some.injEq]
  rw [htr, TrSL_append, TrSL_of_tabLe (((ht₁.trans ht₃).trans ht₄).trans ht₆) hpre,
    TrSL_of_tabLe ht₆ hbso, hbst, TrSL_of_tabLe (ht₃.trans ht₄) hfo]
  unfold InLean.mkAppL
  rw [TrS_mkAppN, hvt, TrSL_append, TrSL_of_tabLe ht₁₆ hfo, TrSL_of_tabLe ht₆ hihso]
  rfl

end InLeanProof

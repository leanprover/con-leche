module

public import InLeanProof.PassRecs7
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.Cached.IndWalksC

/-!
# O7-recursors: the stream's recursors against the generated ones (task #451, round 6)

`streamRecsCheck` (InLean's at `.verified`) against master's at
`fueledOpsM .verified`, bottom-up:

* `ruleAgreeI_run`: one stored rule against the generated one (closed
  readings, both inferred, their types and they compared);
* `streamRulesCheckI_run`, `streamRulesShapeI_run`: the rules, their shape;
* `recDomsAtI_run`, `recTyCheckI_run`: a stored recursor type against the
  generated one, opened binder by binder (`FvAt`: the opened variables at
  their positions, `fvAt_of_open`);
* `streamRecCompareI_run`: the type unless equal, then the rules.
-/

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached

/-- **One stored rule against the generated one** (`ruleAgree`): both
with closed readings, at the job's environment. -/
theorem ruleAgreeI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    {rec ctor : Lean.Name} {lps : List Lean.Name} {sr g : Lean.Expr} {s₀ s' : InLean.CState}
    (hs : CSOKI .verified false L s₀) (hokS : okC sr = true) (hokG : okC g = true)
    (hlbbG : (trC g).looseBVarsBounded 0 = true)
    (h : InLean.ruleAgree .verified fe rec ctor lps sr g s₀ =
      .ok ((), s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.ruleAgree (ConLeche.fueledOpsM .verified) (ConLeche.mkFEnv L)
        (toName rec) (toName ctor) (lps.map toName) (trC sr) (trC g)) () := by
  unfold InLean.ruleAgree at h
  have hth : ∀ {α : Type} {e : InLean.CheckError} {k : α → InLean.CheckCM Unit} {s : InLean.CState},
      ¬ ((throw e : InLean.CheckCM α) >>= k) s = .ok ((), s') := fun h => by
    obtain ⟨_, _, h1, -⟩ := bind_run h; exact throw_run h1
  have hr := RangeOk_of_okE hokS
  have hfS : sr.hasFVar = false := by rw [Expr.hasFVar_eq hr]; exact fvarS_of_okC hokS
  have hfG : g.hasFVar = false := by
    rw [Expr.hasFVar_eq (RangeOk_of_okE hokG)]; exact fvarS_of_okC hokG
  cases g1 : sr.hasLooseBVars <;>
    simp only [g1, hfS, hfG, Bool.not_true, Bool.not_false, Bool.and_true, Bool.false_eq_true,
      ↓reduceIte] at h <;> try exact absurd h hth
  have hlbb := lbb_trC_of_range hr hokS g1
  obtain ⟨l, s₁, hl, h⟩ := bindI_ok h
  obtain ⟨hs1, rfl⟩ := allLevelParamsDefined_noFVar hfS hl
  rw [hs1] at h
  cases gl : (!sr.hasLevelParam || (EO.levelParams sr).all lps.contains) <;>
    simp only [gl, Bool.false_eq_true, ↓reduceIte] at h <;> try exact absurd h hth
  have hlp : (trC sr).allLevelParamsDefined (lps.map toName) = true :=
    allLevelParamsDefined_of_guard hr fun hh => by simpa [hh] using gl
  obtain ⟨c, s₁, hc, h⟩ := bindI_ok h
  have hc' : InLean.constsResolveF fe sr s₀ = .ok (c, s₁) := hc
  rw [constsResolveF_state hc'] at h
  cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] at h <;> try exact absurd h hth
  have gR := constsResolveF_tr hJ.pres hokS hc'
  -- the two inferences
  obtain ⟨ts, s₂, hI1, h⟩ := bindI_ok h
  obtain ⟨hs₂, ht₂, hok₂, hR2, hw₂, hl₂⟩ := tripleI_iff_run.1 (hJ.ops.infer (s₀ := s₀) (d := 0)
    (i := sr) hs (OkS_of_okC _ hokS) (by rw [TrS_of_okC _ hokS]; exact trC_wscoped 0 _)
    (by rw [TrS_of_okC _ hokS]; exact hlbb)) ts s₂ hI1
  obtain ⟨tg, s₃, hI2, h⟩ := bindI_ok h
  obtain ⟨hs₃, ht₃, hok₃, hR3, hw₃, hl₃⟩ := tripleI_iff_run.1 (hJ.ops.infer (s₀ := s₂) (d := 0)
    (i := g) hs₂ (OkS_of_okC _ hokG) (by rw [TrS_of_okC _ hokG]; exact trC_wscoped 0 _)
    (by rw [TrS_of_okC _ hokG]; exact hlbbG)) tg s₃ hI2
  rw [TrS_of_okC _ hokS] at hR2
  rw [TrS_of_okC _ hokG] at hR3
  have e₂ := TrS_of_tabLe ht₃ hok₂
  -- the types compared
  obtain ⟨b1, s₄, hD1, h⟩ := bindI_ok h
  obtain ⟨hs₄, ht₄, hR4⟩ := tripleI_iff_run.1 (hJ.ops.defeq (s₀ := s₃) (d := 0) (i := ts) (j := tg)
    hs₃ (okS_of_tabLe ht₃ hok₂) hok₃ (by rw [e₂]; exact hw₂) hw₃ (by rw [e₂]; exact hl₂) hl₃)
    b1 s₄ hD1
  rw [e₂] at hR4
  cases b1 <;> simp only [Bool.false_eq_true, ↓reduceIte] at h <;>
    first | exact absurd h hth | exact (throwI_ok h).elim | skip
  -- the terms compared
  obtain ⟨b2, s₅, hD2, h⟩ := bindI_ok h
  obtain ⟨hs₅, ht₅, hR5⟩ := tripleI_iff_run.1 (hJ.ops.defeq (s₀ := s₄) (d := 0) (i := sr) (j := g)
    hs₄ (OkS_of_okC _ hokS) (OkS_of_okC _ hokG) (by rw [TrS_of_okC _ hokS]; exact trC_wscoped 0 _)
    (by rw [TrS_of_okC _ hokG]; exact trC_wscoped 0 _) (by rw [TrS_of_okC _ hokS]; exact hlbb)
    (by rw [TrS_of_okC _ hokG]; exact hlbbG)) b2 s₅ hD2
  rw [TrS_of_okC _ hokS, TrS_of_okC _ hokG] at hR5
  cases b2 <;> simp only [Bool.false_eq_true, ↓reduceIte] at h <;>
    first | exact absurd h hth | exact (throwI_ok h).elim | skip
  obtain ⟨-, rfl⟩ := pureI_ok h
  refine ⟨hs₅, ht₂.trans (ht₃.trans (ht₄.trans ht₅)), ?_⟩
  unfold ConLeche.ruleAgree
  simp only [ConLeche.mkFEnv_env, ConLeche.constsResolveF_eq, hlbb,
    trC_hasFvar, hlp, gR, Bool.not_false, Bool.and_self, ↓reduceIte]
  refine Runs.bind hR2 (Runs.bind hR3 (Runs.bind hR4 ?_))
  simp only [↓reduceIte]
  refine Runs.bind hR5 ?_
  simp only [↓reduceIte]
  exact Runs.pure _

/-- **The stored rules against the generated ones** (`streamRulesCheck`): a
rule InLean finds equal needs no check, and its reading is master's
generated one (`trC_of_clEq`). -/
theorem streamRulesCheckI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    {rec : Lean.Name} {lps : List Lean.Name} :
    ∀ (rs : List Lean.RecursorRule) (gs : List Lean.Expr) {s₀ s' : InLean.CState},
      CSOKI .verified false L s₀ → (∀ r ∈ rs, okC r.rhs = true) →
      (∀ g ∈ gs, okC g = true ∧ (trC g).looseBVarsBounded 0 = true) →
      InLean.streamRulesCheck .verified fe rec lps rs gs s₀ =
        .ok ((), s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
        Runs (ConLeche.streamRulesCheck (ConLeche.fueledOpsM .verified) (ConLeche.mkFEnv L)
          (toName rec) (lps.map toName) (rs.map trRule) (gs.map trC)) ()
  | r :: rs, g :: gs, s₀, s', hs, hr, hg, h => by
    unfold InLean.streamRulesCheck at h
    simp only [List.map_cons]
    unfold ConLeche.streamRulesCheck
    have hrr := hr r List.mem_cons_self
    have hrs : ∀ x ∈ rs, okC x.rhs = true := fun x hx => hr x (List.mem_cons_of_mem _ hx)
    have hgg := hg g List.mem_cons_self
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    dsimp only at h ⊢
    cases hb : (r.rhs == g)
    · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨_, s₁, h1, h⟩ := bind_run h
      obtain ⟨hs₁, ht₁, hR⟩ := ruleAgreeI_run hJ hs hrr hgg.1 hgg.2 h1
      obtain ⟨hs₂, ht₂, hR2⟩ := streamRulesCheckI_run hJ rs gs hs₁ hrs hgs h
      refine ⟨hs₂, ht₁.trans ht₂, ?_⟩
      split
      · exact hR2
      · exact Runs.bind hR hR2
    · simp only [hb, ↓reduceIte] at h
      obtain ⟨hs₂, ht₂, hR2⟩ := streamRulesCheckI_run hJ rs gs hs hrs hgs h
      have he : (trRule r).rhs = trC g := trC_of_clEq hrr hgg.1 hb
      refine ⟨hs₂, ht₂, ?_⟩
      split
      · exact hR2
      · rename_i hne; simp [he] at hne
  | [], [], s₀, s', hs, _, _, h => by
    unfold InLean.streamRulesCheck at h
    obtain ⟨-, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, by unfold ConLeche.streamRulesCheck; exact Runs.pure _⟩
  | [], _ :: _, s₀, s', _, _, _, h | _ :: _, [], s₀, s', _, _, _, h => by
    unfold InLean.streamRulesCheck at h; exact (throw_run h).elim

/-- **The stored rules' shape** (`streamRulesShape`): pure guards, read. -/
theorem streamRulesShapeI_run {rec : Lean.Name} :
    ∀ (rs : List Lean.RecursorRule) (cs : List (Lean.ConstantVal × Nat)) {s₀ s' : InLean.CState},
      InLean.streamRulesShape rec rs cs s₀ = .ok ((), s') →
      s' = s₀ ∧ Runs (ConLeche.streamRulesShape (toName rec) (rs.map trRule) (cs.map trCtor) :
        ConLeche.FueledM Unit) ()
  | r :: rs, c :: cs, s₀, s', h => by
    unfold InLean.streamRulesShape at h
    simp only [List.map_cons]
    unfold ConLeche.streamRulesShape
    dsimp only at h ⊢
    cases hb : (r.ctor == c.1.name && r.nfields == c.2) <;>
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
    · obtain ⟨_, _, h1, -⟩ := bind_run h; exact (throw_run h1).elim
    obtain ⟨rfl, hR⟩ := streamRulesShapeI_run rs cs h
    refine ⟨rfl, ?_⟩
    have hb' : ((trRule r).ctor == (trCtor c).1.name && (trRule r).nfields == (trCtor c).2) = true := by
      simpa [trRule, trCtor, trCV, toName_beq] using hb
    simp only [hb', ↓reduceIte]
    exact hR
  | [], [], s₀, s', h => by
    unfold InLean.streamRulesShape at h
    obtain ⟨-, rfl⟩ := pure_run h
    exact ⟨rfl, by unfold ConLeche.streamRulesShape; exact Runs.pure _⟩
  | [], _ :: _, s₀, s', h | _ :: _, [], s₀, s', h => by
    unfold InLean.streamRulesShape at h; exact (throw_run h).elim

/-! ## The recursor type, binder by binder -/

/-- Opened variables: each reads as a variable at its own position, its
annotation scoped there. -/
@[expose] def FvAt (s : InLean.CState) (fvs : List Lean.Expr) : Prop :=
  OkSL s fvs = true ∧
    ∀ j x, fvs[j]? = some x → ∃ ty, TrS s x = .fvar j ty ∧ ConLeche.Expr.WScoped j ty

theorem FvAt.mono {s₀ s₁ : InLean.CState} (h : TabLe s₀ s₁) {fvs : List Lean.Expr}
    (hf : FvAt s₀ fvs) : FvAt s₁ fvs ∧ TrSL s₁ fvs = TrSL s₀ fvs := by
  have hok := hf.1
  simp only [OkSL, List.all_eq_true] at hok
  refine ⟨⟨okSL_of_tabLe h hf.1, fun j x hx => ?_⟩, TrSL_of_tabLe h hf.1⟩
  rw [TrS_of_tabLe h (hok x (List.mem_of_getElem? hx))]
  exact hf.2 j x hx

theorem getElem?_TrSL (s : InLean.CState) (l : List Lean.Expr) (j : Nat) :
    (TrSL s l)[j]? = l[j]?.map (TrS s) := by
  simp only [TrSL, List.getElem?_map]

/-- **The domains compared** (`recDomsAt`): at binder `j` both opened
variables' annotations, compared at depth `j`. -/
theorem recDomsAtI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    {rec : Lean.Name} {sfvs gfvs : List Lean.Expr} :
    ∀ (k j : Nat) {s₀ s' : InLean.CState},
      CSOKI .verified false L s₀ → FvAt s₀ sfvs → FvAt s₀ gfvs →
      InLean.recDomsAt .verified fe rec sfvs gfvs j k s₀ = .ok ((), s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
        Runs (ConLeche.recDomsAt (ConLeche.fueledOpsM .verified) L (toName rec) (TrSL s₀ sfvs)
          (TrSL s₀ gfvs) j k) ()
  | 0, j, s₀, s', hs, _, _, h => by
    unfold InLean.recDomsAt at h
    obtain ⟨-, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, by unfold ConLeche.recDomsAt; exact Runs.pure _⟩
  | k + 1, j, s₀, s', hs, hsf, hgf, h => by
    unfold InLean.recDomsAt at h
    unfold ConLeche.recDomsAt
    obtain ⟨a, s₁, h1, hA⟩ := bind_run h
    obtain ⟨ha, e1⟩ := unwrapOrI_run h1
    subst s₁
    obtain ⟨b, s₂, h2, hB⟩ := bind_run hA
    obtain ⟨hb, e2⟩ := unwrapOrI_run h2
    subst s₂
    obtain ⟨ta, s₃, h3, hC⟩ := bind_run hB
    have hoa : OkS s₀ a = true := by
      have := hsf.1; simp only [OkSL, List.all_eq_true] at this
      exact this a (List.mem_of_getElem? ha)
    have hob : OkS s₀ b = true := by
      have := hgf.1; simp only [OkSL, List.all_eq_true] at this
      exact this b (List.mem_of_getElem? hb)
    obtain ⟨tya, hta, hwa⟩ := hsf.2 j a ha
    obtain ⟨tyb, htb, hwb⟩ := hgf.2 j b hb
    obtain ⟨hs1, hota, htta, hla⟩ := fvarTypeDI_run hs hoa hta h3
    subst s₃
    obtain ⟨tb, s₄, h4, hD⟩ := bind_run hC
    obtain ⟨hs2, hotb, httb, hlb⟩ := fvarTypeDI_run hs hob htb h4
    subst s₄
    obtain ⟨c, s₂, h2, h⟩ := bind_run hD
    obtain ⟨hs₂, ht₂, hR⟩ := tripleI_iff_run.1 (hJ.ops.defeq (s₀ := s₀) (d := j) (i := ta) (j := tb)
      hs hota hotb (by rw [htta]; exact hwa) (by rw [httb]; exact hwb) (by rw [htta]; exact hla)
      (by rw [httb]; exact hlb)) c s₂ h2
    rw [htta, httb] at hR
    cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
    · obtain ⟨_, _, h3, -⟩ := bind_run h; exact (throw_run h3).elim
    obtain ⟨hsf₂, hsfT⟩ := hsf.mono ht₂
    obtain ⟨hgf₂, hgfT⟩ := hgf.mono ht₂
    obtain ⟨hs₃, ht₃, hR3⟩ := recDomsAtI_run hJ k (j + 1) hs₂ hsf₂ hgf₂ h
    rw [hsfT, hgfT] at hR3
    refine ⟨hs₃, ht₂.trans ht₃, ?_⟩
    simp only [getElem?_TrSL, ha, hb, Option.map_some, ConLeche.unwrapOr, hta, htb,
      ConLeche.Expr.fvarTypeD]
    rw [Runs.pure_bind_eq, Runs.pure_bind_eq]
    refine Runs.bind hR ?_
    simp only [↓reduceIte]
    exact hR3

/-- An opening, read: its variables are at their positions (`FvAt`). -/
theorem fvAt_of_open {s' : InLean.CState} {n : Nat} {E : ConLeche.Expr} {fvs : List Lean.Expr}
    {B : ConLeche.Expr} (hok : OkSL s' fvs = true) (hw : ConLeche.Expr.WScoped 0 E)
    (h : ConLeche.openPisAtFvars n E 0 = some (TrSL s' fvs, B)) : FvAt s' fvs := by
  refine ⟨hok, fun j x hx => ?_⟩
  have hx' : (TrSL s' fvs)[j]? = some (TrS s' x) := by rw [getElem?_TrSL, hx]; rfl
  obtain ⟨ty, hty⟩ := ConLeche.openPisAtFvars_index n _ 0 h j _ hx'
  have hwt := ConLeche.openPisAtFvars_typeWScoped n h hw j _ hx'
  rw [Nat.zero_add] at hty hwt
  refine ⟨ty, hty, ?_⟩
  rw [hty] at hwt
  exact hwt

/-- **A stored recursor type against the generated one** (`recTyCheck`):
the stored type with a closed reading, the generated one closed. -/
theorem recTyCheckI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    {rec : Lean.Name} {lps : List Lean.Name} {n : Nat} {sT gT : Lean.Expr} {s₀ s' : InLean.CState}
    (hs : CSOKI .verified false L s₀) (hokS : okC sT = true) (hokG : okC gT = true)
    (hlbbG : (trC gT).looseBVarsBounded 0 = true)
    (h : InLean.recTyCheck .verified fe rec lps n sT gT s₀ =
      .ok ((), s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.recTyCheck (ConLeche.fueledOpsM .verified) (ConLeche.mkFEnv L)
        (toName rec) (lps.map toName) n (trC sT) (trC gT)) () := by
  unfold InLean.recTyCheck at h
  have hth : ∀ {α : Type} {e : InLean.CheckError} {k : α → InLean.CheckCM Unit} {s : InLean.CState},
      ¬ ((throw e : InLean.CheckCM α) >>= k) s = .ok ((), s') := fun h => by
    obtain ⟨_, _, h1, -⟩ := bind_run h; exact throw_run h1
  have hr := RangeOk_of_okE hokS
  have hfS : sT.hasFVar = false := by rw [Expr.hasFVar_eq hr]; exact fvarS_of_okC hokS
  have hfG : gT.hasFVar = false := by
    rw [Expr.hasFVar_eq (RangeOk_of_okE hokG)]; exact fvarS_of_okC hokG
  cases g1 : sT.hasLooseBVars <;>
    simp only [g1, hfS, hfG, Bool.not_true, Bool.not_false, Bool.and_true, Bool.false_eq_true,
      ↓reduceIte] at h <;> try exact absurd h hth
  have hlbb := lbb_trC_of_range hr hokS g1
  obtain ⟨l, s₁, hl, h⟩ := bindI_ok h
  obtain ⟨hs1, rfl⟩ := allLevelParamsDefined_noFVar hfS hl
  rw [hs1] at h
  cases gl : (!sT.hasLevelParam || (EO.levelParams sT).all lps.contains) <;>
    simp only [gl, Bool.false_eq_true, ↓reduceIte] at h <;> try exact absurd h hth
  have hlp : (trC sT).allLevelParamsDefined (lps.map toName) = true :=
    allLevelParamsDefined_of_guard hr fun hh => by simpa [hh] using gl
  obtain ⟨c, s₁, hc, h⟩ := bindI_ok h
  have hc' : InLean.constsResolveF fe sT s₀ = .ok (c, s₁) := hc
  rw [constsResolveF_state hc'] at h
  cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] at h <;> try exact absurd h hth
  have gR := constsResolveF_tr hJ.pres hokS hc'
  -- the stored type is a type
  obtain ⟨st, s₂, hI1, h⟩ := bindI_ok h
  obtain ⟨hs₂, ht₂, hok₂, hR2, hw₂, hl₂⟩ := tripleI_iff_run.1 (hJ.ops.infer (s₀ := s₀) (d := 0)
    (i := sT) hs (OkS_of_okC _ hokS) (by rw [TrS_of_okC _ hokS]; exact trC_wscoped 0 _)
    (by rw [TrS_of_okC _ hokS]; exact hlbb)) st s₂ hI1
  rw [TrS_of_okC _ hokS] at hR2
  obtain ⟨u, s₃, hI2, h⟩ := bindI_ok h
  obtain ⟨hs₃, ht₃, -, hR3⟩ := tripleI_iff_run.1 (hJ.ops.sort (s₀ := s₂) (d := 0) (i := st) hs₂ hok₂
    hw₂ hl₂) u s₃ hI2
  -- the two openings
  obtain ⟨os, s₄, hO1, h⟩ := bindI_ok h
  obtain ⟨hs₄, ht₄, hos⟩ := openPisAtFvarsI_run n 0 hs₃ (OkS_of_okC _ hokS)
    (by rw [TrS_of_okC _ hokS]; exact hlbb) hO1
  obtain ⟨og, s₅, hO2, h⟩ := bindI_ok h
  obtain ⟨hs₅, ht₅, hog⟩ := openPisAtFvarsI_run n 0 hs₄ (OkS_of_okC _ hokG)
    (by rw [TrS_of_okC _ hokG]; exact hlbbG) hO2
  rw [TrS_of_okC _ hokS] at hos
  rw [TrS_of_okC _ hokG] at hog
  have hth' : ∀ {e : InLean.CheckError} {s : InLean.CState},
      ¬ (throw e : InLean.CheckCM Unit) s = .ok ((), s') := fun h => throw_run h
  rcases os with _ | ⟨sf, sb⟩
  · unfold InLean.recTyOpened at h; exact absurd h hth'
  rcases og with _ | ⟨gf, gb⟩
  · unfold InLean.recTyOpened at h; exact absurd h hth'
  obtain ⟨hsfo, hsbo, hopS⟩ := hos sf sb rfl
  obtain ⟨hgfo, hgbo, hopG⟩ := hog gf gb rfl
  rw [ConLeche.Cached.openPisAtFvarsC_eq] at hopS hopG
  have hfS := fvAt_of_open hsfo (trC_wscoped 0 _) hopS
  have hfG := fvAt_of_open hgfo (trC_wscoped 0 _) hopG
  obtain ⟨hfS₅, hfST⟩ := hfS.mono ht₅
  unfold InLean.recTyOpened at h
  obtain ⟨_, s₆, h6, h⟩ := bindI_ok h
  obtain ⟨hs₆, ht₆, hR6⟩ := recDomsAtI_run hJ n 0 hs₅ hfS₅ hfG h6
  rw [hfST] at hR6
  obtain ⟨b, s₇, h7, h⟩ := bindI_ok h
  have hbS := ConLeche.Verify.openPisAtFvars_bounded n hopS hlbb
  have hbG := ConLeche.Verify.openPisAtFvars_bounded n hopG hlbbG
  have hwS := (ConLeche.openPisAtFvars_WScoped n _ 0 hopS (trC_wscoped 0 _)).2
  have hwG := (ConLeche.openPisAtFvars_WScoped n _ 0 hopG (trC_wscoped 0 _)).2
  rw [Nat.zero_add] at hwS hwG
  have ht46 := ht₅.trans ht₆
  have eS := TrS_of_tabLe ht46 hsbo
  have eG := TrS_of_tabLe ht₆ hgbo
  obtain ⟨hs₇, ht₇, hR7⟩ := tripleI_iff_run.1 (hJ.ops.defeq (s₀ := s₆) (d := n) (i := sb) (j := gb)
    hs₆ (okS_of_tabLe ht46 hsbo) (okS_of_tabLe ht₆ hgbo) (by rw [eS]; exact hwS)
    (by rw [eG]; exact hwG) (by rw [eS]; exact hbS.1) (by rw [eG]; exact hbG.1)) b s₇ h7
  rw [eS, eG] at hR7
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
  · exact absurd h hth'
  obtain ⟨-, rfl⟩ := pureI_ok h
  refine ⟨hs₇, ht₂.trans (ht₃.trans (ht₄.trans (ht46.trans ht₇))), ?_⟩
  unfold ConLeche.recTyCheck
  simp only [ConLeche.mkFEnv_env, ConLeche.constsResolveF_eq, hlbb,
    trC_hasFvar, hlp, gR, Bool.not_false, Bool.and_self, ↓reduceIte]
  refine Runs.bind hR2 (Runs.bind hR3 ?_)
  rw [hopS, hopG]
  unfold ConLeche.recTyOpened
  refine Runs.bind hR6 (Runs.bind hR7 ?_)
  simp only [↓reduceIte]
  exact Runs.pure _

/-- **One stored recursor's type and rules against the generated one's**
(`streamRecCompare`): a type InLean finds equal needs no check, its reading
is master's generated one. -/
theorem streamRecCompareI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    {rc : InLean.RecShape} {g : Lean.ConstantVal × InLean.TargetMajor × List Lean.Expr}
    (sx : InLean.CState) {s₀ s' : InLean.CState} (hs : CSOKI .verified false L s₀)
    (hokS : okC rc.cvR.type = true) (hrl : ∀ r ∈ rc.rules, okC r.rhs = true)
    (hokG : okC g.1.type = true) (hlbbG : (trC g.1.type).looseBVarsBounded 0 = true)
    (hgr : ∀ r ∈ g.2.2, okC r = true ∧ (trC r).looseBVarsBounded 0 = true)
    (h : InLean.streamRecCompare .verified fe rc g s₀ = .ok ((), s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.streamRecCompare (ConLeche.fueledOpsM .verified) (ConLeche.mkFEnv L)
        (trRec rc) (trOut sx g)) () := by
  unfold InLean.streamRecCompare at h
  unfold ConLeche.streamRecCompare
  have hgT : (trOut sx g).2.2 = g.2.2.map trC := TrSL_of_okC sx fun r hr => (hgr r hr).1
  simp only [trOut, trRec, trCV] at hgT ⊢
  rw [hgT]
  dsimp only at h ⊢
  cases hb : (rc.cvR.type == g.1.type)
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨_, s₁, h1, h⟩ := bind_run h
    obtain ⟨hs₁, ht₁, hR⟩ := recTyCheckI_run hJ hs hokS hokG hlbbG h1
    obtain ⟨hs₂, ht₂, hR2⟩ := streamRulesCheckI_run hJ rc.rules g.2.2 hs₁ hrl hgr h
    refine ⟨hs₂, ht₁.trans ht₂, ?_⟩
    by_cases hm : trC rc.cvR.type = trC g.fst.type
    · simp only [hm, beq_self_eq_true, ↓reduceIte]; exact hR2
    · simp only [beq_iff_eq, hm, ↓reduceIte]; exact Runs.bind hR hR2
  · simp only [hb, ↓reduceIte] at h
    obtain ⟨hs₂, ht₂, hR2⟩ := streamRulesCheckI_run hJ rc.rules g.2.2 hs hrl hgr h
    have he : trC rc.cvR.type = trC g.1.type := trC_of_clEq hokS hokG hb
    refine ⟨hs₂, ht₂, ?_⟩
    simp only [he, beq_self_eq_true, ↓reduceIte]
    exact hR2

end InLeanProof

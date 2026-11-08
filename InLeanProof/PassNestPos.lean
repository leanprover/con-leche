module

public import InLeanProof.PassNestPos0
import ConLeche.Verify.Inductives.NestScope

/-!
# O7-positivity: the positivity walk against master's (task #451, lane O7-positivity)

The walk's monadic steps, each master's on the readings of
`PassNestPos0.lean`, functional (`bind_run`, `pure_run`) as O7's:

* `RecSpecI`: what a walk's recursive call provides (the twin of master's
  cached `RecSpec`, `Verify/Cached/NestPosC.lean`): at a readable input,
  well scoped at its depth and closed, a successful run answers master's
  on the readings, its normal form readable, scoped and closed, the state's
  records readable.
* `nestFieldsI_run`: a constructor's field telescope through the recursion.
-/

public section

namespace InLeanProof

open Lean InLean ConLeche.Cached

/-- A term with a reading at a state, well scoped at depth `d` and closed. -/
@[expose] def TOk (s : InLean.CState) (d : Nat) (e : Lean.Expr) : Prop :=
  OkS s e = true ∧ ConLeche.Expr.WScoped d (TrS s e) ∧ (TrS s e).looseBVarsBounded 0 = true

theorem TOk.mono {s₀ s₁ : InLean.CState} (ht : TabLe s₀ s₁) {d : Nat} {e : Lean.Expr}
    (h : TOk s₀ d e) : TOk s₁ d e ∧ TrS s₁ e = TrS s₀ e := by
  have he := TrS_of_tabLe ht h.1
  exact ⟨⟨okS_of_tabLe ht h.1, he ▸ h.2.1, he ▸ h.2.2⟩, he⟩

/-- **The triple a walk's recursive call provides** (master's `RecSpec`'s
twin). -/
@[expose] def RecSpecI (fe : InLean.FEnv) (L : ConLeche.Env) (ctx : InLean.NestCtx)
    (cctx : ConLeche.NestCtx) (rec : InLean.NestRec)
    (rec' : List ConLeche.NestHole → Nat → Nat → ConLeche.Expr → ConLeche.NestState →
      ConLeche.FueledM (ConLeche.NestFieldKind × ConLeche.Expr × ConLeche.NestState)) : Prop :=
  ∀ (prog : List InLean.NestHole) (dep kb : Nat) (e : Lean.Expr) (st : InLean.NestState)
    {s₀ s' : InLean.CState} {v : InLean.NestFieldKind × Lean.Expr × InLean.NestState},
    CSOKI .verified false L s₀ → WalkRel fe L s₀ ctx cctx → ProgOk s₀ prog → StOk s₀ st →
    TOk s₀ dep e → rec prog dep kb e st s₀ = .ok (v, s') →
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ TOk s' dep v.2.1 ∧ StOk s' v.2.2 ∧
      Runs (rec' (prog.map (trHole s₀)) dep kb (TrS s₀ e) (trSt s₀ st))
        (trNK v.1, TrS s' v.2.1, trSt s' v.2.2)

/-- A telescope of readable domains, the `k`-th scoped at `i + k`, all closed. -/
@[expose] def TeleOk (s : InLean.CState) (i : Nat) (nds : List Lean.Expr) : Prop :=
  OkSL s nds = true ∧ TeleWS i (TrSL s nds) ∧ ∀ nd ∈ nds, (TrS s nd).looseBVarsBounded 0 = true

theorem TeleOk.mono {s₀ s₁ : InLean.CState} (ht : TabLe s₀ s₁) {i : Nat} {nds : List Lean.Expr}
    (h : TeleOk s₀ i nds) : TeleOk s₁ i nds ∧ TrSL s₁ nds = TrSL s₀ nds := by
  have he := TrSL_of_tabLe ht h.1
  exact ⟨⟨okSL_of_tabLe ht h.1, he ▸ h.2.1, closed_of_tabLe ht h.1 h.2.2⟩, he⟩

/-- **A constructor's field telescope** (`nestFields`): each field through
the recursion at its depth, opened at an interned variable; master's on the
readings (at any error value: only the success is simulated). -/
theorem nestFieldsI_run {fe : InLean.FEnv} {L : ConLeche.Env} {ctx : InLean.NestCtx}
    {cctx : ConLeche.NestCtx} {rec : InLean.NestRec}
    {rec' : List ConLeche.NestHole → Nat → Nat → ConLeche.Expr → ConLeche.NestState →
      ConLeche.FueledM (ConLeche.NestFieldKind × ConLeche.Expr × ConLeche.NestState)}
    (hrec : RecSpecI fe L ctx cctx rec rec') (prog : List InLean.NestHole) (base : Nat)
    (err : InLean.CheckError) (err' : ConLeche.CheckError) :
    ∀ (nF j : Nat) (cur : Lean.Expr) (st : InLean.NestState) {s₀ s' : InLean.CState}
      {v : List InLean.NestFieldKind × List Lean.Expr × Lean.Expr × InLean.NestState},
      CSOKI .verified false L s₀ → WalkRel fe L s₀ ctx cctx → ProgOk s₀ prog → StOk s₀ st →
      TOk s₀ (base + j) cur →
      InLean.nestFields rec prog base err nF j cur st s₀ = .ok (v, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ TeleOk s' (base + j) v.2.1 ∧
        TOk s' (base + j + v.2.1.length) v.2.2.1 ∧ StOk s' v.2.2.2 ∧
        Runs (ConLeche.nestFields rec' (prog.map (trHole s₀)) base err' nF j (TrS s₀ cur)
          (trSt s₀ st)) (v.1.map trNK, TrSL s' v.2.1, TrS s' v.2.2.1, trSt s' v.2.2.2)
  | 0, j, cur, st, s₀, s', v, hs, _, _, hst, hcur, h => by
    unfold InLean.nestFields at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    refine ⟨hs, TabLe.refl _, ⟨rfl, by simp [TrSL, TeleWS], by simp⟩, by simpa using hcur, hst, ?_⟩
    unfold ConLeche.nestFields
    exact Runs.pure _
  | nF + 1, j, cur, st, s₀, s', v, hs, hW, hp, hst, hcur, h => by
    unfold InLean.nestFields at h
    have hT : TrS s₀ cur = TrS s₀ (EO.stripTop cur) := (TrS_stripTop s₀ cur).symm
    have hOk : OkS s₀ (EO.stripTop cur) = true := by rw [OkS_stripTop]; exact hcur.1
    have hnm : ∀ m b, EO.stripTop cur ≠ .mdata m b := fun m b he => stripTop_ne_mdata he
    obtain ⟨-, hwc, hcc⟩ := hcur
    rw [hT] at hwc hcc ⊢
    generalize EO.stripTop cur = x at h hOk hnm hwc hcc
    cases x with
    | forallE nm a b bi =>
      simp only at h
      simp only [OkS_forallE, Bool.and_eq_true] at hOk
      rw [TrS_forallE] at hwc hcc ⊢
      rw [lbb_forallE, Bool.and_eq_true] at hcc
      simp only [ConLeche.Expr.WScoped] at hwc
      obtain ⟨⟨k, nd, st₁⟩, s₁, h1, h⟩ := bind_run h
      obtain ⟨hs₁, ht₁, hnd, hst₁, hR1⟩ :=
        hrec prog (base + j) 0 a st hs hW hp hst ⟨hOk.1, hwc.1, hcc.1⟩ h1
      obtain ⟨r, s₂, h2, h⟩ := bind_run h
      have hoka₁ := okS_of_tabLe ht₁ hOk.1
      have hta₁ := TrS_of_tabLe ht₁ hOk.1
      obtain ⟨hs₂, ht₂, hokr, htrr⟩ := tripleI_iff_run.1
        (mkFVarM_specI hs₁ (base + j) hoka₁ (by rw [hta₁]; exact hcc.1)) r s₂ h2
      rw [hta₁] at htrr
      obtain ⟨⟨ks, nds, res, st₂⟩, s₃, h3, h⟩ := bind_run h
      obtain ⟨rfl, rfl⟩ := pure_run h
      have ht12 := ht₁.trans ht₂
      have hokb := okS_of_tabLe ht12 hOk.2
      have htb := TrS_of_tabLe ht12 hOk.2
      have hrcl : (TrS s₂ r).looseBVarsBounded 0 = true := by
        rw [htrr]; rfl
      have hTI : TrS s₂ (b.inst1I r) =
          (TrS s₀ b).instantiate1 (.fvar (base + j) (TrS s₀ a)) 0 := by
        rw [inst1I_eq, TrS_inst1_eq hokb hokr hrcl, htb, htrr]
      have hcur₂ : TOk s₂ (base + (j + 1)) (b.inst1I r) := by
        refine ⟨OkS_inst1 hokb hokr hrcl, ?_, ?_⟩
        · rw [hTI, show base + (j + 1) = base + j + 1 by omega]
          exact ConLeche.Expr.WScoped.instantiate1 hwc.1 0 hwc.2
        · rw [hTI]; exact lbb_instantiate1 rfl hcc.2
      obtain ⟨hW₂, hp₂, hst₂⟩ : WalkRel fe L s₂ ctx cctx ∧ ProgOk s₂ prog ∧ StOk s₂ st₁ :=
        ⟨hW.mono ht12, (hp.mono ht12).1, (hst₁.mono ht₂).1⟩
      obtain ⟨hs₃, ht₃, hnds, hres, hst₃, hR3⟩ :=
        nestFieldsI_run hrec prog base err err' nF (j + 1) (b.inst1I r) st₁ hs₂ hW₂ hp₂ hst₂
          hcur₂ h3
      have ht23 := ht₂.trans ht₃
      obtain ⟨hnd₃, hndE⟩ := TOk.mono ht23 hnd
      refine ⟨hs₃, ht12.trans ht₃, ⟨?_, ?_, ?_⟩, ?_, hst₃, ?_⟩
      · simp only [OkSL_cons, hnd₃.1, hnds.1, Bool.and_self]
      · rw [TrSL_cons, TeleWS.cons_eq, hndE]
        exact ⟨hnd.2.1, by rw [show base + j + 1 = base + (j + 1) by omega]; exact hnds.2.1⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hnd₃.2.2
        · exact hnds.2.2 x hx
      · simp only [List.length_cons, show base + j + (nds.length + 1) = base + (j + 1) + nds.length
          by omega]
        exact hres
      · unfold ConLeche.nestFields
        simp only
        refine Runs.bind hR1 ?_
        rw [hTI, (hp.mono ht12).2] at hR3
        have hst12 : trSt s₂ st₁ = trSt s₁ st₁ := (hst₁.mono ht₂).2
        rw [hst12] at hR3
        simp only [List.map_cons, TrSL_cons, hndE]
        refine Runs.bind hR3 ?_
        exact Runs.pure _
    | mdata m b => exact (hnm m b rfl).elim
    | _ => simp only at h; exact (throw_run h).elim

end InLeanProof

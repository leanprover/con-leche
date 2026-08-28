import Setlec.TTVerify.StdAxiomKey
import Setlec.Verify.NatOpFrag

/-!
# The structural-`Nat` recurrence pin

`NatOpPinTT`, the obligation `DeclDefnTT` left at `certifyNatEqs`.

The content is `denote_substConst0` (`Setlec/TTVerify/SubstConst.lean`)
plus one induction.  `certifyNatEqs` certifies the recurrences in the
**pre-insertion** environment with the operation's self-references
replaced by its stored value; the bridge moves the resulting `Deq`
across that substitution, and what it needs on the way is that both
sides of every equation *denote* and carry their frame conditions.

## The fragment, and why the guard already delimits it

`natOpEquations` are spines over `Nat.zero`, `Nat.succ`, the operation
itself, at most one dependency operation, and (for `beq`/`ble`) the two
`Bool` constructors — with two free variables and no binder anywhere.
Every one of those constants is *exactly* what `natOpGuard` checks is
stored at empty level parameters: `natLitSupported` covers `Nat.zero`
and `Nat.succ`, `natOpDeps` lists the dependency operations, and the
`beq`/`ble` branch adds the `Bool` pair.

> **`natOpDeps` was written so the checker could certify the
> recurrences; it lists precisely the constants the bridge must be able
> to denote.**  §8.4 once more, and unusually literally: the guard's
> dependency list and the bridge's denotation obligation are the same
> list.
-/

namespace Setlec.TTVerify

open Setlec.TT

/-! The fragment's *syntactic* half — `natFragOk`,
`natOpEquations_frag`, `storedNoLevels` and the `natOpGuard_*`
inversions — moved to `Setlec/Verify/NatOpFrag.lean` (task #148 T6):
both soundness routes need it and neither may import the other.  What
remains here is the one piece that is stated over an `EnvTT`. -/

/-- **Everything the claim needs about a substituted equation side**,
in one induction: its frame conditions at depth `2`, its context
correspondence in `[Nat, Nat]`, and its denotation. -/
theorem natFrag_subst_facts {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {c : Name} {v : Expr} {V : VExpr}
    (hvf : v.hasFvar = false) (hvb : v.looseBVarsBounded 0 = true)
    (hv : denoteClosed m.cval env φ v = some V)
    {d : Nat} {Δ : List VExpr} (hd : 2 ≤ d) (hlen : Δ.length = d)
    (hx : HasType Δ (.bvar (d - 1 - 0)) (m.cval natName φ))
    (hy : HasType Δ (.bvar (d - 1 - 1)) (m.cval natName φ))
    {ciN : ConstantInfo} (hfN : env.find? natName = some ciN)
    (hlpN : ciN.toConstantVal.levelParams = []) :
    ∀ e : Expr, natFragOk env c e = true →
      Expr.WScoped d (Expr.substConst0 c v e) ∧
      (Expr.substConst0 c v e).looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded (Expr.substConst0 c v e) ∧
      CtxOk m.cval env φ d Δ (Expr.substConst0 c v e) ∧
      ∃ w, denote m.cval env φ d (Expr.substConst0 c v e) = some w := by
  intro e
  induction e with
  | sort u =>
    intro _
    rw [show Expr.substConst0 c v (.sort u) = .sort u from rfl]
    exact ⟨by simp [Expr.WScoped], rfl,
      fun l hl => by simp [Expr.fvarLeaves] at hl,
      ⟨hlen, fun l hl => by simp [Expr.fvarLeaves] at hl⟩,
      _, by rw [denote_sort]⟩
  | fvar i n ty =>
    intro h
    simp only [natFragOk, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨hi01, rfl⟩ := h
    have hlt : i < d := by rcases hi01 with rfl | rfl <;> omega
    rw [show Expr.substConst0 c v (.fvar i n (.const natName []))
      = .fvar i n (.const natName []) from rfl]
    refine ⟨by simp only [Expr.WScoped]; exact ⟨hlt, trivial⟩, rfl, ?_,
      ⟨hlen, ?_⟩, VExpr.bvar (d - 1 - i), by rw [denote_fvar]⟩
    · intro l hl
      rw [Expr.fvarLeaves] at hl
      rcases List.mem_cons.mp hl with rfl | hl'
      · rfl
      · simp [Expr.fvarLeaves] at hl'
    · intro l hl
      rw [Expr.fvarLeaves] at hl
      rcases List.mem_cons.mp hl with rfl | hl'
      · refine ⟨hlt, by simp [Expr.fvarsBelow], m.cval natName φ, ?_, ?_⟩
        · exact denote_const_nolevels m φ hfN hlpN d
        · rcases hi01 with rfl | rfl
          · exact hx
          · exact hy
      · simp [Expr.fvarLeaves] at hl'
  | const n us =>
    intro h
    simp only [natFragOk, Bool.and_eq_true, List.isEmpty_iff,
      Bool.or_eq_true, decide_eq_true_eq] at h
    by_cases hn : n = c ∧ us = []
    · obtain ⟨rfl, rfl⟩ := hn
      rw [show Expr.substConst0 n v (.const n []) = v from by
        rw [Expr.substConst0, if_pos ⟨rfl, rfl⟩]]
      exact ⟨Expr.WScoped.of_not_hasFvar hvf, hvb,
        Expr.LeavesBounded.of_not_hasFvar hvf,
        ⟨hlen, fun l hl => by
          rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hvf] at hl
          exact nomatch hl⟩,
        V, by rw [denote_depth_closed m.cval_closed hvf hvb d]; exact hv⟩
    · rw [show Expr.substConst0 c v (.const n us) = .const n us from by
        rw [Expr.substConst0, if_neg (fun hh => hn ⟨hh.1, hh.2⟩)]]
      refine ⟨by simp [Expr.WScoped], rfl,
        fun l hl => by simp [Expr.fvarLeaves] at hl,
        ⟨hlen, fun l hl => by simp [Expr.fvarLeaves] at hl⟩, ?_⟩
      replace h2 : (match env.find? n with
          | some ci => us.length == ci.toConstantVal.levelParams.length
          | none => false) = true := by
        rcases h with h2 | h2
        · exact absurd h2 hn
        · exact h2
      cases hf : env.find? n with
      | none => rw [hf] at h2; exact nomatch h2
      | some ci =>
        rw [hf] at h2
        refine ⟨m.cval n (Level.substFn φ ci.toConstantVal.levelParams us),
          ?_⟩
        rw [denote_const, hf]
        exact if_pos (by simpa using h2)
  | app f a ihf iha =>
    intro h
    simp only [natFragOk, Bool.and_eq_true] at h
    obtain ⟨hwf, hbf, hLf, hCf, wf, hdf⟩ := ihf h.1
    obtain ⟨hwa, hba, hLa, hCa, wa, hda⟩ := iha h.2
    rw [show Expr.substConst0 c v (.app f a)
      = .app (Expr.substConst0 c v f) (Expr.substConst0 c v a) from rfl]
    refine ⟨by simp only [Expr.WScoped]; exact ⟨hwf, hwa⟩,
      by simp [Expr.looseBVarsBounded, hbf, hba], ?_,
      CtxOk.app hCf hCa, VExpr.app wf wa, ?_⟩
    · intro l hl
      rw [Expr.fvarLeaves] at hl
      rcases List.mem_append.mp hl with h' | h'
      · exact hLf l h'
      · exact hLa l h'
    · rw [denote_app, hdf, hda]
  | bvar _ | lam _ _ _ _ | forallE _ _ _ _ | letE _ _ _ _
  | proj _ _ _ | lit _ =>
    intro h; simp [natFragOk] at h

/-! ## The assembly -/

/-- **`NatOpPinTT`.**  `certifyNatEqs` certified each recurrence in the
pre-insertion environment with the operation replaced by its stored
value; `denote_substConst0` carries that certificate — and only it —
into the extended environment. -/
theorem natOpPinTT : NatOpPinTT F := by
  intro env m cv value value' hint hmem hfresh _hannv hvf hbv hden hguard
    hcerts eq hq φ
  obtain ⟨V, hV⟩ := hden φ
  obtain ⟨hN', hz', hs', hdeps', hbool'⟩ := natOpGuard_stored hguard
  have tr : ∀ {n : Name}, n ≠ cv.name →
      storedNoLevels ⟨ConstantInfo.defnInfo cv value' hint :: env.consts⟩ n →
      storedNoLevels env n := fun hne h =>
    storedNoLevels_of_cons (ci := .defnInfo cv value' hint) (c := cv.name)
      rfl hne h
  have hnN : natName ≠ cv.name := ne_of_mem_natOpNames (by decide) hmem
  have hnz : natZeroName ≠ cv.name := ne_of_mem_natOpNames (by decide) hmem
  have hns : natSuccName ≠ cv.name := ne_of_mem_natOpNames (by decide) hmem
  have hnT : boolTrueName ≠ cv.name := ne_of_mem_natOpNames (by decide) hmem
  have hnF : boolFalseName ≠ cv.name := ne_of_mem_natOpNames (by decide) hmem
  obtain ⟨ciN, hfN, hlpN⟩ := storedNoLevels_exists (tr hnN hN')
  -- the operation is its own dependency, so the guard pins its levels
  have hselfdep : cv.name ∈ natOpDeps cv.name := by
    simp only [natOpNames, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h | h | h | h | h <;> rw [h] <;> decide
  have hlp : (ConstantInfo.defnInfo cv value' hint).toConstantVal.levelParams
      = [] := by
    have hd := hdeps' cv.name hselfdep
    unfold storedNoLevels at hd
    rw [show (⟨ConstantInfo.defnInfo cv value' hint :: env.consts⟩ : Env).find?
          cv.name = some (.defnInfo cv value' hint) from by
        rw [Env.find?_cons]; exact if_pos rfl] at hd
    simpa [List.isEmpty_iff] using hd
  -- both sides are in the fragment
  obtain ⟨hf1, hf2⟩ := natOpEquations_frag (env := env) (c := cv.name)
    (tr hnz hz') (tr hns hs') (fun n hn hne => tr hne (hdeps' n hn))
    (fun hc => tr hnT (hbool' (by rcases hc with h | h <;> rw [h] <;> simp)).1)
    (fun hc => tr hnF (hbool' (by rcases hc with h | h <;> rw [h] <;> simp)).2) eq hq
  have hxT : HasType [m.cval natName φ, m.cval natName φ]
      (.bvar (2 - 1 - 0)) (m.cval natName φ) := by
    have := HasType.bvar (Γ := [m.cval natName φ, m.cval natName φ])
      (i := 1) (A := m.cval natName φ) (by simp)
    rwa [VExpr.liftN_eq_self_of_closed (m.cval_closed natName φ) _ 0] at this
  have hyT : HasType [m.cval natName φ, m.cval natName φ]
      (.bvar (2 - 1 - 1)) (m.cval natName φ) := by
    have := HasType.bvar (Γ := [m.cval natName φ, m.cval natName φ])
      (i := 0) (A := m.cval natName φ) (by simp)
    rwa [VExpr.liftN_eq_self_of_closed (m.cval_closed natName φ) _ 0] at this
  obtain ⟨hw1, hb1, hL1, hC1, w1, hd1⟩ :=
    natFrag_subst_facts m φ hvf hbv hV (Nat.le_refl 2) rfl hxT hyT hfN hlpN
      _ hf1
  obtain ⟨hw2, hb2, hL2, hC2, w2, hd2⟩ :=
    natFrag_subst_facts m φ hvf hbv hV (Nat.le_refl 2) rfl hxT hyT hfN hlpN
      _ hf2
  -- the certificate, transported by `checkClaimsTT`
  obtain ⟨-, -, ihd, -⟩ := checkClaimsTT m φ F
  have hdeq := ihd (hcerts _ (List.mem_map.mpr ⟨eq, hq, rfl⟩))
    hw1 hb1 hL1 hw2 hb2 hL2 hC1 hC2 hd1 hd2
  -- and moved across the install by `denote_substConst0`
  have hsub := denote_substConst0 m.cval_closed (c₀ := .defnInfo cv value' hint)
    (c := cv.name) φ rfl hfresh hlp hV hvf hbv 2
  refine ⟨w1, w2, ?_, ?_, ?_⟩
  · rw [hsub _ (shallowE_of_natFragOk hf1)]; exact hd1
  · rw [hsub _ (shallowE_of_natFragOk hf2)]; exact hd2
  · rw [cvalAt_ne hnN]; exact hdeq

end Setlec.TTVerify

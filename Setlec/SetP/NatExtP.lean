import Setlec.SetP.DivModP
import Setlec.SetP.Step2.BitRepr

/-!
# The `Nat` laws are valuation-independent (the packed `pw` datum, 2026-09-06)

The three `Nat` fields of `EnvS2PM` — `nat_heads`, `nat_ops`,
`div_mod` — speak only about universe-**monomorphic** constants (the
guards pin every head's stored `levelParams` to `[]`), so their
readings and leaves do not move with the valuation at all
(`acval_params` at the empty list).  The harvests establish them at
the representative valuation (where the tier's claims are available:
`Level.NonzeroOutside env.lpsL`) and carry them to every valuation
through the `_ext` lemmas below.
-/

namespace Setlec.SetP
open Setlec.Semantics
open Setlec.SetModel
open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.Semantics (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal natOpGuard)

universe w
variable {V : Type w} [SetTheory V] {env : Env}

/-- The leaf of a universe-monomorphic stored constant is the same at
every valuation. -/
theorem acval_ext_of_univFree (m : EnvS2Core V env) {n : Name}
    {ci : ConstantInfo} (hf : env.find? n = some ci)
    (h0 : ci.toConstantVal.levelParams = []) (φ φ' : Name → Nat) :
    m.acval n φ = m.acval n φ' :=
  m.acval_params n ci hf φ φ' (by
    rw [h0]; intro p hp; exact absurd hp (List.not_mem_nil))

/-- Binder-free, and every constant is a universe-monomorphic stored
one at the empty level list. -/
def UnivFreeConsts (env : Env) : Expr → Prop
  | .const n us => us = [] ∧ ∃ ci, env.find? n = some ci ∧ ci.toConstantVal.levelParams = []
  | .app f a => UnivFreeConsts env f ∧ UnivFreeConsts env a
  | .fvar _ _ _ => True
  | .bvar _ => True
  | _ => False

/-- A `UnivFreeConsts` subject reads the same at every valuation. -/
theorem denoteP_ext_of_univFree (m : EnvS2Core V env) (φ φ' : Name → Nat) :
    ∀ {d : Nat} {e : Expr}, UnivFreeConsts env e →
      denoteP m.acval env φ d e = denoteP m.acval env φ' d e
  | _, .const n us, ⟨hus, ci, hf, h0⟩ => by
    subst hus
    rw [denoteP, denoteP, hf]
    simp only [h0, List.length_nil, ↓reduceIte]
    rw [acval_ext_of_univFree m hf h0 (Level.substFn φ [] []) (Level.substFn φ' [] [])]
  | _, .app f a, ⟨hf, ha⟩ => by
    rw [denoteP, denoteP, denoteP_ext_of_univFree m φ φ' hf,
      denoteP_ext_of_univFree m φ φ' ha]
  | _, .fvar _ _ _, _ => by rw [denoteP, denoteP]
  | _, .bvar _, _ => by rw [denoteP.eq_def, denoteP.eq_def]
  | _, .sort _, h | _, .forallE _ _ _ _, h | _, .lam _ _ _ _, h
  | _, .letE _ _ _ _, h | _, .lit _, h | _, .proj _ _ _, h => h.elim

/-- **`NatHeadsP` is valuation-independent.** -/
theorem NatHeadsP_ext {m : EnvS2Core V env} {φ : Name → Nat}
    (h : NatHeadsP m φ) (φ' : Name → Nat) : NatHeadsP m φ' := by
  intro hg ρ
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlN, hl0, hl1, -⟩ :=
    Setlec.natLitSupported_inv hg
  have eN := acval_ext_of_univFree m hfN hlN (Level.substFn φ' [] []) (Level.substFn φ [] [])
  have eZ := acval_ext_of_univFree m hfZ hl0 (Level.substFn φ' [] []) (Level.substFn φ [] [])
  have eS := acval_ext_of_univFree m hfS hl1 (Level.substFn φ' [] []) (Level.substFn φ [] [])
  rw [eN, eZ, eS]
  exact h hg ρ

/-- Every constant the structural recurrences mention is stored
universe-monomorphic (the guard). -/
theorem natOpEquations_univFree {c : Name} (hg : natOpGuard env c = true)
    (hc : c ∈ Setlec.natOpNames) (d : Nat) :
    ∀ eq ∈ Setlec.natOpEquations d c, UnivFreeConsts env eq.1 ∧ UnivFreeConsts env eq.2 := by
  obtain ⟨hlit, hdeps, hbool⟩ := Setlec.natOpGuard_inv hg
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlN, hl0, hl1, -⟩ :=
    Setlec.natLitSupported_inv hlit
  have hZ : UnivFreeConsts env (.const Setlec.natZeroName []) := ⟨rfl, _, hfZ, hl0⟩
  have hS : UnivFreeConsts env (.const Setlec.natSuccName []) := ⟨rfl, _, hfS, hl1⟩
  have hD : ∀ n ∈ Setlec.natOpDeps c, UnivFreeConsts env (.const n []) := by
    intro n hn
    obtain ⟨cvn, vn, hn', hfn, hln⟩ := hdeps n hn
    exact ⟨rfl, _, hfn, hln⟩
  have hX : UnivFreeConsts env (.fvar d (.str .anonymous "x") (.const Setlec.natName [])) :=
    trivial
  have hY : UnivFreeConsts env
      (.fvar (d + 1) (.str .anonymous "y") (.const Setlec.natName [])) := trivial
  intro eq heq
  rcases (show c = Setlec.natPredName ∨ c = Setlec.natAddName ∨ c = Setlec.natSubName ∨
      c = Setlec.natMulName ∨ c = Setlec.natPowName ∨ c = Setlec.natBeqName ∨
      c = Setlec.natBleName from by simpa [Setlec.natOpNames] using hc) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hC := hD _ (by decide)
    simp +decide only [Setlec.natOpEquations, if_true, if_false, List.mem_cons,
      List.mem_nil_iff, or_false] at heq
    rcases heq with rfl | rfl
    · exact ⟨⟨hC, hZ⟩, hZ⟩
    · exact ⟨⟨hC, hS, hX⟩, hX⟩
  · have hC := hD _ (by decide)
    simp +decide only [Setlec.natOpEquations, if_true, if_false, List.mem_cons,
      List.mem_nil_iff, or_false] at heq
    rcases heq with rfl | rfl
    · exact ⟨⟨⟨hC, hX⟩, hZ⟩, hX⟩
    · exact ⟨⟨⟨hC, hX⟩, hS, hY⟩, hS, ⟨hC, hX⟩, hY⟩
  · have hC := hD _ (by decide)
    have hP := hD Setlec.natPredName (by decide)
    simp +decide only [Setlec.natOpEquations, if_true, if_false, List.mem_cons,
      List.mem_nil_iff, or_false] at heq
    rcases heq with rfl | rfl
    · exact ⟨⟨⟨hC, hX⟩, hZ⟩, hX⟩
    · exact ⟨⟨⟨hC, hX⟩, hS, hY⟩, hP, ⟨hC, hX⟩, hY⟩
  · have hC := hD _ (by decide)
    have hA := hD Setlec.natAddName (by decide)
    simp +decide only [Setlec.natOpEquations, if_true, if_false, List.mem_cons,
      List.mem_nil_iff, or_false] at heq
    rcases heq with rfl | rfl
    · exact ⟨⟨⟨hC, hX⟩, hZ⟩, hZ⟩
    · exact ⟨⟨⟨hC, hX⟩, hS, hY⟩, ⟨hA, ⟨hC, hX⟩, hY⟩, hX⟩
  · have hC := hD _ (by decide)
    have hM := hD Setlec.natMulName (by decide)
    simp +decide only [Setlec.natOpEquations, if_true, if_false, List.mem_cons,
      List.mem_nil_iff, or_false] at heq
    rcases heq with rfl | rfl
    · exact ⟨⟨⟨hC, hX⟩, hZ⟩, hS, hZ⟩
    · exact ⟨⟨⟨hC, hX⟩, hS, hY⟩, ⟨hM, ⟨hC, hX⟩, hY⟩, hX⟩
  · have hC := hD _ (by decide)
    obtain ⟨⟨ciT, hfT, hlT⟩, ⟨ciF, hfF, hlF⟩⟩ := hbool (Or.inl rfl)
    have hT : UnivFreeConsts env (.const Setlec.boolTrueName []) := ⟨rfl, _, hfT, hlT⟩
    have hF : UnivFreeConsts env (.const Setlec.boolFalseName []) := ⟨rfl, _, hfF, hlF⟩
    simp +decide only [Setlec.natOpEquations, if_true, if_false, List.mem_cons,
      List.mem_nil_iff, or_false] at heq
    rcases heq with rfl | rfl | rfl | rfl
    · exact ⟨⟨⟨hC, hZ⟩, hZ⟩, hT⟩
    · exact ⟨⟨⟨hC, hZ⟩, hS, hY⟩, hF⟩
    · exact ⟨⟨⟨hC, hS, hX⟩, hZ⟩, hF⟩
    · exact ⟨⟨⟨hC, hS, hX⟩, hS, hY⟩, ⟨hC, hX⟩, hY⟩
  · have hC := hD _ (by decide)
    obtain ⟨⟨ciT, hfT, hlT⟩, ⟨ciF, hfF, hlF⟩⟩ := hbool (Or.inr (Or.inl rfl))
    have hT : UnivFreeConsts env (.const Setlec.boolTrueName []) := ⟨rfl, _, hfT, hlT⟩
    have hF : UnivFreeConsts env (.const Setlec.boolFalseName []) := ⟨rfl, _, hfF, hlF⟩
    simp +decide only [Setlec.natOpEquations, if_true, if_false, List.mem_cons,
      List.mem_nil_iff, or_false] at heq
    rcases heq with rfl | rfl | rfl
    · exact ⟨⟨⟨hC, hZ⟩, hY⟩, hT⟩
    · exact ⟨⟨⟨hC, hS, hX⟩, hZ⟩, hF⟩
    · exact ⟨⟨⟨hC, hS, hX⟩, hS, hY⟩, ⟨hC, hX⟩, hY⟩

/-- **`NatOpsP` is valuation-independent.** -/
theorem NatOpsP_ext {m : EnvS2Core V env} {φ : Name → Nat}
    (h : NatOpsP m φ) (φ' : Name → Nat) : NatOpsP m φ' := by
  intro c hc cv v hint hf
  obtain ⟨hg, heqs⟩ := h c hc cv v hint hf
  refine ⟨hg, ?_⟩
  intro eq heq
  obtain ⟨L, R, hL, hR, hlaw⟩ := heqs eq heq
  obtain ⟨hu1, hu2⟩ := natOpEquations_univFree hg hc 0 eq heq
  obtain ⟨ciN, hfN, hlN, -⟩ := Setlec.natOpGuard_natTy hg
  refine ⟨L, R, ?_, ?_, ?_⟩
  · rw [denoteP_ext_of_univFree m φ' φ hu1]; exact hL
  · rw [denoteP_ext_of_univFree m φ' φ hu2]; exact hR
  · intro ρ x y hx hy
    rw [acval_ext_of_univFree m hfN hlN φ' φ] at hx hy
    exact hlaw ρ x y hx hy

/-- Every head the WF recurrences read is stored universe-monomorphic
(the guard, plus the literal support). -/
theorem dmValNames_univFree {c : Name} (hc : c ∈ Setlec.natDivModNames)
    (hg : natOpGuard env c = true) {cv : ConstantVal} {v : Expr}
    {hint : Setlec.ReducibilityHint}
    (hf : env.find? c = some (.defnInfo cv v hint)) (hcl : cv.levelParams = []) :
    ∀ n ∈ dmValNames c, ∃ ci, env.find? n = some ci ∧ ci.toConstantVal.levelParams = [] := by
  obtain ⟨hs, hdeps, hbool⟩ := Setlec.natOpGuard_inv hg
  obtain ⟨⟨ciT, hfT, hlT⟩, ⟨ciF, hfF, hlF⟩⟩ :=
    hbool (Or.inr (Or.inr (by simpa using hc)))
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlN, hl0, hl1, -⟩ :=
    Setlec.natLitSupported_inv hs
  have hble : Setlec.natBleName ∈ Setlec.natOpDeps c := by
    rcases (show c = Setlec.natDivName ∨ c = Setlec.natModName ∨
        c = Setlec.natGcdName ∨ c = Setlec.natLandName ∨
        c = Setlec.natLorName ∨ c = Setlec.natXorName ∨
        c = Setlec.natShiftLeftName ∨ c = Setlec.natShiftRightName ∨
        c = Setlec.natLog2Name from by
      simpa [Setlec.natDivModNames] using hc) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  intro n hn
  simp only [dmValNames, List.mem_cons] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hn
  · exact ⟨_, hfN, hlN⟩
  · exact ⟨_, hfT, hlT⟩
  · exact ⟨_, hfF, hlF⟩
  · exact ⟨_, hfZ, hl0⟩
  · exact ⟨_, hfS, hl1⟩
  · obtain ⟨cvb, vb, hb, hfb, hlb⟩ := hdeps _ hble
    exact ⟨_, hfb, hlb⟩
  · exact ⟨_, hf, hcl⟩
  · obtain ⟨cvn, vn, hn', hfn, hln⟩ := hdeps n hn
    exact ⟨_, hfn, hln⟩

/-- **`DivModP` is valuation-independent.** -/
theorem DivModP_ext {m : EnvS2Core V env} {φ : Name → Nat}
    (h : DivModP m φ) (φ' : Name → Nat) : DivModP m φ' := by
  intro c hc cv v hint hf
  obtain ⟨hg, hcl⟩ := h c hc cv v hint hf
  refine ⟨hg, fun ρ x y hx hy => ?_⟩
  have hcl0 : cv.levelParams = [] := by
    obtain ⟨-, hdeps, -⟩ := Setlec.natOpGuard_inv hg
    have hself : c ∈ Setlec.natOpDeps c := by
      rcases (show c = Setlec.natDivName ∨ c = Setlec.natModName ∨
          c = Setlec.natGcdName ∨ c = Setlec.natLandName ∨
          c = Setlec.natLorName ∨ c = Setlec.natXorName ∨
          c = Setlec.natShiftLeftName ∨ c = Setlec.natShiftRightName ∨
          c = Setlec.natLog2Name from by
        simpa [Setlec.natDivModNames] using hc) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    obtain ⟨cvn, vn, hn', hfn, hln⟩ := hdeps c hself
    rw [hf] at hfn
    obtain ⟨rfl, -, -⟩ := ConstantInfo.defnInfo.inj (Option.some.inj hfn)
    exact hln
  have hmove : ∀ n ∈ dmValNames c, m.acval n φ' = m.acval n φ := by
    intro n hn
    obtain ⟨ci, hfn, hln⟩ := dmValNames_univFree hc hg hf hcl0 n hn
    exact acval_ext_of_univFree m hfn hln φ' φ
  rw [hmove Setlec.natName (by simp [dmValNames])] at hx hy
  exact (divModClausesV_congr hc (fun n hn => by rw [hmove n hn])).mp
    (hcl ρ x y hx hy)

end Setlec.SetP

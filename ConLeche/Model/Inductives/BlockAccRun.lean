module

import ConLeche.Verify.Denote.IndFrame
public import ConLeche.Model.Inductives.NestPosAcc
public import ConLeche.Model.Env.LfpAcc
public import ConLeche.Model.Inductives.BlockPosRun
import ConLeche.Model.Inductives.StructEntryKit

public section

/-!
# Accessibility from the check's run

The producer side of (W) by accessibility: at a uniform block's
install every member constructor's field telescope is accessible along
the accessibility relation at the hole frame (`LfpDatum.accRel`), which
`LfpDatum.fitAcc_holeOp` turns into the hole fit's accessibility (at
every level, task #327), whence the operator's, (W) and monotonicity.

This file holds the pieces between the derivation's accessibility
(`memberCtorD_acc`, on the walked crest's reading) and the datum's
fields with holes (`d.absF`, the normal form's reading); the block
theorems are in `BlockAccRunCont.lean`:

* `teleAccP_of_piAccThen`: the walked fields' accessibility moves onto
  the datum's fields (they read alike at every satisfying frame, so the
  relations under them coincide), one bound per field;
* U4 on the opened normal form (`u4_nestOccAt`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level NestCtx NestHole ConstantVal BlockShape BlockShape)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-! ## The walked accessibility onto the datum's fields -/

/-- `TeleAccP` reads the bounds from field `l` on only. -/
theorem TeleAccP.congr {w : Nat} {Af Af' : Nat → (Nat → V) → V} :
    ∀ (Fs : List Term) (l : Nat) (Q : Nat → Nat → Prop) (R : FrameRel V),
      (∀ l', l ≤ l' → l' < l + Fs.length → Af l' = Af' l') → TeleAccP w Af l Q R Fs →
        TeleAccP w Af' l Q R Fs
  | [], _, _, _, _, _ => trivial
  | F :: Fs, l, Q, R, h, ⟨h1, h2, h3, h4⟩ => by
    have hl : Af l = Af' l := h l (Nat.le_refl _) (by simp)
    refine ⟨hl ▸ h1, hl ▸ h2, h3, ?_⟩
    exact TeleAccP.congr Fs (l + 1) (shiftQ Q) (R.underBoth F)
      (fun l' hl' hl'' => h l' (by omega) (by simp at hl'' ⊢; omega)) h4

theorem shiftQ_congr {Q Q' : Nat → Nat → Prop} (h : ∀ i n, Q i n ↔ Q' i n) :
    ∀ i n, shiftQ Q i n ↔ shiftQ Q' i n
  | 0, _ => Iff.rfl
  | i + 1, n => h i n

/-- **The walked fields' accessibility moves onto the datum's fields**
(see the module docstring): one bound per field, reading only its walk
output's non-hole positions, and the walk's result fact at the relation
under the datum's fields. -/
theorem teleAccP_of_piAccThen {w : Nat} {ctx : NestCtx} {prog : List NestHole}
    {Qf : FrameRel V → Term → Prop} :
    ∀ (abD abN : List Term) (B : Term) (d l : Nat) (nds : List Expr)
      (Δ : List Term) (R : FrameRel V) (Q : Nat → Nat → Prop),
      FieldsEqOn V Δ (abD) (abN) →
      (∀ ρ ρ₀, R ρ ρ₀ → Sat V Δ ρ ∧ Sat V Δ ρ₀) →
      (∀ ρ ρ₀, R ρ ρ₀ → w ≠ 0 → FieldsBound w ρ (abN)) →
      (∀ i n, HoleQ ctx prog d i n ↔ Q i n) → ctx.hiAt prog.length ≤ d →
      PiAccThen w ctx prog Qf abD.length d nds R (mkPisAV abD B) →
      ∃ Af : Nat → (Nat → V) → V, TeleAccP w Af l Q R (abN) ∧
        (∀ (i : Nat) (nd : Expr), i < abD.length → nds[i]? = some nd →
          InvOn (MentP ctx.nP (ctx.hiAt prog.length) (d + i) nd) (Af (l + i))) ∧
        Qf (R.underBothTele (abN)) B
  | [], [], B, _, _, _, _, R, _, _, _, _, _, _, hP =>
    ⟨fun _ _ => empty, trivial, fun _ _ h => absurd h (Nat.not_lt_zero _), hP⟩
  | x :: abD, y :: abN, B, d, l, nds, Δ, R, Q, hE, hdom, hok, hQ, hd, hP => by
    obtain ⟨h0, hrest⟩ := hE
    match nds, hP with
    | [], hP => exact hP.elim
    | nd :: nds', ⟨⟨Af0, hacc0, hsz0, hinv0⟩, hP'⟩ =>
      have hUE : R.underBoth x = R.underBoth y := underBoth_eq_of_eqOn h0 hdom
      have hok' : ∀ σ σ₀, R.underBoth x σ σ₀ → w ≠ 0 →
          FieldsBound w σ (abN) := by
        rintro _ _ ⟨a, ρ, ρ₀, rfl, rfl, hR, ha, -⟩ hw
        have hok0 := hok ρ ρ₀ hR hw
        exact hok0.2 a (h0 ρ (hdom ρ ρ₀ hR).1 ▸ ha)
      have hQ' : ∀ i n, HoleQ ctx prog (d + 1) i n ↔ shiftQ Q i n := by
        intro i n
        rw [← shiftQ_holeQ hd i n]
        exact shiftQ_congr hQ i n
      obtain ⟨Af', htele', hinv', hQf⟩ :=
        teleAccP_of_piAccThen abD abN B (d + 1) (l + 1) nds' (x :: Δ) (R.underBoth x)
          (shiftQ Q) hrest (underBoth_dom hdom) hok' hQ' (by omega) hP'
      classical
      refine ⟨fun l' => if l' = l then Af0 else Af' l', ?_, ?_, ?_⟩
      · refine ⟨?_, ?_, fun ρ ρ₀ hR => ?_, ?_⟩
        · simp only
          exact AccOn.of_eqOn (P := Sat V Δ) hdom (fun ρ hρ => (h0 ρ hρ).symm)
            (AccOn.congrQ hQ hacc0)
        · simp only
          exact hsz0
        · intro hw
          have hok0 := hok ρ ρ₀ hR hw
          exact mem_tg_of_mem_univ hok0.1
        · rw [← hUE]
          exact TeleAccP.congr _ (l + 1) (shiftQ Q) _
            (fun l' hl' _ => by simp only [ite_eq_right (show l' ≠ l by omega)]) htele'
      · intro i nd' hi hnd
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hnd
          subst hnd
          simp only [Nat.add_zero]
          exact hinv0
        | succ i =>
          simp only [List.getElem?_cons_succ] at hnd
          simp only [ite_eq_right (show l + (i + 1) ≠ l by omega)]
          have := hinv' i nd' (by simpa using hi) hnd
          rwa [show d + 1 + i = d + (i + 1) by omega, show l + 1 + i = l + (i + 1) by omega]
            at this
      · show Qf ((R.underBoth y).underBothTele (abN)) B
        rw [← hUE]
        exact hQf
  | [], _ :: _, _, _, _, _, _, _, _, hE, _, _, _, _, _ => hE.elim
  | _ :: _, [], _, _, _, _, _, _, _, hE, _, _, _, _, _ => hE.elim

/-! ## The result indices -/

/-- **The result indices read alike** at two frames under a spine fitting
the fields at both, from the walk's result fact. -/
theorem resC_of_resultIdxConst {R : FrameRel V} {Fs : List Term} {h : Nat}
    {es : List Term}
    (hQ : ResultIdxConst (R.underBothTele Fs) (Term.mkAppN (.bvar h) es)) :
    ∀ ρ ρ', R ρ ρ' → ∀ fs, SpineFit ρ Fs fs → SpineFit ρ' Fs fs →
      ∀ e ∈ es, interp V (consList fs ρ) e = interp V (consList fs ρ') e := by
  obtain ⟨i, vs, heq, hvs⟩ := hQ
  obtain ⟨-, rfl⟩ := mkAppN_bvar_inj heq.symm
  intro ρ ρ' hR fs hf hf' e he
  exact hvs e he _ _ (FrameRel.underBothTele_consList Fs fs hR hf hf')

/-! ## The relation at the walk's top -/

omit [SetTheory V] in
/-- **The admissible items at the walk's top are the member holes at
their full arity.** -/
theorem holeQ_top_iff {d : BlockData V} {ψ : Name → Nat} {ctx : NestCtx}
    (hhi : ctx.hiAt 0 = d.nP + d.k) (hcN : ctx.names.length = d.k) (hcP : ctx.nP = d.nP)
    (har : ∀ t, t < d.k → (d.toLfp.ids t ψ).length = ctx.nIdxs.getD t 0) :
    ∀ i n, HoleQ ctx [] (ctx.hiAt 0) i n ↔ d.toLfp.MemberQ ψ i n := by
  intro i n
  show _ ↔ ∃ t, t < d.k ∧ i = d.k - 1 - t ∧ n = (d.toLfp.ids t ψ).length
  constructor
  · rintro (⟨t, ht, hlt, rfl, rfl⟩ | ⟨j, hk, hj, -⟩)
    · rw [hcN] at ht
      exact ⟨t, ht, by rw [hhi, hcP]; omega, (har t ht).symm⟩
    · simp at hj
  · rintro ⟨t, ht, rfl, rfl⟩
    exact Or.inl ⟨t, by rw [hcN]; exact ht, by rw [hhi, hcP]; omega,
      by rw [hhi, hcP]; omega, har t ht⟩

/-- **The accessibility relation at the hole frame is an accessibility
hole relation of the walk's context**: its frames satisfy the context,
agree off the member holes, and at a `Type`-valued block its member
holes are rich. -/
theorem holeRelA_accRel {d : BlockData V} {ψ : Name → Nat} {ρp : Nat → V} {ctx : NestCtx}
    (hhi : ctx.hiAt 0 = d.nP + d.k) (hcN : ctx.names.length = d.k)
    (hcP : ctx.nP = d.nP)
    (har : ∀ t, t < d.k → (d.toLfp.ids t ψ).length = ctx.nIdxs.getD t 0)
    {Δa : List Term}
    (hsat : ∀ X, InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X →
      Sat V Δa (d.toLfp.frame ψ ρp X)) :
    HoleRelA m ψ (d.w ψ) ctx [] (ctx.hiAt 0) Δa (d.toLfp.accRel ψ ρp) where
  dom := by
    rintro _ _ ⟨X, Y, hX, hY, rfl, rfl⟩
    exact ⟨hsat X hX, hsat Y hY⟩
  agree := by
    intro σ σ' hr i hi
    refine LfpDatum.accRel_agreeOff hr i ?_
    show d.k ≤ i
    refine Nat.le_of_not_lt fun hlt => hi ?_
    simp only [holeP, List.length_nil, hhi, hcP]
    omega
  dsScoped := fun _ _ h => by simp at h
  symm := LfpDatum.accRel_symm
  ptFree hw := PtFreeOn.congrQ (fun i n => (holeQ_top_iff hhi hcN hcP har i n).symm)
    (LfpDatum.accRel_ptFree (Nat.le_add_right _ _) hw)
  lrefl := by
    rintro _ _ ⟨X, Y, hX, -, rfl, -⟩
    exact LfpDatum.accRel_refl hX

/-! ## U4 on the normal form (syntactic) -/

section Syntax

open ConLeche (openPisAtFvars structUsedLater)

/-- **U4, on the opened normal form**: a later field's domain does not
mention a field no later binder uses — at any base depth. -/
theorem u4_nestOccAt {b nF j l : Nat} {tyN rest : Expr} {xs : List Expr} {x : Expr}
    (hop : openPisAtFvars nF tyN (b) = some (xs, rest))
    (hW : Expr.WScoped (b) tyN) (hU : structUsedLater tyN 0 j = false)
    (hj : j < nF) (hjl : j < l) (hx : xs[l]? = some x) :
    x.fvarTypeD.nestOcc [] (b + j) (b + j + 1) = false := by
  obtain ⟨⟨bs, r⟩, hst⟩ := Option.isSome_iff_exists.mp
    (stripPis_of_openPis nF hop (j + 1) (by omega))
  have hfree : r.hasLooseBVar 0 = false := by
    unfold structUsedLater at hU
    rw [Nat.zero_add, hst] at hU
    simpa [Expr.hasLooseBVarB_eq] using hU
  obtain ⟨h1, -⟩ := openPisAtFvars_leaf_free nF j hop hj hst hfree fun z hz => by
    have := Expr.fvarLeaves_lt_of_wscoped hW z hz
    omega
  refine nestOcc_nil_of_leaves _ fun z hz => ?_
  obtain ⟨ty, rfl⟩ := ConLeche.openPisAtFvars_index nF tyN (b) hop l x hx
  exact h1 l hjl _ hx z (by simp only [Expr.fvarTypeD] at hz; simp [Expr.fvarLeaves, hz])

/-- **U4, on the opened normal form**: a later field's domain does not
mention a field no later binder uses. -/
theorem u4_nestOcc {ctx : NestCtx} {nF j l : Nat} {tyN rest : Expr} {xs : List Expr} {x : Expr}
    (hop : openPisAtFvars nF tyN (ctx.hiAt 0) = some (xs, rest))
    (hW : Expr.WScoped (ctx.hiAt 0) tyN) (hU : structUsedLater tyN 0 j = false)
    (hj : j < nF) (hjl : j < l) (hx : xs[l]? = some x) :
    x.fvarTypeD.nestOcc [] (ctx.hiAt 0 + j) (ctx.hiAt 0 + j + 1) = false :=
  u4_nestOccAt hop hW hU hj hjl hx

end Syntax

/-- NoBVar of a disjunction. -/
theorem noBVar_or {P₁ P₂ : Nat → Prop} {e : Term} (h₁ : NoBVar P₁ e) (h₂ : NoBVar P₂ e) :
    NoBVar (fun i => P₁ i ∨ P₂ i) e := by
  have := noBVar_exists' (α := Bool) (P := fun b i => if b then P₁ i else P₂ i) (e := e)
    fun b => by cases b <;> simpa
  refine NoBVar.mono (fun i hi => ?_) this
  rcases hi with h | h
  · exact ⟨true, by simpa using h⟩
  · exact ⟨false, by simpa using h⟩

end ConLeche.Model

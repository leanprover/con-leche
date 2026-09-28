module

public import ConLeche.Model.Inductives.NestPosAcc
public import ConLeche.Model.Annot.LfpAcc
public import ConLeche.Model.Inductives.BlockPosRun
import ConLeche.Model.Inductives.ClassAccTele

public section

/-!
# Accessibility from the install's run

The producer side of (W) by accessibility: at a uniform block's
install every member constructor's field telescope is accessible along
the accessibility relation at the hole frame (`LfpDatum.accRel`), which
`LfpDatum.accTuple_holeOp` turns into the hole operator's accessibility
and `closed_of_acc` into (W).

This file holds the pieces between the derivation's accessibility
(`memberCtorD_acc`, on the walked crest's reading) and the datum's
fields with holes (`d.absF`, the normal form's reading); the block
theorems are in `BlockAccRunCont.lean`:

* `teleSmall_mkPisAV`: the walked fields' values are small, from the
  datum's hereditary grading (`FieldsOkB`) through the link
  (`FieldsEqOn`);
* `teleAccP_of_piAccThen`: the walked fields' accessibility moves onto
  the datum's fields (they read alike at every satisfying frame, so the
  relations under them coincide), one bound per field;
* U4 on the opened normal form (`u4_nestOccAt`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level NestCtx NestHole ConstantVal BlockShape BlockParts)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-! ## The walked fields' values are small -/

/-! ## The walked accessibility onto the datum's fields -/

/-- **The walked fields' accessibility moves onto the datum's fields**
(see the module docstring): one bound per field, reading only its walk
output's non-hole positions, and the walk's result fact at the relation
under the datum's fields. -/
theorem teleAccP_of_piAccThen {w : Nat} (hw : w ≠ 0) {ctx : NestCtx} {prog : List NestHole}
    {Qf : FrameRel V → AnnotTerm → Prop} :
    ∀ (abD abN : List (Nat × Nat × AnnotTerm)) (B : AnnotTerm) (d l : Nat) (nds : List Expr)
      (Δ : List AnnotTerm) (R : FrameRel V) (Q : Nat → Nat → Prop),
      FieldsEqOn V Δ (abD.map (·.2.2)) (abN.map (·.2.2)) →
      (∀ ρ ρ₀, R ρ ρ₀ → Sat V Δ ρ ∧ Sat V Δ ρ₀) →
      (∀ ρ ρ₀, R ρ ρ₀ → FieldsBound w ρ (abN.map (·.2.2))) →
      (∀ i n, HoleQ ctx prog d i n ↔ Q i n) → ctx.hiAt prog.length ≤ d →
      PiAccThen w ctx prog Qf abD.length d nds R (mkPisAV abD B) →
      ∃ Af : Nat → (Nat → V) → V, TeleAccP w Af l Q R (abN.map (·.2.2)) ∧
        (∀ (i : Nat) (nd : Expr), i < abD.length → nds[i]? = some nd →
          InvOn (MentP ctx.nP (ctx.hiAt prog.length) (d + i) nd) (Af (l + i))) ∧
        Qf (R.underBothTele (abN.map (·.2.2))) B
  | [], [], B, _, _, _, _, R, _, _, _, _, _, _, hP =>
    ⟨fun _ _ => empty, trivial, fun _ _ h => absurd h (Nat.not_lt_zero _), hP⟩
  | x :: abD, y :: abN, B, d, l, nds, Δ, R, Q, hE, hdom, hok, hQ, hd, hP => by
    have hE' := hE
    simp only [List.map_cons] at hE'
    obtain ⟨h0, hrest⟩ := hE'
    match nds, hP with
    | [], hP => exact hP.elim
    | nd :: nds', ⟨⟨Af0, hacc0, hsz0, hinv0⟩, hP'⟩ =>
      have hUE : R.underBoth x.2.2 = R.underBoth y.2.2 := underBoth_eq_of_eqOn h0 hdom
      have hok' : ∀ σ σ₀, R.underBoth x.2.2 σ σ₀ → FieldsBound w σ (abN.map (·.2.2)) := by
        rintro _ _ ⟨a, ρ, ρ₀, rfl, rfl, hR, ha, -⟩
        have hok0 := hok ρ ρ₀ hR
        simp only [List.map_cons] at hok0
        exact hok0.2 a (h0 ρ (hdom ρ ρ₀ hR).1 ▸ ha)
      have hQ' : ∀ i n, HoleQ ctx prog (d + 1) i n ↔ shiftQ Q i n := by
        intro i n
        rw [← shiftQ_holeQ hd i n]
        exact shiftQ_congr hQ i n
      obtain ⟨Af', htele', hinv', hQf⟩ :=
        teleAccP_of_piAccThen hw abD abN B (d + 1) (l + 1) nds' (x.2.2 :: Δ) (R.underBoth x.2.2)
          (shiftQ Q) hrest (underBoth_dom hdom) hok' hQ' (by omega) hP'
      classical
      refine ⟨fun l' => if l' = l then Af0 else Af' l', ?_, ?_, ?_⟩
      · simp only [List.map_cons]
        refine ⟨?_, ?_, fun ρ ρ₀ hR => ?_, ?_⟩
        · simp only
          exact AccOn.of_eqOn (P := Sat V Δ) hdom (fun ρ hρ => (h0 ρ hρ).symm)
            (AccOn.congrQ hQ hacc0)
        · simp only
          exact hsz0
        · have hok0 := hok ρ ρ₀ hR
          simp only [List.map_cons] at hok0
          exact hok0.1
        · rw [← hUE]
          exact TeleAccP.congr _ (l + 1) (shiftQ Q) _
            (fun l' hl' _ => by simp only [if_neg (show l' ≠ l by omega)]) htele'
      · intro i nd' hi hnd
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hnd
          subst hnd
          simp only [Nat.add_zero]
          exact hinv0
        | succ i =>
          simp only [List.getElem?_cons_succ] at hnd
          simp only [if_neg (show l + (i + 1) ≠ l by omega)]
          have := hinv' i nd' (by simpa using hi) hnd
          rwa [show d + 1 + i = d + (i + 1) by omega, show l + 1 + i = l + (i + 1) by omega]
            at this
      · show Qf ((R.underBoth y.2.2).underBothTele (abN.map (·.2.2))) B
        rw [← hUE]
        exact hQf
  | [], _ :: _, _, _, _, _, _, _, _, hE, _, _, _, _, _ => hE.elim
  | _ :: _, [], _, _, _, _, _, _, _, hE, _, _, _, _, _ => hE.elim

/-! ## The result indices -/

/-! ## The relation at the walk's top -/

omit [SetTheory V] in
/-- **The admissible items at the walk's top are the member holes at
their full arity.** -/
theorem holeQ_top_iff {d : BlockData V} {ψ : Name → Nat} {ctx : NestCtx}
    (hhi : ctx.hiAt 0 = d.nP + d.k) (hcN : ctx.names.length = d.k) (hcP : ctx.nP = d.nP)
    (har : ∀ t, t < d.k →
      (d.toLfp.pars t ψ).length + (d.toLfp.ids t ψ).length = ctx.nP + ctx.nIdxs.getD t 0) :
    ∀ i n, HoleQ ctx [] (ctx.hiAt 0) i n ↔ d.toLfp.MemberQ ψ i n := by
  intro i n
  show _ ↔ ∃ t, t < d.k ∧ i = d.k - 1 - t ∧
    n = (d.toLfp.pars t ψ).length + (d.toLfp.ids t ψ).length
  constructor
  · rintro (⟨t, ht, hlt, rfl, rfl⟩ | ⟨j, hk, hj, -⟩)
    · rw [hcN] at ht
      exact ⟨t, ht, by rw [hhi, hcP]; omega, (har t ht).symm⟩
    · simp at hj
  · rintro ⟨t, ht, rfl, rfl⟩
    exact Or.inl ⟨t, by rw [hcN]; exact ht, by rw [hhi, hcP]; omega,
      by rw [hhi, hcP]; omega, har t ht⟩

/-- **The accessibility relation at the hole frame is an accessibility
hole relation of the walk's context** (at a positive level): its frames
satisfy the context, agree off the member holes, and its member holes
are rich. -/
theorem holeRelA_accRel {d : BlockData V} {ψ : Name → Nat} {ρp : Nat → V} {ctx : NestCtx}
    (hw : d.w ψ ≠ 0) (hhi : ctx.hiAt 0 = d.nP + d.k) (hcN : ctx.names.length = d.k)
    (hcP : ctx.nP = d.nP)
    (har : ∀ t, t < d.k →
      (d.toLfp.pars t ψ).length + (d.toLfp.ids t ψ).length = ctx.nP + ctx.nIdxs.getD t 0)
    {Δa : List AnnotTerm}
    (hsat : ∀ X, InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X →
      Sat V Δa (d.toLfp.frame ψ ρp X)) :
    HoleRelA m ψ ctx [] (ctx.hiAt 0) Δa (d.toLfp.accRel ψ ρp) where
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
  frame := fun _ _ h => by simp at h
  dsScoped := fun _ _ h => by simp at h
  symm := LfpDatum.accRel_symm
  rich := RichOn.congrQ (fun i n => (holeQ_top_iff hhi hcN hcP har i n).symm)
    (LfpDatum.accRel_rich (Nat.le_add_right _ _) hw)
  lrefl := by
    rintro _ _ ⟨X, Y, hX, -, rfl, -⟩
    exact LfpDatum.accRel_refl hX

/-! ## U4 on the normal form (syntactic) -/

end ConLeche.Model

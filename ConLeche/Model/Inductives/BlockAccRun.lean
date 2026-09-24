module

public import ConLeche.Model.Inductives.NestPosAcc
public import ConLeche.Model.Annot.LfpAcc
public import ConLeche.Model.Inductives.BlockPosRun
public import ConLeche.Model.Inductives.NestPosOut
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Model.Inductives.StructEntryFree
public import ConLeche.Model.Inductives.StoredShapes

public section

/-!
# Accessibility from the install's run (lane ACCMODEL)

The producer side of the maintainer's ruling "(W) by ACCESSIBILITY"
(2026-09-24), the twin of `BlockPosRun.lean`: at a uniform block's
install every member constructor's field telescope is accessible along
the accessibility relation at the hole frame (`LfpDatum.accRel`), which
`LfpDatum.accTuple_holeOp` turns into the hole operator's accessibility
and `closed_of_acc` into (W).

This file holds the pieces between the run inversion
(`nestMemberCtor_acc`, on the walked crest's reading) and the datum's
fields with holes (`d.absF`, the normal form's reading):

* `teleSmall_mkPisAV`: the walked fields' values are small, from the
  datum's hereditary grading (`FieldsOkB`) through the link
  (`FieldsEqOn`);
* `teleAccP_of_piAccThen`: the walked fields' accessibility moves onto
  the datum's fields (they read alike at every satisfying frame, so the
  relations under them coincide), one bound per field.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level NestCtx NestHole)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-! ## The walked fields' values are small -/

/-- **The walked fields' values are small** at every frame of the
relation: they read like the datum's fields, whose hereditary grading
bounds them. -/
theorem teleSmall_mkPisAV {w : Nat} (hw : w ≠ 0) :
    ∀ (abD abN : List (Nat × Nat × AnnotTerm)) (B : AnnotTerm) (Δ : List AnnotTerm)
      (R : FrameRel V),
      FieldsEqOn V Δ (abD.map (·.2.2)) (abN.map (·.2.2)) →
      (∀ ρ ρ₀, R ρ ρ₀ → Sat V Δ ρ ∧ Sat V Δ ρ₀) →
      (∀ ρ ρ₀, R ρ ρ₀ → FieldsOkB w ρ (abN.map (·.2.2))) →
      TeleSmall w abD.length R (mkPisAV abD B)
  | [], [], _, _, _, _, _, _ => trivial
  | x :: abD, y :: abN, B, Δ, R, hE, hdom, hok => by
    have hE' := hE
    simp only [List.map_cons] at hE'
    obtain ⟨h0, hrest⟩ := hE'
    refine ⟨fun ρ ρ₀ hR a ha => ?_, ?_⟩
    · have hok0 := hok ρ ρ₀ hR
      simp only [List.map_cons] at hok0
      rw [h0 ρ (hdom ρ ρ₀ hR).1] at ha
      exact (univ_isTGUniverse hw).transitive (hok0.2.1 hw) ha
    · refine teleSmall_mkPisAV hw abD abN B (x.2.2 :: Δ) (R.underBoth x.2.2) hrest
        (underBoth_dom hdom) ?_
      rintro _ _ ⟨a, ρ, ρ₀, rfl, rfl, hR, ha, -⟩
      have hok0 := hok ρ ρ₀ hR
      simp only [List.map_cons] at hok0
      exact hok0.2.2 a (h0 ρ (hdom ρ ρ₀ hR).1 ▸ ha)
  | [], _ :: _, _, _, _, hE, _, _ => hE.elim
  | _ :: _, [], _, _, _, hE, _, _ => hE.elim

/-! ## The walked accessibility onto the datum's fields -/

/-- `TeleAccP` reads the bounds from field `l` on only. -/
theorem TeleAccP.congr {w : Nat} {Af Af' : Nat → (Nat → V) → V} :
    ∀ (Fs : List AnnotTerm) (l : Nat) (Q : Nat → Nat → Prop) (R : FrameRel V),
      (∀ l', l ≤ l' → Af l' = Af' l') → TeleAccP w Af l Q R Fs → TeleAccP w Af' l Q R Fs
  | [], _, _, _, _, _ => trivial
  | F :: Fs, l, Q, R, h, ⟨h1, h2, h3, h4⟩ => by
    refine ⟨h l (Nat.le_refl _) ▸ h1, h l (Nat.le_refl _) ▸ h2, h3, ?_⟩
    exact TeleAccP.congr Fs (l + 1) (shiftQ Q) (R.underBoth F)
      (fun l' hl' => h l' (by omega)) h4

theorem shiftQ_congr {Q Q' : Nat → Nat → Prop} (h : ∀ i n, Q i n ↔ Q' i n) :
    ∀ i n, shiftQ Q i n ↔ shiftQ Q' i n
  | 0, _ => Iff.rfl
  | i + 1, n => h i n

/-- **The walked fields' accessibility moves onto the datum's fields**
(see the module docstring): one bound per field, reading only its walk
output's non-hole positions, and the walk's result fact at the relation
under the datum's fields. -/
theorem teleAccP_of_piAccThen {w : Nat} (hw : w ≠ 0) {ctx : NestCtx}
    {Qf : FrameRel V → AnnotTerm → Prop} :
    ∀ (abD abN : List (Nat × Nat × AnnotTerm)) (B : AnnotTerm) (d l : Nat) (nds : List Expr)
      (Δ : List AnnotTerm) (R : FrameRel V) (Q : Nat → Nat → Prop),
      FieldsEqOn V Δ (abD.map (·.2.2)) (abN.map (·.2.2)) →
      (∀ ρ ρ₀, R ρ ρ₀ → Sat V Δ ρ ∧ Sat V Δ ρ₀) →
      (∀ ρ ρ₀, R ρ ρ₀ → FieldsOkB w ρ (abN.map (·.2.2))) →
      (∀ i n, HoleQ ctx [] d i n ↔ Q i n) → ctx.hiAt 0 ≤ d →
      PiAccThen w ctx [] Qf abD.length d nds R (mkPisAV abD B) →
      ∃ Af : Nat → (Nat → V) → V, TeleAccP w Af l Q R (abN.map (·.2.2)) ∧
        (∀ (i : Nat) (nd : Expr), i < abD.length → nds[i]? = some nd →
          InvOn (MentNH ctx.nP (ctx.hiAt 0) (d + i) nd) (Af (l + i))) ∧
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
      have hok' : ∀ σ σ₀, R.underBoth x.2.2 σ σ₀ → FieldsOkB w σ (abN.map (·.2.2)) := by
        rintro _ _ ⟨a, ρ, ρ₀, rfl, rfl, hR, ha, -⟩
        have hok0 := hok ρ ρ₀ hR
        simp only [List.map_cons] at hok0
        exact hok0.2.2 a (h0 ρ (hdom ρ ρ₀ hR).1 ▸ ha)
      have hQ' : ∀ i n, HoleQ ctx [] (d + 1) i n ↔ shiftQ Q i n := by
        intro i n
        rw [← shiftQ_holeQ (by simpa using hd) i n]
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
          exact hok0.2.1 hw
        · rw [← hUE]
          exact TeleAccP.congr _ (l + 1) (shiftQ Q) _
            (fun l' hl' => by simp only [if_neg (show l' ≠ l by omega)]) htele'
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

/-- **The result indices read alike** at two frames under a spine fitting
the fields at both, from the walk's result fact. -/
theorem resC_of_resultIdxConst {nP : Nat} {R : FrameRel V} {Fs : List AnnotTerm} {h : Nat}
    {ps es : List AnnotTerm} (hps : ps.length = nP)
    (hQ : ResultIdxConst nP (R.underBothTele Fs) (AnnotTerm.mkAppN (.bvar h) (ps ++ es))) :
    ∀ ρ ρ', R ρ ρ' → ∀ fs, SpineFit ρ Fs fs → SpineFit ρ' Fs fs →
      ∀ e ∈ es, interp V (consList fs ρ) e = interp V (consList fs ρ') e := by
  obtain ⟨i, vs, heq, hvs⟩ := hQ
  obtain ⟨-, rfl⟩ := mkAppN_bvar_inj heq.symm
  intro ρ ρ' hR fs hf hf' e he
  refine hvs e ?_ _ _ (FrameRel.underBothTele_consList Fs fs hR hf hf')
  rw [List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega),
    List.nil_append]
  exact he

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

/-! ## The walk's outputs at any kind (syntactic) -/

section Syntax

open ConLeche (CheckM CheckError NestState NestFieldKind BinderMeta nestPos nestFields
  nestMemberCtor closeTelescope fueledOps openPisAtFvars structUsedLater)

/-- **A top-level output is bvar-closed, and hole-free at an ordinary
kind** (`nestPos_out` without the flat restriction). -/
theorem nestPos_top_out {env : Env} (henv : ConLeche.EnvWF env) {ctx : NestCtx} {F : Nat} :
    ∀ (fuel dep kb : Nat) (e : Expr) (st : NestState) (k : NestFieldKind) (nd : Expr)
      (st' : NestState),
      nestPos (fueledOps .verified F) env ctx fuel [] dep kb e st = .ok (k, nd, st') →
      e.looseBVarsBounded 0 = true → ctx.hiAt 0 ≤ dep →
      nd.looseBVarsBounded 0 = true ∧
      (k = .ordinary → nd.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = false) := by
  intro fuel
  induction fuel with
  | zero =>
    intro dep kb e st k nd st' hrun
    simp [nestPos, throw, throwThe, MonadExceptOf.throw] at hrun
  | succ fuel ih =>
    intro dep kb e st k nd st' hrun hcl hhi
    rw [nestPos] at hrun
    cases hw : ConLeche.whnf .verified env F dep e with
    | error err =>
      have hw' : (fueledOps .verified F).whnf env dep e = .error err := hw
      simp [hw', bind, Except.bind] at hrun
    | ok w =>
      have hw' : (fueledOps .verified F).whnf env dep e = .ok w := hw
      simp only [hw', bind, Except.bind, List.length_nil] at hrun
      have hwcl : w.looseBVarsBounded 0 = true := ConLeche.whnf_looseBVars henv F hw hcl
      by_cases hocc : w.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = false
      · rw [if_pos (by simpa using hocc)] at hrun
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl, -⟩ := hrun
        refine ⟨?_, fun _ => ?_⟩
        · split
          · exact hwcl
          · exact hcl
        · split
          · exact hocc
          · rename_i h; simpa using h
      rw [if_neg (by simpa using hocc)] at hrun
      split at hrun
      · -- `pi`
        rename_i a b mb
        by_cases ha : a.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = true
        · rw [if_pos ha] at hrun
          simp [throw, throwThe, MonadExceptOf.throw] at hrun
        rw [if_neg ha] at hrun
        split at hrun
        · simp at hrun
        rename_i v hv
        obtain ⟨k₁, nb, st₁⟩ := v
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl, rfl⟩ := hrun
        simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hwcl
        have hbcl := ConLeche.looseBVarsBounded_instantiate1 (d := dep) (ty := a) b 0 hwcl.2
        obtain ⟨h1, h2⟩ := ih (dep + 1) (kb + 1) _ st k₁ nb _ hv hbcl (by omega)
        have ha' : a.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = false := by simpa using ha
        refine ⟨?_, fun ho => ?_⟩
        · simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
          exact ⟨hwcl.1, ConLeche.looseBVarsBounded_abstract1 nb 0 h1⟩
        · simp only [Expr.nestOcc, ha', Bool.false_or]
          rw [nestOcc_abstract1 (by omega) nb 0]
          exact h2 ho
      · -- a head applied to arguments: the output is the reduct, which mentions a hole
        refine ⟨?_, fun hk => ?_⟩
        · repeat' split at hrun
          all_goals first
            | (simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
               obtain ⟨-, rfl, -⟩ := hrun; exact hwcl)
            | simp [throw, throwThe, MonadExceptOf.throw] at hrun
            | simp at hrun
            | skip
          all_goals (rename_i v hv; obtain ⟨k₁, st₁⟩ := v
                     simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
                     obtain ⟨-, rfl, -⟩ := hrun; exact hwcl)
        · repeat' split at hrun
          all_goals first
            | (simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
               obtain ⟨rfl, -, -⟩ := hrun; exact absurd hk (by simp))
            | simp [throw, throwThe, MonadExceptOf.throw] at hrun
            | simp at hrun
            | skip
          all_goals (rename_i v hv; obtain ⟨k₁, st₁⟩ := v
                     simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
                     obtain ⟨rfl, -, -⟩ := hrun
                     have := nestCont_not_flat hv
                     rw [hk] at this
                     exact absurd this (by decide))

/-- The kinds U4 guards: a recursive, reflexive or nested field. -/
@[expose] def nonOrd : NestFieldKind → Bool
  | .recursive _ | .reflexive _ | .nested _ _ => true
  | _ => false

/-- **U4, every guarded kind**: no later field and not the result uses a
recursive, reflexive or nested field (the walk's own check on its normal
form; `nestMemberCtor_inv` states the flat half). -/
theorem nestMemberCtor_u4 {ops : ConLeche.CheckerOps CheckM} {env : Env} {ctx : NestCtx}
    {nF : Nat} {crest : Expr} {st : NestState} {ks : List NestFieldKind} {tyN : Expr}
    {st' : NestState}
    (h : nestMemberCtor ops env ctx nF crest st = .ok (ks, tyN, st')) :
    ∀ i, i < nF → nonOrd (ks.getD i .ordinary) = true → structUsedLater tyN 0 i = false := by
  simp only [nestMemberCtor, bind, Except.bind] at h
  split at h
  · simp at h
  rename_i v hv
  obtain ⟨ks₁, nds, cur, st₁⟩ := v
  simp only at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i hany
  split at h
  · split at h
    rotate_left
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    intro i hi hno
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, not_exists, not_and] at hany
    cases hu : structUsedLater (closeTelescope nds (ctx.hiAt 0) cur) 0 i
    · rfl
    · exfalso
      refine hany i hi ?_ hu
      revert hno
      cases ks₁.getD i .ordinary <;> simp [nonOrd]
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **A member constructor's normal form, opened**, at every kind: its
telescope opens at the walk's depth; every opened domain is
erasure-equal to its field's output, hole-free at an ordinary kind. -/
theorem memberCtor_open {env : Env} (henv : ConLeche.EnvWF env) {ctx : NestCtx} {F : Nat}
    {nF : Nat} {crest tyN : Expr} {st₀ st₁ : NestState} {ks : List NestFieldKind}
    (hcl : crest.looseBVarsBounded 0 = true)
    (hm : nestMemberCtor (fueledOps .verified F) env ctx nF crest st₀ = .ok (ks, tyN, st₁)) :
    ∃ (nds : List (Expr × BinderMeta)) (xs : List Expr) (rest : Expr),
      openPisAtFvars nF tyN (ctx.hiAt 0) = some (xs, rest) ∧ ks.length = nF ∧
      nds.length = nF ∧
      ∀ (i : Nat) (x : Expr), xs[i]? = some x → ∃ k nd, ks[i]? = some k ∧
        nds[i]?.map (·.1) = some nd ∧ Expr.ErasedEq x.fvarTypeD nd ∧
        (k = .ordinary → nd.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = false) := by
  obtain ⟨err, nds, cur, hf, hr, htyN, -, -, -⟩ := nestMemberCtor_inv hm
  obtain ⟨xs₀, hop₀, hkl, hnl, hall⟩ := nestFields_inv nF 0 crest st₀ ks nds cur st₁ hf hr
  rw [Nat.add_zero] at hop₀
  obtain ⟨hcurcl, hxcl⟩ := ConLeche.Verify.openPisAtFvars_bounded nF hop₀ hcl
  have hxl₀ : xs₀.length = nF := ConLeche.Verify.openPisAtFvars_length nF hop₀
  have hfield : ∀ (i : Nat) (x : Expr), xs₀[i]? = some x → ∃ k nd,
      ks[i]? = some k ∧ nds[i]?.map (·.1) = some nd ∧ nd.looseBVarsBounded 0 = true ∧
      (k = .ordinary → nd.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = false) := by
    intro i x hx
    obtain ⟨k, nd, s1, s2, hk, hnd, hrun⟩ := hall i x hx
    rw [Nat.add_zero] at hrun
    obtain ⟨h1, h2⟩ := nestPos_top_out henv (ConLeche.whnfWalkFuel crest) _ 0 _ s1 k nd s2 hrun
      (hxcl x (List.mem_of_getElem? hx)) (by omega)
    exact ⟨k, nd, hk, hnd, h1, h2⟩
  have hndcl : ∀ p ∈ nds, p.1.looseBVarsBounded 0 = true := by
    intro p hp
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hp
    have hil : i < xs₀.length := by
      rw [hxl₀, ← hnl]; exact (List.getElem?_eq_some_iff.mp hi).1
    obtain ⟨k, nd, -, hnd, hcl', -⟩ := hfield i _ (List.getElem?_eq_getElem hil)
    rw [hi, Option.map_some, Option.some.injEq] at hnd
    rw [hnd]; exact hcl'
  obtain ⟨xs, rest, hop, -, hdoms⟩ := open_of_erasedEq_closeTelescope nds (ctx.hiAt 0) cur
    tyN hndcl hcurcl (by rw [htyN]; exact Expr.ErasedEq.rfl _)
  rw [hnl] at hop
  have hxl : xs.length = nF := ConLeche.Verify.openPisAtFvars_length nF hop
  refine ⟨nds, xs, rest, hop, hkl, hnl, fun i x hx => ?_⟩
  have hi : i < nF := by rw [← hxl]; exact (List.getElem?_eq_some_iff.mp hx).1
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, xs₀[i]? = some x₀ := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨k, nd, hk, hnd, -, hord⟩ := hfield i x₀ hx₀
  exact ⟨k, nd, hk, hnd, hdoms i x nd hx hnd, hord⟩

/-- No leaf at `q`: no occurrence in `[q, q + 1)`. -/
theorem nestOcc_nil_of_leaves {q : Nat} :
    ∀ (e : Expr), (∀ z ∈ e.fvarLeaves, z.1 ≠ q) → e.nestOcc [] q (q + 1) = false := by
  intro e
  induction e with
  | bvar _ => intro _; rfl
  | sort _ => intro _; rfl
  | lit _ => intro _; rfl
  | const n _ => intro _; simp [Expr.nestOcc]
  | fvar i ty _ =>
    intro h
    have := h (i, ty) (by simp [Expr.fvarLeaves])
    simp only [Expr.nestOcc, decide_eq_false_iff_not]
    omega
  | app f a ihf iha =>
    intro h
    simp only [Expr.nestOcc, Bool.or_eq_false_iff]
    exact ⟨ihf fun z hz => h z (by simp [Expr.fvarLeaves, hz]),
      iha fun z hz => h z (by simp [Expr.fvarLeaves, hz])⟩
  | lam ty b _ iht ihb =>
    intro h
    simp only [Expr.nestOcc, Bool.or_eq_false_iff]
    exact ⟨iht fun z hz => h z (by simp [Expr.fvarLeaves, hz]),
      ihb fun z hz => h z (by simp [Expr.fvarLeaves, hz])⟩
  | forallE ty b _ iht ihb =>
    intro h
    simp only [Expr.nestOcc, Bool.or_eq_false_iff]
    exact ⟨iht fun z hz => h z (by simp [Expr.fvarLeaves, hz]),
      ihb fun z hz => h z (by simp [Expr.fvarLeaves, hz])⟩
  | letE t v b iht ihv ihb =>
    intro h
    simp only [Expr.nestOcc, Bool.or_eq_false_iff]
    exact ⟨⟨iht fun z hz => h z (by simp [Expr.fvarLeaves, hz]),
      ihv fun z hz => h z (by simp [Expr.fvarLeaves, hz])⟩,
      ihb fun z hz => h z (by simp [Expr.fvarLeaves, hz])⟩
  | proj _ _ e ihe =>
    intro h
    simp only [Expr.nestOcc]
    exact ihe fun z hz => h z (by simp [Expr.fvarLeaves, hz])

/-- **U4, on the opened normal form**: a later field's domain does not
mention a field no later binder uses. -/
theorem u4_nestOcc {ctx : NestCtx} {nF j l : Nat} {tyN rest : Expr} {xs : List Expr} {x : Expr}
    (hop : openPisAtFvars nF tyN (ctx.hiAt 0) = some (xs, rest))
    (hW : Expr.WScoped (ctx.hiAt 0) tyN) (hU : structUsedLater tyN 0 j = false)
    (hj : j < nF) (hjl : j < l) (hx : xs[l]? = some x) :
    x.fvarTypeD.nestOcc [] (ctx.hiAt 0 + j) (ctx.hiAt 0 + j + 1) = false := by
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
  obtain ⟨ty, rfl⟩ := ConLeche.openPisAtFvars_index nF tyN (ctx.hiAt 0) hop l x hx
  exact h1 l hjl _ hx z (by simp only [Expr.fvarTypeD] at hz; simp [Expr.fvarLeaves, hz])

end Syntax

end ConLeche.Model

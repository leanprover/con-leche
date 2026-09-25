module

public import ConLeche.Model.Inductives.NestPosAcc
public import ConLeche.Model.Annot.LfpAcc
public import ConLeche.Model.Inductives.BlockPosRun
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Model.Inductives.StructEntryFree

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
      (∀ ρ ρ₀, R ρ ρ₀ → FieldsBound w ρ (abN.map (·.2.2))) →
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
      exact (univ_isTGUniverse hw).transitive hok0.1 ha
    · refine teleSmall_mkPisAV hw abD abN B (x.2.2 :: Δ) (R.underBoth x.2.2) hrest
        (underBoth_dom hdom) ?_
      rintro _ _ ⟨a, ρ, ρ₀, rfl, rfl, hR, ha, -⟩
      have hok0 := hok ρ ρ₀ hR
      simp only [List.map_cons] at hok0
      exact hok0.2 a (h0 ρ (hdom ρ ρ₀ hR).1 ▸ ha)
  | [], _ :: _, _, _, _, hE, _, _ => hE.elim
  | _ :: _, [], _, _, _, hE, _, _ => hE.elim

/-! ## The walked accessibility onto the datum's fields -/

/-- `TeleAccP` reads the bounds from field `l` on only. -/
theorem TeleAccP.congr {w : Nat} {Af Af' : Nat → (Nat → V) → V} :
    ∀ (Fs : List AnnotTerm) (l : Nat) (Q : Nat → Nat → Prop) (R : FrameRel V),
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
  lrefl := by
    rintro _ _ ⟨X, Y, hX, -, rfl, -⟩
    exact LfpDatum.accRel_refl hX

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

/-! ### `inProgress` never survives a member walk -/

set_option linter.unusedSimpArgs false in
theorem nestContNew_inProgress {ctx : NestCtx} {ops : ConLeche.CheckerOps CheckM} {env' : Env}
    {rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)}
    {prog : List NestHole} {kb : Nat} {n : Name} {us : List Level}
    {ds : List Expr} {nPc : Nat} {old : Option Nat} {st st' : NestState}
    (h : ConLeche.nestContNew ctx ops env' rec prog kb n us ds nPc old st = .ok (.inProgress, st')) :
    st'.restart.isSome = true := by
  unfold ConLeche.nestContNew at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' (first
    | (split at h)
    | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; assumption)
    | (simp [throw, throwThe, MonadExceptOf.throw] at h)
    | (simp at h))

theorem nestContKey_inProgress {ctx : NestCtx} {ops : ConLeche.CheckerOps CheckM} {env' : Env}
    {rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)}
    {prog : List NestHole} {kb : Nat} {n : Name} {us : List Level}
    {ds : List Expr} {nPc : Nat} {st st' : NestState}
    (h : ConLeche.nestContKey ctx ops env' rec prog kb n us ds nPc st = .ok (.inProgress, st')) :
    st'.restart.isSome = true := by
  unfold ConLeche.nestContKey at h
  split at h
  · split at h
    · simp at h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      rfl
  · split at h
    · split at h
      · simp [pure, Except.pure] at h
      · exact nestContNew_inProgress h
    · exact nestContNew_inProgress h

set_option linter.unusedSimpArgs false in
theorem nestCont_inProgress {ctx : NestCtx} {ops : ConLeche.CheckerOps CheckM} {env' : Env}
    {rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)}
    {prog : List NestHole} {kb : Nat} {n : Name} {us : List Level}
    {args : List Expr} {st st' : NestState}
    (h : ConLeche.nestCont ctx ops env' rec prog kb n us args st = .ok (.inProgress, st')) :
    st'.restart.isSome = true := by
  unfold ConLeche.nestCont at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' (first
    | (exact nestContKey_inProgress h)
    | (split at h)
    | (simp [throw, throwThe, MonadExceptOf.throw] at h)
    | (simp at h))

/-- **At the top, an in-progress kind comes with a pending restart.** -/
theorem nestPos_top_inProgress {env : Env} {ctx : NestCtx} {F : Nat} :
    ∀ (fuel dep kb : Nat) (e : Expr) (st : NestState) (nd : Expr) (st' : NestState),
      nestPos (fueledOps .verified F) env ctx fuel [] dep kb e st = .ok (.inProgress, nd, st') →
      st'.restart.isSome = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro dep kb e st nd st' hrun
    simp [nestPos, throw, throwThe, MonadExceptOf.throw] at hrun
  | succ fuel ih =>
    intro dep kb e st nd st' hrun
    rw [nestPos] at hrun
    cases hw : ConLeche.whnf .verified env F dep e with
    | error err =>
      have hw' : (fueledOps .verified F).whnf env dep e = .error err := hw
      simp [hw', bind, Except.bind] at hrun
    | ok w =>
      have hw' : (fueledOps .verified F).whnf env dep e = .ok w := hw
      simp only [hw', bind, Except.bind, List.length_nil] at hrun
      by_cases hocc : w.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = false
      · rw [if_pos (by simpa using hocc)] at hrun
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
        exact nomatch hrun.1
      rw [if_neg (by simpa using hocc)] at hrun
      split at hrun
      · -- `pi`
        split at hrun
        · simp [throw, throwThe, MonadExceptOf.throw] at hrun
        split at hrun
        · simp at hrun
        rename_i v hv
        obtain ⟨k₁, nb, st₁⟩ := v
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -, rfl⟩ := hrun
        exact ih _ _ _ _ _ _ hv
      · split at hrun
        · rename_i i ty hfn
          by_cases hmem : (decide (ctx.nP ≤ i) && decide (i < ctx.hiAt 0)) = true
          · rw [if_pos hmem] at hrun
            split at hrun
            · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
              obtain ⟨hk, -, -⟩ := hrun
              split at hk <;> exact nomatch hk
            · simp [throw, throwThe, MonadExceptOf.throw] at hrun
          · rw [if_neg hmem] at hrun
            by_cases hfr' : (decide (ctx.hiAt 0 ≤ i) && decide (i < ctx.hiAt 0)) = true
            · simp only [Bool.and_eq_true, decide_eq_true_eq] at hfr'
              omega
            · rw [if_neg hfr'] at hrun
              simp [throw, throwThe, MonadExceptOf.throw] at hrun
        · rename_i n us hfn
          split at hrun
          · simp [throw, throwThe, MonadExceptOf.throw] at hrun
          split at hrun
          · simp at hrun
          rename_i v hv
          obtain ⟨k₁, st₁⟩ := v
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -, rfl⟩ := hrun
          exact nestCont_inProgress hv
        · simp [throw, throwThe, MonadExceptOf.throw] at hrun

/-- **`nestFields`, inverted, each field's run leaving no restart
pending** (`nestFields_inv` with the post-states). -/
theorem nestFields_inv_nr
    {rec : List NestHole → Nat → Nat → Expr → NestState →
      CheckM (NestFieldKind × Expr × NestState)}
    {prog : List NestHole} {base : Nat} {err : CheckError} :
    ∀ (n j : Nat) (cur : Expr) (st : NestState) (ks : List NestFieldKind)
      (nds : List (Expr × BinderMeta)) (res : Expr) (st' : NestState),
      nestFields rec prog base err n j cur st = .ok (ks, nds, res, st') → st'.restart = none →
      ∃ xs, openPisAtFvars n cur (base + j) = some (xs, res) ∧ ks.length = n ∧ nds.length = n ∧
        ∀ (i : Nat) (x : Expr), xs[i]? = some x → ∃ k nd st₁ st₂, ks[i]? = some k ∧
          nds[i]?.map (·.1) = some nd ∧
          rec prog (base + j + i) 0 x.fvarTypeD st₁ = .ok (k, nd, st₂) ∧ st₂.restart = none
  | 0, j, cur, st, ks, nds, res, st', h, _ => by
    simp only [nestFields, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨[], by simp [openPisAtFvars], rfl, rfl, fun i x hx => nomatch hx⟩
  | n + 1, j, cur, st, ks, nds, res, st', h, hr => by
    cases cur with
    | forallE a b bm =>
      simp only [nestFields, bind, Except.bind] at h
      split at h
      · simp at h
      rename_i v hv
      obtain ⟨k, nd, st₁⟩ := v
      simp only at h
      split at h
      · rename_i hsome
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, -, -, rfl⟩ := h
        simp [hr] at hsome
      rename_i hnone
      split at h
      · simp at h
      rename_i v' hv'
      obtain ⟨ks', nds', res', st₂⟩ := v'
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      obtain ⟨xs, hop, hkl, hnl, hall⟩ := nestFields_inv_nr n (j + 1) _ st₁ ks' nds' res' st₂ hv' hr
      refine ⟨.fvar (base + j) a :: xs, ?_, by simp [hkl], by simp [hnl], ?_⟩
      · simp only [openPisAtFvars]
        rw [show base + j + 1 = base + (j + 1) by omega, hop]
      · intro i x hx
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          subst hx
          exact ⟨k, nd, st, st₁, rfl, rfl, by simpa [Expr.fvarTypeD] using hv,
            by simpa using hnone⟩
        | succ i =>
          simp only [List.getElem?_cons_succ] at hx
          obtain ⟨k', nd', s1, s2, h1, h2, h3, h4⟩ := hall i x hx
          refine ⟨k', nd', s1, s2, by simpa using h1, by simpa using h2, ?_, h4⟩
          rw [show base + j + (i + 1) = base + (j + 1) + i by omega]
          exact h3
    | _ => simp [nestFields, throw, throwThe, MonadExceptOf.throw] at h

/-- **A member constructor's normal form, opened**, at every kind: its
telescope opens at the walk's depth; every opened domain is
erasure-equal to its field's output, hole-free at an ordinary kind. -/
theorem memberCtor_open {env : Env} (henv : ConLeche.EnvWF env) {ctx : NestCtx} {F : Nat}
    {nF : Nat} {crest tyN cur : Expr} {st₀ st₁ : NestState} {ks : List NestFieldKind}
    {nds : List (Expr × BinderMeta)} {err : CheckError}
    (hcl : crest.looseBVarsBounded 0 = true)
    (hf : nestFields (nestPos (fueledOps .verified F) env ctx (ConLeche.whnfWalkFuel crest)) []
      (ctx.hiAt 0) err nF 0 crest st₀ = .ok (ks, nds, cur, st₁))
    (hr : st₁.restart = none) (htyN : tyN = closeTelescope nds (ctx.hiAt 0) cur) :
    ∃ (xs : List Expr) (rest : Expr),
      openPisAtFvars nF tyN (ctx.hiAt 0) = some (xs, rest) ∧ ks.length = nF ∧
      nds.length = nF ∧
      ∀ (i : Nat) (x : Expr), xs[i]? = some x → ∃ k nd, ks[i]? = some k ∧
        nds[i]?.map (·.1) = some nd ∧ Expr.ErasedEq x.fvarTypeD nd ∧
        (k = .ordinary → nd.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = false) ∧
        k ≠ .inProgress := by
  obtain ⟨xs₀, hop₀, hkl, hnl, hall⟩ := nestFields_inv_nr nF 0 crest st₀ ks nds cur st₁ hf hr
  rw [Nat.add_zero] at hop₀
  obtain ⟨hcurcl, hxcl⟩ := ConLeche.Verify.openPisAtFvars_bounded nF hop₀ hcl
  have hxl₀ : xs₀.length = nF := ConLeche.Verify.openPisAtFvars_length nF hop₀
  have hfield : ∀ (i : Nat) (x : Expr), xs₀[i]? = some x → ∃ k nd,
      ks[i]? = some k ∧ nds[i]?.map (·.1) = some nd ∧ nd.looseBVarsBounded 0 = true ∧
      (k = .ordinary → nd.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = false) ∧
      k ≠ .inProgress := by
    intro i x hx
    obtain ⟨k, nd, s1, s2, hk, hnd, hrun, hnr⟩ := hall i x hx
    rw [Nat.add_zero] at hrun
    obtain ⟨h1, h2⟩ := nestPos_top_out henv (ConLeche.whnfWalkFuel crest) _ 0 _ s1 k nd s2 hrun
      (hxcl x (List.mem_of_getElem? hx)) (by omega)
    refine ⟨k, nd, hk, hnd, h1, h2, fun hin => ?_⟩
    subst hin
    have := nestPos_top_inProgress (ConLeche.whnfWalkFuel crest) _ 0 _ s1 nd s2 hrun
    rw [hnr] at this
    exact absurd this (by decide)
  have hndcl : ∀ p ∈ nds, p.1.looseBVarsBounded 0 = true := by
    intro p hp
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hp
    have hil : i < xs₀.length := by
      rw [hxl₀, ← hnl]; exact (List.getElem?_eq_some_iff.mp hi).1
    obtain ⟨k, nd, -, hnd, hcl', -, -⟩ := hfield i _ (List.getElem?_eq_getElem hil)
    rw [hi, Option.map_some, Option.some.injEq] at hnd
    rw [hnd]; exact hcl'
  obtain ⟨xs, rest, hop, -, hdoms⟩ := open_of_erasedEq_closeTelescope nds (ctx.hiAt 0) cur
    tyN hndcl hcurcl (by rw [htyN]; exact Expr.ErasedEq.rfl _)
  rw [hnl] at hop
  have hxl : xs.length = nF := ConLeche.Verify.openPisAtFvars_length nF hop
  refine ⟨xs, rest, hop, hkl, hnl, fun i x hx => ?_⟩
  have hi : i < nF := by rw [← hxl]; exact (List.getElem?_eq_some_iff.mp hx).1
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, xs₀[i]? = some x₀ := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨k, nd, hk, hnd, -, hord, hnip⟩ := hfield i x₀ hx₀
  exact ⟨k, nd, hk, hnd, hdoms i x nd hx hnd, hord, hnip⟩

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

/-- **A walked telescope's normal form, opened** (any walk `rec`, any
frames, any base depth — lane ACCMODEL session 3, a container frame's
constructors): the closed normal form opens at the base; every opened
domain is erasure-equal to its field's output. -/
theorem fields_open
    {rec : List NestHole → Nat → Nat → Expr → NestState →
      CheckM (NestFieldKind × Expr × NestState)}
    {prog : List NestHole} {base : Nat} {err : CheckError} {nF : Nat} {cur res : Expr}
    {st₀ st₁ : NestState} {ks : List NestFieldKind} {nds : List (Expr × BinderMeta)}
    (hcl : cur.looseBVarsBounded 0 = true)
    (hf : nestFields rec prog base err nF 0 cur st₀ = .ok (ks, nds, res, st₁))
    (hr : st₁.restart = none) (hndcl : ∀ p ∈ nds, p.1.looseBVarsBounded 0 = true) :
    ∃ (xs : List Expr) (rest : Expr),
      openPisAtFvars nF (closeTelescope nds base res) base = some (xs, rest) ∧ ks.length = nF ∧
      nds.length = nF ∧
      ∀ (i : Nat) (x : Expr), xs[i]? = some x → ∃ nd,
        nds[i]?.map (·.1) = some nd ∧ Expr.ErasedEq x.fvarTypeD nd := by
  obtain ⟨xs₀, hop₀, hkl, hnl, -⟩ := nestFields_inv_nr nF 0 cur st₀ ks nds res st₁ hf hr
  rw [Nat.add_zero] at hop₀
  obtain ⟨hcurcl, -⟩ := ConLeche.Verify.openPisAtFvars_bounded nF hop₀ hcl
  obtain ⟨xs, rest, hop, -, hdoms⟩ := open_of_erasedEq_closeTelescope nds base res
    (closeTelescope nds base res) hndcl hcurcl (Expr.ErasedEq.rfl _)
  rw [hnl] at hop
  have hxl : xs.length = nF := ConLeche.Verify.openPisAtFvars_length nF hop
  refine ⟨xs, rest, hop, hkl, hnl, fun i x hx => ?_⟩
  have hi : i < nF := by rw [← hxl]; exact (List.getElem?_eq_some_iff.mp hx).1
  obtain ⟨p, hp⟩ : ∃ p, nds[i]? = some p := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  exact ⟨p.1, by rw [hp]; rfl, hdoms i x p.1 hx (by rw [hp]; rfl)⟩

end Syntax

/-! ## One constructor -/

section OneCtor

open ConLeche (ConstantVal CheckM NestState NestFieldKind BlockParts BlockShape instPisWith
  nestAbstract nestHoles nestMemberCtor openPisAtFvars fueledOps)

/-- NoBVar of a disjunction. -/
theorem noBVar_or {P₁ P₂ : Nat → Prop} {e : AnnotTerm} (h₁ : NoBVar P₁ e) (h₂ : NoBVar P₂ e) :
    NoBVar (fun i => P₁ i ∨ P₂ i) e := by
  have := noBVar_exists' (α := Bool) (P := fun b i => if b then P₁ i else P₂ i) (e := e)
    fun b => by cases b <;> simpa
  refine NoBVar.mono (fun i hi => ?_) this
  rcases hi with h | h
  · exact ⟨true, by simpa using h⟩
  · exact ⟨false, by simpa using h⟩

/-- **A member constructor's field telescope is accessible along the
accessibility relation at the hole frame** (at a positive level), with
bounds reading only the agreeing positions, its ordinary fields' readings
likewise, and its result indices alike at any two hole frames — the
premises `LfpDatum.accTuple_holeOp` asks of one constructor.  From the
walk (`nestMemberCtor_acc`, the container case the premise `hcont`), its
U2 typing, the datum's reading facts and grading, and U4. -/
theorem blockCtorAcc_of_walk {env : Env} {m : EnvModel V env} {ψ : Name → Nat}
    (hin : Rules.RulesInputs V m ψ) {F : Nat}
    {d : BlockData V} {lps : List Name} {cvTas : List ConstantVal} {p₁ : BlockShape}
    {isRec : Bool}
    (hN : BlockNamesOk (V := V) d cvTas) (hcore : BlockHoleCtxFacts m d lps cvTas p₁ isRec)
    {p : BlockParts} (hnames : p.memberNames = d.memberNames) (hlps : p.lps = lps)
    (hnP : p.nP = d.nP) (hnIdxs : p.nIdxs = d.nIdxs) (hk : d.k = d.memberNames.length)
    {cvTa0 : ConstantVal} {fvsP : List Expr} {rest : Expr} {holes : List Expr}
    (hcv0 : cvTas.head? = some cvTa0)
    (hop0 : openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest))
    (hholes : nestHoles (p.nestCtx fvsP env.find? env.consts) = some holes)
    {c j : Nat} {cA : ConstantVal × Nat} (hcj : (d.ctorsM c)[j]? = some cA)
    (hCf : cA.1.type.hasFvar = false) (hCb : cA.1.type.looseBVarsBounded 0 = true)
    {crest : Expr}
    (hcrest : instPisWith fvsP
      (nestAbstract (p.nestCtx fvsP env.find? env.consts) holes cA.1.type) = some crest)
    {P : NestFieldKind → Prop} {I : NestState → Prop}
    (hcont : ∀ rec, NestPosAcc m ψ (d.w ψ) (p.nestCtx fvsP env.find? env.consts) P I rec →
      ContAcc m ψ (d.w ψ) (p.nestCtx fvsP env.find? env.consts) P I F rec)
    {st₀ st₁ : NestState} {ks : List NestFieldKind} {tyN : Expr}
    (hm : nestMemberCtor (fueledOps .verified F) env (p.nestCtx fvsP env.find? env.consts) cA.2
      crest st₀ = .ok (ks, tyN, st₁))
    (hks : ∀ k ∈ ks, P k) (hI : I st₀)
    {ty : Expr} (hinf : ConLeche.inferTypeCore .verified env F
      ((p.nestCtx fvsP env.find? env.consts).hiAt 0) crest = .ok ty)
    (hnf : d.nfFF c j = tyN)
    {ρp : Nat → V} (hs : Sat V (d.params ψ).reverse ρp) (hw : d.w ψ ≠ 0)
    (hG : ∀ X, InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X →
      FieldsOkB (d.w ψ) (d.toLfp.frame ψ ρp X) (d.absF ψ c j)) :
    ∃ (ord : Nat → Bool) (Af : Nat → (Nat → V) → V),
      TeleAccP (d.w ψ) Af 0 (d.toLfp.MemberQ ψ) (d.toLfp.accRel ψ ρp) (d.absF ψ c j) ∧
      (∀ l τ τ', TAgr d.k ord l τ τ' → Af l τ = Af l τ') ∧
      (∀ (i : Nat) (G : AnnotTerm), (d.absF ψ c j)[i]? = some G → ord i = true →
        ∀ τ τ', TAgr d.k ord i τ τ' → interp V τ G = interp V τ' G) ∧
      (∀ X X', InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X →
        InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X' →
        ∀ fs, SpineFit (d.toLfp.frame ψ ρp X) (d.absF ψ c j) fs →
          SpineFit (d.toLfp.frame ψ ρp X') (d.absF ψ c j) fs →
          ∀ e ∈ d.absE ψ c j, interp V (consList fs (d.toLfp.frame ψ ρp X)) e
            = interp V (consList fs (d.toLfp.frame ψ ρp X')) e) := by
  obtain ⟨ab, abN, hhi, hca, hNr, hab, habLen, hlabN, hfr, hCP, hgr, hfrN, -, -, hEq,
    hsatFrame⟩ := blockCtorHoleCtx hin hN hcore hnames hlps hnP hnIdxs hk hcv0 hop0 hholes hcj
      hCf hCb hcrest hinf hm hnf
  generalize hL : d.holeCtx ψ = L at hCP hgr hEq hsatFrame
  have hcN : (p.nestCtx fvsP env.find? env.consts).names = d.memberNames := hnames
  have hcP : (p.nestCtx fvsP env.find? env.consts).nP = d.nP := hnP
  have hcI : (p.nestCtx fvsP env.find? env.consts).nIdxs = d.nIdxs := hnIdxs
  rw [← hhi] at hca hgr hfr hCP hfrN hNr
  generalize hctx : p.nestCtx fvsP env.find? env.consts = ctx at *
  have hcNl : ctx.names.length = d.k := by rw [hcN, hk]
  -- the members' arities
  have har : ∀ t, t < d.k → (d.toLfp.pars t ψ).length + (d.toLfp.ids t ψ).length
      = ctx.nP + ctx.nIdxs.getD t 0 := by
    intro t ht
    obtain ⟨cvTb, hcvb⟩ : ∃ cvTb, cvTas[t]? = some cvTb :=
      ⟨_, List.getElem?_eq_getElem (by rw [hN.2.2]; exact ht)⟩
    have hFDt := (hcore.1 t cvTb hcvb).2
    show (((d.ppsM t ψ).take d.nP).map (·.2.2)).length
      + (((d.ppsM t ψ).drop d.nP).map (·.2.2)).length = _
    simp only [List.length_map, List.length_take, List.length_drop, hFDt.len ψ, hcP, hcI]
    show _ = d.nP + d.nIdxAt t
    omega
  -- the relation, and the fields' values small
  have hR := holeRelA_accRel (m := m) hw hhi hcNl hcP har (hsatFrame ρp hs)
  have hG' : ∀ ρ ρ₀, d.toLfp.accRel ψ ρp ρ ρ₀ → FieldsOkB (d.w ψ) ρ (abN.map (·.2.2)) := by
    rintro _ _ ⟨X, Y, hX, -, rfl, -⟩
    rw [hab]
    exact hG X hX
  have hsm : TeleSmall (d.w ψ) ab.length (d.toLfp.accRel ψ ρp)
      (mkPisAV ab (AnnotTerm.mkAppN (.bvar (cA.2 + (d.k - 1 - c)))
        (paramBvarsAt d.nP (ctx.hiAt 0 + cA.2) ++ d.absE ψ c j))) :=
    teleSmall_mkPisAV hw ab abN _ L.reverse _ hEq hR.dom fun ρ ρ₀ h => (hG' ρ ρ₀ h).toBound hw
  rw [habLen] at hsm
  -- the walk
  obtain ⟨⟨nds, cur, err, hf, hr, htyN, hPi⟩, -⟩ :=
    nestMemberCtor_acc hin ctx F hw hcont hm hks hfr hI hCP hca hgr hR hsm
  rw [← habLen] at hPi
  obtain ⟨Af, htele, hinv, hQf⟩ := teleAccP_of_piAccThen hw ab abN _ (ctx.hiAt 0) 0
    (nds.map (·.1)) L.reverse _ (d.toLfp.MemberQ ψ) hEq hR.dom (fun ρ ρ₀ h => (hG' ρ ρ₀ h).toBound hw)
    (holeQ_top_iff hhi hcNl hcP har) (Nat.le_refl _) hPi
  -- the syntax: the opened normal form, U4
  obtain ⟨xs, rest', hopN, hkl, hnl, hxs⟩ := memberCtor_open m.wf hfr.2.1 hf hr htyN
  have hU4 := nestMemberCtor_u4 hm
  obtain ⟨pps, b, hst, -, hppl, hdoms⟩ := denoteMeta_openPis cA.2 hopN hNr
  rw [← hlabN, stripPisAV_mkPisAV] at hst
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hst).symm
  have hxl : xs.length = cA.2 := ConLeche.Verify.openPisAtFvars_length cA.2 hopN
  classical
  let ord : Nat → Bool := fun l => !nonOrd (ks.getD l .ordinary)
  refine ⟨ord, fun l => if l < cA.2 then Af l else fun _ => empty, ?_, ?_, ?_, ?_⟩
  · -- the telescope
    rw [← hab]
    refine TeleAccP.congr _ 0 _ _ (fun l' _ hl' => ?_) htele
    have : l' < cA.2 := by simpa [hlabN] using hl'
    simp only [if_pos this]
  · -- the fields' bounds read the agreeing positions
    intro l τ τ' hag
    by_cases hl : l < cA.2
    · simp only [if_pos hl]
      obtain ⟨x, hx⟩ : ∃ x, xs[l]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨k, nd, hkk, hnd, hE, -, -⟩ := hxs l x hx
      have hnd' : (nds.map (·.1))[l]? = some nd := by
        rw [List.getElem?_map]; exact hnd
      have hinvl := hinv l nd (by omega) hnd'
      rw [Nat.zero_add] at hinvl
      refine hinvl τ τ' fun i hi => ?_
      rcases hi with hi | ⟨hlt, hpar⟩
      rotate_left
      · refine (hag i).2 ?_
        rw [hhi, hcP] at hpar
        omega
      obtain ⟨hlt, hocc, hnh⟩ := hi
      by_cases hil : i < l
      · by_cases hoj : ord (l - 1 - i) = true
        · exact (hag i).1 hil hoj
        · exfalso
          have hno : nonOrd (ks.getD (l - 1 - i) .ordinary) = true := by
            simpa [ord] using hoj
          have hU := hU4 (l - 1 - i) (by omega) hno
          have hfree := u4_nestOcc hopN hfrN.1 hU (by omega) (by omega) hx
          rw [erasedEq_nestOcc _ _ hE] at hfree
          rw [show ctx.hiAt 0 + l - 1 - i = ctx.hiAt 0 + (l - 1 - i) by omega,
            show ctx.hiAt 0 + l - i = ctx.hiAt 0 + (l - 1 - i) + 1 by omega, hfree] at hocc
          exact Bool.false_ne_true hocc
      · refine (hag i).2 ?_
        refine Nat.le_of_not_lt fun hlk => hnh ?_
        simp only [holeP, List.length_nil, hhi]
        omega
    · simp only [if_neg hl]
  · -- the ordinary fields read the agreeing positions
    intro i G hGi hoi τ τ' hag
    rw [← hab] at hGi
    have hi : i < cA.2 := by
      have := (List.getElem?_eq_some_iff.mp hGi).1
      simpa [hlabN] using this
    obtain ⟨x, hx⟩ : ∃ x, xs[i]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨k, nd, hkk, -, hE, hord, hnip⟩ := hxs i x hx
    obtain ⟨p', hp', -, hread⟩ := hdoms i x hx
    rw [List.getElem?_map, hp', Option.map_some, Option.some.injEq] at hGi
    subst hGi
    have hkD : ks.getD i .ordinary = k := by rw [List.getD_eq_getElem?_getD, hkk]; rfl
    have hkord : k = .ordinary := by
      have h' : (!nonOrd (ks.getD i .ordinary)) = true := hoi
      rw [hkD] at h'
      have : nonOrd k = false := by simpa using h'
      cases k with
      | ordinary => rfl
      | inProgress => exact absurd rfl hnip
      | _ => simp [nonOrd] at this
    have hwx := openPisAtFvars_typeWScoped cA.2 hopN hfrN.1 i x hx
    have hholes' : NoBVar (holeP (ctx.hiAt 0 + i) ctx.nP (ctx.hiAt 0)) p'.2.2 := by
      refine denoteMeta_noBVar_of_nestOcc (m := m) (names := ctx.names) _ _ hwx
        (by simp [NestCtx.hiAt]) ?_ hread
      rw [erasedEq_nestOcc _ _ hE]
      exact hord hkord
    have hslots : NoBVar (fun q => ∃ jj, jj < i ∧ ord jj = false ∧ LfpDatum.fieldSlot jj i q)
        p'.2.2 := by
      refine noBVar_exists' (P := fun jj q => jj < i ∧ ord jj = false ∧ LfpDatum.fieldSlot jj i q)
        fun jj => ?_
      by_cases hjj : jj < i ∧ ord jj = false
      · have h' : (!nonOrd (ks.getD jj .ordinary)) = false := hjj.2
        have hno : nonOrd (ks.getD jj .ordinary) = true := by simpa using h'
        exact NoBVar.mono (fun q hq => hq.2.2)
          (u4_fieldSlot (m := m) hopN hfrN.1 (hU4 jj (by omega) hno) (by omega) hjj.1 hx hread)
      · exact NoBVar.mono (fun q hq => absurd ⟨hq.1, hq.2.1⟩ hjj) hholes'
    refine interp_congr_noBVar _ (noBVar_or hholes' hslots) fun q hq => ?_
    by_cases hqi : q < i
    · refine (hag q).1 hqi (Classical.byContradiction fun hqo => ?_)
      exact hq (Or.inr ⟨i - 1 - q, by omega, by simpa using hqo, by
        simp only [LfpDatum.fieldSlot]; omega⟩)
    · refine (hag q).2 (Nat.le_of_not_lt fun hlt => hq (Or.inl ?_))
      simp only [holeP, hhi]
      omega
  · -- the result indices
    intro X X' hX hX' fs hf hf' e he
    rw [← hab] at hf hf'
    exact resC_of_resultIdxConst (by simp [paramBvarsAt, hcP]) hQf _ _
      ⟨X, X', hX, hX', rfl, rfl⟩ fs hf hf' e he

end OneCtor

end ConLeche.Model

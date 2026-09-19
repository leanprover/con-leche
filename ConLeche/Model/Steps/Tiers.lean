module

import ConLeche.Model.Steps.Reads
public import ConLeche.Model.Steps.ReadsIO
import ConLeche.Model.Steps.CapsRows
import ConLeche.Model.Steps.StrLit
public import ConLeche.Model.Steps.ProjRows
import ConLeche.Model.Steps.IotaRows
import ConLeche.Model.Steps.IrrelFast
public import ConLeche.Model.Rules.Inputs
public section

/-!
# The tiers assembly (task #161, P4): one env-fixed bundle, one induction

`checkSoundP_of_inputs` (`AssemblyP.lean`) closes the induction over
the three quarters' ∀-environment input structures.  The declaration
fold cannot inhabit those: it holds an `EnvModelM` for **one**
environment at a time.  This file is the env-fixed re-assembly:

* `TierInputsAt` — every residue the P ladder still routes, at one
  `(env, m, φ)`, sorted by discharge tier (install / iota / literal /
  caps).  The env-tier entries are `EnvModelM` consequences
  (`TierInputsAt.ofEnvModelM`); the rest are the semantic-content bill
  the frontier-transformation table records.  Since task #305 R-nat
  the two literal entries are the SEMANTIC rows
  `Rules.NatSuccRow`/`Rules.NatOpRow` (`Model/Rules/Inputs.lean`) and
  not the run rows: `reduceNatStep_of_rows` below is the `reduceNat`
  run inversion, and the only thing in the literal tier that ever
  needed a `WhnfClaim`.
* `checkSoundAt` — the four claims at every fuel, at the fixed
  environment, with the of_claims discharges (batches 6/7) **wired
  in**: proof irrelevance, the spine congruences, η, `stuckIrrel`'s
  cascade, the string expansion, the delta identity, the totality
  factors, and the derived sort fact are all supplied from the
  induction hypotheses at each step — none of them appears in the
  bundle.

The quarter-level ∀-env assemblies (`AssemblyP.lean`) remain the
frozen quarter statements; this file is what the fold consumes.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## The literal accelerations: the run rows, from the semantic rows

`TierInputsAt`'s two literal fields are the SEMANTIC rows
`Rules.NatSuccRow`/`Rules.NatOpRow` (`Model/Rules/Inputs.lean`),
discharged from `EnvModelM.nat_ops`/`div_mod` in `Model/NatStep.lean`.
What is left here is the RUN side, and only it: the `reduceNat` branch
analysis, the whnf induction hypothesis at the two arguments (the one
place a `WhnfClaim` is needed), and the reduct's frame.  The
`natOpV_*` case split over the fourteen operations lives in
`Model/NatStep.lean` and nowhere else. -/

/-- An application's grading splits. -/
theorem wellDenotedV_app_inv {ρ : Nat → V} {fa aa : AnnotTerm}
    (h : WellDenotedV V ρ (.app fa aa)) :
    WellDenotedV V ρ fa ∧ WellDenotedV V ρ aa := by
  obtain ⟨h1, h2⟩ := h
  rw [WellDenoted_app] at h1
  rw [AnnotValid_app] at h2
  exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2.1, h2.2⟩⟩

/-- An application's grading transports along an argument of equal
interpretation: the slot witness only mentions the argument's
`interp`. -/
theorem wellDenotedV_app_congr {ρ : Nat → V} {fa aa aa' : AnnotTerm}
    (h : WellDenotedV V ρ (.app fa aa)) (hok : WellDenotedV V ρ aa')
    (hi : interp V ρ aa = interp V ρ aa') :
    WellDenotedV V ρ (.app fa aa') := by
  obtain ⟨h1, h2⟩ := h
  rw [WellDenoted_app] at h1
  rw [AnnotValid_app] at h2
  obtain ⟨hf, -, v, A, B, hfm, ham, hcod⟩ := h1
  refine ⟨?_, ?_⟩
  · rw [WellDenoted_app]
    exact ⟨hf, hok.1, v, A, B, hfm, by rw [← hi]; exact ham, hcod⟩
  · rw [AnnotValid_app]
    exact ⟨h2.1, hok.2⟩

/-- The same at the function position. -/
theorem wellDenotedV_appFn_congr {ρ : Nat → V} {fa fa' aa : AnnotTerm}
    (h : WellDenotedV V ρ (.app fa aa)) (hok : WellDenotedV V ρ fa')
    (hi : interp V ρ fa = interp V ρ fa') :
    WellDenotedV V ρ (.app fa' aa) := by
  obtain ⟨h1, h2⟩ := h
  rw [WellDenoted_app] at h1
  rw [AnnotValid_app] at h2
  obtain ⟨-, ha, v, A, B, hfm, ham, hcod⟩ := h1
  refine ⟨?_, ?_⟩
  · rw [WellDenoted_app]
    exact ⟨hok.1, ha, v, A, B, by rw [← hi]; exact hfm, ham, hcod⟩
  · rw [AnnotValid_app]
    exact ⟨hok.2, h2.2⟩

/-- A two-part reading, assembled. -/
theorem denoteMeta_app_mk {acval : Name → (Name → Nat) → AnnotTerm}
    {d : Nat} {f a : Expr} {fa aa : AnnotTerm}
    (hf : denoteMeta acval env φ d f = some fa)
    (ha : denoteMeta acval env φ d a = some aa) :
    denoteMeta acval env φ d (.app f a) = some (.app fa aa) := by
  rw [denoteMeta, hf, ha]
  rfl

/-- The frame conditions of a unary application's argument
(`frame_app1R`'s mirror). -/
theorem frame_app1 {m : EnvModel V env} {d : Nat}
    {Δa : List AnnotTerm} {c : Name} {a : Expr}
    (hws : Expr.WScoped d (.app (.const c []) a))
    (hb : (Expr.app (.const c []) a).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app (.const c []) a))
    (hC : CtxOk m φ d Δa (.app (.const c []) a)) :
    Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded a ∧ CtxOk m φ d Δa a := by
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact ⟨hws.2, hb.2, fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]),
    hC.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl])⟩

/-- The frame conditions of a binary application's two arguments
(`frame_app2R`'s mirror). -/
theorem frame_app2 {m : EnvModel V env} {d : Nat}
    {Δa : List AnnotTerm} {c : Name} {a b : Expr}
    (hws : Expr.WScoped d (.app (.app (.const c []) a) b))
    (hb : (Expr.app (.app (.const c []) a) b).looseBVarsBounded 0
      = true)
    (hLb : Expr.LeavesBounded (.app (.app (.const c []) a) b))
    (hC : CtxOk m φ d Δa (.app (.app (.const c []) a) b)) :
    (Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded a ∧ CtxOk m φ d Δa a) ∧
      (Expr.WScoped d b ∧ b.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded b ∧ CtxOk m φ d Δa b) := by
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  refine ⟨⟨hws.1.2, hb.1.2, fun l hl => hLb l ?_,
      hC.of_subset (fun l hl => ?_)⟩,
    hws.2, hb.2, fun l hl => hLb l ?_, hC.of_subset (fun l hl => ?_)⟩ <;>
    simp [Expr.fvarLeaves, hl]

/-- **The reduct of a literal acceleration is a closed atom**, so its
frame conditions and its leaf list are free (`ConLeche.reduceNat_inv`;
the guarded strengthening `Steps/Nat.lean`'s `reduceNat_natLeaf` adds
is not needed here — the reduct's READING comes from the semantic
rows). -/
theorem frame_of_reduceNat {fuel d : Nat} {e e₂ : Expr}
    (h : ConLeche.reduceNatFueled μ env fuel d e = .ok (some e₂)) :
    Expr.WScoped d e₂ ∧ e₂.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded e₂ ∧ e₂.fvarLeaves = [] := by
  rcases ConLeche.reduceNat_inv h with ⟨n, rfl⟩ | ⟨bn, rfl⟩ <;>
    exact ⟨Expr.WScoped.of_not_hasFvar rfl, rfl,
      Expr.LeavesBounded.of_not_hasFvar rfl, by simp [Expr.fvarLeaves]⟩

/-- **The unary clause's run inversion**: `Nat.succ` packing.  The
argument is head-normalised (`hwr` reads the reduct, `ihw` identifies
it) and `Rules.NatSuccRow` does the rest. -/
theorem reduceNatCore_unary {m : EnvModel V env} {fuel : Nat}
    (hsucc : Rules.NatSuccRow m φ) (hwr : WhnfReads m μ φ fuel)
    (ihw : WhnfClaim μ m φ fuel)
    {d : Nat} {Δa : List AnnotTerm} {c : Name} {a e₂ : Expr}
    {ea : AnnotTerm}
    (h : ConLeche.reduceNatFueled μ env fuel d (.app (.const c []) a)
      = .ok (some e₂))
    (hws : Expr.WScoped d (.app (.const c []) a))
    (hb : (Expr.app (.const c []) a).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app (.const c []) a))
    (hC : CtxOk m φ d Δa (.app (.const c []) a))
    (hea : denoteMeta m.acval env φ d (.app (.const c []) a) = some ea)
    (hok : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) :
    ∃ ea₂, denoteMeta m.acval env φ d e₂ = some ea₂ ∧
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea₂) ∧
      ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea = interp V ρ ea₂ := by
  obtain ⟨hwsa, hba, hLa, hCa⟩ := frame_app1 hws hb hLb hC
  obtain ⟨fa, aa, hfa, haa, rfl⟩ := denoteMeta_app_inv hea
  have hokA : ∀ ρ' : Nat → V, Sat V Δa ρ' → WellDenotedV V ρ' aa :=
    fun ρ' hρ' => (wellDenotedV_app_inv (hok ρ' hρ')).2
  simp only [ConLeche.reduceNatFueled, ConLeche.reduceNat, Bind.bind,
    Except.bind, ConLeche.whnf_def] at h
  split at h
  · next hcond =>
    obtain ⟨rfl, hnat⟩ := hcond
    cases hwa : ConLeche.whnf μ env fuel d a with
    | error err => rw [hwa] at h; exact nomatch h
    | ok a0 =>
    rw [hwa] at h
    dsimp only at h
    cases hra : ConLeche.rawNatLit? a0 with
    | none => rw [hra] at h; simp [pure, Except.pure] at h
    | some n =>
      rw [hra] at h
      simp only [pure, Except.pure, Except.ok.injEq,
        Option.some.injEq] at h
      subst h
      obtain ⟨aa0, haa0⟩ :=
        hwr hwa hwsa hba hLa (LeafReads.of_ctxOk hCa) haa
      obtain ⟨hokA0, hiA⟩ := ihw hwa hwsa hba hLa hCa haa haa0 hokA
      obtain ⟨ra, hrar, hgra, heq⟩ :=
        hsucc hnat hra (denoteMeta_app_mk hfa haa0)
          (fun ρ hρ =>
            wellDenotedV_app_congr (hok ρ hρ) (hokA0 ρ hρ) (hiA ρ hρ))
      refine ⟨ra, hrar, hgra, fun ρ hρ => ?_⟩
      refine Eq.trans ?_ (heq ρ hρ)
      rw [interp_app, interp_app, hiA ρ hρ]
  · simp [pure, Except.pure] at h

/-- **The binary clause's run inversion**: the fourteen certified
operations, and the WF-pin safety net (which throws on literal
arguments).  Both arguments are head-normalised, then
`Rules.NatOpRow` folds. -/
theorem reduceNatCore_binary {m : EnvModel V env} {fuel : Nat}
    (hop : Rules.NatOpRow m φ) (hwr : WhnfReads m μ φ fuel)
    (ihw : WhnfClaim μ m φ fuel)
    {d : Nat} {Δa : List AnnotTerm} {c : Name} {a b e₂ : Expr}
    {ea : AnnotTerm}
    (h : ConLeche.reduceNatFueled μ env fuel d
      (.app (.app (.const c []) a) b) = .ok (some e₂))
    (hws : Expr.WScoped d (.app (.app (.const c []) a) b))
    (hb : (Expr.app (.app (.const c []) a) b).looseBVarsBounded 0
      = true)
    (hLb : Expr.LeavesBounded (.app (.app (.const c []) a) b))
    (hC : CtxOk m φ d Δa (.app (.app (.const c []) a) b))
    (hea : denoteMeta m.acval env φ d
      (.app (.app (.const c []) a) b) = some ea)
    (hok : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) :
    ∃ ea₂, denoteMeta m.acval env φ d e₂ = some ea₂ ∧
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea₂) ∧
      ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea = interp V ρ ea₂ := by
  obtain ⟨⟨hwsa, hba, hLa, hCa⟩, hwsb, hbb, hLb', hCb⟩ :=
    frame_app2 hws hb hLb hC
  obtain ⟨fab, ba, hfab, hba', rfl⟩ := denoteMeta_app_inv hea
  obtain ⟨fa, aa, hfa, haa, rfl⟩ := denoteMeta_app_inv hfab
  have hokAB : ∀ ρ' : Nat → V, Sat V Δa ρ' →
      WellDenotedV V ρ' ((.app fa aa : AnnotTerm)) :=
    fun ρ' hρ' => (wellDenotedV_app_inv (hok ρ' hρ')).1
  have hokB : ∀ ρ' : Nat → V, Sat V Δa ρ' → WellDenotedV V ρ' ba :=
    fun ρ' hρ' => (wellDenotedV_app_inv (hok ρ' hρ')).2
  have hokA : ∀ ρ' : Nat → V, Sat V Δa ρ' → WellDenotedV V ρ' aa :=
    fun ρ' hρ' => (wellDenotedV_app_inv (hokAB ρ' hρ')).2
  simp only [ConLeche.reduceNatFueled, ConLeche.reduceNat, Bind.bind,
    Except.bind, ConLeche.whnf_def] at h
  split at h
  · next hcond =>
    obtain ⟨h14, hstored⟩ := hcond
    have hmem : c ∈ _root_.ConLeche.Rules.natBinOpNames := by
      rcases h14 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
        rfl|rfl <;> decide
    cases hwa : ConLeche.whnf μ env fuel d a with
    | error err => rw [hwa] at h; exact nomatch h
    | ok a0 =>
    rw [hwa] at h
    dsimp only at h
    cases hra : ConLeche.rawNatLit? a0 with
    | none => rw [hra] at h; simp [pure, Except.pure] at h
    | some n₁ =>
    rw [hra] at h
    dsimp only at h
    cases hwb : ConLeche.whnf μ env fuel d b with
    | error err => rw [hwb] at h; exact nomatch h
    | ok b0 =>
    rw [hwb] at h
    dsimp only at h
    cases hrb : ConLeche.rawNatLit? b0 with
    | none => rw [hrb] at h; simp [pure, Except.pure] at h
    | some n₂ =>
      rw [hrb] at h
      dsimp only at h
      cases hres : ConLeche.natOpResult c n₁ n₂ with
      | none => rw [hres] at h; simp [pure, Except.pure] at h
      | some r =>
        rw [hres] at h
        simp only [pure, Except.pure, Except.ok.injEq,
          Option.some.injEq] at h
        subst h
        obtain ⟨aa0, haa0⟩ :=
          hwr hwa hwsa hba hLa (LeafReads.of_ctxOk hCa) haa
        obtain ⟨hokA0, hiA⟩ := ihw hwa hwsa hba hLa hCa haa haa0 hokA
        obtain ⟨ba0, hba0⟩ :=
          hwr hwb hwsb hbb hLb' (LeafReads.of_ctxOk hCb) hba'
        obtain ⟨hokB0, hiB⟩ := ihw hwb hwsb hbb hLb' hCb hba' hba0 hokB
        have hiAB : ∀ ρ : Nat → V, Sat V Δa ρ →
            interp V ρ ((.app fa aa : AnnotTerm))
              = interp V ρ ((.app fa aa0 : AnnotTerm)) := by
          intro ρ hρ
          rw [interp_app, interp_app, hiA ρ hρ]
        obtain ⟨ra, hrar, hgra, heq⟩ :=
          hop hmem hstored hra hrb hres
            (denoteMeta_app_mk (denoteMeta_app_mk hfa haa0) hba0)
            (fun ρ hρ =>
              wellDenotedV_app_congr
                (wellDenotedV_appFn_congr (hok ρ hρ)
                  (wellDenotedV_app_congr (hokAB ρ hρ) (hokA0 ρ hρ)
                    (hiA ρ hρ))
                  (hiAB ρ hρ))
                (hokB0 ρ hρ) (hiB ρ hρ))
        refine ⟨ra, hrar, hgra, fun ρ hρ => ?_⟩
        refine Eq.trans ?_ (heq ρ hρ)
        simp only [interp_app]
        rw [hiA ρ hρ, hiB ρ hρ]
  · split at h
    · -- the WF-pin safety net: it throws
      cases hwa : ConLeche.whnf μ env fuel d a with
      | error err => rw [hwa] at h; exact nomatch h
      | ok a0 =>
      rw [hwa] at h
      dsimp only at h
      cases hra : ConLeche.rawNatLit? a0 with
      | none => rw [hra] at h; simp [pure, Except.pure] at h
      | some n₁ =>
      rw [hra] at h
      dsimp only at h
      cases hwb : ConLeche.whnf μ env fuel d b with
      | error err => rw [hwb] at h; exact nomatch h
      | ok b0 =>
      rw [hwb] at h
      dsimp only at h
      cases hrb : ConLeche.rawNatLit? b0 with
      | none => rw [hrb] at h; simp [pure, Except.pure] at h
      | some n₂ =>
        rw [hrb] at h
        simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [pure, Except.pure] at h

/-- **`ReduceNatStep`, from the two semantic rows.**  The run
inversion above, the reduct's frame from `frame_of_reduceNat`, and its
reading, grading and `interp` equality from the rows. -/
theorem reduceNatStep_of_rows {m : EnvModel V env} {fuel : Nat}
    (hsucc : Rules.NatSuccRow m φ) (hop : Rules.NatOpRow m φ)
    (hwr : WhnfReads m μ φ fuel) (ihw : WhnfClaim μ m φ fuel) :
    ReduceNatStep μ m φ fuel := by
  intro d e e₂ Δa h hws hb hLb ea hC hea hok
  obtain ⟨hws₂, hb₂, hLb₂, hfl₂⟩ := frame_of_reduceNat h
  have hC₂ : CtxOk m φ d Δa e₂ := by
    refine ⟨hC.1, fun l hl => ?_⟩
    rw [hfl₂] at hl
    exact nomatch hl
  have hcore : ∃ ea₂, denoteMeta m.acval env φ d e₂ = some ea₂ ∧
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea₂) ∧
      ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea = interp V ρ ea₂ := by
    match e, h, hws, hb, hLb, hC, hea, hok with
    | .app (.const c []) a, h, hws, hb, hLb, hC, hea, hok =>
      exact reduceNatCore_unary hsucc hwr ihw h hws hb hLb hC hea hok
    | .app (.app (.const c []) a) b, h, hws, hb, hLb, hC, hea, hok =>
      exact reduceNatCore_binary hop hwr ihw h hws hb hLb hC hea hok
    | .bvar _, h, _, _, _, _, _, _ | .fvar _ _, h, _, _, _, _, _, _
    | .sort _, h, _, _, _, _, _, _ | .lam _ _ _, h, _, _, _, _, _, _
    | .forallE _ _ _, h, _, _, _, _, _, _
    | .letE _ _ _, h, _, _, _, _, _, _
    | .lit _, h, _, _, _, _, _, _ | .proj _ _ _, h, _, _, _, _, _, _
    | .const _ _, h, _, _, _, _, _, _ =>
      simp [ConLeche.reduceNatFueled, ConLeche.reduceNat, pure,
        Except.pure] at h
    | .app (.bvar _) _, h, _, _, _, _, _, _
    | .app (.fvar _ _) _, h, _, _, _, _, _, _
    | .app (.sort _) _, h, _, _, _, _, _, _
    | .app (.lam _ _ _) _, h, _, _, _, _, _, _
    | .app (.forallE _ _ _) _, h, _, _, _, _, _, _
    | .app (.letE _ _ _) _, h, _, _, _, _, _, _
    | .app (.lit _) _, h, _, _, _, _, _, _
    | .app (.proj _ _ _) _, h, _, _, _, _, _, _ =>
      simp [ConLeche.reduceNatFueled, ConLeche.reduceNat, pure,
        Except.pure] at h
    | .app (.const c (_ :: _)) _, h, _, _, _, _, _, _ =>
      simp [ConLeche.reduceNatFueled, ConLeche.reduceNat, pure,
        Except.pure] at h
    | .app (.app (.bvar _) _) _, h, _, _, _, _, _, _
    | .app (.app (.fvar _ _) _) _, h, _, _, _, _, _, _
    | .app (.app (.sort _) _) _, h, _, _, _, _, _, _
    | .app (.app (.app _ _) _) _, h, _, _, _, _, _, _
    | .app (.app (.lam _ _ _) _) _, h, _, _, _, _, _, _
    | .app (.app (.forallE _ _ _) _) _, h, _, _, _, _, _, _
    | .app (.app (.letE _ _ _) _) _, h, _, _, _, _, _, _
    | .app (.app (.lit _) _) _, h, _, _, _, _, _, _
    | .app (.app (.proj _ _ _) _) _, h, _, _, _, _, _, _ =>
      simp [ConLeche.reduceNatFueled, ConLeche.reduceNat, pure,
        Except.pure] at h
    | .app (.app (.const c (_ :: _)) _) _, h, _, _, _, _, _, _ =>
      simp [ConLeche.reduceNatFueled, ConLeche.reduceNat, pure,
        Except.pure] at h
  obtain ⟨ea₂, hea₂, hg₂, hi₂⟩ := hcore
  exact ⟨ea₂, hea₂, hg₂, hi₂, hws₂, hb₂, hLb₂, hC₂⟩

/-- **`ReduceNatStepPQ`, from the two semantic rows** — the defeq
quarter's row differs from the whnf quarter's only in where the
subject's annotation is bound. -/
theorem reduceNatStepPQ_of_rows {m : EnvModel V env} {fuel : Nat}
    (hsucc : Rules.NatSuccRow m φ) (hop : Rules.NatOpRow m φ)
    (hwr : WhnfReads m μ φ fuel) (ihw : WhnfClaim μ m φ fuel) :
    ReduceNatStepPQ μ m φ fuel := by
  intro d e e₂ Δa ea h hws hb hLb hC hea hok
  exact reduceNatStep_of_rows hsucc hop hwr ihw h hws hb hLb hC hea hok

/-- **The routed residues, at one environment** (see the module
docstring).  Field order groups the tiers: the `reads` bundle carries
the install/iota/proj/literal *readability* leaves inside it. -/
structure TierInputsAt (V : Type w) [SetTheory V] (μ : CheckMode)
    {env : Env} (m : EnvModel V env) (φ : Name → Nat) : Prop where
  /-- install tier: the readability bundle (its own four leaves are
  iota/proj/literal reads) -/
  reads : ReadsInputs μ m φ
  /-- install tier: leaf bit-validity -/
  acval_valid : AcvalValid m
  /-- install tier: the numeral heads -/
  nat_heads : NatHeads m φ
  /-- iota tier: the stored recursors' fired contracts — an `EnvModelM`
  field (`rec_rules`), which with the claims discharges both ι rows
  (`iotaStep_of`, `iotaReads_of`) -/
  rec_rules : RecRules m φ
  /-- literal tier: the successor packing's SEMANTIC row (task #305
  R-nat: the field used to be the run row `ReduceNatStep` at every
  fuel; the run inversion is `reduceNatStep_of_rows` above) -/
  nat_succ : Rules.NatSuccRow m φ
  /-- literal tier: the fourteen binary operations' SEMANTIC row -/
  nat_op : Rules.NatOpRow m φ
  /-- caps tier: the stored families' fired capability laws — an
  `EnvModelM` field (`caps_ok`), which is what discharges the stored
  structure's η and unit fallbacks (`structEtaIrrel_of_claims`,
  `structUnitIrrel_of_claims` — the latter after the ratified
  one-premise repair of the unit half; all four capability rows are
  now discharged) -/
  caps_ok : CapsOk m

/-- **The P soundness ladder at one environment — the five-way joint
induction** (task #172 B4), with every of_claims discharge wired in.
The io claim joined the induction the moment the first converted call
site (the β certificate) made the head-normalisation quarter consume
the slot claim at the same fuel; the four-way form survives as the
projection `checkSoundAt` below, so every landed consumer stands
verbatim. -/
theorem checkSoundAtP5 (hμ : μ.verifiedChecks = true)
    {m : EnvModel V env} (h : TierInputsAt V μ m φ) :
    ∀ fuel : Nat,
      WhnfCoreClaim μ m φ fuel ∧ WhnfClaim μ m φ fuel ∧
        DefEqClaim μ m φ fuel ∧ InferClaim μ m φ fuel ∧
          InferClaimIO μ m φ fuel := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro d e e' Δa hrun
      rw [ConLeche.whnfCore_zero] at hrun
      simp [throw, throwThe, MonadExceptOf.throw] at hrun
    · intro d e e' Δa hrun
      rw [ConLeche.whnf_zero] at hrun
      simp [throw, throwThe, MonadExceptOf.throw] at hrun
    · intro d a b Δa hrun
      rw [ConLeche.isDefEqCore_zero] at hrun
      simp [throw, throwThe, MonadExceptOf.throw] at hrun
    · intro d e t Δa hrun
      rw [ConLeche.inferTypeCore_zero] at hrun
      simp [throw, throwThe, MonadExceptOf.throw] at hrun
    · intro d e t Δa hrun
      rw [ConLeche.inferTypeCoreIO_zero] at hrun
      simp [throw, throwThe, MonadExceptOf.throw] at hrun
  | succ fuel ih =>
    obtain ⟨ihwc, ihw, ihd, ihi, ihio⟩ := ih
    -- the totality factors, from the reads bundle
    have hreads : InferReads m μ φ fuel := inferReads_of h.reads
    have hwreads : WhnfReads m μ φ fuel := whnfReads_of h.reads
    have hex : WhnfCoreExists μ m φ fuel := whnfCoreExists_of h.reads
    have hexi : InferExists μ m φ fuel := inferExists_of h.reads
    have hreads_io : InferReadsIO m μ φ fuel :=
      inferReadsIO_of h.reads fuel
    -- the slot facts (task #172 B4): existence and the premise-form
    -- claim at the knot's io slot, from the two lanes
    have hexis : InferExistsIOS μ m φ fuel := by
      intro d e t Δa hrun hws hb hLb ea hC hea
      cases hg : μ.betaGate with
      | false =>
        rw [ConLeche.inferTypeIO_off hg] at hrun
        exact hexi hrun hws hb hLb hC hea
      | true =>
        rw [ConLeche.inferTypeIO_on hg] at hrun
        exact hreads_io hrun hws hb hLb (LeafReads.of_ctxOk hC) hea
    have ihis : InferClaimIOS μ m φ fuel :=
      inferClaimIOS_of ihi ihio
    -- the derived sort facts
    have hss : SortSemAt m μ φ fuel :=
      sortSemAt_of_claims ihw ihi hreads
    have hssio : SortSemAtIO m μ φ fuel :=
      sortSemAtIO_of_claims ihw ihio hreads_io
    have hsss : SortSemAtIOS m μ φ fuel :=
      sortSemAtIOS_of hss hssio
    have hreads_ios : InferReadsIOS m μ φ fuel :=
      inferReadsIOS_of hreads hreads_io
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- the head-normalisation quarter
      exact whnfCore_claims m hex
        (betaCert_of_claims m hexis ihd ihis)
        (iotaStep_of h.rec_rules h.caps_ok h.reads.tower_ok h.reads.const_ty
          h.acval_valid ihw ihd ihis hsss hexis hreads_ios hwreads)
        (projStep_of_claims hμ h.reads.tower_ok h.reads.const_ty ihwc ihw ihd ihis
          hexis hwreads) ihwc
    · -- the reduction loop
      exact whnf_claims m hex ihwc
        (reduceNatStep_of_rows h.nat_succ h.nat_op hwreads ihw)
        (delta_of m h.reads.defn)
    · -- the defeq quarter, of_claims discharges wired
      have hsi : StuckIrrelPQ μ m φ fuel :=
        stuckIrrelFueled_of_claims ihis hsss hreads_ios
          (unitIrrelPQ_of_claims ihw ihis hreads_ios hwreads)
          (structEtaIrrel_of_claims h.caps_ok h.reads.tower_ok h.reads.const_ty
            h.acval_valid ihw ihd ihis hexis hwreads)
          (structUnitIrrel_of_claims h.caps_ok ihw ihd ihis hexis
            hwreads)
      have hstep : DefEqStepAt μ m φ fuel :=
        defeqStep_claim (whnfCoreReductExists_of' h.reads) ihwc ihw
          (denoteMetaDelta_of h.reads)
          (reduceNatStepPQ_of_rows h.nat_succ h.nat_op hwreads ihw)
          (propIrrelPQ_of_claims h.reads.const_ty ihis hsss hreads_ios)
          (defeqStuck_claim hμ ihd hsi denotePStrLit_of_guard
            (acvalParams m) (appCongrStuck_of_claims ihd)
            (etaCertStep_of_claims hμ ihw ihd ihis hreads_ios hwreads))
          (defEqSpine_of_claims ihd (acvalParams m))
      -- (`defeq_claims hstep` trips an implicit-eta unification
      -- wrinkle at the `DefEqStepAt` unfolding; its two-line body is
      -- inlined instead)
      intro d a b Δa hrun hwa hba' hLa hwb hbb hLb aa ba hCa hCb
        hda hdb
      rw [ConLeche.isDefEqCore_succ, defeqBody] at hrun
      exact defeqLoop_cont hstep defeqLoopFuel d true hrun hwa hba' hLa
        hwb hbb hLb hCa hCb hda hdb
    · -- the infer quarter (the eleven-arm dispatcher, env-fixed)
      intro d e t Δa hrun hws hb hLb ea ta hC hea hta
      match e, hrun, hws, hb, hLb, hC, hea with
      | .sort u, hrun, _, _, _, _, hea =>
        exact infer_sort_claim m hrun hea hta
      | .bvar i, hrun, _, _, _, _, hea =>
        exact infer_bvar_claim m hrun hea hta
      | .fvar idx ty, hrun, _, _, _, hC, hea =>
        exact infer_fvar_claim m hC hrun hea hta
      | .const nm us, hrun, _, _, _, _, hea =>
        exact infer_const_claim m h.reads.const_ty h.acval_valid
          hrun hea hta
      | .lit (.natVal k), hrun, _, _, _, _, hea =>
        exact infer_natLit_claim m h.nat_heads h.acval_valid
          hrun hea hta
      | .lit (.strVal s), hrun, _, _, _, _, hea =>
        exact inferStrLitStep_of_claims h.reads.const_ty h.acval_valid
          h.nat_heads hrun hea hta
      | .forallE ty body mb, hrun, hws, hb, hLb, hC, hea =>
        exact infer_forallE_claim m hμ hss hrun hws hb hLb hC hea hta
      | .lam ty body mb, hrun, hws, hb, hLb, hC, hea =>
        exact infer_lam_claim m hμ hss hsss ihi hrun hws hb hLb hC hea
          hta
      | .app fe ae, hrun, hws, hb, hLb, hC, hea =>
        exact infer_app_claim m hreads hwreads ihw ihd ihi hrun
          hws hb hLb hC hea hta
      | .letE ty val bd, hrun, hws, hb, hLb, hC, hea =>
        exact (ConLeche.inferTypeCore_letE_inv hrun).elim
      | .proj sn i pe, hrun, hws, hb, hLb, hC, hea =>
        exact inferProjStep_of_claims h.reads.tower_ok ihw ihi hreads
          hwreads hrun hws hb
          hLb hC hea hta
    · -- the io quarter (the eleven-arm dispatcher, env-fixed;
      -- task #172 B4)
      intro d e t Δa hrun hws hb hLb ea ta hC hea hta hok
      match e, hrun, hws, hb, hLb, hC, hea, hok with
      | .sort u, hrun, _, _, _, _, hea, _ =>
        exact infer_sort_claimIO m hrun hea hta
      | .bvar i, hrun, _, _, _, _, hea, _ =>
        exact infer_bvar_claimIO m hrun hea hta
      | .fvar idx ty, hrun, _, _, _, hC, hea, _ =>
        exact infer_fvar_claimIO m hC hrun hea hta
      | .const nm us, hrun, _, _, _, _, hea, _ =>
        exact infer_const_claimIO m (h.reads.const_ty) hrun hea hta
      | .lit (.natVal k), hrun, _, _, _, _, hea, _ =>
        exact infer_natLit_claimIO m h.nat_heads h.acval_valid hrun
          hea hta
      | .lit (.strVal str), hrun, _, _, _, _, hea, _ =>
        exact infer_strLit_claimIO m
          (inferStrLitStep_of_claims h.reads.const_ty h.acval_valid
            h.nat_heads) hrun hea hta
      | .forallE ty body mb, hrun, hws, hb, hLb, hC, hea, hok =>
        exact infer_forallE_claimIO m hμ hssio hrun hws hb hLb hC hea
          hta hok
      | .lam ty body mb, hrun, hws, hb, hLb, hC, hea, hok =>
        exact infer_lam_claimIO m hμ hssio ihio hrun hws hb hLb hC hea
          hta hok
      | .app fe ae, hrun, hws, hb, hLb, hC, hea, hok =>
        exact infer_app_claimIO m hreads_io hwreads ihw ihd ihio hrun
          hws hb hLb hC hea hta hok
      | .letE ty val bd, hrun, hws, hb, hLb, hC, hea, hok =>
        exact (ConLeche.inferTypeCoreIO_letE_inv hrun).elim
      | .proj sn i pe, hrun, hws, hb, hLb, hC, hea, hok =>
        exact inferProjStepIO_of_claims h.reads.tower_ok ihw ihio hreads_io
          hwreads hrun
          hws hb hLb hC hea hta hok

/-- The four sealed claims at every fuel — the joint induction's first
four conjuncts, kept under the landed name so every consumer stands
verbatim. -/
theorem checkSoundAt (hμ : μ.verifiedChecks = true)
    {m : EnvModel V env} (h : TierInputsAt V μ m φ) :
    ∀ fuel : Nat,
      WhnfCoreClaim μ m φ fuel ∧ WhnfClaim μ m φ fuel ∧
        DefEqClaim μ m φ fuel ∧ InferClaim μ m φ fuel := fun fuel =>
  ⟨(checkSoundAtP5 hμ h fuel).1, (checkSoundAtP5 hμ h fuel).2.1,
    (checkSoundAtP5 hμ h fuel).2.2.1, (checkSoundAtP5 hμ h fuel).2.2.2.1⟩

/-- **The env-tier entries, from the fold's invariant**: an `EnvModelM`
supplies the readability bundle, the leaf validity, and the numeral
heads; what remains as arguments is exactly the semantic-content bill
(iota / proj / literal / caps / the two infer clause rows), each named
by its tier in the frontier-transformation table.  The two literal
rows stay arguments rather than `EnvModelM` projections for an import
reason: `natSuccRow_of`/`natOpRow_of` (`Model/NatStep.lean`) stand on
the numeral transports, which sit ABOVE this file. -/
theorem TierInputsAt.ofEnvModelM (mp : EnvModelM V μ env)
    (hnat_r : ∀ fuel, ReduceNatReads μ mp.base2 φ fuel)
    (hsucc : Rules.NatSuccRow mp.base2 φ)
    (hop : Rules.NatOpRow mp.base2 φ) :
    TierInputsAt V μ mp.base2 φ where
  reads := ReadsInputs.ofEnvModelM mp
    (fun _fuel ihw ihio => iotaReads_of (mp.rec_rules φ) ihw ihio)
    hnat_r
  acval_valid := mp.acvalValid
  nat_heads := mp.nat_heads φ
  rec_rules := mp.rec_rules φ
  nat_succ := hsucc
  nat_op := hop
  caps_ok := mp.caps_ok

end ConLeche.Model

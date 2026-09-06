import Setlec.SetP.Direct.DirectEntryKitP

/-!
# The projection entry's data (task #175 W4c, P3 module 7, part 2)

`EntryData`: the entry type's reading, peeled — the Π-tower over
`nP + 1` binder data (parameters, subject) ending in the field's
residual, opened at the checker's own variables, with every codomain
bit zero exactly when the residual's inferred sort is (`vb`), graded,
bounded, depending only on the block's level parameters; and the
residual's sort membership at the opened frame.  Derived once from the
entry stage's runs (`entryData_of`).
-/

namespace Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify SetTheory Setlec.SetTheory.Tower
open Setlec.Semantics (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-- **The entry type's reading, peeled and opened.** -/
structure EntryData {env : Env} (m : EnvS2Core V env) (ptyA : Expr)
    (lps : List Name) (nP : Nat) (vb : Level) (fvsE : List Expr) (oE : Expr)
    (eds : (Name → Nat) → List (Nat × Nat × AVExpr))
    (R : (Name → Nat) → AVExpr) : Prop where
  read : ∀ ψ : Name → Nat, denoteP m.acval env ψ 0 ptyA
    = some (mkPisAV (eds ψ) (R ψ))
  len : ∀ ψ : Name → Nat, (eds ψ).length = nP + 1
  bits : ∀ (ψ : Name → Nat) (d : Nat × Nat × AVExpr), d ∈ eds ψ →
    (d.2.1 = 0 ↔ vb.eval ψ = 0)
  okTy : ∀ (ψ : Name → Nat) (ρ : Nat → V),
    AnnotOkP V ρ (mkPisAV (eds ψ) (R ψ))
  below : ∀ ψ : Name → Nat, DomsBelow 0 (eds ψ)
  params : ∀ ψ₁ ψ₂ : Name → Nat, (∀ p ∈ lps, ψ₁ p = ψ₂ p) →
    eds ψ₁ = eds ψ₂ ∧ R ψ₁ = R ψ₂
  opened : ∀ ψ : Name → Nat,
    OpenedP m ψ (nP + 1) ptyA fvsE oE (((eds ψ).map (·.2.2)).reverse) (R ψ)
  /-- the residual lands in the universe of its inferred sort at every
  satisfying frame -/
  resSort : ∀ (ψ : Name → Nat) (ρ : Nat → V),
    Sat2 V (((eds ψ).map (·.2.2)).reverse) ρ →
    interp2 V ρ (R ψ) ∈ˢ (univ (vb.eval ψ) : V)

/-- The entry's data, from the stage's runs (the shape lemma's
pieces). -/
theorem entryData_of (hμ : μ.verified = true) (mp : EnvS2PM V μ env)
    {F nP : Nat} {ptyA sty prest resid : Expr} {u : Level} {lps : List Name}
    {fvsP tFvs : List Expr}
    (hlpd : ptyA.allLevelParamsDefined lps = true)
    (hb : ptyA.looseBVarsBounded 0 = true) (hnf : ptyA.hasFvar = false)
    (hinf : Setlec.inferTypeCore μ env F 0 ptyA = .ok sty)
    (hens : Setlec.ensureSortCore μ env F 0 sty = .ok u)
    (hopP : openPisAtFvars nP ptyA 0 = some (fvsP, prest))
    (hopT : openPisAtFvars 1 prest nP = some (tFvs, resid)) :
    ∃ (vb : Level) (eds : (Name → Nat) → List (Nat × Nat × AVExpr))
      (R : (Name → Nat) → AVExpr),
      EntryData mp.base2 ptyA lps nP vb (fvsP ++ tFvs) resid eds R := by
  have hw : Expr.WScoped 0 ptyA := Expr.WScoped.of_not_hasFvar hnf
  have hL : Expr.LeavesBounded ptyA := Expr.LeavesBounded.of_not_hasFvar hnf
  have hnil : ptyA.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar hnf
  have hopAll : openPisAtFvars (nP + 1) ptyA 0 = some (fvsP ++ tFvs, resid) :=
    openPisAtFvars_add nP hopP (by rw [Nat.zero_add]; exact hopT)
  -- the bits: the residual's inferred sort
  obtain ⟨F', tb, vb, hib, hensb, -, hbits⟩ :=
    piBits_of_infer hμ (nP + 1) hopAll hinf hens
  rw [Nat.zero_add] at hib hensb
  -- per assignment: the reading, its peel, its grading, its opening
  have hper : ∀ ψ : Name → Nat, ∃ (eds : List (Nat × Nat × AVExpr)) (R : AVExpr),
      denoteP mp.base2.acval env ψ 0 ptyA = some (mkPisAV eds R) ∧
      eds.length = nP + 1 ∧
      (∀ d ∈ eds, (d.2.1 = 0 ↔ vb.eval ψ = 0)) ∧
      (∀ ρ : Nat → V, AnnotOkP V ρ (mkPisAV eds R)) ∧
      DomsBelow 0 eds ∧
      OpenedP mp.base2 ψ (nP + 1) ptyA (fvsP ++ tFvs) resid ((eds.map (·.2.2)).reverse) R ∧
      (∀ ρ : Nat → V, Sat2 V ((eds.map (·.2.2)).reverse) ρ →
        interp2 V ρ R ∈ˢ (univ (vb.eval ψ) : V)) := by
    intro ψ
    have hc := claimsAtP_of hμ mp ψ F
    have hc' := claimsAtP_of hμ mp ψ F'
    obtain ⟨Ta, hTa⟩ := acceptedReadsP_of mp.base2 ψ hinf hw hb hL
    obtain ⟨-, -, hokT, -, -⟩ := hc.inferRow hinf hw hb hL (CtxOkP.nil hnil) hTa
    have hokT' : ∀ ρ : Nat → V, AnnotOkP V ρ Ta := fun ρ =>
      hokT ρ (Sat2_nil V ρ)
    obtain ⟨Γ, R, htele, hop'⟩ := openedP_of hopAll hnf hb hTa hokT'
    obtain ⟨eds, hst', hΓ⟩ := stripPisAV_of_piTeleP htele
    obtain ⟨hTeq, hlen⟩ := stripPisAV_eq_mkPis hst'
    subst hTeq
    subst hΓ
    refine ⟨eds, R, hTa, hlen, ?_, hokT', ?_, hop', ?_⟩
    · intro d hd
      exact stripPisAV_bits (nP + 1) (hbits ψ) hTa hst' d hd
    · exact (stripPisAV_below hst' (bvarsBelow_of_reading hw hb hTa)).1
    · intro ρ hρ
      have hsort := hc'.sortRow hib hensb hop'.bodyScoped.1 hop'.bodyScoped.2.1
        hop'.bodyScoped.2.2.1 (hop'.ctx (Nat.le_refl _) hop'.bodyScoped.1
          hop'.bodyScoped.2.2.2) hop'.body ρ
      rw [Nat.sub_self, List.drop_zero] at hsort
      exact (hsort hρ).2
  refine ⟨vb, fun ψ => Classical.choose (hper ψ),
    fun ψ => Classical.choose (Classical.choose_spec (hper ψ)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun ψ => (Classical.choose_spec (Classical.choose_spec (hper ψ))).1
  · exact fun ψ => (Classical.choose_spec (Classical.choose_spec (hper ψ))).2.1
  · exact fun ψ => (Classical.choose_spec (Classical.choose_spec (hper ψ))).2.2.1
  · exact fun ψ => (Classical.choose_spec (Classical.choose_spec (hper ψ))).2.2.2.1
  · exact fun ψ => (Classical.choose_spec (Classical.choose_spec (hper ψ))).2.2.2.2.1
  · intro ψ₁ ψ₂ hφ
    have h2 := (Classical.choose_spec (Classical.choose_spec (hper ψ₂))).1
    have h1 : denoteP mp.base2.acval env ψ₂ 0 ptyA
        = some (mkPisAV (Classical.choose (hper ψ₁))
          (Classical.choose (Classical.choose_spec (hper ψ₁)))) := by
      rw [← denoteP_params_ext mp.base2 hφ 0 ptyA hlpd]
      exact (Classical.choose_spec (Classical.choose_spec (hper ψ₁))).1
    exact mkPisAV_inj
      (by rw [(Classical.choose_spec (Classical.choose_spec (hper ψ₁))).2.1,
        (Classical.choose_spec (Classical.choose_spec (hper ψ₂))).2.1])
      (Option.some.inj (h1.symm.trans h2))
  · exact fun ψ => (Classical.choose_spec (Classical.choose_spec (hper ψ))).2.2.2.2.2.1
  · exact fun ψ => (Classical.choose_spec (Classical.choose_spec (hper ψ))).2.2.2.2.2.2

/-- The entry's data crosses a cons whose head is not a tower entry
at a slot the stored type mentions. -/
theorem EntryData.cross {m : EnvS2Core V env} {ptyA : Expr} {lps : List Name}
    {nP : Nat} {vb : Level} {fvsE : List Expr} {oE : Expr}
    {eds : (Name → Nat) → List (Nat × Nat × AVExpr)} {R : (Name → Nat) → AVExpr}
    (h : EntryData m ptyA lps nP vb fvsE oE eds R)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none) (hat : ConsCrossAt c₀ ptyA)
    (hcb : ConstsBound env ptyA)
    (m₂ : EnvS2Core V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    ∀ ψ : Name → Nat, denoteP m₂.acval ⟨c₀ :: env.consts⟩ ψ 0 ptyA
      = some (mkPisAV (eds ψ) (R ψ)) := by
  intro ψ
  rw [hac]
  exact denoteP_cons_mono hfresh hat ψ 0 hcb (h.read ψ)

end Setlec.Semantics

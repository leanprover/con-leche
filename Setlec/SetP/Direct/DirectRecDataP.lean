import Setlec.SetP.Direct.DirectRecKitP

/-!
# The recursor's data (task #175 W4c, P3 module 6, part 7)

`RecData`: the recursor type's reading, peeled — the Π-tower over
`nP + 3` binder data (parameters, motive, minor, major) ending in the
motive applied to the major (`.app (.bvar 2) (.bvar 0)`), with every
codomain bit zero exactly when the elimination level is (`elimLevel`:
the fresh parameter of the large eliminator, `zero` for the small
one), graded, bounded, depending only on the recursor's level
parameters.  Derived once from the stage's runs (`recData_of`) and
crossed to the recursor's own extension (`RecData.cross`).
-/

namespace Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify SetTheory Setlec.SetTheory.Tower
open Setlec.Semantics (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## Kit -/

/-- The recursor's elimination level: the fresh parameter at the large
eliminator, `zero` at the small one (`checkDirectRecTy`'s motive
codomain). -/
def elimLevel (p : DirectParts) : Level :=
  if p.large then .param p.elim else .zero

theorem stripPis_one_inv {e : Expr} {bs : List (Name × Expr × BinderMeta)}
    {b : Expr} (h : e.stripPis 1 = some (bs, b)) :
    ∃ nm dom mb, e = .forallE nm dom b mb ∧ bs = [(nm, dom, mb)] := by
  match e, h with
  | .forallE nm dom body mb, h =>
    simp only [Expr.stripPis, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨nm, dom, mb, rfl, rfl⟩
  | .bvar _, h | .fvar _ _ _, h | .sort _, h | .const _ _, h | .app _ _, h
  | .lam _ _ _ _, h | .letE _ _ _ _, h | .lit _, h | .proj _ _ _, h =>
    simp [Expr.stripPis] at h

theorem openPisAtFvars_one (nm : Name) (dom body : Expr) (mb : BinderMeta)
    (d : Nat) :
    openPisAtFvars 1 (.forallE nm dom body mb) d
      = some ([.fvar d nm dom], body.instantiate1 (.fvar d nm dom)) := rfl

/-! ## The recursor's data -/

/-- **The recursor type's reading, peeled.** -/
structure RecData {env : Env} (m : EnvS2Core V env) (cvR : ConstantVal)
    (nP : Nat) (elimL : Level)
    (rds : (Name → Nat) → List (Nat × Nat × AVExpr)) : Prop where
  read : ∀ ψ : Name → Nat, denoteP m.acval env ψ 0 cvR.type
    = some (mkPisAV (rds ψ) (.app (.bvar 2) (.bvar 0)))
  len : ∀ ψ : Name → Nat, (rds ψ).length = nP + 3
  bits : ∀ (ψ : Name → Nat) (d : Nat × Nat × AVExpr), d ∈ rds ψ →
    (elimL.eval ψ = 0 ↔ d.2.1 = 0)
  okTy : ∀ (ψ : Name → Nat) (ρ : Nat → V),
    AnnotOkP V ρ (mkPisAV (rds ψ) (.app (.bvar 2) (.bvar 0)))
  below : ∀ ψ : Name → Nat, DomsBelow 0 (rds ψ)
  params : ∀ ψ₁ ψ₂ : Name → Nat, (∀ p ∈ cvR.levelParams, ψ₁ p = ψ₂ p) →
    rds ψ₁ = rds ψ₂

/-- The recursor's data, from its `checkConstantVal` run and the
recursor-type stage's shape. -/
theorem recData_of (hμ : μ.verified = true) (mp : EnvS2PM V μ env)
    {F : Nat} {p : DirectParts} {cvTa cvCa cvRa : ConstantVal}
    (hccv : Setlec.checkConstantVal (Setlec.fueledOps μ F) env p.cvR = .ok cvRa)
    (hRec : Setlec.checkDirectRecTy (Setlec.fueledOps μ F) env p cvTa cvCa cvRa
      = .ok ()) :
    ∃ rds : (Name → Nat) → List (Nat × Nat × AVExpr),
      RecData mp.base2 cvRa p.nP (elimLevel p) rds := by
  obtain ⟨-, fvsP, rest, -, -, mfv, mbs, -, -, -, -, -, -, jbs, jbody, -,
    hopR, -, -, hmfv, hmstrip, -, -, -, -, -, -, -, -, hjs, -, -, hjbody⟩ :=
    Setlec.checkDirectRecTy_shape hRec
  obtain ⟨-, -, -, -, hlbt, hitf, type', stype, u, hann', htp', htr', hst,
    hens, rfl⟩ := Setlec.checkConstantVal_inv hccv
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann' hitf hlbt
  simp only at htf' hbt' htp' htr' hst hens hopR
  have hw : Expr.WScoped 0 type' := Expr.WScoped.of_not_hasFvar htf'
  have hL : Expr.LeavesBounded type' := Expr.LeavesBounded.of_not_hasFvar htf'
  have hnil : type'.fvarLeaves = [] :=
    Expr.fvarLeaves_eq_nil_of_not_hasFvar htf'
  -- the motive variable and the major binder
  obtain ⟨nmM, tyM, rfl⟩ := openPisAtFvars_index _ _ _ hopR p.nP mfv hmfv
  obtain ⟨nmJ, jdom, mbJ, rfl, -⟩ := stripPis_one_inv hjs
  subst hjbody
  -- the full opening, at `nP + 3`
  have hopAll : openPisAtFvars (p.nP + 3) type' 0
      = some (fvsP ++ [.fvar (p.nP + 2) nmJ jdom],
          .app (.fvar (0 + p.nP) nmM tyM) (.fvar (p.nP + 2) nmJ jdom)) := by
    have := openPisAtFvars_add (p.nP + 2) hopR
      (openPisAtFvars_one nmJ jdom (.app (.fvar (0 + p.nP) nmM tyM) (.bvar 0)) mbJ
        (0 + (p.nP + 2)))
    rw [Nat.zero_add] at this
    simpa using this
  -- the bits: the opened body's sort is the elimination level
  obtain ⟨F', tb, vb, hib, hensb, -, hbits⟩ :=
    piBits_of_infer hμ (p.nP + 3) hopAll hst hens
  rw [Nat.zero_add] at hib hensb
  have hvb : vb = elimLevel p := by
    obtain ⟨tf, n', ty', body', m', hif, hwh, rfl, -⟩ :=
      Setlec.inferTypeCore_app_inv' hib
    obtain ⟨-, rfl⟩ := inferTypeCore_fvar_inv hif
    obtain ⟨nmm, mdom, mbm, hty, -⟩ := stripPis_one_inv hmstrip
    simp only [Expr.fvarTypeD] at hty
    subst hty
    obtain ⟨-, -, rfl, -⟩ := Expr.forallE.inj (Setlec.whnf_forallE_eq hwh)
    rw [Expr.instantiate1_sort] at hensb
    exact ensureSortCore_sort_eq hensb
  subst hvb
  -- per assignment: the reading, its peel, its grading
  have hper : ∀ ψ : Name → Nat, ∃ rds : List (Nat × Nat × AVExpr),
      denoteP mp.base2.acval env ψ 0 type'
        = some (mkPisAV rds (.app (.bvar 2) (.bvar 0))) ∧
      rds.length = p.nP + 3 ∧
      (∀ d ∈ rds, ((elimLevel p).eval ψ = 0 ↔ d.2.1 = 0)) ∧
      (∀ ρ : Nat → V, AnnotOkP V ρ (mkPisAV rds (.app (.bvar 2) (.bvar 0)))) ∧
      DomsBelow 0 rds := by
    intro ψ
    have hc := claimsAtP_of hμ mp ψ F
    obtain ⟨Ta, hTa⟩ := acceptedReadsP_of mp.base2 ψ hst hw hbt' hL
    obtain ⟨-, -, hokT, -, -⟩ := hc.inferRow hst hw hbt' hL (CtxOkP.nil hnil) hTa
    have hokT' : ∀ ρ : Nat → V, AnnotOkP V ρ Ta := fun ρ =>
      hokT ρ (Sat2_nil V ρ)
    obtain ⟨Γ, R, htele, hop'⟩ := openedP_of hopAll htf' hbt' hTa hokT'
    have hR : R = .app (.bvar 2) (.bvar 0) := by
      obtain ⟨fa, aa, hfa, haa, rfl⟩ := denoteP_app_inv hop'.body
      rw [denoteP_fvar] at hfa haa
      obtain rfl := Option.some.inj hfa
      obtain rfl := Option.some.inj haa
      rw [show p.nP + 3 - 1 - (0 + p.nP) = 2 from by omega,
        show p.nP + 3 - 1 - (p.nP + 2) = 0 from by omega]
    subst hR
    obtain ⟨rds, hst', -⟩ := stripPisAV_of_piTeleP htele
    obtain ⟨hTeq, hlen⟩ := stripPisAV_eq_mkPis hst'
    subst hTeq
    refine ⟨rds, hTa, hlen, ?_, hokT', ?_⟩
    · intro d hd
      exact (stripPisAV_bits (p.nP + 3) (hbits ψ) hTa hst' d hd).symm
    · exact (stripPisAV_below hst' (bvarsBelow_of_reading hw hbt' hTa)).1
  refine ⟨fun ψ => Classical.choose (hper ψ), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun ψ => (Classical.choose_spec (hper ψ)).1
  · exact fun ψ => (Classical.choose_spec (hper ψ)).2.1
  · exact fun ψ => (Classical.choose_spec (hper ψ)).2.2.1
  · exact fun ψ => (Classical.choose_spec (hper ψ)).2.2.2.1
  · exact fun ψ => (Classical.choose_spec (hper ψ)).2.2.2.2
  · intro ψ₁ ψ₂ hφ
    have h2 := (Classical.choose_spec (hper ψ₂)).1
    have h1 : denoteP mp.base2.acval env ψ₂ 0 type'
        = some (mkPisAV (Classical.choose (hper ψ₁)) (.app (.bvar 2) (.bvar 0))) := by
      rw [← denoteP_params_ext mp.base2 hφ 0 type' htp']
      exact (Classical.choose_spec (hper ψ₁)).1
    exact (mkPisAV_inj
      (by rw [(Classical.choose_spec (hper ψ₁)).2.1,
        (Classical.choose_spec (hper ψ₂)).2.1])
      (Option.some.inj (h1.symm.trans h2))).1

/-- The recursor's data crosses a cons whose slot does not mention the
stored recursor. -/
theorem RecData.cross {m : EnvS2Core V env} {cvR : ConstantVal}
    {nP : Nat} {elimL : Level}
    {rds : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (h : RecData m cvR nP elimL rds)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none) (hat : ConsCrossAt c₀ cvR.type)
    (hcb : ConstsBound env cvR.type)
    (m₂ : EnvS2Core V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    RecData m₂ cvR nP elimL rds where
  read ψ := by
    rw [hac]
    exact denoteP_cons_mono hfresh hat ψ 0 hcb (h.read ψ)
  len := h.len
  bits := h.bits
  okTy := h.okTy
  below := h.below
  params := h.params

end Setlec.Semantics

import Setlec.SetP.Step2.DefEqP
import Setlec.SetP.Step2.InferP
import Setlec.Verify.PinnedShapes
import Setlec.Verify.InferIOLeaves

/-!
# Proof irrelevance over `interp2` (task #161, P4 — the semantic rows begin)

The defeq quarter routes `ProofIrrelPQ` (residue 3).  This file
discharges its **`Prop` branch outright** — and the discharge is
*stronger* than the collapse lane's: at `interp2` a proof of a
proposition interprets to `pt` because its type's interpretation is a
truth value (`mem_univ_zero`), so two proofs are equal **without any
side condition relating the two propositions** — the heterogeneous
comparison the v1 lane had to rule unreachable by call-site
discipline is simply harmless here.  This is the historically loaded
row: proof irrelevance at a collapse-free model is what task #100's
crisis was about, and here it is three `have`s.

The **unit-like branch** (`isUnitLikeTy` on both sides) is routed as
`UnitIrrelPQ`: its content is the structure-capability tier's
(unit-like types are subsingletons at `interp2`), discharged with the
caps/install machinery, not here.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level inferTypeCore whnf
  isUnitLikeTy)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

/-- **The unit-like branch of proof irrelevance**, routed: both
sides' types whnf to a unit-like type.  Discharged at the
structure-capability tier (a unit-like type's `interp2` is a
subsingleton — the caps invariant), not in the quarter. -/
def UnitIrrelPQ (μ : CheckMode) {env : Env} (m : EnvS2Core V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b ta wta tb wtb : Expr} {Δa : List AVExpr},
    Setlec.inferTypeIO μ env fuel d a = .ok ta →
    whnf μ env fuel d ta = .ok wta →
    isUnitLikeTy env wta = true →
    Setlec.inferTypeIO μ env fuel d b = .ok tb →
    whnf μ env fuel d tb = .ok wtb →
    isUnitLikeTy env wtb = true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {aa ba : AVExpr},
      CtxOkP m φ d Δa a → CtxOkP m φ d Δa b →
      denoteP m.acval env φ d a = some aa →
      denoteP m.acval env φ d b = some ba →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ aa) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ba) →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ aa = interp2 V ρ ba

/-- One side of the `Prop` branch: a term whose type's sort is a
zero-equivalent level interprets to `pt`. -/
private theorem prop_side_pt {m : EnvS2Core V env}
    (ihis : InferClaimsIOS2P μ m φ fuel)
    (hsss : SortSemAtIOSP m μ φ fuel)
    (hreads : InferReadsIOSP m μ φ fuel)
    {d : Nat} {a ta sta : Expr} {uT : Level} {Δa : List AVExpr}
    {aa : AVExpr}
    (hta : Setlec.inferTypeIO μ env fuel d a = .ok ta)
    (hsta : Setlec.inferTypeIO μ env fuel d ta = .ok sta)
    (hwsta : whnf μ env fuel d sta = .ok (.sort uT))
    (huT : Level.isEquiv uT .zero = some true)
    (hwa : Expr.WScoped d a) (hba : a.looseBVarsBounded 0 = true)
    (hLa : Expr.LeavesBounded a)
    (hCa : CtxOkP m φ d Δa a)
    (hda : denoteP m.acval env φ d a = some aa)
    (hokA : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ aa)
    (ρ : Nat → V) (hρ : Sat2 V Δa ρ) :
    interp2 V ρ aa = (pt : V) := by
  obtain ⟨taa, htaa⟩ :=
    hreads hta hwa hba hLa (LeafReadsP.of_ctxOkP hCa) hda
  obtain ⟨hokTa, hmemA⟩ := ihis hta hwa hba hLa hCa hda htaa hokA
  have hwta : Expr.WScoped d ta :=
    Setlec.inferTypeIO_WScoped m.wf fuel hta hwa
  have hbta : ta.looseBVarsBounded 0 = true :=
    Setlec.inferTypeIO_looseBVars m.wf fuel hta hwa hba hLa
  have hLta : Expr.LeavesBounded ta := fun l hl =>
    hLa l (Setlec.inferTypeIO_fvarLeaves m.wf fuel hta hwa l hl)
  have hCta : CtxOkP m φ d Δa ta :=
    hCa.of_subset (Setlec.inferTypeIO_fvarLeaves m.wf fuel hta hwa)
  have hA := hsss hCta hwta hbta hLta hsta hwsta htaa hokTa ρ hρ
  have h0 : Level.eval φ uT = 0 := Setlec.Level.isEquiv_sound huT φ
  rw [h0] at hA
  exact mem_univ_zero hA.2 (hmemA ρ hρ)

/-- One side of the unit-like branch: a term whose inferred type
whnf-reduces to a unit-like type interprets to `pt`.

`isUnitLikeTy` accepts only the **pinned** basis shapes
(`Kernel/Core.lean:149` — the reserved-recursor conjunct), and among
the pins only `PUnit` passes its three conditions
(`unitLike_eq_punit`), so this is a basis-level fact: the annotated
`PUnit` leaf is the pinned constant by erasure injectivity, its
`interp2` is `unitSet`, and `unitSet` is `{pt}`.  The caps tier's
first discharged row (task #161). -/
private theorem unit_side_pt {m : EnvS2Core V env}
    (ihw : WhnfClaims2P μ m φ fuel)
    (ihis : InferClaimsIOS2P μ m φ fuel)
    (hreads : InferReadsIOSP m μ φ fuel)
    (hwreads : WhnfReadsP m μ φ fuel)
    {d : Nat} {a ta wta : Expr} {Δa : List AVExpr} {aa : AVExpr}
    (hta : Setlec.inferTypeIO μ env fuel d a = .ok ta)
    (hwta : whnf μ env fuel d ta = .ok wta)
    (hu : isUnitLikeTy env wta = true)
    (hwa : Expr.WScoped d a) (hba : a.looseBVarsBounded 0 = true)
    (hLa : Expr.LeavesBounded a)
    (hCa : CtxOkP m φ d Δa a)
    (hda : denoteP m.acval env φ d a = some aa)
    (hokA : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ aa)
    (ρ : Nat → V) (hρ : Sat2 V Δa ρ) :
    interp2 V ρ aa = (pt : V) := by
  obtain ⟨taa, htaa⟩ :=
    hreads hta hwa hba hLa (LeafReadsP.of_ctxOkP hCa) hda
  obtain ⟨hokTa, hmemA⟩ := ihis hta hwa hba hLa hCa hda htaa hokA
  -- the inferred type's frames
  have hwt : Expr.WScoped d ta :=
    Setlec.inferTypeIO_WScoped m.wf fuel hta hwa
  have hbt : ta.looseBVarsBounded 0 = true :=
    Setlec.inferTypeIO_looseBVars m.wf fuel hta hwa hba hLa
  have hLt : Expr.LeavesBounded ta := fun l hl =>
    hLa l (Setlec.inferTypeIO_fvarLeaves m.wf fuel hta hwa l hl)
  have hCt : CtxOkP m φ d Δa ta :=
    hCa.of_subset (Setlec.inferTypeIO_fvarLeaves m.wf fuel hta hwa)
  -- the head normal form reads, and the reduction preserves interp2
  obtain ⟨wtaa, hwtaa⟩ := hwreads hwta hwt hbt hLt
    (LeafReadsP.of_ctxOkP hCt) htaa
  obtain ⟨-, heqW⟩ := ihw hwta hwt hbt hLt hCt htaa hwtaa hokTa
  -- the unit-like type is the pinned `PUnit`
  obtain ⟨us, rfl, hfind⟩ :=
    Setlec.TTVerify.unitLike_eq_punit m.basis_pinned hu
  -- its reading is the annotated `PUnit` leaf
  rw [denoteP, hfind] at hwtaa
  dsimp only at hwtaa
  split at hwtaa
  case isFalse => exact nomatch hwtaa
  case isTrue hlen =>
  obtain rfl : wtaa = m.acval Setlec.punitName
      (Level.substFn φ Setlec.punitA.toConstantVal.levelParams us) :=
    (Option.some.inj hwtaa).symm
  -- the leaf is the pinned constant, and its `interp2` is `unitSet`
  have hpin : m.cvalE Setlec.punitName
      (Level.substFn φ Setlec.punitA.toConstantVal.levelParams us)
      = Setlec.TT.punitT
        (Level.substFn φ Setlec.punitA.toConstantVal.levelParams us
          Setlec.uN) :=
    (m.basis_pinned Setlec.punitName _ hfind (by decide)).2 _ _ rfl
  have hleaf : m.acval Setlec.punitName
      (Level.substFn φ Setlec.punitA.toConstantVal.levelParams us)
      = .const .punit
        [Level.substFn φ Setlec.punitA.toConstantVal.levelParams us
          Setlec.uN] :=
    erase_eq_const (by rw [m.acval_erase, hpin]; rfl)
  -- the membership chain
  have hmem := hmemA ρ hρ
  rw [heqW ρ hρ, hleaf, interp2_const] at hmem
  exact mem_unitSet hmem

/-- **The unit-like branch, discharged** — `UnitIrrelPQ` is a theorem
of the claims plus the pinned basis, so it leaves the caps tier's bill
(task #161; the first of the four capability rows to fall). -/
theorem unitIrrelPQ_of_claims {m : EnvS2Core V env}
    (ihw : WhnfClaims2P μ m φ fuel)
    (ihis : InferClaimsIOS2P μ m φ fuel)
    (hreads : InferReadsIOSP m μ φ fuel)
    (hwreads : WhnfReadsP m μ φ fuel) :
    UnitIrrelPQ μ m φ fuel := by
  intro d a b ta wta tb wtb Δa hta hwta hu htb hwtb hub hwa hba hLa
    hwb hbb hLb aa ba hCa hCb hda hdb hokA hokB ρ hρ
  rw [unit_side_pt ihw ihis hreads hwreads hta hwta hu hwa hba hLa
      hCa hda hokA ρ hρ,
    unit_side_pt ihw ihis hreads hwreads htb hwtb hub hwb hbb hLb
      hCb hdb hokB ρ hρ]

/-- **Residue 3's discharge, `Prop` branch outright** (see the module
docstring); the unit-like branch routes to `UnitIrrelPQ`. -/
theorem proofIrrelPQ_of_claims {m : EnvS2Core V env}
    (ihis : InferClaimsIOS2P μ m φ fuel)
    (hsss : SortSemAtIOSP m μ φ fuel)
    (hreads : InferReadsIOSP m μ φ fuel)
    (hunit : UnitIrrelPQ μ m φ fuel) :
    ProofIrrelPQ μ m φ fuel := by
  intro d a b Δa h hwa hba hLa hwb hbb hLb aa ba hCa hCb hda hdb
    hokA hokB ρ hρ
  obtain ⟨ta, wta, hta, hwta, hbranch⟩ := Setlec.proofIrrel_inv h
  rcases hbranch with
    ⟨hu, tb, wtb, htb, hwtb, hub⟩ |
    ⟨sta, uT, tb, stb, vT, hsta, hwsta, huT, htb, hstb, hwstb, hvT⟩
  · exact hunit hta hwta hu htb hwtb hub hwa hba hLa hwb hbb hLb
      hCa hCb hda hdb hokA hokB ρ hρ
  · rw [prop_side_pt ihis hsss hreads hta hsta hwsta huT hwa hba hLa
        hCa hda hokA ρ hρ,
      prop_side_pt ihis hsss hreads htb hstb hwstb hvT hwb hbb hLb
        hCb hdb hokB ρ hρ]

end Setlec.SetR.Interp2

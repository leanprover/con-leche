module

public import ConLeche.Model.Steps.DefEq
public import ConLeche.Model.Steps.Infer
public import ConLeche.Verify.PinnedShapes
public import ConLeche.Verify.InferIOLeaves

@[expose] public section

/-!
# Proof irrelevance over `interp` (task #161, P4 — the semantic rows begin)

The defeq quarter routes `ProofIrrelPQ` (residue 3).  This file
discharges its **`Prop` branch outright** — and the discharge is
*stronger* than the collapse lane's: at `interp` a proof of a
proposition interprets to `pt` because its type's interpretation is a
truth value (`mem_univ_zero`), so two proofs are equal **without any
side condition relating the two propositions** — the heterogeneous
comparison the v1 lane had to rule unreachable by call-site
discipline is simply harmless here.  This is the historically loaded
row: proof irrelevance at a collapse-free model is what task #100's
crisis was about, and here it is three `have`s.

The **unit-like branch** (`isUnitLikeTy` on both sides) is routed as
`UnitIrrelPQ`: its content is the structure-capability tier's
(unit-like types are subsingletons at `interp`), discharged with the
caps/install machinery, not here.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level inferTypeCore whnf
  isUnitLikeTy)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

/-- **The unit-like branch of proof irrelevance**, routed: both
sides' types whnf to a unit-like type.  Discharged at the
structure-capability tier (a unit-like type's `interp` is a
subsingleton — the caps invariant), not in the quarter. -/
def UnitIrrelPQ (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b ta wta tb wtb : Expr} {Δa : List AnnotTerm},
    ConLeche.inferTypeIO μ env fuel d a = .ok ta →
    whnf μ env fuel d ta = .ok wta →
    isUnitLikeTy env wta = true →
    ConLeche.inferTypeIO μ env fuel d b = .ok tb →
    whnf μ env fuel d tb = .ok wtb →
    isUnitLikeTy env wtb = true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {aa ba : AnnotTerm},
      CtxOk m φ d Δa a → CtxOk m φ d Δa b →
      denoteMeta m.acval env φ d a = some aa →
      denoteMeta m.acval env φ d b = some ba →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ aa) →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ba) →
      ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ aa = interp V ρ ba

/-- One side of the `Prop` branch: a term whose type's sort is a
zero-equivalent level interprets to `pt`. -/
theorem prop_side_pt {m : EnvModel V env}
    (ihis : InferClaimIOS μ m φ fuel)
    (hsss : SortSemAtIOS m μ φ fuel)
    (hreads : InferReadsIOS m μ φ fuel)
    {d : Nat} {a ta sta : Expr} {uT : Level} {Δa : List AnnotTerm}
    {aa : AnnotTerm}
    (hta : ConLeche.inferTypeIO μ env fuel d a = .ok ta)
    (hsta : ConLeche.inferTypeIO μ env fuel d ta = .ok sta)
    (hwsta : whnf μ env fuel d sta = .ok (.sort uT))
    (huT : Level.isEquiv uT .zero = some true)
    (hwa : Expr.WScoped d a) (hba : a.looseBVarsBounded 0 = true)
    (hLa : Expr.LeavesBounded a)
    (hCa : CtxOk m φ d Δa a)
    (hda : denoteMeta m.acval env φ d a = some aa)
    (hokA : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ aa)
    (ρ : Nat → V) (hρ : Sat V Δa ρ) :
    interp V ρ aa = (pt : V) := by
  obtain ⟨taa, htaa⟩ :=
    hreads hta hwa hba hLa (LeafReads.of_ctxOk hCa) hda
  obtain ⟨hokTa, hmemA⟩ := ihis hta hwa hba hLa hCa hda htaa hokA
  have hwta : Expr.WScoped d ta :=
    ConLeche.inferTypeIO_WScoped m.wf fuel hta hwa
  have hbta : ta.looseBVarsBounded 0 = true :=
    ConLeche.inferTypeIO_looseBVars m.wf fuel hta hwa hba hLa
  have hLta : Expr.LeavesBounded ta := fun l hl =>
    hLa l (ConLeche.inferTypeIO_fvarLeaves m.wf fuel hta hwa l hl)
  have hCta : CtxOk m φ d Δa ta :=
    hCa.of_subset (ConLeche.inferTypeIO_fvarLeaves m.wf fuel hta hwa)
  have hA := hsss hCta hwta hbta hLta hsta hwsta htaa hokTa ρ hρ
  have h0 : Level.eval φ uT = 0 := ConLeche.Level.isEquiv_sound huT φ
  rw [h0] at hA
  exact mem_univ_zero hA.2 (hmemA ρ hρ)

/-- One side of the unit-like branch: a term whose inferred type
whnf-reduces to a unit-like type interprets to `pt`.

`isUnitLikeTy` accepts only the **pinned** basis shapes
(`Kernel/Core.lean:149` — the reserved-recursor conjunct), and among
the pins only `PUnit` passes its three conditions
(`unitLike_eq_punit`), so this is a basis-level fact: the annotated
`PUnit` leaf is the pinned constant by erasure injectivity, its
`interp` is `unitSet`, and `unitSet` is `{pt}`.  The caps tier's
first discharged row (task #161). -/
private theorem unit_side_pt {m : EnvModel V env}
    (ihw : WhnfClaim μ m φ fuel)
    (ihis : InferClaimIOS μ m φ fuel)
    (hreads : InferReadsIOS m μ φ fuel)
    (hwreads : WhnfReads m μ φ fuel)
    {d : Nat} {a ta wta : Expr} {Δa : List AnnotTerm} {aa : AnnotTerm}
    (hta : ConLeche.inferTypeIO μ env fuel d a = .ok ta)
    (hwta : whnf μ env fuel d ta = .ok wta)
    (hu : isUnitLikeTy env wta = true)
    (hwa : Expr.WScoped d a) (hba : a.looseBVarsBounded 0 = true)
    (hLa : Expr.LeavesBounded a)
    (hCa : CtxOk m φ d Δa a)
    (hda : denoteMeta m.acval env φ d a = some aa)
    (hokA : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ aa)
    (ρ : Nat → V) (hρ : Sat V Δa ρ) :
    interp V ρ aa = (pt : V) := by
  obtain ⟨taa, htaa⟩ :=
    hreads hta hwa hba hLa (LeafReads.of_ctxOk hCa) hda
  obtain ⟨hokTa, hmemA⟩ := ihis hta hwa hba hLa hCa hda htaa hokA
  -- the inferred type's frames
  have hwt : Expr.WScoped d ta :=
    ConLeche.inferTypeIO_WScoped m.wf fuel hta hwa
  have hbt : ta.looseBVarsBounded 0 = true :=
    ConLeche.inferTypeIO_looseBVars m.wf fuel hta hwa hba hLa
  have hLt : Expr.LeavesBounded ta := fun l hl =>
    hLa l (ConLeche.inferTypeIO_fvarLeaves m.wf fuel hta hwa l hl)
  have hCt : CtxOk m φ d Δa ta :=
    hCa.of_subset (ConLeche.inferTypeIO_fvarLeaves m.wf fuel hta hwa)
  -- the head normal form reads, and the reduction preserves interp
  obtain ⟨wtaa, hwtaa⟩ := hwreads hwta hwt hbt hLt
    (LeafReads.of_ctxOk hCt) htaa
  obtain ⟨-, heqW⟩ := ihw hwta hwt hbt hLt hCt htaa hwtaa hokTa
  -- the unit-like type is the pinned `PUnit`
  obtain ⟨us, rfl, hfind⟩ :=
    ConLeche.Verify.unitLike_eq_punit m.basis_pinned hu
  -- its reading is the annotated `PUnit` leaf
  rw [denoteMeta, hfind] at hwtaa
  dsimp only at hwtaa
  split at hwtaa
  case isFalse => exact nomatch hwtaa
  case isTrue hlen =>
  obtain rfl : wtaa = m.acval ConLeche.punitName
      (Level.substFn φ ConLeche.punitA.toConstantVal.levelParams us) :=
    (Option.some.inj hwtaa).symm
  -- the leaf is the pinned constant, and its `interp` is `unitSet`
  have hpin : m.cvalE ConLeche.punitName
      (Level.substFn φ ConLeche.punitA.toConstantVal.levelParams us)
      = ConLeche.Term.punitT
        (Level.substFn φ ConLeche.punitA.toConstantVal.levelParams us
          ConLeche.uN) :=
    (m.basis_pinned ConLeche.punitName _ hfind (by decide)).2 _ _ rfl
  have hleaf : m.acval ConLeche.punitName
      (Level.substFn φ ConLeche.punitA.toConstantVal.levelParams us)
      = .const .punit
        [Level.substFn φ ConLeche.punitA.toConstantVal.levelParams us
          ConLeche.uN] :=
    erase_eq_const (by rw [m.acval_erase, hpin]; rfl)
  -- the membership chain
  have hmem := hmemA ρ hρ
  rw [heqW ρ hρ, hleaf, interp_const] at hmem
  exact mem_unitSet hmem

/-- **The unit-like branch, discharged** — `UnitIrrelPQ` is a theorem
of the claims plus the pinned basis, so it leaves the caps tier's bill
(task #161; the first of the four capability rows to fall). -/
theorem unitIrrelPQ_of_claims {m : EnvModel V env}
    (ihw : WhnfClaim μ m φ fuel)
    (ihis : InferClaimIOS μ m φ fuel)
    (hreads : InferReadsIOS m μ φ fuel)
    (hwreads : WhnfReads m μ φ fuel) :
    UnitIrrelPQ μ m φ fuel := by
  intro d a b ta wta tb wtb Δa hta hwta hu htb hwtb hub hwa hba hLa
    hwb hbb hLb aa ba hCa hCb hda hdb hokA hokB ρ hρ
  rw [unit_side_pt ihw ihis hreads hwreads hta hwta hu hwa hba hLa
      hCa hda hokA ρ hρ,
    unit_side_pt ihw ihis hreads hwreads htb hwtb hub hwb hbb hLb
      hCb hdb hokB ρ hρ]

/-- **Residue 3's discharge, `Prop` branch outright** (see the module
docstring); the unit-like branch routes to `UnitIrrelPQ`. -/
theorem proofIrrelPQ_of_claims {m : EnvModel V env}
    (ihis : InferClaimIOS μ m φ fuel)
    (hsss : SortSemAtIOS m μ φ fuel)
    (hreads : InferReadsIOS m μ φ fuel)
    (hunit : UnitIrrelPQ μ m φ fuel) :
    ProofIrrelPQ μ m φ fuel := by
  intro d a b Δa h hwa hba hLa hwb hbb hLb aa ba hCa hCb hda hdb
    hokA hokB ρ hρ
  obtain ⟨ta, wta, hta, hwta, hbranch⟩ := ConLeche.proofIrrel_inv h
  rcases hbranch with
    ⟨hu, tb, wtb, htb, hwtb, hub⟩ |
    ⟨sta, uT, tb, stb, vT, hsta, hwsta, huT, htb, hstb, hwstb, hvT⟩
  · exact hunit hta hwta hu htb hwtb hub hwa hba hLa hwb hbb hLb
      hCa hCb hda hdb hokA hokB ρ hρ
  · rw [prop_side_pt ihis hsss hreads hta hsta hwsta huT hwa hba hLa
        hCa hda hokA ρ hρ,
      prop_side_pt ihis hsss hreads htb hstb hwstb hvT hwb hbb hLb
        hCb hdb hokB ρ hρ]

end ConLeche.Model

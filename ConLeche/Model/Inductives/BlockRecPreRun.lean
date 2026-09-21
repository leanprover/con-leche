module

public import ConLeche.Model.Inductives.BlockRecTyping
public import ConLeche.Model.Inductives.BlockRecRegimes
public import ConLeche.Model.Inductives.BlockRecMem
public import ConLeche.Semantics.Tower.BlockRecWfI
import ConLeche.Model.Inductives.BlockRecRead

public section

/-!
# `BlockRecPre` AT THE RUN — the regime data from `BlockModelAt` (task #315, M5 model half)

`blockRecStaged_run` (`Model/Inductives/BlockRecAssembly.lean`) closes
the recursor stage's syntactic half and leaves two semantic seams.
This file is the second of them:

```
hpre : ∀ ψ ρ, BlockRecPre V s K (blockRecTyAV mpC.base2.acval envC rs ψ) (eqs ψ) ρ
```

`blockRecPre_of` / `_kit` / `_ind` (`BlockRecRegimes.lean`) are the
DISPATCH; what was missing is the regime DATA — a `RecFamData`
(`Semantics/Tower/BlockRecKitI.lean`) built from the block's
representation `BlockModelAt` (`BlockRep.lean`), and the per-rule
certificates that make its step land in the motive.

The parts, in the order they compose:

* **§1 the rule's certificates, bundled** (`BlockRuleCerts`): every
  run-level argument of `residueOk_blockFrame`
  (`BlockRecTyping.lean`) except the frame, so that a regime consumes
  ONE hypothesis per rule and instantiates it at its own spine.  The
  bundle is the rule stage's own (`checkBlockRule_typing`); nothing
  here re-derives it;
* **§2 the carrier's case analysis** (`blockCarrier_case`): an element
  of a component's carrier IS an injection of a spine fitting one of
  the component's constructors — `BlockModelAt.fibre` at the least
  pre-fixed tuple, through the fixed-point equation — and at a
  `Type`-valued block the decomposition is UNIQUE (`mkInj`), which is
  what lets the WF regime's step be *defined* by it;
* **§3 the WF regime's family data** (`blockWfData`): `RecFamData` at
  the block's own index sets and carriers — the index set is the
  component's index-tuple set and the carrier the least pre-fixed
  tuple's component, i.e. the member's former at the prefix frame
  (`BlockModelAt.leaf`);
* **§4 `OneElimLevel` from the check** (`blockRecOneElimLevel`): D-d
  at a ground assignment, `blockRecElimAgree_eval` (`BlockRecRead.lean`)
  turned into the bit condition the candidate's λ-tower needs;
* **§5 the regimes at the run**: IND (`blockRecPre_ind_run`) and the
  `hpre` shape `blockRecStaged_run` consumes
  (`blockRecPre_run_allProp`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo openPisAtFvars)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## 1. One rule's typing certificates, bundled

`residueOk_blockFrame` takes the rule stage's two runs, the three
openings that build the frame and the frame's own correspondence, and
returns `ResidueOk` at ONE spine.  A regime instantiates it at MANY
spines — every fitting `(x⃗, f⃗)` — so the run-level arguments are
bundled once, per rule, and the frame stays free.

The bundle is exactly `checkBlockRule_typing`'s output plus the two
frame premises the typing lane does not own (`hdoms`, `hokΔ`: the
openers' stored types read to the context's entries, and the context
is graded); it is a PREMISE here, in the spelling its owners export. -/

/-- **One rule's certificates**: everything `residueOk_blockFrame`
needs that does not mention the frame. -/
def BlockRuleCerts (V : Type w) [SetTheory V] {μ : CheckMode} {envT : Env}
    (mp : EnvModelM V μ envT) (F : Nat) (ψ : Name → Nat) (rP nF nR : Nat)
    (pdoms fdoms ihdoms : List AnnotTerm) (Rb Ca : AnnotTerm) : Prop :=
  ∃ (recTy crest ihTele : Expr) (fvsPref fvsF fvsIh : List Expr)
    (o₁ o₂ o₃ bodyO ty concl : Expr),
    openPisAtFvars rP recTy 0 = some (fvsPref, o₁) ∧
    openPisAtFvars nF crest rP = some (fvsF, o₂) ∧
    openPisAtFvars nR ihTele (rP + nF) = some (fvsIh, o₃) ∧
    Expr.WScoped 0 recTy ∧ Expr.WScoped rP crest ∧ Expr.WScoped (rP + nF) ihTele ∧
    (∀ x ∈ fvsPref ++ fvsF ++ fvsIh, (Expr.fvarTypeD x).looseBVarsBounded 0 = true) ∧
    pdoms.length = rP ∧ fdoms.length = nF ∧ ihdoms.length = nR ∧
    (∀ (i : Nat) (x : Expr), (fvsPref ++ fvsF ++ fvsIh)[i]? = some x →
      denoteMeta mp.base2.acval envT ψ i (Expr.fvarTypeD x)
        = some ((ihdoms.reverse ++ (pdoms ++ fdoms).reverse).getD
            (rP + nF + nR - 1 - i) default)) ∧
    (∀ i, i < rP + nF + nR →
      ∀ ρ : Nat → V, Sat V (ihdoms.reverse ++ (pdoms ++ fdoms).reverse) ρ →
        WellDenotedV V (fun j => ρ (j + (rP + nF + nR - 1 - i) + 1))
          ((ihdoms.reverse ++ (pdoms ++ fdoms).reverse).getD (rP + nF + nR - 1 - i) default)) ∧
    ConLeche.inferTypeCore μ envT F (rP + nF + nR) bodyO = .ok ty ∧
    ConLeche.isDefEqCore μ envT F (rP + nF + nR) ty concl = .ok true ∧
    bodyO.looseBVarsBounded 0 = true ∧ concl.looseBVarsBounded 0 = true ∧
    (∀ l ∈ bodyO.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF ++ fvsIh) ∧
    (∀ l ∈ concl.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF ++ fvsIh) ∧
    denoteMeta mp.base2.acval envT ψ (rP + nF + nR) bodyO = some Rb ∧
    denoteMeta mp.base2.acval envT ψ (rP + nF + nR) concl = some Ca ∧
    (∀ ρ : Nat → V, Sat V (ihdoms.reverse ++ (pdoms ++ fdoms).reverse) ρ →
      WellDenotedV V ρ Ca)

/-- **The certificates, at one spine**: `residueOk_blockFrame` with
the run-level arguments read off the bundle.  What a regime supplies
is the frame — the prefix and field values (its own `SpineFit`) and
the `ih` openers' values (WF: `graph_mem_B`; IND: `pt`). -/
theorem BlockRuleCerts.residueOk {envT : Env} (hμ : μ.verifiedChecks = true)
    {mp : EnvModelM V μ envT} {ψ : Name → Nat} {F rP nF nR : Nat}
    {pdoms fdoms ihdoms : List AnnotTerm} {Rb Ca : AnnotTerm}
    (h : BlockRuleCerts V mp F ψ rP nF nR pdoms fdoms ihdoms Rb Ca)
    {ρ₀ : Nat → V} {xs fs ihvals : List V}
    (hsp : SpineFit ρ₀ (pdoms ++ fdoms) (xs ++ fs))
    (hih : SpineFit (consList (xs ++ fs) ρ₀) ihdoms ihvals) :
    ResidueOk V Rb ihvals (consList (xs ++ fs) ρ₀)
      (interp V (consList ihvals (consList (xs ++ fs) ρ₀)) Ca) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h₁, h₂, h₃, hw₁, hw₂, hw₃, hlbF, hp, hf, hidx,
    hdoms, hokΔ, hinf, hdeq, hbR, hbC, hleafR, hleafC, hRb, hCa, hokC⟩ := h
  exact residueOk_blockFrame hμ mp h₁ h₂ h₃ hw₁ hw₂ hw₃ hlbF hp hf hidx hdoms hokΔ
    hinf hdeq hbR hbC hleafR hleafC hRb hCa hokC hsp hih

/-- **Regime IND's per-rule obligation, from the certificates**: at
`ℓ = 0` the residue's reading lands in a truth value, which is what
`indCand_hCand`'s `hres` asks for.  `hT` — the conclusion's reading IS
a truth value — is O-2's, at the recursor's stored conclusion. -/
theorem BlockRuleCerts.hres {envT : Env} (hμ : μ.verifiedChecks = true)
    {mp : EnvModelM V μ envT} {ψ : Name → Nat} {F rP nF nR : Nat}
    {pdoms fdoms ihdoms : List AnnotTerm} {Rb Ca : AnnotTerm}
    (h : BlockRuleCerts V mp F ψ rP nF nR pdoms fdoms ihdoms Rb Ca)
    {ρ₀ : Nat → V} {xs fs ihvals : List V}
    (hsp : SpineFit ρ₀ (pdoms ++ fdoms) (xs ++ fs))
    (hih : SpineFit (consList (xs ++ fs) ρ₀) ihdoms ihvals)
    (hT : interp V (consList ihvals (consList (xs ++ fs) ρ₀)) Ca ∈ˢ (univZero : V)) :
    ∃ T : V, T ∈ˢ (univZero : V) ∧
      interp V (consList ihvals (consList (xs ++ fs) ρ₀)) Rb ∈ˢ T :=
  ⟨_, hT, (h.residueOk hμ hsp hih).2⟩

end ConLeche.Model

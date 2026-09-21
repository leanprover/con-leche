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

/-! ## 2. The carrier's case analysis

The WF regime's step must be DEFINED at an arbitrary element of a
component's carrier, and the only thing it can be defined by is the
constructor that built it.  `BlockModelAt.fibre` says that at the
OPERATOR: component `c`'s fibre of `Φ X` at `t` consists exactly of
the injections of the spines fitting one of `c`'s constructors.  The
carrier is the least pre-fixed TUPLE, and the fixed-point equation
(`app_lfpTuple_eq`, off the clause's own `functor`) moves the
statement onto it.

At a `Type`-valued block (`w ψ ≠ 0`) the decomposition is UNIQUE
(`mkInj`), and `blockDecomp` is that unique pair as a FUNCTION — the
step reads its residue at those field values. -/

/-- A fitting field spine is as long as the constructor's field
list. -/
theorem BlockData.ChainFit.length_eq {d : BlockData V} {ψ : Name → Nat} {ρp X : Nat → V}
    {t : V} {c j : Nat} {fs : List V} (h : d.ChainFit ψ ρp X t c j fs) :
    fs.length = ((d.Fss c ψ).getD j []).length :=
  FitsFrom.length_eq h.1

/-- **The carrier's case analysis**: an element of component `c`'s
carrier at the index tuple `t` is the injection of a spine fitting one
of `c`'s constructors at `(carrier, t)`.  `BlockModelAt.fibre` through
the fixed-point equation — and the tuple it is stated at is the
carrier itself, which is what makes the fields' own memberships
available (`ChainFit`'s recursive slots are at the carrier). -/
theorem blockCarrier_case {env : Env} {mo : EnvModel V env} {names : List Name}
    {d : BlockData V} (hM : BlockModelAt mo names d) {ψ : Name → Nat} {ρp : Nat → V}
    (hsat : Sat V (d.params ψ).reverse ρp) {c : Nat} (hc : c < d.N) {t : V}
    (ht : t ∈ˢ d.idx ψ ρp c) {x : V}
    (hx : x ∈ˢ app (lfpTuple (d.w ψ) d.N (d.idx ψ ρp) (d.Φ ψ ρp) c) t) :
    ∃ j fs, j < (d.ctorsM c).length ∧
      d.ChainFit ψ ρp (lfpTuple (d.w ψ) d.N (d.idx ψ ρp) (d.Φ ψ ρp)) t c j fs ∧
      x = d.inj ψ c j fs := by
  obtain ⟨hmono, hmaps, hcl⟩ := hM.functor ψ ρp hsat
  rw [← app_lfpTuple_eq hcl hmono hmaps hc ht] at hx
  exact (hM.fibre ψ ρp hsat _ (lfpTuple_mem _ _ _ _) c hc t ht x).mp hx

/-- **The decomposition is unique** at a `Type`-valued block: two
fitting spines of the same component with the same injection are the
same constructor and the same spine (`mkInj`, whose length side
conditions are `ChainFit`'s own). -/
theorem blockCarrier_case_unique {env : Env} {mo : EnvModel V env} {names : List Name}
    {d : BlockData V} (hM : BlockModelAt mo names d) {ψ : Name → Nat} {ρp X : Nat → V}
    (hw : d.w ψ ≠ 0) {c : Nat} (hc : c < d.N) {t : V} {j j' : Nat} {fs fs' : List V}
    (hj : j < (d.ctorsM c).length) (hj' : j' < (d.ctorsM c).length)
    (hfit : d.ChainFit ψ ρp X t c j fs) (hfit' : d.ChainFit ψ ρp X t c j' fs')
    (heq : d.inj ψ c j fs = d.inj ψ c j' fs') : j = j' ∧ fs = fs' :=
  hM.mkInj ψ hw c hc j fs j' fs' hj hj' hfit.length_eq hfit'.length_eq heq

open Classical in
/-- **The decomposition, as a function**: the constructor and the
field spine that built `x`, at component `c` and index tuple `t`.  Off
the carrier (and at a block where nothing fits) it is `(0, [])`, which
no clause ever reads. -/
noncomputable def blockDecomp (d : BlockData V) (ψ : Name → Nat) (ρp X : Nat → V) (c : Nat)
    (t x : V) : Nat × List V :=
  if h : ∃ p : Nat × List V, p.1 < (d.ctorsM c).length ∧
      d.ChainFit ψ ρp X t c p.1 p.2 ∧ x = d.inj ψ c p.1 p.2 then h.choose else (0, [])

/-- The decomposition's specification, where there is one. -/
theorem blockDecomp_spec {d : BlockData V} {ψ : Name → Nat} {ρp X : Nat → V} {c : Nat} {t x : V}
    (h : ∃ j fs, j < (d.ctorsM c).length ∧ d.ChainFit ψ ρp X t c j fs ∧ x = d.inj ψ c j fs) :
    (blockDecomp d ψ ρp X c t x).1 < (d.ctorsM c).length ∧
      d.ChainFit ψ ρp X t c (blockDecomp d ψ ρp X c t x).1 (blockDecomp d ψ ρp X c t x).2 ∧
      x = d.inj ψ c (blockDecomp d ψ ρp X c t x).1 (blockDecomp d ψ ρp X c t x).2 := by
  have hex : ∃ p : Nat × List V, p.1 < (d.ctorsM c).length ∧
      d.ChainFit ψ ρp X t c p.1 p.2 ∧ x = d.inj ψ c p.1 p.2 := by
    obtain ⟨j, fs, hj, hfit, hxe⟩ := h
    exact ⟨(j, fs), hj, hfit, hxe⟩
  classical
  rw [blockDecomp, dif_pos hex]
  exact hex.choose_spec

/-- **The decomposition reads back the constructor it was built
with**, at a `Type`-valued block. -/
theorem blockDecomp_eq {env : Env} {mo : EnvModel V env} {names : List Name} {d : BlockData V}
    (hM : BlockModelAt mo names d) {ψ : Name → Nat} {ρp X : Nat → V} (hw : d.w ψ ≠ 0)
    {c : Nat} (hc : c < d.N) {t : V} {j : Nat} {fs : List V}
    (hj : j < (d.ctorsM c).length) (hfit : d.ChainFit ψ ρp X t c j fs) :
    blockDecomp d ψ ρp X c t (d.inj ψ c j fs) = (j, fs) := by
  obtain ⟨hj', hfit', heq⟩ := blockDecomp_spec (x := d.inj ψ c j fs) ⟨j, fs, hj, hfit, rfl⟩
  obtain ⟨h1, h2⟩ := blockCarrier_case_unique hM hw hc hj' hj hfit' hfit heq.symm
  exact Prod.ext h1 h2

/-! ## 4. `OneElimLevel` from the check

D-d — one elimination level per family — is `checkBlockRecElimAgree`'s
own verdict, and `blockRecElimAgree_eval` (`BlockRecRead.lean`) turns
it into equalities of `Level.eval` at a ground assignment.  What the
candidate's λ-tower needs (`famCand_hCand`'s `hbits`) is the ZERONESS
bit of every binder of every class's binder data, and that is the same
bit once each class's binder numerals follow its own conclusion's sort
— the reading's fact, taken here as `hbits`. -/

/-- **D-d, in the shape the candidate consumes**: at the family's
single level `ℓ = (us.headD .zero).eval ψ` every binder numeral of
every class's binder data is zero exactly when `ℓ` is. -/
theorem blockRecOneElimLevel {us : List Level}
    (h : ConLeche.checkBlockRecElimAgree (m := ConLeche.CheckM) us = .ok ())
    (ψ : Name → Nat) {K : Nat} {rds : Nat → List (Nat × Nat × AnnotTerm)} {uOf : Nat → Level}
    (hmem : ∀ c, c < K → uOf c ∈ us)
    (hbits : ∀ c, c < K → ∀ b ∈ rds c, (b.2.1 = 0 ↔ (uOf c).eval ψ = 0)) :
    OneElimLevel ((us.headD .zero).eval ψ) K rds :=
  fun c hc b hb => (blockRecElimAgree_zero_iff h ψ (hmem c hc)).trans (hbits c hc b hb).symm

/-! ## 5. Regime IND at the run

At `ℓ = 0` the candidate is the point and `BlockRecPre`'s `hCand`
reduces to the induction principle (`hind`, the SetModel tier's) and
the residue's certified typing at every fitting spine — which is
`BlockRuleCerts.hres`.  The two things a regime still pays for are the
`ih` openers' `SpineFit` (at `ℓ = 0` the openers' values are the
point, and their domains are inhabited truth values) and `hT`, the
conclusion's reading BEING a truth value; both are named premises. -/

section IndRun

variable {envT : Env} {mp : EnvModelM V μ envT} {F s K : Nat} {ψ : Name → Nat}
  {RecTy : Nat → AnnotTerm} {nCt rP : Nat → Nat} {pdoms : Nat → List AnnotTerm}
  {fdoms es ihdoms : Nat → Nat → List AnnotTerm} {mk : Nat → Nat → AnnotTerm}
  {ihs : Nat → Nat → List AnnotTerm} {Rb Ca : Nat → Nat → AnnotTerm} {ρ : Nat → V}

/-- **Regime IND, from the run's certificates.**  `blockRecPre_ind`
with its `hres` discharged per rule by `BlockRuleCerts.hres`. -/
theorem blockRecPre_ind_run (hμ : μ.verifiedChecks = true)
    (hTy : ∀ c, c < K → interp V ρ (RecTy c) ∈ˢ (univ s : V) ∧ WellDenoted V ρ (RecTy c))
    (hwd : ∀ rs : List V, rs.length = K →
      (∀ c, c < K → rs.getD c pt ∈ˢ interp V ρ (RecTy c)) →
      ∀ c, c < K → ∀ j, j < nCt c →
        FieldsOkB 0 (consList rs ρ) (pdoms c ++ fdoms c j) ∧
        ∀ ys, SpineFit (consList rs ρ) (pdoms c ++ fdoms c j) ys →
          WellDenoted V (consList ys (consList rs ρ))
              (AnnotTerm.mkAppN (.bvar ((pdoms c).length + (fdoms c j).length + (K - 1 - c)))
                (prefVarsAV (pdoms c).length (fdoms c j).length ++ es c j ++ [mk c j])) ∧
            WellDenoted V (consList ys (consList rs ρ)) (instsAV 0 (ihs c j) (Rb c j)))
    (hind : ∀ c, c < K → (pt : V) ∈ˢ interp V ρ (RecTy c))
    (hcerts : ∀ c, c < K → ∀ j, j < nCt c →
      BlockRuleCerts V mp F ψ (rP c) (fdoms c j).length (ihdoms c j).length
        (pdoms c) (fdoms c j) (ihdoms c j) (Rb c j) (Ca c j))
    (hih : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (fun _ => (pt : V)) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      SpineFit (consList (xs ++ fs) (chainFrame K (fun _ => (pt : V)) ρ)) (ihdoms c j)
        ((ihs c j).map (interp V (consList (xs ++ fs) (chainFrame K (fun _ => (pt : V)) ρ)))))
    (hT : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (fun _ => (pt : V)) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      interp V
          (consList ((ihs c j).map (interp V (consList (xs ++ fs) (chainFrame K (fun _ => (pt : V)) ρ))))
            (consList (xs ++ fs) (chainFrame K (fun _ => (pt : V)) ρ))) (Ca c j) ∈ˢ (univZero : V)) :
    BlockRecPre V s K RecTy (iotaEqsAV K nCt pdoms fdoms es mk ihs Rb) ρ :=
  blockRecPre_ind hTy hwd hind fun c hc j hj xs fs hxl hsp =>
    (hcerts c hc j hj).hres hμ hsp (hih c hc j hj xs fs hxl hsp)
      (hT c hc j hj xs fs hxl hsp)

end IndRun

/-! ## 6. `hpre`, in `blockRecStaged_run`'s own spelling

`blockRecStaged_run` (`BlockRecAssembly.lean`) consumes

```
hpre : ∀ ψ ρ, BlockRecPre V s K (blockRecTyAV mpC.base2.acval envC rs ψ) (eqs ψ) ρ
```

with `eqs ψ` the rule data's ι equations at `ψ`.  At an all-`Prop`
family (`ℓ = 0`, which every mutual or nested `Prop` block is by the
elimination guard) that is `blockRecPre_ind_run` at every `ψ` and
every `ρ`, and this is it verbatim — the theorem the coordinator
`exact`s into the assembly. -/

/-- **`hpre` at an all-`Prop` family**, in the assembly's spelling. -/
theorem blockRecPre_run_allProp {envC envT : Env} (hμ : μ.verifiedChecks = true)
    {mpC : EnvModelM V μ envC} {mp : EnvModelM V μ envT} {F s K : Nat}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {nCt rP : Nat → Nat} {pdoms : (Name → Nat) → Nat → List AnnotTerm}
    {fdoms es ihdoms : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {mk : (Name → Nat) → Nat → Nat → AnnotTerm}
    {ihs : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {Rb Ca : (Name → Nat) → Nat → Nat → AnnotTerm}
    (hTy : ∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ c, c < K →
      interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c) ∈ˢ (univ s : V) ∧
        WellDenoted V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c))
    (hwd : ∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ as : List V, as.length = K →
      (∀ c, c < K → as.getD c pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c)) →
      ∀ c, c < K → ∀ j, j < nCt c →
        FieldsOkB 0 (consList as ρ) (pdoms ψ c ++ fdoms ψ c j) ∧
        ∀ ys, SpineFit (consList as ρ) (pdoms ψ c ++ fdoms ψ c j) ys →
          WellDenoted V (consList ys (consList as ρ))
              (AnnotTerm.mkAppN
                (.bvar ((pdoms ψ c).length + (fdoms ψ c j).length + (K - 1 - c)))
                (prefVarsAV (pdoms ψ c).length (fdoms ψ c j).length ++ es ψ c j
                  ++ [mk ψ c j])) ∧
            WellDenoted V (consList ys (consList as ρ)) (instsAV 0 (ihs ψ c j) (Rb ψ c j)))
    (hind : ∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ c, c < K →
      (pt : V) ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c))
    (hcerts : ∀ (ψ : Name → Nat), ∀ c, c < K → ∀ j, j < nCt c →
      BlockRuleCerts V mp F ψ (rP c) (fdoms ψ c j).length (ihdoms ψ c j).length
        (pdoms ψ c) (fdoms ψ c j) (ihdoms ψ c j) (Rb ψ c j) (Ca ψ c j))
    (hih : ∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms ψ c).length →
      SpineFit (chainFrame K (fun _ => (pt : V)) ρ) (pdoms ψ c ++ fdoms ψ c j) (xs ++ fs) →
      SpineFit (consList (xs ++ fs) (chainFrame K (fun _ => (pt : V)) ρ)) (ihdoms ψ c j)
        ((ihs ψ c j).map
          (interp V (consList (xs ++ fs) (chainFrame K (fun _ => (pt : V)) ρ)))))
    (hT : ∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms ψ c).length →
      SpineFit (chainFrame K (fun _ => (pt : V)) ρ) (pdoms ψ c ++ fdoms ψ c j) (xs ++ fs) →
      interp V
          (consList
            ((ihs ψ c j).map
              (interp V (consList (xs ++ fs) (chainFrame K (fun _ => (pt : V)) ρ))))
            (consList (xs ++ fs) (chainFrame K (fun _ => (pt : V)) ρ))) (Ca ψ c j)
        ∈ˢ (univZero : V)) :
    ∀ (ψ : Name → Nat) (ρ : Nat → V),
      BlockRecPre V s K (blockRecTyAV mpC.base2.acval envC rs ψ)
        (iotaEqsAV K nCt (pdoms ψ) (fdoms ψ) (es ψ) (mk ψ) (ihs ψ) (Rb ψ)) ρ :=
  fun ψ ρ =>
    blockRecPre_ind_run hμ (hTy ψ ρ) (hwd ψ ρ) (hind ψ ρ) (hcerts ψ) (hih ψ ρ) (hT ψ ρ)

end ConLeche.Model

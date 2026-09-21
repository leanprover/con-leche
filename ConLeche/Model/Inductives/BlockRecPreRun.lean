module

import ConLeche.Model.Inductives.BlockRecTyping
import ConLeche.Model.Inductives.BlockRecRegimes
public import ConLeche.Model.Inductives.BlockRecMem
public import ConLeche.Semantics.Tower.BlockRecWfI
import ConLeche.Model.Inductives.BlockRecRead
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockAssemblyKit
import ConLeche.Model.Inductives.BlockModel
public import ConLeche.Model.Inductives.BlockStageCtors
import ConLeche.Model.Inductives.FixAssemblyKit

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

/-! ## 3. The WF regime's family data, at the block's own carriers

`RecFamData` (`Semantics/Tower/BlockRecKitI.lean`) asks, per PREFIX
SPINE, for the classes' index sets and ORDINARY carriers, the index
tuple, a class kit, and the two readings the recursors' TYPES fix.
For a block the first three are not a choice:

* the prefix spine's first `nP` values ARE the block's parameters (the
  recursor's rule prefix begins with them, `checkBlockRecTys`), so the
  parameter frame is `consList (xs.take nP) ρ`;
* class `c` eliminates the member `mem c`, so its index set is that
  component's index-tuple set and its carrier the least pre-fixed
  tuple's component — which is the member's FORMER at the parameter
  frame, by `BlockModelAt.leaf`.

That last identification is the whole content of `blockWf_hsplit`: the
major's binder domain is the member's former applied, the clause's
`leaf` turns the fold into `app (lfpTuple …) ⟨ı⃗⟩`, and the index
tuple lands in the index set by `tupW_mem`. -/

section WfData

variable {env : Env} {mo : EnvModel V env} {names : List Name} {d : BlockData V}

/-- Class `c`'s index set at a prefix spine: the eliminated
component's own index-tuple set, at the parameter frame. -/
@[expose] noncomputable def blockRecIs (d : BlockData V) (ψ : Name → Nat) (ρ : Nat → V)
    (mem : Nat → Nat) (xs : List V) (c : Nat) : V :=
  d.idx ψ (consList (xs.take d.nP) ρ) (mem c)

/-- Class `c`'s ORDINARY carrier at a prefix spine: the eliminated
component of the block's least pre-fixed tuple. -/
@[expose] noncomputable def blockRecCr (d : BlockData V) (ψ : Name → Nat) (ρ : Nat → V)
    (mem : Nat → Nat) (xs : List V) (c : Nat) : V :=
  lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
    (d.Φ ψ (consList (xs.take d.nP) ρ)) (mem c)

/-- **What O-2 owes about a recursor's binder data**: a fitting spine
of `rec_c`'s type is the rule prefix, the eliminated member's indices
and the major; the prefix begins with the block's parameters; the
index values fit the member's own index telescope there; and the
major lies in the member's former applied to both.  Every conjunct is
a statement about the STORED type's reading, none about the
recursion. -/
@[expose] def BlockRecSplitAt (V : Type w) [SetTheory V] {env : Env} (mo : EnvModel V env)
    (d : BlockData V) (ψ : Name → Nat) (K : Nat) (rP mem : Nat → Nat)
    (rds : Nat → List (Nat × Nat × AnnotTerm)) (ρ : Nat → V) : Prop :=
  ∀ c, c < K → ∀ ys : List V, SpineFit ρ ((rds c).map (·.2.2)) ys →
    (prefOf (rP c) ys).length = rP c ∧
    ys = prefOf (rP c) ys ++ (idxOf (rP c) ys ++ [majOf ys]) ∧
    SpineFit ρ (d.params ψ) ((prefOf (rP c) ys).take d.nP) ∧
    SpineFit (consList ((prefOf (rP c) ys).take d.nP) ρ) (d.IdsM (mem c) ψ)
      (idxOf (rP c) ys) ∧
    majOf ys ∈ˢ ((prefOf (rP c) ys).take d.nP ++ idxOf (rP c) ys).foldl app
      (interp V ρ (mo.acval (d.memberName (mem c)) ψ))

/-- **`RecFamData.hsplit` at the block's carriers**, from the stored
type's reading and the representation's `leaf` clause. -/
theorem blockWf_hsplit (hM : BlockModelAt mo names d) {ψ : Name → Nat} {ρ : Nat → V}
    {K : Nat} {rP mem : Nat → Nat} {rds : Nat → List (Nat × Nat × AnnotTerm)}
    (hmem : ∀ c, c < K → mem c < d.k)
    (hsplit : BlockRecSplitAt V mo d ψ K rP mem rds ρ) :
    ∀ c, c < K → ∀ ys, SpineFit ρ ((rds c).map (·.2.2)) ys →
      (prefOf (rP c) ys).length = rP c ∧
      ys = prefOf (rP c) ys ++ (idxOf (rP c) ys ++ [majOf ys]) ∧
      d.tup ψ (mem c) (idxOf (rP c) ys) ∈ˢ blockRecIs d ψ ρ mem (prefOf (rP c) ys) c ∧
      majOf ys ∈ˢ app (blockRecCr d ψ ρ mem (prefOf (rP c) ys) c)
        (d.tup ψ (mem c) (idxOf (rP c) ys)) := by
  intro c hc ys hfit
  obtain ⟨hlen, hdec, hpar, hidx, hmaj⟩ := hsplit c hc ys hfit
  refine ⟨hlen, hdec, tupW_mem hidx, ?_⟩
  rw [blockRecCr, ← hM.leaf (mem c) (hmem c hc) ψ ρ ((prefOf (rP c) ys).take d.nP)
    (idxOf (rP c) ys) hpar hidx]
  exact hmaj

/-- **The WF regime's family data at a block**: `RecFamData` with the
index sets, the carriers and the index tuple fixed by the
representation, and the kit F5's (`WfRecKit`, whose motive and step
are the regime's own). -/
@[expose] noncomputable def blockWfData {ℓ K : Nat} {rP mem : Nat → Nat}
    {rds : Nat → List (Nat × Nat × AnnotTerm)} {concl : Nat → AnnotTerm} {ψ : Name → Nat}
    {ρ : Nat → V} (d : BlockData V)
    (kitW : ∀ xs : List V, WfRecKit ℓ K (blockRecIs d ψ ρ mem xs) (blockRecCr d ψ ρ mem xs))
    (hsplit : ∀ c, c < K → ∀ ys, SpineFit ρ ((rds c).map (·.2.2)) ys →
      (prefOf (rP c) ys).length = rP c ∧
      ys = prefOf (rP c) ys ++ (idxOf (rP c) ys ++ [majOf ys]) ∧
      d.tup ψ (mem c) (idxOf (rP c) ys) ∈ˢ blockRecIs d ψ ρ mem (prefOf (rP c) ys) c ∧
      majOf ys ∈ˢ app (blockRecCr d ψ ρ mem (prefOf (rP c) ys) c)
        (d.tup ψ (mem c) (idxOf (rP c) ys)))
    (hconcl : ∀ c, c < K → ∀ ys, SpineFit ρ ((rds c).map (·.2.2)) ys →
      (kitW (prefOf (rP c) ys)).B
          (tagged c (d.tup ψ (mem c) (idxOf (rP c) ys)) (majOf ys))
        = interp V (consList ys ρ) (concl c)) :
    RecFamData V ℓ K rP rds concl ρ :=
  wfData (rds := rds) (concl := concl) (rP := rP) (ρ := ρ)
    (blockRecIs d ψ ρ mem) (blockRecCr d ψ ρ mem) (fun c is => d.tup ψ (mem c) is)
    kitW hsplit hconcl

end WfData

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

/-- **The `c`-th recursor's RULE COUNT** — the lanes' shared choice of
`nCt` (`M5M-data-REPORT` §6): what `sumRules` enumerates. -/
@[expose] def blockRecNCt
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))) (c : Nat) : Nat :=
  (rs.getD c default).2.2.2.length

/-- **`hpre` at an all-`Prop` family**, in the assembly's spelling and
at the lanes' shared choice of `K`, `nCt` and `eqs`. -/
theorem blockRecPre_run_allProp {envC envT : Env} (hμ : μ.verifiedChecks = true)
    {mpC : EnvModelM V μ envC} {mp : EnvModelM V μ envT} {F s : Nat}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {rP : Nat → Nat} {pdoms : (Name → Nat) → Nat → List AnnotTerm}
    {fdoms es ihdoms : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {mk : (Name → Nat) → Nat → Nat → AnnotTerm}
    {ihs : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {Rb Ca : (Name → Nat) → Nat → Nat → AnnotTerm}
    (hTy : ∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ c, c < rs.length →
      interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c) ∈ˢ (univ s : V) ∧
        WellDenoted V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c))
    (hwd : ∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ as : List V, as.length = rs.length →
      (∀ c, c < rs.length →
        as.getD c pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c)) →
      ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
        FieldsOkB 0 (consList as ρ) (pdoms ψ c ++ fdoms ψ c j) ∧
        ∀ ys, SpineFit (consList as ρ) (pdoms ψ c ++ fdoms ψ c j) ys →
          WellDenoted V (consList ys (consList as ρ))
              (AnnotTerm.mkAppN
                (.bvar ((pdoms ψ c).length + (fdoms ψ c j).length + (rs.length - 1 - c)))
                (prefVarsAV (pdoms ψ c).length (fdoms ψ c j).length ++ es ψ c j
                  ++ [mk ψ c j])) ∧
            WellDenoted V (consList ys (consList as ρ)) (instsAV 0 (ihs ψ c j) (Rb ψ c j)))
    (hind : ∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ c, c < rs.length →
      (pt : V) ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c))
    (hcerts : ∀ (ψ : Name → Nat), ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      BlockRuleCerts V mp F ψ (rP c) (fdoms ψ c j).length (ihdoms ψ c j).length
        (pdoms ψ c) (fdoms ψ c j) (ihdoms ψ c j) (Rb ψ c j) (Ca ψ c j))
    (hih : ∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      ∀ xs fs : List V, xs.length = (pdoms ψ c).length →
      SpineFit (chainFrame rs.length (fun _ => (pt : V)) ρ) (pdoms ψ c ++ fdoms ψ c j)
        (xs ++ fs) →
      SpineFit (consList (xs ++ fs) (chainFrame rs.length (fun _ => (pt : V)) ρ))
        (ihdoms ψ c j)
        ((ihs ψ c j).map
          (interp V (consList (xs ++ fs) (chainFrame rs.length (fun _ => (pt : V)) ρ)))))
    (hT : ∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      ∀ xs fs : List V, xs.length = (pdoms ψ c).length →
      SpineFit (chainFrame rs.length (fun _ => (pt : V)) ρ) (pdoms ψ c ++ fdoms ψ c j)
        (xs ++ fs) →
      interp V
          (consList
            ((ihs ψ c j).map
              (interp V (consList (xs ++ fs) (chainFrame rs.length (fun _ => (pt : V)) ρ))))
            (consList (xs ++ fs) (chainFrame rs.length (fun _ => (pt : V)) ρ))) (Ca ψ c j)
        ∈ˢ (univZero : V)) :
    ∀ (ψ : Name → Nat) (ρ : Nat → V),
      BlockRecPre V s rs.length (blockRecTyAV mpC.base2.acval envC rs ψ)
        (iotaEqsAV rs.length (blockRecNCt rs) (pdoms ψ) (fdoms ψ) (es ψ) (mk ψ) (ihs ψ)
          (Rb ψ)) ρ :=
  fun ψ ρ =>
    blockRecPre_ind_run hμ (hTy ψ ρ) (hwd ψ ρ) (hind ψ ρ) (hcerts ψ) (hih ψ ρ) (hT ψ ρ)

/-! ## 7. The LEAF's bridge from the dummy chains to the real ones

`blockModelAt_of_stages` asks for the members' leaves at the REAL
field readings `d.Fss`, while every stage supplies them at the dummy
former's `fssZ` (`BlockCtorsStage.leaf`): the constructors are checked
against a former whose recursive fields are not yet the member's own.
The operator's half of that bridge is `blockChainsOk_congr_ord`
(`BlockAssemblyKit.lean`); the LEAF's half is here, and it is a pure
CONGRUENCE — `blockTyAV` reads the field lists only through
`chainsXBI`, and `chainsXBI_congr_ord` already says those are the same
list when the two readings agree at the ordinary positions.

Its home is `BlockAssemblyKit.lean`, beside the operator's half; it is
here because this lane owns one file. -/

/-- The tuple-maker is congruent in its component function over the
range it reads. -/
theorem ndMkTowerAV_congr_lt {r : Nat} {Gty G G' : Nat → AnnotTerm} :
    ∀ (n s : Nat), (∀ i, i < n → G (s + i) = G' (s + i)) →
      ndMkTowerAV r Gty G s n = ndMkTowerAV r Gty G' s n
  | 0, _, _ => rfl
  | n + 1, s, h => by
    have h0 : G s = G' s := by simpa using h 0 (Nat.succ_pos n)
    have hrest : ∀ i, i < n → G (s + 1 + i) = G' (s + 1 + i) := by
      intro i hi
      have := h (i + 1) (by omega)
      rwa [show s + (i + 1) = s + 1 + i from by omega] at this
    show AnnotTerm.mkAppN _ [_, _, G s, ndMkTowerAV r Gty G (s + 1) n] = _
    rw [h0, ndMkTowerAV_congr_lt n (s + 1) hrest]
    rfl

/-- **The block's operator term is congruent** in the field readings,
at equal chains. -/
theorem blockFunAV_congr_chains {k w : Nat} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
    {rsss : Nat → List (List Bool)} {tgtsss : Nat → List (List Nat)}
    {tlsss : Nat → List (List (List (Nat × Nat × AnnotTerm)))}
    {Eisss : Nat → List (List (List AnnotTerm))} {Fsss Fsss' Esss : Nat → List (List AnnotTerm)}
    (hchains : ∀ m, m < k →
      chainsXBI uf Idss (Idss m).length (rsss m) (tgtsss m) (tlsss m) (Eisss m) (Fsss m) (Esss m)
        = chainsXBI uf Idss (Idss m).length (rsss m) (tgtsss m) (tlsss m) (Eisss m) (Fsss' m)
            (Esss m)) :
    blockFunAV k w uf Idss rsss tgtsss tlsss Eisss Fsss Esss
      = blockFunAV k w uf Idss rsss tgtsss tlsss Eisss Fsss' Esss := by
  unfold blockFunAV
  refine congrArg _ (ndMkTowerAV_congr_lt k 0 fun i hi => ?_)
  rw [Nat.zero_add]
  unfold blockArmAV
  rw [hchains i hi]

/-- **The LEAF's bridge**: a member's former leaf is the same term at
the dummy former's field readings and at the members' real ones, when
the two agree at the ORDINARY positions — the `blockTyAV` twin of
`blockChainsOk_congr_ord`. -/
theorem blockTyAV_congr_ord {k w : Nat} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
    {rsss : Nat → List (List Bool)} {tgtsss : Nat → List (List Nat)}
    {tlsss : Nat → List (List (List (Nat × Nat × AnnotTerm)))}
    {Eisss : Nat → List (List (List AnnotTerm))} {Fsss Fsss' Esss : Nat → List (List AnnotTerm)}
    (hlen : ∀ m, m < k → (Fsss m).length = (Fsss' m).length)
    (hlenj : ∀ m, m < k → ∀ j, j < (Fsss m).length →
      ((Fsss m).getD j []).length = ((Fsss' m).getD j []).length)
    (hord : ∀ m, m < k → ∀ j, j < (Fsss m).length → ∀ l, l < ((Fsss m).getD j []).length →
      ((rsss m).getD j []).getD l false = false →
      ((Fsss m).getD j []).getD l default = ((Fsss' m).getD j []).getD l default)
    (pps : List (Nat × Nat × AnnotTerm)) (m : Nat) :
    blockTyAV k w uf Idss rsss tgtsss tlsss Eisss Fsss Esss pps m
      = blockTyAV k w uf Idss rsss tgtsss tlsss Eisss Fsss' Esss pps m := by
  have hchains : ∀ m', m' < k →
      chainsXBI uf Idss (Idss m').length (rsss m') (tgtsss m') (tlsss m') (Eisss m') (Fsss m')
          (Esss m')
        = chainsXBI uf Idss (Idss m').length (rsss m') (tgtsss m') (tlsss m') (Eisss m')
            (Fsss' m') (Esss m') :=
    fun m' hm' => chainsXBI_congr_ord (hlen m' hm') (hlenj m' hm') (hord m' hm')
  unfold blockTyAV blockBodyAV
  rw [blockFunAV_congr_chains (w := w) hchains]

/-! ## 8. `BlockModelAt` from the stages' three records

`declBlock` hands the recursor lane the block data `dR` with the three
records `blockModelAt_of_stages` consumes (`BlockNamesOk`,
`BlockCtorsStage`, `BlockCtorsCore`) rather than the representation
itself, because the records state the operator's premise bundle and
the members' leaves at the DUMMY former's field readings `fssZ` while
the record wants them at the members' real ones.  Both bridges are
congruences at the chains — `blockChainsOk_congr_ord` for the operator
and §7's `blockTyAV_congr_ord` for the leaf — and this is the call.

**Session 2**: the three clauses `blockModelAt_of_stages` used to
state at an UNBOUNDED component index (`hlenPps`, `hparams`,
`hparamsC`) are now bounded by `d.N` — at `c ≥ d.N` they were not
facts about the block at all — so the records suffice and only the
operator's and the injections' identification stay premises (both
`rfl` at `blockDataOf`), beside `d.nInst = 0` and `0 < d.k`. -/

/-- **The block's representation, from the stages' three records.** -/
theorem blockModelAt_of_records {envC envI : Env} {mo : EnvModel V envC} {d : BlockData V}
    {lps : List Name} {cvTas : List ConstantVal} {p₁ : ConLeche.BlockShape} {isRec : Bool}
    {F : Nat} {A : Nat → (Name → Nat) → AnnotTerm}
    {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)} {ctorsOf : Name → List Name}
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d lps cvTas p₁ isRec A fssZ envI ctorsOf)
    (hcore : BlockCtorsCore mo d lps cvTas p₁ isRec A d.k)
    (hinst : d.nInst = 0) (hk0 : 0 < d.k)
    (hPhi : ∀ (ψ : Name → Nat) (ρp : Nat → V), d.Φ ψ ρp
      = blockPhi d.N (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) d.rss d.tgtss
          (fun c => d.tlss c ψ) (fun c => d.Eiss c ψ) (fun c => d.Fss c ψ) (fun c => d.Ess c ψ))
    (hinj : ∀ (ψ : Name → Nat) (c j : Nat) (fs : List V),
      d.inj ψ c j fs = if d.w ψ = 0 then (pt : V) else inj j (mkTower (fs ++ [pt]))) :
    BlockModelAt mo d.memberNames d := by
  have hNk : d.N = d.k := by rw [BlockData.N, hinst]; rfl

  have hcAof : ∀ (c j : Nat) (hj : j < (d.ctorsM c).length),
      (d.ctorsM c)[j]? = some (d.ctorsM c)[j] := fun _ _ hj => List.getElem?_eq_getElem hj
  -- the field chains' shape, off the data
  have hlenC : ∀ (ψ : Name → Nat) (c : Nat), (d.Fss c ψ).length = (d.ctorsM c).length := by
    intro ψ c
    show (fssOfR _ _).length = _
    rw [fssOfR_length]
    exact fixCtorDataList_length _ _ _ _ _ _ _ _
  have hFssD : ∀ (ψ : Name → Nat) (c j : Nat) (cA : ConstantVal × Nat),
      (d.ctorsM c)[j]? = some cA →
      (d.Fss c ψ).getD j [] = ((d.dsF c j ψ).drop d.nP).map (·.2.2) :=
    fun _ _ _ _ hj => fssOfR_fixCtorDataList_getD hj
  have hdsLenA : ∀ (ψ : Name → Nat) (c j : Nat) (cA : ConstantVal × Nat),
      (d.ctorsM c)[j]? = some cA → (d.dsF c j ψ).length = d.nP + cA.2 :=
    fun ψ c j cA hj => (hcore.2.2.1 c j cA hj).2.2.len ψ
  have hnF : ∀ (ψ : Name → Nat) (c j : Nat) (cA : ConstantVal × Nat),
      (d.ctorsM c)[j]? = some cA → ((d.Fss c ψ).getD j []).length = cA.2 := by
    intro ψ c j cA hj
    rw [hFssD ψ c j cA hj, List.length_map, List.length_drop, hdsLenA ψ c j cA hj]
    omega
  -- the parameter frame, at every component and every constructor
  have hlenPps : ∀ (ψ : Name → Nat) (c : Nat), c < d.N →
      (d.ppsM c ψ).length = d.nP + (d.IdsM c ψ).length :=
    fun ψ c hc => hS.lenPps c ψ (by rw [← hNk]; exact hc)
  have hparams : ∀ (ψ : Name → Nat) (c : Nat), c < d.N → ∀ ρ : Nat → V,
      Sat V (d.params ψ).reverse ρ ↔
        Sat V (((d.ppsM c ψ).take d.nP).map (·.2.2)).reverse ρ := by
    intro ψ c hc ρ
    have hck : c < d.k := by rw [← hNk]; exact hc
    exact ⟨fun h => hS.paramsOf 0 hk0 ψ ρ h c hck, fun h => hS.paramsOf c hck ψ ρ h 0 hk0⟩
  have hparamsC : ∀ (ψ : Name → Nat) (c j : Nat), c < d.N → j < (d.ctorsM c).length →
      ∀ ρ : Nat → V,
      Sat V (d.params ψ).reverse ρ ↔
        Sat V (((d.dsF c j ψ).take d.nP).map (·.2.2)).reverse ρ := by
    intro ψ c j hc hj ρ
    exact (hparams ψ c hc ρ).trans
      ((hS.frames c (by rw [← hNk]; exact hc) j _ (hcAof c j hj)).1 ψ ρ)
  -- the per-field targets, off the data and the names
  have hks : ∀ (ψ : Name → Nat) (c j : Nat), j < (d.ctorsM c).length →
      (d.ksF c j).length = ((d.Fss c ψ).getD j []).length := by
    intro ψ c j hj
    rw [hnF ψ c j _ (hcAof c j hj)]
    exact (hcore.2.2.1 c j _ (hcAof c j hj)).2.2.ksLen
  have htgts : ∀ (ψ : Name → Nat) (c j l : Nat), j < (d.ctorsM c).length →
      l < ((d.Fss c ψ).getD j []).length →
      ((d.tgtss c).getD j []).getD l 0 = d.tgts c j l ∧ d.tgts c j l < d.N := by
    intro ψ c j l hj hl
    have hlk : l < (d.ksF c j).length := by rw [hks ψ c j hj]; exact hl
    refine ⟨?_, ?_⟩
    · have hinner : (d.tgtss c).getD j [] = (List.range (d.ksF c j).length).map (d.tgts c j) := by
        show (((List.range (d.ctorsM c).length).map fun j' =>
          (List.range (d.ksF c j').length).map (d.tgts c j')).getD j []) = _
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
        rfl
      rw [hinner, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlk]
      rfl
    · rw [hNk, ← hN.2.2.2]
      exact hN.2.1 c j l
  -- the two chain lists agree: lengths, and the ordinary positions
  have hlenZF : ∀ (ψ : Name → Nat) (m : Nat), m < d.k → (fssZ ψ m).length = (d.Fss m ψ).length :=
    fun ψ m hm => by rw [hS.lenZ m hm ψ, hlenC ψ m]
  have hlenjZF : ∀ (ψ : Name → Nat) (m : Nat), m < d.k → ∀ j, j < (fssZ ψ m).length →
      ((fssZ ψ m).getD j []).length = ((d.Fss m ψ).getD j []).length := by
    intro ψ m hm j hj
    have hjc : j < (d.ctorsM m).length := by rw [← hS.lenZ m hm ψ]; exact hj
    rw [hS.lenZj m hm ψ j _ (hcAof m j hjc), hnF ψ m j _ (hcAof m j hjc)]
  have hordF : ∀ (ψ : Name → Nat) (m : Nat), m < d.k → ∀ j, j < (fssZ ψ m).length →
      ∀ l, l < ((fssZ ψ m).getD j []).length →
      ((d.rss m).getD j []).getD l false = false →
      ((fssZ ψ m).getD j []).getD l default = ((d.Fss m ψ).getD j []).getD l default := by
    intro ψ m hm j hj l hl hr
    have hjc : j < (d.ctorsM m).length := by rw [← hS.lenZ m hm ψ]; exact hj
    have hlj : ((fssZ ψ m).getD j []).length = ((d.ctorsM m)[j]).2 :=
      hS.lenZj m hm ψ j _ (hcAof m j hjc)
    have hks : (d.ksF m j).length = ((d.ctorsM m)[j]).2 :=
      (hcore.2.2.1 m j _ (hcAof m j hjc)).2.2.ksLen
    have hlk : l < (d.ksF m j).length := by rw [hks, ← hlj]; exact hl
    have hrs : (d.rss m).getD j [] = rsOf (d.ksF m j) := rssOfK_getD hjc
    have hnrec : ¬ recAt d.nP (d.ksF m j) (d.nP + l) := by
      rw [recAt_iff_rsOf hlk, ← hrs, hr]
      exact Bool.false_ne_true
    exact (hS.ord m hm j _ (hcAof m j hjc) ψ l (by rw [← hlj]; exact hl) hnrec).symm
  refine blockModelAt_of_stages mo rfl hPhi hinj ?_ hlenC (by rw [hNk]; exact hk0) hlenPps
    htgts ?_ hparams ?_ (fun ψ c j hj => hFssD ψ c j _ (hcAof c j hj)) ?_ hparamsC ?_
  -- the operator's premise bundle, at the REAL chains
  · intro ψ ρp hsat
    rw [hNk]
    exact blockChainsOk_congr_ord (hlenZF ψ) (hlenjZF ψ) (hordF ψ)
      (hS.chainsOk 0 hk0 ψ ρp ((hparams ψ 0 (by rw [hNk]; exact hk0) ρp).mp hsat))
  -- the members' leaves, at the REAL chains
  · intro mm hmm ψ
    obtain ⟨hnameOf, -, -, hlenCv⟩ := hN
    have hmmlt : mm < cvTas.length := by rw [hlenCv]; exact hmm
    have hcv : cvTas[mm]? = some cvTas[mm] := List.getElem?_eq_getElem hmmlt
    rw [hnameOf mm _ hcv, (hcore.1 mm _ hcv).2.2.1 ψ, hS.leaf mm ψ, hNk]
    exact blockTyAV_congr_ord (hlenZF ψ) (hlenjZF ψ) (hordF ψ) _ _
  -- the constructors' leaves
  · intro c hc j cA hj ψ
    exact (hcore.2.2.2 c (by rw [← hNk]; exact hc) j cA hj).2.2 ψ
  -- the field lists' lengths against the constructors' binder data
  · intro ψ c j hj
    rw [hdsLenA ψ c j _ (hcAof c j hj), hnF ψ c j _ (hcAof c j hj)]
  -- the field chains are graded at every parameter frame
  · intro ψ ρ hsat c hc
    refine SumFieldsOkB_uChains fun Fs hFs => ?_
    obtain ⟨j, hjget⟩ := List.getElem?_of_mem hFs
    have hjlt : j < (d.Fss c ψ).length := (List.getElem?_eq_some_iff.mp hjget).1
    have hjc : j < (d.ctorsM c).length := by rw [← hlenC ψ c]; exact hjlt
    have hFsEq : Fs = ((d.dsF c j ψ).drop d.nP).map (·.2.2) := by
      rw [← hFssD ψ c j _ (hcAof c j hjc), List.getD_eq_getElem?_getD, hjget]
      rfl
    rw [hFsEq]
    have hfr := hS.frames c (by rw [← hNk]; exact hc) j _ (hcAof c j hjc)
    exact (hfr.2 ψ ρ ((hfr.1 ψ ρ).mp ((hparams ψ c hc ρ).mp hsat))).1

/-! ## 9. The WF kit's MOTIVE

`WfRecKit.B` is a function of the TAGGED element alone, so the motive
must recover the spine the conclusion is read at: the class, the index
tuple and the major.  `tagged` is injective (`tagged_inj`), so below
`K` the decoding is unique and `tagDec` is it as a function; the index
SPINE comes back out of its tuple by `isOfW` (`isOfW_tupW`, at the
member's own index telescope), exactly as regime SQ reads it.

With that the two clauses the kit and the family data owe about the
motive are one rewrite each: `hconcl` (`RecFamData`'s) says the motive
at the tagged index IS the conclusion's reading at the fitting spine,
and `hB` (the kit's) says it is a set of the family's level, which is
O-2's reading fact restated at the decoded data. -/

open Classical in
/-- **A tagged element's class, index and value**, as a function. -/
noncomputable def tagDec (K : Nat) (u : V) : Nat × V × V :=
  if h : ∃ p : Nat × V × V, p.1 < K ∧ u = tagged p.1 p.2.1 p.2.2 then h.choose else (0, pt, pt)

theorem tagDec_tagged {K c : Nat} (hc : c < K) (i x : V) :
    tagDec K (tagged c i x) = (c, i, x) := by
  classical
  have hex : ∃ p : Nat × V × V, p.1 < K ∧ (tagged c i x : V) = tagged p.1 p.2.1 p.2.2 :=
    ⟨(c, i, x), hc, rfl⟩
  rw [tagDec, dif_pos hex]
  obtain ⟨-, heq⟩ := hex.choose_spec
  obtain ⟨h1, h2, h3⟩ := tagged_inj heq
  exact Prod.ext h1.symm (Prod.ext h2.symm h3.symm)

/-- **The WF kit's motive**: the recursor's CONCLUSION, read at the
spine the tagged element carries — the prefix, the index spine
recovered from the tuple, and the major. -/
noncomputable def blockRecMot (K : Nat) (concl : Nat → AnnotTerm) (uOf nIdxOf : Nat → Nat)
    (ρ : Nat → V) (xs : List V) (u : V) : V :=
  interp V
    (consList (xs ++ (isOfW (uOf (tagDec K u).1) (nIdxOf (tagDec K u).1) (tagDec K u).2.1
      ++ [(tagDec K u).2.2])) ρ) (concl (tagDec K u).1)

theorem blockRecMot_tagged {K c : Nat} (hc : c < K) {concl : Nat → AnnotTerm}
    {uOf nIdxOf : Nat → Nat} {ρ : Nat → V} {xs : List V} {i x : V} :
    blockRecMot K concl uOf nIdxOf ρ xs (tagged c i x)
      = interp V (consList (xs ++ (isOfW (uOf c) (nIdxOf c) i ++ [x])) ρ) (concl c) := by
  rw [blockRecMot, tagDec_tagged hc]

/-- **The kit's `hB`**: the motive is a set of the family's level —
O-2's reading fact (the conclusion reads to a set of level `ℓ` at
every fitting spine), restated at the decoded data. -/
theorem blockRecMot_mem_univ {K ℓ : Nat} {concl : Nat → AnnotTerm} {uOf nIdxOf : Nat → Nat}
    {ρ : Nat → V} {xs : List V} {Is Cr : Nat → V}
    (h : ∀ c, c < K → ∀ i, i ∈ˢ Is c → ∀ x, x ∈ˢ app (Cr c) i →
      interp V (consList (xs ++ (isOfW (uOf c) (nIdxOf c) i ++ [x])) ρ) (concl c)
        ∈ˢ (univ ℓ : V)) :
    ∀ u, u ∈ˢ unionSet K Is Cr → blockRecMot K concl uOf nIdxOf ρ xs u ∈ˢ (univ ℓ : V) := by
  intro u hu
  obtain ⟨c, hc, i, hi, x, hx, rfl⟩ := mem_unionSet.mp hu
  rw [blockRecMot_tagged hc]
  exact h c hc i hi x hx

/-- **`RecFamData.hconcl` at the block's motive**: the motive at the
tagged index IS the conclusion's reading at the fitting spine.  The
index spine comes back out of its tuple at the member's own index
telescope (`isOfW_tupW`, whose `IdxOk` is the representation's own
`idxOk` clause), and the spine is the frame by `hsplit`'s
decomposition. -/
theorem blockWf_hconcl {env : Env} {mo : EnvModel V env} {names : List Name} {d : BlockData V}
    (hM : BlockModelAt mo names d) {ψ : Name → Nat} {ρ : Nat → V} {K : Nat} {rP mem : Nat → Nat}
    {rds : Nat → List (Nat × Nat × AnnotTerm)} {concl : Nat → AnnotTerm}
    (hmem : ∀ c, c < K → mem c < d.N)
    (hlenIds : ∀ c, c < K → (d.IdsM (mem c) ψ).length = d.nIdxAt (mem c))
    (hsplit : BlockRecSplitAt V mo d ψ K rP mem rds ρ) :
    ∀ c, c < K → ∀ ys, SpineFit ρ ((rds c).map (·.2.2)) ys →
      blockRecMot K concl (fun c' => d.uM (mem c') ψ) (fun c' => d.nIdxAt (mem c')) ρ
          (prefOf (rP c) ys) (tagged c (d.tup ψ (mem c) (idxOf (rP c) ys)) (majOf ys))
        = interp V (consList ys ρ) (concl c) := by
  intro c hc ys hfit
  obtain ⟨-, hdec, hpar, hidx, -⟩ := hsplit c hc ys hfit
  have hIdx : IdxOk (d.uM (mem c) ψ) (consList ((prefOf (rP c) ys).take d.nP) ρ)
      (d.IdsM (mem c) ψ) := hM.idxOk ψ _ (d.satOfSpine hpar) (mem c) (hmem c hc)
  have hret : isOfW (d.uM (mem c) ψ) (d.nIdxAt (mem c))
      (d.tup ψ (mem c) (idxOf (rP c) ys)) = idxOf (rP c) ys := by
    rw [← hlenIds c hc]
    exact isOfW_tupW hIdx hidx
  rw [blockRecMot_tagged hc, hret, ← hdec]

/-! ## 10. The equation list's BIT-VALIDITY at the chain frame

RM8's `blockRecLeafAV_valid` leaves `heqV` — the equation list is
`AnnotValid` at every tuple typed at the recursor types — to this
lane, because it is the exact twin of `blockRecPre_of`'s `hwd`: the
same quantifier over the same tuple, in the bit currency instead of
the grading one.  At the shared choice `eqs = iotaEqsAV …` it is
`annotValid_iotaEqAV` (`BlockRecData.lean`) under
`forall_iotaEqsAV`. -/

/-- **`heqV` at the shared `eqs`** — one rule's `annotValid_iotaEqAV`,
lifted over the family's equation list. -/
theorem annotValid_iotaEqsAV_of {K : Nat} {nCt : Nat → Nat} {RecTy : Nat → AnnotTerm}
    {pdoms : Nat → List AnnotTerm} {fdoms es : Nat → Nat → List AnnotTerm}
    {mk : Nat → Nat → AnnotTerm} {ihs : Nat → Nat → List AnnotTerm}
    {Rb : Nat → Nat → AnnotTerm} {ρ : Nat → V}
    (hv : ∀ tup : List V, tup.length = K →
      (∀ mm, mm < K → tup.getD mm pt ∈ˢ interp V ρ (RecTy mm)) →
      ∀ c, c < K → ∀ j, j < nCt c →
        FieldsValid (consList tup ρ) (pdoms c ++ fdoms c j) ∧
        ∀ ys, SpineFit (consList tup ρ) (pdoms c ++ fdoms c j) ys →
          (∀ e ∈ es c j, AnnotValid V (consList ys (consList tup ρ)) e) ∧
          AnnotValid V (consList ys (consList tup ρ)) (mk c j) ∧
          (∀ v ∈ ihs c j, AnnotValid V (consList ys (consList tup ρ)) v) ∧
          AnnotValid V
            (consList ((ihs c j).map (interp V (consList ys (consList tup ρ))))
              (consList ys (consList tup ρ))) (Rb c j)) :
    ∀ tup : List V, tup.length = K →
      (∀ mm, mm < K → tup.getD mm pt ∈ˢ interp V ρ (RecTy mm)) →
      ∀ e ∈ iotaEqsAV K nCt pdoms fdoms es mk ihs Rb,
        AnnotValid V (consList tup ρ) e := by
  intro tup hlen hmem
  refine forall_iotaEqsAV fun c hc j hj => ?_
  obtain ⟨hd, hb⟩ := hv tup hlen hmem c hc j hj
  exact annotValid_iotaEqAV hd hb

/-- The same at the run, in `blockRecLeafAV_valid`'s spelling. -/
theorem heqV_run {envC : Env} {mpC : EnvModelM V μ envC}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {pdoms : (Name → Nat) → Nat → List AnnotTerm}
    {fdoms es : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {mk : (Name → Nat) → Nat → Nat → AnnotTerm}
    {ihs : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {Rb : (Name → Nat) → Nat → Nat → AnnotTerm}
    (hv : ∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V), tup.length = rs.length →
      (∀ mm, mm < rs.length →
        tup.getD mm pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ mm)) →
      ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
        FieldsValid (consList tup ρ) (pdoms ψ c ++ fdoms ψ c j) ∧
        ∀ ys, SpineFit (consList tup ρ) (pdoms ψ c ++ fdoms ψ c j) ys →
          (∀ e ∈ es ψ c j, AnnotValid V (consList ys (consList tup ρ)) e) ∧
          AnnotValid V (consList ys (consList tup ρ)) (mk ψ c j) ∧
          (∀ v ∈ ihs ψ c j, AnnotValid V (consList ys (consList tup ρ)) v) ∧
          AnnotValid V
            (consList ((ihs ψ c j).map (interp V (consList ys (consList tup ρ))))
              (consList ys (consList tup ρ))) (Rb ψ c j)) :
    ∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V), tup.length = rs.length →
      (∀ mm, mm < rs.length →
        tup.getD mm pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ mm)) →
      ∀ e ∈ iotaEqsAV rs.length (blockRecNCt rs) (pdoms ψ) (fdoms ψ) (es ψ) (mk ψ) (ihs ψ)
          (Rb ψ),
        AnnotValid V (consList tup ρ) e :=
  fun ψ ρ => annotValid_iotaEqsAV_of (hv ψ ρ)

/-! ## 11. The WF kit's STEP, and the kit

`UnionRecKitC.st` is TOTAL, so the step at a carrier element must name
the constructor and the fields that built it: §2's `blockDecomp` at
the tagged element's own component (`blockDecTag`), and the residue
read at that spine and at the ih values the graph supplies
(`blockRecStep`).  At a CONSTRUCTED element the decomposition reads
back what built it (`blockDecomp_eq`, i.e. `mkInj`), which is
`blockRecStep_at` — the equation the ι law's right-hand side needs.

The kit's `hst` is then `BlockRuleCerts.residueOk` at that spine, with
three seams, each in the shape its owner exports:

* **`hihF`** — the ih openers' values fit their domains, given that
  the graph is MOTIVE-VALUED at the predecessors.  That hypothesis on
  the graph is proved here off the raw recursion-graph lemmas
  (`app_mem_B_of_piSet`), because the kit is not built yet and
  `WfRecKit.graph_mem_B` is not available; what remains is the ih
  openers' own reading (RM8's rule data) together with
  `blockData_mkDepth`, which is what puts the arguments in `tcPred`;
* **`hspF`** — the fields fitting the constructor at the CARRIER
  (`ChainFit`) fit the rule's field domains (`SpineFit`); the two
  differ only at a recursive position, where the block's slot is the
  member's former applied (`BlockModelAt.leaf`);
* **`hCaB`** — the recursor's conclusion instantiated at the rule's
  spine reads to the MOTIVE at the constructed element. -/

section WfStep

variable {env : Env} {mo : EnvModel V env} {names : List Name} {d : BlockData V}

/-- The carrier's decomposition at a TAGGED element: the constructor
and the field spine that built its value, in its own component. -/
@[expose] noncomputable def blockDecTag (K : Nat) (d : BlockData V) (ψ : Name → Nat)
    (ρ : Nat → V) (mem : Nat → Nat) (xs : List V) (u : V) : Nat × List V :=
  blockDecomp d ψ (consList (xs.take d.nP) ρ)
    (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
      (d.Φ ψ (consList (xs.take d.nP) ρ)))
    (mem (tagDec K u).1) (tagDec K u).2.1 (tagDec K u).2.2

/-- **The WF kit's step**: the rule's RESIDUE, read at the spine the
tagged element decomposes to and at the ih values the graph `g`
supplies. -/
@[expose] noncomputable def blockRecStep (K : Nat) (d : BlockData V) (ψ : Name → Nat)
    (ρ : Nat → V) (mem : Nat → Nat) (Rb0 : Nat → Nat → AnnotTerm)
    (ihv : Nat → Nat → List V → V → List V) (xs : List V) (u g : V) : V :=
  interp V
    (consList (ihv (tagDec K u).1 (blockDecTag K d ψ ρ mem xs u).1
        (blockDecTag K d ψ ρ mem xs u).2 g)
      (consList (xs ++ (blockDecTag K d ψ ρ mem xs u).2) ρ))
    (Rb0 (tagDec K u).1 (blockDecTag K d ψ ρ mem xs u).1)

/-- **The step at a CONSTRUCTED element**: the decomposition reads back
the constructor and the fields, so the step is the rule's residue at
the rule's own spine — the ι law's right-hand side. -/
theorem blockRecStep_at (hM : BlockModelAt mo names d) {K : Nat} {ψ : Name → Nat} {ρ : Nat → V}
    {mem : Nat → Nat} {Rb0 : Nat → Nat → AnnotTerm}
    {ihv : Nat → Nat → List V → V → List V} {xs : List V} (hw : d.w ψ ≠ 0)
    {c : Nat} (hc : c < K) (hmemN : mem c < d.N) {i : V} {j : Nat} {fs : List V}
    (hj : j < (d.ctorsM (mem c)).length)
    (hfit : d.ChainFit ψ (consList (xs.take d.nP) ρ)
      (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
        (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs)
    (g : V) :
    blockRecStep K d ψ ρ mem Rb0 ihv xs (tagged c i (d.inj ψ (mem c) j fs)) g
      = interp V (consList (ihv c j fs g) (consList (xs ++ fs) ρ)) (Rb0 c j) := by
  rw [blockRecStep, blockDecTag, tagDec_tagged hc, blockDecomp_eq hM hw hmemN hj hfit]

/-- **The graph is motive-valued at the predecessors** — stated off the
raw recursion-graph lemmas, because the kit whose `graph_mem_B` would
say it is the one being built. -/
theorem app_mem_B_of_piSet {ℓ : Nat} {U : V} {B : V → V} {st : V → V → V} {u g : V}
    (hB : ∀ i, i ∈ˢ U → B i ∈ˢ (univ ℓ : V))
    (hg : g ∈ˢ piSet (tcPred U u) (fun v => app (recGraph ℓ U (tcPred U) B st) v))
    {v : V} (hv : v ∈ˢ tcPred U u) : app g v ∈ˢ B v := by
  have h1 := app_mem_of_mem_piSet hg hv
  rw [app_recGraph_eq hB (fun i _ => tcPred_subset U i) (tcPred_subset U u v hv)] at h1
  exact (mem_recGraphFibre.mp h1).1

section Kit

variable {ℓ K : Nat} {ψ : Name → Nat} {ρ : Nat → V} {mem nCt : Nat → Nat} {xs : List V}
  {concl : Nat → AnnotTerm} {pdoms : Nat → List AnnotTerm}
  {fdoms ihdoms : Nat → Nat → List AnnotTerm} {Rb0 Ca : Nat → Nat → AnnotTerm}
  {ihv : Nat → Nat → List V → V → List V} {envT : Env} {mp : EnvModelM V μ envT} {F : Nat}
  {rP : Nat → Nat}

/-- **The WF regime's kit at a prefix spine**: F5's `WfRecKit` over the
block's own index sets and carriers, with §9's motive and §11's step.
Its two obligations are O-2's reading (`hconclTy`) and the rule's
certificates at the decomposed spine, under the three seams the
module docstring names. -/
noncomputable def blockWfKit (hμ : μ.verifiedChecks = true)
    (hM : BlockModelAt mo names d) (hw : d.w ψ ≠ 0)
    (hmemN : ∀ c, c < K → mem c < d.N)
    (hsatP : Sat V (d.params ψ).reverse (consList (xs.take d.nP) ρ))
    (hnCt : ∀ c, c < K → (d.ctorsM (mem c)).length = nCt c)
    (hconclTy : ∀ c, c < K → ∀ i, i ∈ˢ blockRecIs d ψ ρ mem xs c →
      ∀ x, x ∈ˢ app (blockRecCr d ψ ρ mem xs c) i →
      interp V
          (consList (xs ++ (isOfW (d.uM (mem c) ψ) (d.nIdxAt (mem c)) i ++ [x])) ρ) (concl c)
        ∈ˢ (univ ℓ : V))
    (hcerts : ∀ c, c < K → ∀ j, j < nCt c →
      BlockRuleCerts V mp F ψ (rP c) (fdoms c j).length (ihdoms c j).length
        (pdoms c) (fdoms c j) (ihdoms c j) (Rb0 c j) (Ca c j))
    (hspF : ∀ c, c < K → ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs →
      SpineFit ρ (pdoms c ++ fdoms c j) (xs ++ fs))
    (hihF : ∀ c, c < K → ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs → ∀ g : V,
      (∀ v, v ∈ˢ tcPred (unionSet K (blockRecIs d ψ ρ mem xs) (blockRecCr d ψ ρ mem xs))
          (tagged c i (d.inj ψ (mem c) j fs)) →
        app g v ∈ˢ blockRecMot K concl (fun c' => d.uM (mem c') ψ)
          (fun c' => d.nIdxAt (mem c')) ρ xs v) →
      SpineFit (consList (xs ++ fs) ρ) (ihdoms c j) (ihv c j fs g))
    (hCaB : ∀ c, c < K → ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs → ∀ g : V,
      interp V (consList (ihv c j fs g) (consList (xs ++ fs) ρ)) (Ca c j)
        = blockRecMot K concl (fun c' => d.uM (mem c') ψ) (fun c' => d.nIdxAt (mem c')) ρ xs
            (tagged c i (d.inj ψ (mem c) j fs))) :
    WfRecKit ℓ K (blockRecIs d ψ ρ mem xs) (blockRecCr d ψ ρ mem xs) where
  B := blockRecMot K concl (fun c' => d.uM (mem c') ψ) (fun c' => d.nIdxAt (mem c')) ρ xs
  st := blockRecStep K d ψ ρ mem Rb0 ihv xs
  hB := blockRecMot_mem_univ hconclTy
  hst := by
    intro u hu g hg
    obtain ⟨c, hc, i, hi, x, hx, rfl⟩ := mem_unionSet.mp hu
    obtain ⟨j, fs, hj, hfit, rfl⟩ := blockCarrier_case hM hsatP (hmemN c hc) hi hx
    have hjn : j < nCt c := by rw [← hnCt c hc]; exact hj
    have hgB : ∀ v, v ∈ˢ tcPred (unionSet K (blockRecIs d ψ ρ mem xs)
        (blockRecCr d ψ ρ mem xs)) (tagged c i (d.inj ψ (mem c) j fs)) →
        app g v ∈ˢ blockRecMot K concl (fun c' => d.uM (mem c') ψ)
          (fun c' => d.nIdxAt (mem c')) ρ xs v :=
      fun v hv => app_mem_B_of_piSet (blockRecMot_mem_univ hconclTy) hg hv
    have hres := (hcerts c hc j hjn).residueOk hμ (hspF c hc j hjn i fs hfit)
      (hihF c hc j hjn i fs hfit g hgB)
    rw [blockRecStep_at hM hw hc (hmemN c hc) hj hfit, ← hCaB c hc j hjn i fs hfit g]
    exact hres.2

end Kit

end WfStep

end ConLeche.Model

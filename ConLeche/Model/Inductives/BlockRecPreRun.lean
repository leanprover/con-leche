module

import ConLeche.Model.Inductives.BlockRecTyping
import ConLeche.Model.Inductives.BlockRecRegimes
public import ConLeche.Semantics.Tower.BlockRecWfI
import ConLeche.Model.Inductives.BlockRecRead
public import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockAssemblyKit
import ConLeche.Model.Inductives.BlockModel
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

Session 2 adds the other two regimes and the dispatch: §7 the leaf's
dummy-to-real bridge and §8 `BlockModelAt` from the stages' three
records, §9 the WF kit's motive, §10 the equation list's
bit-validity, §11 the WF kit's step and the kit, §12 the kit at every
prefix spine (M5m's O-3), §13 the regime arm over an ABSTRACT step,
§14 regime SQ (the source spine, where `mkInj` fails), and §15 the
dispatch `blockRecPre_run`/`blockRecPre_hpre`.
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
component's own index-tuple set, at the parameter frame — and EMPTY
at a prefix that does not FIT, which is M5m's O-3: the kit is total
over prefix spines, and at a spine that fits nothing the class
carriers are empty and every obligation is vacuous.

**The guard is the WHOLE rule prefix, not only its parameters**
(session 7): the kit's step instantiates the rule's certificates at
`x⃗ ++ f⃗`, and `BlockRuleCerts.residueOk` asks `SpineFit ρ (pdoms c)
x⃗` — a statement about every entry of the prefix, the motives and the
minor premises included.  Guarding on the parameters alone leaves the
step with an obligation at prefixes whose motive entry is arbitrary,
and no hypothesis that decides it. -/
@[expose] noncomputable def blockRecIs (d : BlockData V) (ψ : Name → Nat) (ρ : Nat → V)
    (pdoms : Nat → List AnnotTerm) (mem : Nat → Nat) (xs : List V) (c : Nat) : V :=
  open Classical in
  if SpineFit ρ (d.params ψ) (xs.take d.nP) ∧ SpineFit ρ (pdoms c) xs then
    d.idx ψ (consList (xs.take d.nP) ρ) (mem c)
  else empty

theorem blockRecIs_pos {d : BlockData V} {ψ : Name → Nat} {ρ : Nat → V}
    {pdoms : Nat → List AnnotTerm} {mem : Nat → Nat} {xs : List V} {c : Nat}
    (h : SpineFit ρ (d.params ψ) (xs.take d.nP)) (hp : SpineFit ρ (pdoms c) xs) :
    blockRecIs d ψ ρ pdoms mem xs c = d.idx ψ (consList (xs.take d.nP) ρ) (mem c) := by
  classical
  rw [blockRecIs, if_pos ⟨h, hp⟩]

theorem blockRecIs_neg {d : BlockData V} {ψ : Name → Nat} {ρ : Nat → V}
    {pdoms : Nat → List AnnotTerm} {mem : Nat → Nat} {xs : List V} {c : Nat}
    (h : ¬ (SpineFit ρ (d.params ψ) (xs.take d.nP) ∧ SpineFit ρ (pdoms c) xs)) :
    blockRecIs d ψ ρ pdoms mem xs c = (empty : V) := by
  classical
  rw [blockRecIs, if_neg h]

/-- **The guard, read back off a membership**: an inhabited class
index set is the honest one, so the two fits come back out of any
element of it.  This is what makes the kit TOTAL in the prefix spine
without a branch: every obligation that mentions a class element has
the fits in scope. -/
theorem blockRecIs_fits {d : BlockData V} {ψ : Name → Nat} {ρ : Nat → V}
    {pdoms : Nat → List AnnotTerm} {mem : Nat → Nat} {xs : List V} {c : Nat} {i : V}
    (h : i ∈ˢ blockRecIs d ψ ρ pdoms mem xs c) :
    SpineFit ρ (d.params ψ) (xs.take d.nP) ∧ SpineFit ρ (pdoms c) xs := by
  classical
  by_cases hg : SpineFit ρ (d.params ψ) (xs.take d.nP) ∧ SpineFit ρ (pdoms c) xs
  · exact hg
  · rw [blockRecIs_neg hg] at h
    exact absurd h (not_mem_empty _)

/-- Class `c`'s ORDINARY carrier at a prefix spine: the eliminated
component of the block's least pre-fixed tuple. -/
@[expose] noncomputable def blockRecCr (d : BlockData V) (ψ : Name → Nat) (ρ : Nat → V)
    (mem : Nat → Nat) (xs : List V) (c : Nat) : V :=
  lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
    (d.Φ ψ (consList (xs.take d.nP) ρ)) (mem c)

/-- A fitting spine's prefix fits the domains' prefix — `spineFit_take`
without its length side condition (past the end both takes are the
whole lists). -/
theorem spineFit_take_any {Fs : List AnnotTerm} {ρ : Nat → V} {as : List V}
    (h : SpineFit ρ Fs as) (i : Nat) : SpineFit ρ (Fs.take i) (as.take i) := by
  by_cases hi : i ≤ Fs.length
  · exact spineFit_take h hi
  · rw [List.take_of_length_le (Nat.le_of_not_le hi),
      List.take_of_length_le (by rw [h.length_eq]; exact Nat.le_of_not_le hi)]
    exact h

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
    {pdoms : Nat → List AnnotTerm}
    (hpdE : ∀ c, c < K → pdoms c = ((rds c).map (·.2.2)).take (rP c))
    (hmem : ∀ c, c < K → mem c < d.k)
    (hsplit : BlockRecSplitAt V mo d ψ K rP mem rds ρ) :
    ∀ c, c < K → ∀ ys, SpineFit ρ ((rds c).map (·.2.2)) ys →
      (prefOf (rP c) ys).length = rP c ∧
      ys = prefOf (rP c) ys ++ (idxOf (rP c) ys ++ [majOf ys]) ∧
      d.tup ψ (mem c) (idxOf (rP c) ys) ∈ˢ blockRecIs d ψ ρ pdoms mem (prefOf (rP c) ys) c ∧
      majOf ys ∈ˢ app (blockRecCr d ψ ρ mem (prefOf (rP c) ys) c)
        (d.tup ψ (mem c) (idxOf (rP c) ys)) := by
  intro c hc ys hfit
  obtain ⟨hlen, hdec, hpar, hidx, hmaj⟩ := hsplit c hc ys hfit
  have hpref : SpineFit ρ (pdoms c) (prefOf (rP c) ys) := by
    rw [hpdE c hc]
    exact spineFit_take_any hfit _
  rw [blockRecIs_pos hpar hpref]
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
    {ρ : Nat → V} {pdoms : Nat → List AnnotTerm} (d : BlockData V)
    (kitW : ∀ xs : List V,
      WfRecKit ℓ K (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs))
    (hsplit : ∀ c, c < K → ∀ ys, SpineFit ρ ((rds c).map (·.2.2)) ys →
      (prefOf (rP c) ys).length = rP c ∧
      ys = prefOf (rP c) ys ++ (idxOf (rP c) ys ++ [majOf ys]) ∧
      d.tup ψ (mem c) (idxOf (rP c) ys) ∈ˢ blockRecIs d ψ ρ pdoms mem (prefOf (rP c) ys) c ∧
      majOf ys ∈ˢ app (blockRecCr d ψ ρ mem (prefOf (rP c) ys) c)
        (d.tup ψ (mem c) (idxOf (rP c) ys)))
    (hconcl : ∀ c, c < K → ∀ ys, SpineFit ρ ((rds c).map (·.2.2)) ys →
      (kitW (prefOf (rP c) ys)).B
          (tagged c (d.tup ψ (mem c) (idxOf (rP c) ys)) (majOf ys))
        = interp V (consList ys ρ) (concl c)) :
    RecFamData V ℓ K rP rds concl ρ :=
  wfData (rds := rds) (concl := concl) (rP := rP) (ρ := ρ)
    (blockRecIs d ψ ρ pdoms mem) (blockRecCr d ψ ρ mem) (fun c is => d.tup ψ (mem c) is)
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
    (hnCt : ∀ c, c < K → (d.ctorsM (mem c)).length = nCt c)
    (hconclTy : ∀ c, c < K → ∀ i, i ∈ˢ blockRecIs d ψ ρ pdoms mem xs c →
      ∀ x, x ∈ˢ app (blockRecCr d ψ ρ mem xs c) i →
      interp V
          (consList (xs ++ (isOfW (d.uM (mem c) ψ) (d.nIdxAt (mem c)) i ++ [x])) ρ) (concl c)
        ∈ˢ (univ ℓ : V))
    (hcerts : ∀ c, c < K → ∀ j, j < nCt c →
      BlockRuleCerts V mp F ψ (rP c) (fdoms c j).length (ihdoms c j).length
        (pdoms c) (fdoms c j) (ihdoms c j) (Rb0 c j) (Ca c j))
    (hspF : ∀ c, c < K → SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs →
      SpineFit ρ (pdoms c ++ fdoms c j) (xs ++ fs))
    (hihF : ∀ c, c < K → SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs → ∀ g : V,
      (∀ v, v ∈ˢ tcPred (unionSet K (blockRecIs d ψ ρ pdoms mem xs)
            (blockRecCr d ψ ρ mem xs))
          (tagged c i (d.inj ψ (mem c) j fs)) →
        app g v ∈ˢ blockRecMot K concl (fun c' => d.uM (mem c') ψ)
          (fun c' => d.nIdxAt (mem c')) ρ xs v) →
      SpineFit (consList (xs ++ fs) ρ) (ihdoms c j) (ihv c j fs g))
    (hCaB : ∀ c, c < K → SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs → ∀ g : V,
      interp V (consList (ihv c j fs g) (consList (xs ++ fs) ρ)) (Ca c j)
        = blockRecMot K concl (fun c' => d.uM (mem c') ψ) (fun c' => d.nIdxAt (mem c')) ρ xs
            (tagged c i (d.inj ψ (mem c) j fs))) :
    WfRecKit ℓ K (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs) where
  B := blockRecMot K concl (fun c' => d.uM (mem c') ψ) (fun c' => d.nIdxAt (mem c')) ρ xs
  st := blockRecStep K d ψ ρ mem Rb0 ihv xs
  hB := blockRecMot_mem_univ hconclTy
  hst := by
    intro u hu g hg
    obtain ⟨c, hc, i, hi, x, hx, rfl⟩ := mem_unionSet.mp hu
    obtain ⟨hparFit, hprefFit⟩ := blockRecIs_fits hi
    rw [blockRecIs_pos hparFit hprefFit] at hi
    obtain ⟨j, fs, hj, hfit, rfl⟩ :=
      blockCarrier_case hM (d.satOfSpine hparFit) (hmemN c hc) hi hx
    have hjn : j < nCt c := by rw [← hnCt c hc]; exact hj
    have hgB : ∀ v, v ∈ˢ tcPred (unionSet K (blockRecIs d ψ ρ pdoms mem xs)
        (blockRecCr d ψ ρ mem xs)) (tagged c i (d.inj ψ (mem c) j fs)) →
        app g v ∈ˢ blockRecMot K concl (fun c' => d.uM (mem c') ψ)
          (fun c' => d.nIdxAt (mem c')) ρ xs v :=
      fun v hv => app_mem_B_of_piSet (blockRecMot_mem_univ hconclTy) hg hv
    have hres := (hcerts c hc j hjn).residueOk hμ
      (hspF c hc hparFit hprefFit j hjn i fs hfit)
      (hihF c hc hparFit hprefFit j hjn i fs hfit g hgB)
    rw [blockRecStep_at hM hw hc (hmemN c hc) hj hfit,
      ← hCaB c hc hparFit hprefFit j hjn i fs hfit g]
    exact hres.2

end Kit

end WfStep

/-! ## 12. The kit FAMILY at every prefix spine

`RecFamData.kit` is total over prefix spines (M5m's O-3).  With the
index sets guarded (§3, `blockRecIs`) a spine that does not FIT carries
EMPTY classes, so the kit there has nothing to prove — and since
session 7 the guard is read back off a class MEMBERSHIP
(`blockRecIs_fits`), so §11's kit is already total and
`blockWfKitFam` is it, with no branch: `RecFamData.hconcl` is stated
at one spelling because there is only one.

`blockRecPre_wf_run` is then `blockRecPre_kit` at that family: the ι
law's right-hand side is `blockRecStep_at`, moved to the CHAIN frame
by the residue's lifting (`interp_liftN_chainFrame`, RM8's) and by the
ih values being the ih terms' readings there (`hihChain` — the seam
`ihFunAV_fold` closes once the rule data are functions of the run). -/

section WfFam

variable {env : Env} {mo : EnvModel V env} {names : List Name} {d : BlockData V}
  {ℓ K : Nat} {ψ : Name → Nat} {ρ : Nat → V} {mem nCt rP : Nat → Nat}
  {concl : Nat → AnnotTerm} {pdoms : Nat → List AnnotTerm}
  {fdoms ihdoms : Nat → Nat → List AnnotTerm} {Rb0 Ca : Nat → Nat → AnnotTerm}
  {ihv : Nat → Nat → List V → V → List V} {envT : Env} {mp : EnvModelM V μ envT} {F : Nat}

/-- **The kit at EVERY prefix spine**: §11's, whose obligations are
already vacuous at a non-fitting prefix — the guard sits in
`blockRecIs`, and `blockRecIs_fits` hands the two fits back to every
obligation that mentions a class element. -/
noncomputable def blockWfKitFam (hμ : μ.verifiedChecks = true)
    (hM : BlockModelAt mo names d) (hw : d.w ψ ≠ 0)
    (hmemN : ∀ c, c < K → mem c < d.N)
    (hnCt : ∀ c, c < K → (d.ctorsM (mem c)).length = nCt c)
    (hconclTy : ∀ xs : List V,
      ∀ c, c < K → ∀ i, i ∈ˢ blockRecIs d ψ ρ pdoms mem xs c →
      ∀ x, x ∈ˢ app (blockRecCr d ψ ρ mem xs c) i →
      interp V
          (consList (xs ++ (isOfW (d.uM (mem c) ψ) (d.nIdxAt (mem c)) i ++ [x])) ρ) (concl c)
        ∈ˢ (univ ℓ : V))
    (hcerts : ∀ c, c < K → ∀ j, j < nCt c →
      BlockRuleCerts V mp F ψ (rP c) (fdoms c j).length (ihdoms c j).length
        (pdoms c) (fdoms c j) (ihdoms c j) (Rb0 c j) (Ca c j))
    (hspF : ∀ xs : List V, ∀ c, c < K →
      SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs →
      SpineFit ρ (pdoms c ++ fdoms c j) (xs ++ fs))
    (hihF : ∀ xs : List V, ∀ c, c < K →
      SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs → ∀ g : V,
      (∀ v, v ∈ˢ tcPred (unionSet K (blockRecIs d ψ ρ pdoms mem xs)
            (blockRecCr d ψ ρ mem xs))
          (tagged c i (d.inj ψ (mem c) j fs)) →
        app g v ∈ˢ blockRecMot K concl (fun c' => d.uM (mem c') ψ)
          (fun c' => d.nIdxAt (mem c')) ρ xs v) →
      SpineFit (consList (xs ++ fs) ρ) (ihdoms c j) (ihv c j fs g))
    (hCaB : ∀ xs : List V, ∀ c, c < K →
      SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs → ∀ g : V,
      interp V (consList (ihv c j fs g) (consList (xs ++ fs) ρ)) (Ca c j)
        = blockRecMot K concl (fun c' => d.uM (mem c') ψ) (fun c' => d.nIdxAt (mem c')) ρ xs
            (tagged c i (d.inj ψ (mem c) j fs)))
    (xs : List V) :
    WfRecKit ℓ K (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs) :=
  blockWfKit (nCt := nCt) (rP := rP) (ihdoms := ihdoms) (Ca := Ca) (ihv := ihv) hμ hM hw
    hmemN hnCt (hconclTy xs) hcerts (hspF xs) (hihF xs) (hCaB xs)

/-- The family carries §9's motive. -/
theorem blockWfKitFam_B (hμ : μ.verifiedChecks = true) (hM : BlockModelAt mo names d)
    (hw : d.w ψ ≠ 0) (hmemN) (hnCt) (hconclTy) (hcerts) (hspF) (hihF) (hCaB) (xs : List V) :
    (blockWfKitFam (V := V) (ℓ := ℓ) (K := K) (ρ := ρ) (mem := mem) (nCt := nCt) (rP := rP)
        (concl := concl) (pdoms := pdoms) (fdoms := fdoms) (ihdoms := ihdoms) (Rb0 := Rb0)
        (Ca := Ca) (ihv := ihv) (mp := mp) (F := F)
        hμ hM hw hmemN hnCt hconclTy hcerts hspF hihF hCaB xs).B
      = blockRecMot K concl (fun c' => d.uM (mem c') ψ) (fun c' => d.nIdxAt (mem c')) ρ xs := by
  rfl

/-- The family carries §11's step. -/
theorem blockWfKitFam_st (hμ : μ.verifiedChecks = true) (hM : BlockModelAt mo names d)
    (hw : d.w ψ ≠ 0) (hmemN) (hnCt) (hconclTy) (hcerts) (hspF) (hihF) (hCaB) (xs : List V) :
    (blockWfKitFam (V := V) (ℓ := ℓ) (K := K) (ρ := ρ) (mem := mem) (nCt := nCt) (rP := rP)
        (concl := concl) (pdoms := pdoms) (fdoms := fdoms) (ihdoms := ihdoms) (Rb0 := Rb0)
        (Ca := Ca) (ihv := ihv) (mp := mp) (F := F)
        hμ hM hw hmemN hnCt hconclTy hcerts hspF hihF hCaB xs).st
      = blockRecStep K d ψ ρ mem Rb0 ihv xs := by
  rfl

end WfFam

/-! ## 13. The regime arm, over an ABSTRACT step

`blockRecPre_kit`'s `hst` is the kit's step at the rule's own tagged
element, and §11's `blockRecStep_at` computes it — once the rule's
spine is known to be a CONSTRUCTOR application at the carrier
(`hctorAt`).  Two frame moves finish it: the residue is the BASE-frame
one lifted past the `K` chain binders (`interp_Rb_chain`, RM8's
spelling), and the ih values built from the graph are the ih TERMS'
readings at the chain frame (`hihChain` — `ihFunAV_fold` closes it
once the rule data are functions of the run).

The `RecFamData` is not a parameter of the construction but of the
theorem, with its step pinned by `hDst`: that keeps the premises free
of the kit's own definition, and `blockWfData_st` supplies `hDst` for
the family §12 builds. -/

section WfRun

variable {env : Env} {mo : EnvModel V env} {names : List Name} {d : BlockData V}
  {ℓ s K : Nat} {ψ : Name → Nat} {ρ : Nat → V} {mem nCt rP : Nat → Nat}
  {rds : Nat → List (Nat × Nat × AnnotTerm)} {concl RecTy : Nat → AnnotTerm}
  {pdoms : Nat → List AnnotTerm} {fdoms es : Nat → Nat → List AnnotTerm}
  {mk : Nat → Nat → AnnotTerm} {ihs : Nat → Nat → List AnnotTerm}
  {Rb0 : Nat → Nat → AnnotTerm} {ihv : Nat → Nat → List V → V → List V}

/-- **The residue crosses the chain frame**: the base-frame residue
lifted past the `K` Σ' binders at its own depth reads the same under
the rule's binders and the ih block (RM8's `interp_liftN_chainFrame`
at the rule's frame). -/
theorem interp_Rb_chain {K : Nat} {a ρ : Nat → V} {ws ihvals : List V} {Rb0 : AnnotTerm} :
    interp V (consList ihvals (consList ws (chainFrame K a ρ)))
        (Rb0.liftN K (ws.length + ihvals.length))
      = interp V (consList ihvals (consList ws ρ)) Rb0 := by
  have h := interp_liftN_chainFrame (V := V) (K := K) (a := a) (ρ := ρ) (ws ++ ihvals) Rb0
  rw [List.length_append] at h
  rw [← consList_append, ← consList_append]
  exact h

/-- The family data's step is the kit's. -/
theorem blockWfData_st {rds : Nat → List (Nat × Nat × AnnotTerm)} {concl : Nat → AnnotTerm}
    (kitW : ∀ xs : List V,
      WfRecKit ℓ K (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs))
    (hsplit) (hconcl) (xs : List V) :
    ((blockWfData (rds := rds) (concl := concl) (rP := rP) (ρ := ρ) d kitW hsplit hconcl).kit
      xs).st = (kitW xs).st := rfl

/-- **THE REGIME ARM AT THE RUN**, over an abstract step: whatever the
kit's step is, `BlockRecPre` follows once the step at a RULE's own
tagged element is the rule's residue at the rule's spine (`hstAt`) —
which is all that WF (by `mkInj`) and SQ (by the source spine) prove
differently.  The two frame moves are this theorem's: the residue is
the base-frame one lifted past the `K` chain binders, and the ih
values built from the graph are the ih terms' readings there
(`hihChain`). -/
theorem blockRecPre_step_of (D : RecFamData V ℓ K rP rds concl ρ) {stp : List V → V → V → V}
    (hDst : ∀ xs : List V, (D.kit xs).st = stp xs)
    (hTy : ∀ c, c < K → interp V ρ (RecTy c) ∈ˢ (univ s : V) ∧ WellDenoted V ρ (RecTy c))
    (hwd : ∀ as : List V, as.length = K →
      (∀ c, c < K → as.getD c pt ∈ˢ interp V ρ (RecTy c)) →
      ∀ c, c < K → ∀ j, j < nCt c →
        FieldsOkB 0 (consList as ρ) (pdoms c ++ fdoms c j) ∧
        ∀ ys, SpineFit (consList as ρ) (pdoms c ++ fdoms c j) ys →
          WellDenoted V (consList ys (consList as ρ))
              (AnnotTerm.mkAppN (.bvar ((pdoms c).length + (fdoms c j).length + (K - 1 - c)))
                (prefVarsAV (pdoms c).length (fdoms c j).length ++ es c j ++ [mk c j])) ∧
            WellDenoted V (consList ys (consList as ρ))
              (instsAV 0 (ihs c j)
                ((Rb0 c j).liftN K ((pdoms c).length + (fdoms c j).length + (ihs c j).length))))
    (hℓ : ℓ ≠ 0) (hTyE : ∀ c, c < K → RecTy c = mkPisAV (rds c) (concl c))
    (hbits : OneElimLevel ℓ K rds) (hpl : ∀ c, c < K → (pdoms c).length = rP c)
    (hrule : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (famCand D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      SpineFit ρ ((rds c).map (·.2.2))
        (xs ++ ((es c j).map (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)))
          ++ [interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)) (mk c j)])))
    (hstAt : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (famCand D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) → ∀ g : V,
      stp xs
          (tagged c
            (D.tupOf c
              ((es c j).map (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)))))
            (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)) (mk c j))) g
        = interp V (consList (ihv c j fs g) (consList (xs ++ fs) ρ)) (Rb0 c j))
    (hihChain : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (famCand D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      ihv c j fs
          (kitGraphAt (D.kit xs)
            (tagged c
              (D.tupOf c
                ((es c j).map (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)))))
              (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)) (mk c j))))
        = (ihs c j).map (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)))) :
    BlockRecPre V s K RecTy
      (iotaEqsAV K nCt pdoms fdoms es mk ihs
        (fun c j => (Rb0 c j).liftN K
          ((pdoms c).length + (fdoms c j).length + (ihs c j).length))) ρ := by
  refine blockRecPre_kit hTy hwd D hℓ hTyE hbits hpl hrule ?_
  intro c hc j hj xs fs hxl hsp
  have hlen : (xs ++ fs).length = (pdoms c).length + (fdoms c j).length := by
    rw [hsp.length_eq, List.length_append]
  rw [hDst xs, hstAt c hc j hj xs fs hxl hsp, hihChain c hc j hj xs fs hxl hsp,
    show (pdoms c).length + (fdoms c j).length + (ihs c j).length
      = (xs ++ fs).length + ((ihs c j).map
          (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)))).length from by
      rw [hlen, List.length_map],
    interp_Rb_chain]

/-- **Regime WF's `hstAt`**: the rule's spine is a CONSTRUCTOR
application at the carrier (`hctorAt`), so §11's step reads back the
rule's residue (`blockRecStep_at`, i.e. `mkInj`). -/
theorem blockRecStep_at_rule (hM : BlockModelAt mo names d) (hw : d.w ψ ≠ 0)
    (hmemN : ∀ c, c < K → mem c < d.N)
    (hnCt : ∀ c, c < K → (d.ctorsM (mem c)).length = nCt c)
    (D : RecFamData V ℓ K rP rds concl ρ)
    (hDtup : ∀ (c : Nat) (is : List V), D.tupOf c is = d.tup ψ (mem c) is)
    (hctorAt : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (famCand D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
          (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
            (d.Φ ψ (consList (xs.take d.nP) ρ)))
          (d.tup ψ (mem c)
            ((es c j).map (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)))))
          (mem c) j fs ∧
        interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)) (mk c j)
          = d.inj ψ (mem c) j fs) :
    ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (famCand D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) → ∀ g : V,
      blockRecStep K d ψ ρ mem Rb0 ihv xs
          (tagged c
            (D.tupOf c
              ((es c j).map (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)))))
            (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)) (mk c j))) g
        = interp V (consList (ihv c j fs g) (consList (xs ++ fs) ρ)) (Rb0 c j) := by
  intro c hc j hj xs fs hxl hsp g
  obtain ⟨hfit, hmkv⟩ := hctorAt c hc j hj xs fs hxl hsp
  have hjc : j < (d.ctorsM (mem c)).length := by rw [hnCt c hc]; exact hj
  have h2 := blockRecStep_at (Rb0 := Rb0) (ihv := ihv) hM hw hc (hmemN c hc) hjc hfit g
  rw [hDtup, hmkv]
  exact h2

end WfRun

/-! ## 14. Regime SQ at the run

At `w = 0` every injection is the point (`BlockModelAt.mkZero`), so the
major carries no information and the decomposition of §2 is NOT
available — `mkInj` is exactly what fails there.  What replaces it is
the subsingleton criterion: the constructor's fields are a FUNCTION of
the index values (`srcVals` at the index spine, `FixSquashI`'s
vocabulary, which `BlockRecSqI` re-targets), so the step reads the
residue at that SOURCE spine.  Only the step changes: §13's arm is
untouched. -/

section SqRun

variable {d : BlockData V} {ℓ s K : Nat} {ψ : Name → Nat} {ρ : Nat → V}
  {mem nCt rP : Nat → Nat} {rds : Nat → List (Nat × Nat × AnnotTerm)}
  {concl RecTy : Nat → AnnotTerm} {pdoms : Nat → List AnnotTerm}
  {fdoms es : Nat → Nat → List AnnotTerm} {mk : Nat → Nat → AnnotTerm}
  {ihs : Nat → Nat → List AnnotTerm} {Rb0 : Nat → Nat → AnnotTerm}
  {ihv : Nat → Nat → List V → V → List V} {src : Nat → List (Option Nat)}

/-- **Regime SQ's step**: the rule's residue read at the SOURCE spine
— the fields recovered from the tagged element's INDEX, the major
being the point. -/
@[expose] noncomputable def blockSqStep (K : Nat) (d : BlockData V) (ψ : Name → Nat)
    (ρ : Nat → V) (mem : Nat → Nat) (src : Nat → List (Option Nat))
    (Rb0 : Nat → Nat → AnnotTerm) (ihv : Nat → Nat → List V → V → List V) (xs : List V)
    (u g : V) : V :=
  interp V
    (consList
      (ihv (tagDec K u).1 0
        (srcVals (isOfW (d.uM (mem (tagDec K u).1) ψ) (d.nIdxAt (mem (tagDec K u).1))
          (tagDec K u).2.1) (src (tagDec K u).1)) g)
      (consList
        (xs ++ srcVals (isOfW (d.uM (mem (tagDec K u).1) ψ) (d.nIdxAt (mem (tagDec K u).1))
          (tagDec K u).2.1) (src (tagDec K u).1)) ρ))
    (Rb0 (tagDec K u).1 0)

/-- The step at a tagged element whose source spine is known. -/
theorem blockSqStep_at {c : Nat} (hc : c < K) {i x : V} {fs : List V}
    (hsrc : srcVals (isOfW (d.uM (mem c) ψ) (d.nIdxAt (mem c)) i) (src c) = fs) (g : V) :
    blockSqStep K d ψ ρ mem src Rb0 ihv xs (tagged c i x) g
      = interp V (consList (ihv c 0 fs g) (consList (xs ++ fs) ρ)) (Rb0 c 0) := by
  simp only [blockSqStep, tagDec_tagged hc, hsrc]

/-- **Regime SQ's `hstAt`**: at the lone constructor the rule's own
fields ARE the source spine at the rule's index tuple, so the step
reads back the rule's residue. -/
theorem blockSqStep_at_rule (D : RecFamData V ℓ K rP rds concl ρ)
    (hsrcAt : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (famCand D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      j = 0 ∧
        srcVals
            (isOfW (d.uM (mem c) ψ) (d.nIdxAt (mem c))
              (D.tupOf c
                ((es c j).map (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ))))))
            (src c)
          = fs) :
    ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (famCand D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) → ∀ g : V,
      blockSqStep K d ψ ρ mem src Rb0 ihv xs
          (tagged c
            (D.tupOf c
              ((es c j).map (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)))))
            (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)) (mk c j))) g
        = interp V (consList (ihv c j fs g) (consList (xs ++ fs) ρ)) (Rb0 c j) := by
  intro c hc j hj xs fs hxl hsp g
  obtain ⟨rfl, hsrc⟩ := hsrcAt c hc j hj xs fs hxl hsp
  exact blockSqStep_at hc hsrc g

end SqRun

/-! ## 15. The DISPATCH — `hpre` in every regime

The three regimes are disjoint and exhaustive on `(w, ℓ)`: `ℓ = 0` is
IND, and at `ℓ ≠ 0` the kit arm runs with the WF step (`w ≠ 0`,
`blockRecStep_at_rule`) or the SQ one (`w = 0`,
`blockSqStep_at_rule`).  The `w` split is therefore not in the
dispatch but in whoever supplies `KitRegimeAt`: §13's arm does not
know which kit it is handed, which is the point of stating it over an
abstract step.

Both bundles quantify the run data existentially, so the dispatch's
statement mentions only what the ι equations are built from. -/

section Dispatch

variable {ℓ s K : Nat} {rP nCt : Nat → Nat} {rds : Nat → List (Nat × Nat × AnnotTerm)}
  {concl RecTy : Nat → AnnotTerm} {pdoms : Nat → List AnnotTerm}
  {fdoms es : Nat → Nat → List AnnotTerm} {mk : Nat → Nat → AnnotTerm}
  {ihs : Nat → Nat → List AnnotTerm} {Rb0 : Nat → Nat → AnnotTerm} {ρ : Nat → V}

/-- **The kit regimes' input at one frame** (WF at `w ≠ 0`, SQ at
`w = 0`): a family datum whose step reads the rule's residue at the
rule's spine, and the ih values from its graph. -/
def KitRegimeAt (V : Type w) [SetTheory V] (ℓ K : Nat) (rP nCt : Nat → Nat)
    (rds : Nat → List (Nat × Nat × AnnotTerm)) (concl RecTy : Nat → AnnotTerm)
    (pdoms : Nat → List AnnotTerm) (fdoms es : Nat → Nat → List AnnotTerm)
    (mk : Nat → Nat → AnnotTerm) (ihs : Nat → Nat → List AnnotTerm)
    (Rb0 : Nat → Nat → AnnotTerm) (ρ : Nat → V) : Prop :=
  ∃ (D : RecFamData V ℓ K rP rds concl ρ) (stp : List V → V → V → V)
    (ihv : Nat → Nat → List V → V → List V),
    (∀ xs : List V, (D.kit xs).st = stp xs) ∧
    (∀ c, c < K → RecTy c = mkPisAV (rds c) (concl c)) ∧
    OneElimLevel ℓ K rds ∧
    (∀ c, c < K → (pdoms c).length = rP c) ∧
    (∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (famCand D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      SpineFit ρ ((rds c).map (·.2.2))
        (xs ++ ((es c j).map (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)))
          ++ [interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)) (mk c j)]))) ∧
    (∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (famCand D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) → ∀ g : V,
      stp xs
          (tagged c
            (D.tupOf c
              ((es c j).map (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)))))
            (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)) (mk c j))) g
        = interp V (consList (ihv c j fs g) (consList (xs ++ fs) ρ)) (Rb0 c j)) ∧
    (∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (famCand D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      ihv c j fs
          (kitGraphAt (D.kit xs)
            (tagged c
              (D.tupOf c
                ((es c j).map (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)))))
              (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)) (mk c j))))
        = (ihs c j).map (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ))))

/-- **Regime IND's input at one frame**: the induction principle and
the rules' certificates, with the run data existential. -/
def IndRegimeAt (V : Type w) [SetTheory V] (μ : CheckMode) (K : Nat) (nCt rP : Nat → Nat)
    (ψ : Name → Nat) (RecTy : Nat → AnnotTerm) (pdoms : Nat → List AnnotTerm)
    (fdoms : Nat → Nat → List AnnotTerm) (ihs : Nat → Nat → List AnnotTerm)
    (Rb : Nat → Nat → AnnotTerm) (ρ : Nat → V) : Prop :=
  ∃ (envT : Env) (mp : EnvModelM V μ envT) (F : Nat)
    (ihdoms : Nat → Nat → List AnnotTerm) (Ca : Nat → Nat → AnnotTerm),
    μ.verifiedChecks = true ∧
    (∀ c, c < K → (pt : V) ∈ˢ interp V ρ (RecTy c)) ∧
    (∀ c, c < K → ∀ j, j < nCt c →
      BlockRuleCerts V mp F ψ (rP c) (fdoms c j).length (ihdoms c j).length
        (pdoms c) (fdoms c j) (ihdoms c j) (Rb c j) (Ca c j)) ∧
    (∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (fun _ => (pt : V)) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      SpineFit (consList (xs ++ fs) (chainFrame K (fun _ => (pt : V)) ρ)) (ihdoms c j)
        ((ihs c j).map
          (interp V (consList (xs ++ fs) (chainFrame K (fun _ => (pt : V)) ρ))))) ∧
    (∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (fun _ => (pt : V)) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      interp V
          (consList
            ((ihs c j).map
              (interp V (consList (xs ++ fs) (chainFrame K (fun _ => (pt : V)) ρ))))
            (consList (xs ++ fs) (chainFrame K (fun _ => (pt : V)) ρ))) (Ca c j)
        ∈ˢ (univZero : V))

/-- **`BlockRecPre` at one frame, in EVERY regime.** -/
theorem blockRecPre_run {ψ : Name → Nat}
    (hTy : ∀ c, c < K → interp V ρ (RecTy c) ∈ˢ (univ s : V) ∧ WellDenoted V ρ (RecTy c))
    (hwd : ∀ as : List V, as.length = K →
      (∀ c, c < K → as.getD c pt ∈ˢ interp V ρ (RecTy c)) →
      ∀ c, c < K → ∀ j, j < nCt c →
        FieldsOkB 0 (consList as ρ) (pdoms c ++ fdoms c j) ∧
        ∀ ys, SpineFit (consList as ρ) (pdoms c ++ fdoms c j) ys →
          WellDenoted V (consList ys (consList as ρ))
              (AnnotTerm.mkAppN (.bvar ((pdoms c).length + (fdoms c j).length + (K - 1 - c)))
                (prefVarsAV (pdoms c).length (fdoms c j).length ++ es c j ++ [mk c j])) ∧
            WellDenoted V (consList ys (consList as ρ))
              (instsAV 0 (ihs c j)
                ((Rb0 c j).liftN K ((pdoms c).length + (fdoms c j).length + (ihs c j).length))))
    (hIND : ℓ = 0 → IndRegimeAt V μ K nCt rP ψ RecTy pdoms fdoms ihs
      (fun c j => (Rb0 c j).liftN K
        ((pdoms c).length + (fdoms c j).length + (ihs c j).length)) ρ)
    (hKIT : ℓ ≠ 0 →
      KitRegimeAt V ℓ K rP nCt rds concl RecTy pdoms fdoms es mk ihs Rb0 ρ) :
    BlockRecPre V s K RecTy
      (iotaEqsAV K nCt pdoms fdoms es mk ihs
        (fun c j => (Rb0 c j).liftN K
          ((pdoms c).length + (fdoms c j).length + (ihs c j).length))) ρ := by
  by_cases hℓ : ℓ = 0
  · obtain ⟨envT, mp, F, ihdoms, Ca, hμ, hind, hcerts, hih, hT⟩ := hIND hℓ
    exact blockRecPre_ind_run hμ hTy hwd hind hcerts hih hT
  · obtain ⟨D, stp, ihv, hDst, hTyE, hbits, hpl, hrule, hstAt, hihChain⟩ := hKIT hℓ
    exact blockRecPre_step_of D hDst hTy hwd hℓ hTyE hbits hpl hrule hstAt hihChain

/-- **`hpre` in every regime**, in `blockRecStaged_run`'s spelling and
at the lanes' shared choice of `K`, `nCt` and `eqs`.  The family's
elimination level may depend on the level assignment (the guard is
`ℓ ψ`), the chain's level `s` is one numeral for the block — which is
what the assembly takes. -/
theorem blockRecPre_hpre {envC : Env} {mpC : EnvModelM V μ envC} {s : Nat}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {ℓ : (Name → Nat) → Nat} {rP : Nat → Nat}
    {rds : (Name → Nat) → Nat → List (Nat × Nat × AnnotTerm)}
    {concl : (Name → Nat) → Nat → AnnotTerm} {pdoms : (Name → Nat) → Nat → List AnnotTerm}
    {fdoms es : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {mk : (Name → Nat) → Nat → Nat → AnnotTerm}
    {ihs : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm}
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
            WellDenoted V (consList ys (consList as ρ))
              (instsAV 0 (ihs ψ c j)
                ((Rb0 ψ c j).liftN rs.length
                  ((pdoms ψ c).length + (fdoms ψ c j).length + (ihs ψ c j).length))))
    (hIND : ∀ (ψ : Name → Nat) (ρ : Nat → V), ℓ ψ = 0 →
      IndRegimeAt V μ rs.length (blockRecNCt rs) rP ψ
        (blockRecTyAV mpC.base2.acval envC rs ψ) (pdoms ψ) (fdoms ψ) (ihs ψ)
        (fun c j => (Rb0 ψ c j).liftN rs.length
          ((pdoms ψ c).length + (fdoms ψ c j).length + (ihs ψ c j).length)) ρ)
    (hKIT : ∀ (ψ : Name → Nat) (ρ : Nat → V), ℓ ψ ≠ 0 →
      KitRegimeAt V (ℓ ψ) rs.length rP (blockRecNCt rs) (rds ψ) (concl ψ)
        (blockRecTyAV mpC.base2.acval envC rs ψ) (pdoms ψ) (fdoms ψ) (es ψ) (mk ψ) (ihs ψ)
        (Rb0 ψ) ρ) :
    ∀ (ψ : Name → Nat) (ρ : Nat → V),
      BlockRecPre V s rs.length (blockRecTyAV mpC.base2.acval envC rs ψ)
        (iotaEqsAV rs.length (blockRecNCt rs) (pdoms ψ) (fdoms ψ) (es ψ) (mk ψ) (ihs ψ)
          (fun c j => (Rb0 ψ c j).liftN rs.length
            ((pdoms ψ c).length + (fdoms ψ c j).length + (ihs ψ c j).length))) ρ :=
  fun ψ ρ =>
    blockRecPre_run (ℓ := ℓ ψ) (rds := rds ψ) (concl := concl ψ) (hTy ψ ρ) (hwd ψ ρ)
      (hIND ψ ρ) (hKIT ψ ρ)

end Dispatch

/-! ## 16. The IND arm's inputs (session 3)

At `ℓ = 0` every binder of a recursor's type is a `Prop` binder
(`OneElimLevel` at the family's level), so its reading is a Π-tower of
truth values and inhabiting it is a statement about its BODY at every
fitting spine (`pt_mem_mkPisAV_zero`).  That is what turns the
induction principle `hind` into "the conclusion holds at every fitting
spine", which is where the block's own induction does its work.

`hT` — the rule's conclusion reads to a truth value — is the SAME
premise the WF regime pays (`hCaB`: the conclusion at the rule's spine
IS the motive at the constructed element) at `ℓ = 0`, where the
motive is a member of `univ 0 = univZero`.  The two regimes therefore
share their O-2 input, which is worth saying: it is one reading fact,
not two. -/

section IndInputs

variable {ρ : Nat → V}

/-- **A `Prop` Π-tower is inhabited by the point** exactly when its
body is at every fitting spine. -/
theorem pt_mem_mkPisAV_zero :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (ρ : Nat → V) (b : AnnotTerm),
      (∀ dd ∈ ds, dd.2.1 = 0) →
      (∀ ys : List V, SpineFit ρ (ds.map (·.2.2)) ys →
        (pt : V) ∈ˢ interp V (consList ys ρ) b) →
      (pt : V) ∈ˢ interp V ρ (mkPisAV ds b)
  | [], ρ, b, _, h => h [] trivial
  | dd :: ds, ρ, b, hbits, h => by
    show (pt : V) ∈ˢ piR dd.2.1 (interp V ρ dd.2.2) fun x => interp V (cons x ρ) (mkPisAV ds b)
    rw [hbits dd (.head _)]
    refine pt_mem_piR_zero_of fun x hx => ?_
    refine pt_mem_mkPisAV_zero ds (cons x ρ) b (fun d' hd' => hbits d' (.tail _ hd')) ?_
    intro ys hsp
    exact h (x :: ys) ⟨hx, hsp⟩

/-- **The IND arm's `hind`, from the conclusion at every fitting
spine**: the recursor's type is a `Prop` Π-tower (`OneElimLevel` at
`ℓ = 0`, the bits from `checkBlockRecK_tyPis`), so inhabiting it is
inhabiting its conclusion along the telescope — which is the block's
own induction. -/
theorem hind_of_spines {K : Nat} {rds : Nat → List (Nat × Nat × AnnotTerm)}
    {concl RecTy : Nat → AnnotTerm} (hbits : OneElimLevel 0 K rds)
    (hTyE : ∀ c, c < K → RecTy c = mkPisAV (rds c) (concl c))
    (hconclPt : ∀ c, c < K → ∀ ys : List V, SpineFit ρ ((rds c).map (·.2.2)) ys →
      (pt : V) ∈ˢ interp V (consList ys ρ) (concl c)) :
    ∀ c, c < K → (pt : V) ∈ˢ interp V ρ (RecTy c) := by
  intro c hc
  rw [hTyE c hc]
  exact pt_mem_mkPisAV_zero (rds c) ρ (concl c)
    (fun dd hd => (hbits c hc dd hd).mp rfl) (hconclPt c hc)

/-- **The IND arm's `hT` is the WF arm's `hCaB` at `ℓ = 0`**: the
rule's conclusion reads to the MOTIVE at the constructed element, and
at the zero level the motive is a truth value (`univ 0 = univZero`). -/
theorem hT_of_motive {T B : V} (hCaB : T = B) (hB : B ∈ˢ (univ 0 : V)) :
    T ∈ˢ (univZero : V) := by
  rw [hCaB, ← univ_zero]
  exact hB

end IndInputs

/-! ## 17. The block's INDUCTION, and `hconclPt`

`hind_of_spines` reduces the IND regime's induction principle to "the
conclusion is inhabited at every fitting spine", and THAT is the
block's own simultaneous induction: a fitting spine's major lies in
the component's carrier (`BlockModelAt.leaf`, §3's identification), so
`lfpTuple_induction` applies and its step sees the functor at the
SEPARATED tuple — i.e. a recursive field already satisfies the
property.

The step is the premise here, and it is what `residueOk_blockFrame`
discharges once the ih openers' domains are known to be inhabited: at
`ℓ = 0` the ih values are the point, and their domains are the motive
at the predecessors, which is exactly what the separated tuple
carries.  What is missing to write that proof is the ih openers'
READING (RM8's A-1, blocked on the constructors' stage's
`FieldReadAt`), so the step stays named. -/

section BlockInd

variable {env : Env} {mo : EnvModel V env} {names : List Name} {d : BlockData V}

/-- **The induction's motive**: every class eliminating this
component, at every fitting spine with these parameters, this index
tuple and this major, has its conclusion inhabited. -/
@[expose] def blockIndP (d : BlockData V) (ψ : Name → Nat) (ρ : Nat → V) (K : Nat)
    (rP mem : Nat → Nat) (rds : Nat → List (Nat × Nat × AnnotTerm))
    (concl : Nat → AnnotTerm) (as : List V) (m : Nat) (i x : V) : Prop :=
  ∀ c, c < K → mem c = m → ∀ ys : List V, SpineFit ρ ((rds c).map (·.2.2)) ys →
    (prefOf (rP c) ys).take d.nP = as → d.tup ψ (mem c) (idxOf (rP c) ys) = i →
    majOf ys = x → (pt : V) ∈ˢ interp V (consList ys ρ) (concl c)

/-- **The conclusion at every fitting spine, by the block's own
induction.**  The outer induction is `lfpTuple_induction` at the
block's representation; the step — the conclusion at a CONSTRUCTED
major, with the property already available at the recursive fields —
is the premise. -/
theorem blockIndPt (hM : BlockModelAt mo names d) {ψ : Name → Nat} {ρ : Nat → V} {K : Nat}
    {rP mem : Nat → Nat} {rds : Nat → List (Nat × Nat × AnnotTerm)} {concl : Nat → AnnotTerm}
    (hmemK : ∀ c, c < K → mem c < d.k)
    (hsplit : BlockRecSplitAt V mo d ψ K rP mem rds ρ)
    (hstep : ∀ as : List V, SpineFit ρ (d.params ψ) as →
      ∀ m, m < d.N → ∀ i, i ∈ˢ d.idx ψ (consList as ρ) m → ∀ x,
        x ∈ˢ app (d.Φ ψ (consList as ρ)
            (sepTuple (d.w ψ) d.N (d.idx ψ (consList as ρ)) (d.Φ ψ (consList as ρ))
              (blockIndP d ψ ρ K rP mem rds concl as)) m) i →
        blockIndP d ψ ρ K rP mem rds concl as m i x) :
    ∀ c, c < K → ∀ ys : List V, SpineFit ρ ((rds c).map (·.2.2)) ys →
      (pt : V) ∈ˢ interp V (consList ys ρ) (concl c) := by
  intro c hc ys hfit
  obtain ⟨-, -, hpar, hidx, hmaj⟩ := hsplit c hc ys hfit
  have hsat := d.satOfSpine hpar
  obtain ⟨hmono, -, hcl⟩ := hM.functor ψ (consList ((prefOf (rP c) ys).take d.nP) ρ) hsat
  have hmemN : mem c < d.N := Nat.lt_of_lt_of_le (hmemK c hc) (Nat.le_add_right _ _)
  have hi : d.tup ψ (mem c) (idxOf (rP c) ys)
      ∈ˢ d.idx ψ (consList ((prefOf (rP c) ys).take d.nP) ρ) (mem c) := tupW_mem hidx
  have hmajC : majOf ys ∈ˢ
      app (lfpTuple (d.w ψ) d.N (d.idx ψ (consList ((prefOf (rP c) ys).take d.nP) ρ))
        (d.Φ ψ (consList ((prefOf (rP c) ys).take d.nP) ρ)) (mem c))
        (d.tup ψ (mem c) (idxOf (rP c) ys)) := by
    rw [← hM.leaf (mem c) (hmemK c hc) ψ ρ ((prefOf (rP c) ys).take d.nP) (idxOf (rP c) ys)
      hpar hidx]
    exact hmaj
  exact lfpTuple_induction hcl hmono
    (blockIndP d ψ ρ K rP mem rds concl ((prefOf (rP c) ys).take d.nP))
    (hstep ((prefOf (rP c) ys).take d.nP) hpar) (mem c) hmemN _ hi _ hmajC c hc rfl ys hfit
    rfl rfl rfl

end BlockInd

/-! ## 18. `hTy` from the run

`BlockRecPre.hTy` asks the recursor types' readings to be sets of the
chain's level and to be graded.  The GRADING is `checkBlockRecK_tyPis`'
last component (`WellDenotedV` is the grading and the bit-validity
together, `Model/Currency.lean`), and the membership is the Π-tower's:
a tower all of whose stages carry the level `s` lands in `univ s`,
given its domains and its body do (`piR_mem_univ` at `u = v = s`,
where the `max` collapses).  Both remaining premises are O-2's
readings of the STORED type, at the named spellings `blockRecRdsAV`
and `blockRecConclAV`. -/

section TyRun

/-- **A Π-tower at ONE level lands in that universe.** -/
theorem mkPisAV_mem_univ (s : Nat) :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (ρ : Nat → V) (b : AnnotTerm),
      (∀ dd ∈ ds, dd.2.1 = s) →
      (∀ ys : List V, SpineFit ρ ((ds.take ys.length).map (·.2.2)) ys →
        ∀ dd, ds[ys.length]? = some dd → interp V (consList ys ρ) dd.2.2 ∈ˢ (univ s : V)) →
      (∀ ys : List V, SpineFit ρ (ds.map (·.2.2)) ys →
        interp V (consList ys ρ) b ∈ˢ (univ s : V)) →
      interp V ρ (mkPisAV ds b) ∈ˢ (univ s : V)
  | [], ρ, b, _, _, hb => hb [] trivial
  | dd :: ds, ρ, b, hlvl, hdom, hb => by
    show piR dd.2.1 (interp V ρ dd.2.2) (fun x => interp V (cons x ρ) (mkPisAV ds b))
      ∈ˢ (univ s : V)
    have hA : interp V ρ dd.2.2 ∈ˢ (univ s : V) := hdom [] trivial dd rfl
    have hB : ∀ x, x ∈ˢ interp V ρ dd.2.2 →
        interp V (cons x ρ) (mkPisAV ds b) ∈ˢ (univ s : V) := by
      intro x hx
      refine mkPisAV_mem_univ s ds (cons x ρ) b (fun d' hd' => hlvl d' (.tail _ hd')) ?_ ?_
      · intro ys hsp d' hd'
        exact hdom (x :: ys) ⟨hx, hsp⟩ d' (by simpa using hd')
      · intro ys hsp
        exact hb (x :: ys) ⟨hx, hsp⟩
    rw [hlvl dd (.head _)]
    have h := piR_mem_univ (u := s) (v := s) hA hB
    have hm : Nat.max s s = s := by simp
    have he : (if s = 0 then 0 else Nat.max s s) = s := by
      rw [hm]
      split
      · next h0 => exact h0.symm
      · rfl
    rwa [he] at h

/-- **`hTy` at the run**: the type's grading is the run's
(`checkBlockRecK_tyPis`), its membership the Π-tower's at the run's
own binder data and conclusion. -/
theorem hTy_of_run {envC : Env} (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F s : Nat}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (ψ : Name → Nat) (ρ : Nat → V)
    (hlvl : ∀ c, c < rs.length →
      ∀ dd ∈ blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c, dd.2.1 = s)
    (hdom : ∀ c, c < rs.length → ∀ ys : List V,
      SpineFit ρ
        (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).take ys.length).map
          (·.2.2)) ys →
      ∀ dd, (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c)[ys.length]? = some dd →
        interp V (consList ys ρ) dd.2.2 ∈ˢ (univ s : V))
    (hcon : ∀ c, c < rs.length → ∀ ys : List V,
      SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2)) ys →
      interp V (consList ys ρ)
          (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ c) ∈ˢ (univ s : V)) :
    ∀ c, c < rs.length →
      interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c) ∈ˢ (univ s : V) ∧
        WellDenoted V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c) := by
  intro c hc
  obtain ⟨-, -, -, -, hPis, -, -, -, -, hwd⟩ :=
    checkBlockRecK_tyPis hμ mpC h (List.getElem?_eq_getElem hc) ψ
  refine ⟨?_, (hwd ρ).1⟩
  rw [hPis]
  exact mkPisAV_mem_univ s _ ρ _ (hlvl c hc) (hdom c hc) (hcon c hc)

end TyRun

/-! ## 19. The WF regime's `KitRegimeAt`, assembled

Everything §11–§13 built, in ONE step: from the representation, the
rules' certificates and the six reading bridges, the dispatch's
`KitRegimeAt` at `ℓ ≠ 0 ∧ w ≠ 0`.  The family datum is
`blockWfData` at §12's kit family, its step is §11's, and `hstAt` is
`blockRecStep_at_rule`.

The six bridges are exactly what RM8's session 4 is writing, at the
rule-data spelling of `M5M-data-REPORT` §S3.4 (`pdoms0`, `fdoms0`,
`es0`, `mk0`, `Rb0` as functions of the run; `ihs` the model's own
guarded-call towers, whose reading premise is the constructors'
stage's per-field `FieldReadAt`).  They are premises here in that
spelling — this lane parameterises at the chain-frame components
throughout, which is the side RM8's `ihs` correction moves towards. -/

section KitRegimeWf

variable {env : Env} {mo : EnvModel V env} {names : List Name} {d : BlockData V}
  {ℓ K : Nat} {ψ : Name → Nat} {ρ : Nat → V} {mem nCt rP : Nat → Nat}
  {rds : Nat → List (Nat × Nat × AnnotTerm)} {concl RecTy : Nat → AnnotTerm}
  {pdoms : Nat → List AnnotTerm} {fdoms es ihdoms : Nat → Nat → List AnnotTerm}
  {mk : Nat → Nat → AnnotTerm} {ihs : Nat → Nat → List AnnotTerm}
  {Rb0 Ca : Nat → Nat → AnnotTerm} {ihv : Nat → Nat → List V → V → List V}
  {envT : Env} {mp : EnvModelM V μ envT} {F : Nat}

/-- **`KitRegimeAt` at the WF regime**, from the representation, the
certificates and the reading bridges. -/
theorem blockKitRegime_wf (hμ : μ.verifiedChecks = true) (hM : BlockModelAt mo names d)
    (hw : d.w ψ ≠ 0) (hmemK : ∀ c, c < K → mem c < d.k)
    (hnCt : ∀ c, c < K → (d.ctorsM (mem c)).length = nCt c)
    (hlenIds : ∀ c, c < K → (d.IdsM (mem c) ψ).length = d.nIdxAt (mem c))
    (hsplitR : BlockRecSplitAt V mo d ψ K rP mem rds ρ)
    (hpdE : ∀ c, c < K → pdoms c = ((rds c).map (·.2.2)).take (rP c))
    (hconclTy : ∀ xs : List V,
      ∀ c, c < K → ∀ i, i ∈ˢ blockRecIs d ψ ρ pdoms mem xs c →
      ∀ x, x ∈ˢ app (blockRecCr d ψ ρ mem xs c) i →
      interp V
          (consList (xs ++ (isOfW (d.uM (mem c) ψ) (d.nIdxAt (mem c)) i ++ [x])) ρ) (concl c)
        ∈ˢ (univ ℓ : V))
    (hcerts : ∀ c, c < K → ∀ j, j < nCt c →
      BlockRuleCerts V mp F ψ (rP c) (fdoms c j).length (ihdoms c j).length
        (pdoms c) (fdoms c j) (ihdoms c j) (Rb0 c j) (Ca c j))
    (hspF : ∀ xs : List V, ∀ c, c < K →
      SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs →
      SpineFit ρ (pdoms c ++ fdoms c j) (xs ++ fs))
    (hihF : ∀ xs : List V, ∀ c, c < K →
      SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs → ∀ g : V,
      (∀ v, v ∈ˢ tcPred (unionSet K (blockRecIs d ψ ρ pdoms mem xs)
            (blockRecCr d ψ ρ mem xs))
          (tagged c i (d.inj ψ (mem c) j fs)) →
        app g v ∈ˢ blockRecMot K concl (fun c' => d.uM (mem c') ψ)
          (fun c' => d.nIdxAt (mem c')) ρ xs v) →
      SpineFit (consList (xs ++ fs) ρ) (ihdoms c j) (ihv c j fs g))
    (hCaB : ∀ xs : List V, ∀ c, c < K →
      SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs → ∀ g : V,
      interp V (consList (ihv c j fs g) (consList (xs ++ fs) ρ)) (Ca c j)
        = blockRecMot K concl (fun c' => d.uM (mem c') ψ) (fun c' => d.nIdxAt (mem c')) ρ xs
            (tagged c i (d.inj ψ (mem c) j fs)))
    (hTyE : ∀ c, c < K → RecTy c = mkPisAV (rds c) (concl c))
    (hbits : OneElimLevel ℓ K rds) (hpl : ∀ c, c < K → (pdoms c).length = rP c)
    (hrule : ∀ (D : RecFamData V ℓ K rP rds concl ρ), ∀ c, c < K → ∀ j, j < nCt c →
      ∀ xs fs : List V, xs.length = (pdoms c).length →
      SpineFit (chainFrame K (famCand D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      SpineFit ρ ((rds c).map (·.2.2))
        (xs ++ ((es c j).map (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)))
          ++ [interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)) (mk c j)])))
    (hctorAt : ∀ (D : RecFamData V ℓ K rP rds concl ρ), ∀ c, c < K → ∀ j, j < nCt c →
      ∀ xs fs : List V, xs.length = (pdoms c).length →
      SpineFit (chainFrame K (famCand D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
          (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
            (d.Φ ψ (consList (xs.take d.nP) ρ)))
          (d.tup ψ (mem c)
            ((es c j).map (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)))))
          (mem c) j fs ∧
        interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)) (mk c j)
          = d.inj ψ (mem c) j fs)
    (hihChain : ∀ (D : RecFamData V ℓ K rP rds concl ρ), ∀ c, c < K → ∀ j, j < nCt c →
      ∀ xs fs : List V, xs.length = (pdoms c).length →
      SpineFit (chainFrame K (famCand D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      ihv c j fs
          (kitGraphAt (D.kit xs)
            (tagged c
              (D.tupOf c
                ((es c j).map (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)))))
              (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)) (mk c j))))
        = (ihs c j).map (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)))) :
    KitRegimeAt V ℓ K rP nCt rds concl RecTy pdoms fdoms es mk ihs Rb0 ρ := by
  have hmemN : ∀ c, c < K → mem c < d.N :=
    fun c hc => Nat.lt_of_lt_of_le (hmemK c hc) (Nat.le_add_right _ _)
  refine ⟨blockWfData (rds := rds) (concl := concl) (rP := rP) (ρ := ρ) d
      (blockWfKitFam (ihdoms := ihdoms) (Ca := Ca) (ihv := ihv) (rP := rP) (nCt := nCt)
        hμ hM hw hmemN hnCt hconclTy hcerts hspF hihF hCaB)
      (blockWf_hsplit hM hpdE hmemK hsplitR) ?_,
    blockRecStep K d ψ ρ mem Rb0 ihv, ihv, ?_, hTyE, hbits, hpl, ?_, ?_, ?_⟩
  · intro c hc ys hfit
    rw [blockWfKitFam_B]
    exact blockWf_hconcl hM hmemN hlenIds hsplitR c hc ys hfit
  · intro xs
    rw [blockWfData_st, blockWfKitFam_st]
  · exact hrule _
  · exact blockRecStep_at_rule hM hw hmemN hnCt _ (fun _ _ => rfl) (hctorAt _)
  · exact hihChain _

end KitRegimeWf

/-! ## 20. The components at the RUN's spelling (session 4)

RM8's sessions 4–5 name the rule data's syntactic components as
functions of the run (`M5M-data-REPORT` §A.8): `blockRulePdomsAV`
(the recursor type's first `rP` binder domains),
`blockRuleFdomsAV`/`blockRuleEsAV`/`blockRuleMkAV` (the constructor's
field domains, index expressions and fired spine, read at the rule's
frame), with `blockRuleData_run` identifying them with what the check
actually opened.  The ι equations are stated at those components
LIFTED past the `K` chain binders at their own cutoffs
(`blockIotaEqsAV`), which is the side this lane parameterises at.

These four definitions are that instantiation, so every premise of
§19 reads at RM8's names; `hpl` — the rule's prefix domains are as
long as the rule prefix — is then a theorem, off
`blockRulePdomsAV_length` and `liftDomsK_length`. -/

section RunComponents

/-- The rule's PREFIX domains at the chain frame. -/
@[expose] def blockRecPdomsK (K : Nat) (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env)
    (p : ConLeche.BlockShape)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (ψ : Name → Nat) (c : Nat) : List AnnotTerm :=
  liftDomsK K 0 (blockRulePdomsAV acval envC p rs ψ c)

/-- The constructor's FIELD domains at the chain frame. -/
@[expose] def blockRecFdomsK (K : Nat) (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env)
    (p : ConLeche.BlockShape)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (ψ : Name → Nat) (c i : Nat) : List AnnotTerm :=
  liftDomsK K (blockRulePdomsAV acval envC p rs ψ c).length
    (blockRuleFdomsAV p rs acval envC ψ c i)

/-- The constructor's INDEX expressions at the chain frame. -/
@[expose] def blockRecEsK (K : Nat) (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env)
    (p : ConLeche.BlockShape)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (ψ : Name → Nat) (c i : Nat) : List AnnotTerm :=
  (blockRuleEsAV p rs acval envC ψ c i).map fun e =>
    e.liftN K ((blockRulePdomsAV acval envC p rs ψ c).length
      + (blockRuleFdomsAV p rs acval envC ψ c i).length)

/-- The FIRED SPINE at the chain frame. -/
@[expose] def blockRecMkK (K : Nat) (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env)
    (p : ConLeche.BlockShape)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (ψ : Name → Nat) (c i : Nat) : AnnotTerm :=
  (blockRuleMkAV p rs acval envC ψ c i).liftN K
    ((blockRulePdomsAV acval envC p rs ψ c).length
      + (blockRuleFdomsAV p rs acval envC ψ c i).length)

/-- **`hpl` at the run**: the rule's prefix domains are as long as the
rule prefix (`blockRulePdomsAV_length`, unchanged by the lifting). -/
theorem blockRecPdomsK_length {envC : Env} (hμ : μ.verifiedChecks = true)
    (mpC : EnvModelM V μ envC) {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F K : Nat}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) (ψ : Name → Nat) :
    (blockRecPdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c).length
      = p.toBlockShape.rulePrefixAt c := by
  rw [blockRecPdomsK, liftDomsK_length]
  exact blockRulePdomsAV_length hμ mpC h hr ψ

end RunComponents

/-! ## 21. The family's LEVEL, and `hTy` without pinning any bit
(session 5)

The `hlvl` ruling: **do not pin the reading's binder numerals**.  The
level a recursor's type lives at is the one the CHECK inferred — its
`ensureSort` names it, and that level already accounts for the
binders' levels, so the Π-tower's membership needs no per-binder
hypothesis at all.  `checkConstantVal_reads` (`BlockRecRead.lean`,
strengthened here) returns it: the same claims that grade the reading
place it in `univ (u.eval ψ)`, one component further into the
`InferClaim`/`WhnfClaim` pair (`sortSemAt_of_claims`, at
`ensureSortCore_inv`).

The family's level is then the MAX over the `K` recursors, and each
type's membership rises to it by cumulativity (`univ_mono`).  That is
`blockRecTy_univ_run`, and with it `BlockRecPre.hTy` is a theorem off
the run alone — no `hlvl`, no `hdom`, no `hcon`. -/

section FamilyLevel

/-- A uniform universe for finitely many members, by cumulativity. -/
theorem exists_uniform_univ {n : Nat} {g : Nat → (Nat → V) → V}
    (h : ∀ c, c < n → ∃ s : Nat, ∀ ρ : Nat → V, g c ρ ∈ˢ (univ s : V)) :
    ∃ s : Nat, ∀ c, c < n → ∀ ρ : Nat → V, g c ρ ∈ˢ (univ s : V) := by
  induction n with
  | zero => exact ⟨0, fun c hc => absurd hc (Nat.not_lt_zero c)⟩
  | succ n ih =>
    obtain ⟨s₀, hs₀⟩ := ih fun c hc => h c (Nat.lt_succ_of_lt hc)
    obtain ⟨s₁, hs₁⟩ := h n (Nat.lt_succ_self n)
    refine ⟨Nat.max s₀ s₁, fun c hc ρ => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc' | rfl
    · exact univ_mono (Nat.le_max_left _ _) _ (hs₀ c hc' ρ)
    · exact univ_mono (Nat.le_max_right _ _) _ (hs₁ ρ)

/-- **`hTy` at the run, with the level the CHECK chose.**  The family's
level is the max of the `K` inferred sorts at `ψ`; every recursor
type's reading lands in it by cumulativity, and its grading is the
same run's. -/
theorem blockRecTy_univ_run {envC : Env} (hμ : μ.verifiedChecks = true)
    (mpC : EnvModelM V μ envC) {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (ψ : Name → Nat) :
    ∃ s : Nat, ∀ c, c < rs.length → ∀ ρ : Nat → V,
      interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c) ∈ˢ (univ s : V) ∧
        WellDenoted V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c) := by
  have hmem : ∀ c, c < rs.length → ∃ s : Nat, ∀ ρ : Nat → V,
      interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c) ∈ˢ (univ s : V) := by
    intro c hc
    obtain ⟨ta, u, hta, -, hu⟩ :=
      checkBlockRecK_tyReads hμ mpC h rs[c] (List.getElem_mem hc) ψ
    refine ⟨u.eval ψ, fun ρ => ?_⟩
    rw [blockRecTyAV_eq (List.getElem?_eq_getElem hc) hta]
    exact hu ρ
  obtain ⟨s, hs⟩ := exists_uniform_univ hmem
  refine ⟨s, fun c hc ρ => ⟨hs c hc ρ, ?_⟩⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hwd⟩ :=
    checkBlockRecK_tyPis hμ mpC h (List.getElem?_eq_getElem hc) ψ
  exact (hwd ρ).1

end FamilyLevel

/-! ## 22. `hctorAt` (b) — the fired spine's VALUE at the rule's frame
(session 6)

`blockRuleMkAV_eq` (RM11) identifies the fired spine's reading as the
constructor's leaf applied to the parameter bvars and the field bvars;
what the regime needs is its VALUE at the rule's frame, and that is
three computations:

* the residue of the `K`-lift is the base frame
  (`interp_liftN_chainFrame`, §13);
* a bvar at `|L| − 1 − k` reads the `k`-th entry of the frame's list
  (`interp_bvarAt`), so the parameter bvars read `xs.take nP` and the
  field bvars read `fs` (`map_bvarAt_take`, `map_fieldBvars`);
* the constant's leaf does not see the frame
  (`acval_interp_closedC`), so `BlockModelAt.ctor` applies — at ANY
  fitting parameter spine (`blockCtorFold_params_blind`, RM11). -/

section FiredSpine

/-- **A frame's `k`-th entry, as a bvar.** -/
theorem interp_bvarAt {L : List V} {ρ : Nat → V} {k : Nat} (hk : k < L.length) :
    interp V (consList L ρ) (.bvar (L.length - 1 - k)) = L.getD k pt := by
  rw [interp_bvar, consList_getD_of_lt L ρ _ (by omega),
    show L.length - 1 - (L.length - 1 - k) = k from by omega]

/-- A prefix of a list, as its first entries. -/
theorem take_eq_map_getD : ∀ (L : List V) (n : Nat), n ≤ L.length →
    L.take n = (List.range n).map fun k => L.getD k pt := by
  intro L n hn
  refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
  have hi : i < n := by
    have := h1
    simp only [List.length_take] at this
    omega
  rw [List.getElem_take, List.getElem_map, List.getElem_range,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  rfl

/-- The parameter bvars read the frame's first `nP` entries. -/
theorem map_bvarAt_take {L : List V} {ρ : Nat → V} {nP D : Nat} (hD : D = L.length)
    (hnP : nP ≤ L.length) :
    (paramBvarsAt nP D).map (interp V (consList L ρ)) = L.take nP := by
  subst hD
  rw [take_eq_map_getD L nP hnP, paramBvarsAt, List.map_map]
  refine List.map_congr_left fun k hk => ?_
  exact interp_bvarAt (by simpa using Nat.lt_of_lt_of_le (List.mem_range.mp hk) hnP)

/-- The field bvars read the frame's fields. -/
theorem map_fieldBvars {xs fs : List V} {ρ : Nat → V} {rP nF : Nat}
    (hxs : xs.length = rP) (hfs : fs.length = nF) :
    ((List.range nF).map fun k => (AnnotTerm.bvar (rP + nF - 1 - (rP + k)) : AnnotTerm)).map
        (interp V (consList (xs ++ fs) ρ)) = fs := by
  have hlen : (xs ++ fs).length = rP + nF := by rw [List.length_append, hxs, hfs]
  refine List.ext_getElem (by simp [hfs]) fun i h1 h2 => ?_
  have hi : i < nF := by simpa using h1
  rw [List.getElem_map, List.getElem_map, List.getElem_range]
  have : (AnnotTerm.bvar (rP + nF - 1 - (rP + i)) : AnnotTerm)
      = .bvar ((xs ++ fs).length - 1 - (rP + i)) := by rw [hlen]
  rw [this, interp_bvarAt (by rw [hlen]; omega), List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega), hxs,
    show rP + i - rP = i from by omega, List.getElem?_eq_getElem (by omega)]
  rfl

/-- **`hctorAt` (b), at the run**: the rule's constructed major reads
to the block's injection at the rule's own field values.  The three
computations of the section header, in order. -/
theorem blockRecMkK_value {envC : Env} {mpC : EnvModelM V μ envC} {names : List Name}
    {d : BlockData V} (hM : BlockModelAt mpC.base2 names d)
    {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {ci : ConstantInfo} (hfind : envC.find? cA.1.name = some ci)
    (hlps : ci.toConstantVal.levelParams = p.lps)
    (hnP : p.nP ≤ p.toBlockShape.rulePrefixAt c)
    {mem : Nat → Nat} {j : Nat} (hmemN : mem c < d.N)
    (hcj : (d.ctorsM (mem c))[j]? = some cA)
    (ψ : Name → Nat) {K : Nat} {a ρ : Nat → V} {xs fs : List V}
    (hxs : xs.length = p.toBlockShape.rulePrefixAt c) (hfs : fs.length = cA.2)
    (hcut : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
        + (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i).length
      = xs.length + fs.length)
    (hps : SpineFit ρ (d.params ψ) (xs.take p.nP))
    (hfp : SpineFit (consList (xs.take p.nP) ρ) ((d.Fss (mem c) ψ).getD j []) fs) :
    interp V (consList (xs ++ fs) (chainFrame K a ρ))
        (blockRecMkK K mpC.base2.acval envC p.toBlockShape rs ψ c i)
      = d.inj ψ (mem c) j fs := by
  have hlenL : (xs ++ fs).length = p.toBlockShape.rulePrefixAt c + cA.2 := by
    rw [List.length_append, hxs, hfs]
  -- (1) the K-lift drops to the base frame
  rw [blockRecMkK,
    show (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
        + (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i).length
      = (xs ++ fs).length from by rw [hcut, List.length_append],
    interp_liftN_chainFrame (xs ++ fs),
    blockRuleMkAV_eq h hr hcA hrhs hfind hlps hnP ψ, interp_mkAppN, foldl_app_map,
    List.map_append]
  -- (2) the bvars read the frame's entries
  rw [map_bvarAt_take (hD := by rw [hlenL]) (by rw [hlenL]; omega),
    map_fieldBvars hxs hfs, List.take_append_of_le_length (by omega)]
  -- (3) the constant's leaf does not see the frame
  rw [acval_interp_closedC mpC.base2 cA.1.name _ (consList (xs ++ fs) ρ) ρ,
    Level.substFn_param_self ψ p.lps]
  exact hM.ctor (mem c) hmemN j cA hcj ψ ρ (xs.take p.nP) fs hps hfp

end FiredSpine

/-! ## 23. The lifting transport at an ARBITRARY insertion (session 6)

`interp_liftN_chainFrame`/`spineFit_liftDomsK` (RM11) transport a
reading and a fit past the `K` chain binders.  `hspF` needs the same
transport past the rule prefix's `rP − nP` EXTRA binders — the
recursor's `nP … rP-1` stretch, which `blockRuleFdomsAV_eq` exhibits
as a `liftDomsK (rP − nP) 0` of the constructor's own field domains.
Both are the same lemma at a different inserted block, and this is
that lemma; the chain versions are its instances at
`us := (List.range K).map a`. -/

section Insertion

/-- **A reading crosses an inserted block**: a form read under `ws`
binders reads the same when `us` values are inserted below them, once
lifted by `|us|` at the cutoff `|ws|`. -/
theorem interp_liftN_insert {us ws : List V} {ρ : Nat → V} (e : AnnotTerm) :
    interp V (consList ws (consList us ρ)) (e.liftN us.length ws.length)
      = interp V (consList ws ρ) e := by
  rw [interp_liftN, shiftE_consList_ih (locals := ws) (ihvals := us) rfl rfl]

/-- **A fit crosses an inserted block**: `spineFit_liftDomsK` at an
ARBITRARY insertion (RM11 exposed `liftDomsK` for this; the chain
version is this one at `us := (List.range K).map a`). -/
theorem spineFit_liftDomsK_insert {us : List V} {ρ : Nat → V} :
    ∀ (Ds : List AnnotTerm) (ws vs : List V),
      SpineFit (consList ws (consList us ρ)) (liftDomsK us.length ws.length Ds) vs
        ↔ SpineFit (consList ws ρ) Ds vs
  | [], _, [] => Iff.rfl
  | [], _, _ :: _ => Iff.rfl
  | _ :: _, _, [] => Iff.rfl
  | D :: Ds, ws, v :: vs => by
    have ih := spineFit_liftDomsK_insert (us := us) (ρ := ρ) Ds (ws ++ [v]) vs
    rw [List.length_append, List.length_singleton] at ih
    simp only [consList_append, consList_cons, consList_nil] at ih
    show (v ∈ˢ interp V (consList ws (consList us ρ)) (D.liftN us.length ws.length) ∧ _) ↔ _
    rw [interp_liftN_insert (us := us) (ws := ws) D]
    exact and_congr Iff.rfl ih

/-- **The rule's field domains, at the rule's frame**: the
constructor's own field domains, lifted past the recursor prefix's
extra `rP − nP` binders (`blockRuleFdomsAV_eq`) and then past the `K`
chain binders (`blockRecFdomsK`), fit exactly the spines that fit the
constructor's domains at the PARAMETER frame.

Both lifts are the same transport at a different inserted block: the
chain's is `spineFit_liftDomsK`, the prefix stretch's is
`spineFit_liftDomsK_insert` at `us := x⃗.drop nP`, which is the block
`consList x⃗ ρ` carries above the parameters
(`consList_append` at `x⃗.take nP ++ x⃗.drop nP`). -/
theorem spineFit_liftDomsK_rule {K nP rP : Nat} {a ρ : Nat → V} {xs fs : List V}
    {Fs0 : List AnnotTerm} (hxs : xs.length = rP) :
    SpineFit (consList xs (chainFrame K a ρ)) (liftDomsK K rP (liftDomsK (rP - nP) 0 Fs0)) fs
      ↔ SpineFit (consList (xs.take nP) ρ) Fs0 fs := by
  subst hxs
  refine Iff.trans (spineFit_liftDomsK (K := K) (a := a) (ρ := ρ) _ xs fs) ?_
  have hsplit : consList xs ρ = consList (xs.drop nP) (consList (xs.take nP) ρ) := by
    rw [← consList_append, List.take_append_drop]
  have hlen : (xs.drop nP).length = xs.length - nP := by rw [List.length_drop]
  rw [hsplit, ← hlen]
  have hq := spineFit_liftDomsK_insert (us := xs.drop nP) (ρ := consList (xs.take nP) ρ)
    Fs0 [] fs
  simpa using hq

/-- **The rule's transport at a TERM** — `spineFit_liftDomsK_rule`'s
reading twin, for the components that are single forms rather than
binder lists (the index expressions `es` and the fired spine `mk`,
whose `blockRec*K` are the base forms lifted at the cutoff
`|pdoms| + |fdoms|`).  The same two inserted blocks: the `K` chain
binders below the whole rule frame, and the recursor prefix's extra
`rP − nP` binders below the fields. -/
theorem interp_liftN_rule {K nP rP nF : Nat} {a ρ : Nat → V} {xs fs : List V}
    (hxs : xs.length = rP) (hfs : fs.length = nF) (e : AnnotTerm) :
    interp V (consList (xs ++ fs) (chainFrame K a ρ)) ((e.liftN (rP - nP) nF).liftN K (rP + nF))
      = interp V (consList fs (consList (xs.take nP) ρ)) e := by
  have hlen : (xs ++ fs).length = rP + nF := by rw [List.length_append, hxs, hfs]
  rw [← hlen, interp_liftN_chainFrame (xs ++ fs), consList_append]
  have hsplit : consList xs ρ = consList (xs.drop nP) (consList (xs.take nP) ρ) := by
    rw [← consList_append, List.take_append_drop]
  have hdrop : (xs.drop nP).length = rP - nP := by rw [List.length_drop, hxs]
  rw [hsplit, ← hdrop, ← hfs]
  exact interp_liftN_insert (us := xs.drop nP) (ws := fs) e

end Insertion

/-! ## 24. `hspF` at the run — the rule's spine fits (session 7)

`hspF` is the kit's step passing `BlockRuleCerts.residueOk` its
`SpineFit ρ (pdoms c ++ fdoms c j) (x⃗ ++ f⃗)`, and it splits exactly
where `SpineFit.append` does:

* the PREFIX half is the guard — since session 7 an inhabited class
  index set carries `SpineFit ρ (pdoms c) x⃗` (`blockRecIs_fits`), so
  the step has it in hand and nothing has to be proved about the
  motives and the minor premises;
* the FIELD half is the content: `ChainFit`'s `FitsFrom` asks a
  recursive field's value in the block's SLOT, `SpineFit` asks it in
  the domain's READING, and where the two agree the walks coincide
  (`spineFit_of_fitsFrom`, `BlockModel.lean`).  The domains then cross
  the two lifts — the recursor prefix's extra `rP − nP` binders and
  the `K` chain binders — by §23's transports.

The two identities this takes are named premises in their owners'
spelling: `hfd` is RM11's `blockRuleFdomsAV_eq` composed with the
record's `ds`/`Fss` identification, and `hslot` is the slot-to-domain
step at the block's own carrier (`BlockCtorDataI.recEntry`/`.reflEntry`
through `BlockModelAt.leaf`, the shape `blockChainReal_of` already
discharges against the stage's tower).

`hslot` is quantified at the frames the walk actually REACHES —
`consList b⃗ ρp` for a prefix that already fits — and not at every
`σ`: the identity is `BlockModelAt.leaf`, whose hypotheses are fits,
so at an arbitrary frame the fold of the member's former and the slot
are unrelated and the `∀ σ` form of the premise is FALSE (session 7's
second over-quantification, caught in this lane's own first draft of
this section). -/

section SpineOfChain

/-- **`hspF` at the run.**  With the prefix's fit (the guard) and the
slot-to-domain identity, a field spine fitting the constructor at the
carrier fits the rule's own binder data at the chain frame. -/
theorem blockRecSpF {envC : Env} {mpC : EnvModelM V μ envC} {d : BlockData V}
    {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {i j K : Nat} {mem : Nat → Nat} {ψ : Name → Nat}
    {a ρ : Nat → V} {xs fs : List V} {X : Nat → V} {t : V}
    (hfd : blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i
      = liftDomsK (p.toBlockShape.rulePrefixAt c - d.nP) 0 ((d.Fss (mem c) ψ).getD j []))
    (hslot : ∀ l, l < ((d.Fss (mem c) ψ).getD j []).length → ∀ bs : List V,
      FitsFrom ((d.rss (mem c)).getD j []) (d.slotAt ψ X (mem c) j) 0
        (consList (xs.take d.nP) ρ) (((d.Fss (mem c) ψ).getD j []).take l) bs →
      ((d.rss (mem c)).getD j []).getD l false = true →
      d.slotAt ψ X (mem c) j l (consList bs (consList (xs.take d.nP) ρ))
        = interp V (consList bs (consList (xs.take d.nP) ρ))
            (((d.Fss (mem c) ψ).getD j []).getD l default))
    (hxs : xs.length = p.toBlockShape.rulePrefixAt c)
    (hpref : SpineFit (chainFrame K a ρ)
      (blockRecPdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c) xs)
    (hfit : d.ChainFit ψ (consList (xs.take d.nP) ρ) X t (mem c) j fs) :
    SpineFit (chainFrame K a ρ)
      (blockRecPdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c
        ++ blockRecFdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c i) (xs ++ fs) := by
  refine SpineFit.append hpref ?_
  have hbase : SpineFit (consList (xs.take d.nP) ρ) ((d.Fss (mem c) ψ).getD j []) fs :=
    spineFit_of_fitsFrom (fun l hl bs hb hrb => by
      rw [Nat.zero_add] at hrb ⊢
      exact hslot l hl bs hb hrb) hfit.1
  have hlenP : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
      = p.toBlockShape.rulePrefixAt c := blockRulePdomsAV_length hμ mpC h hr ψ
  rw [blockRecFdomsK, hlenP, hfd]
  exact (spineFit_liftDomsK_rule hxs).mpr hbase

/-- **`hctorAt`'s first conjunct, the FIT half**: `blockRecSpF`'s
converse.  A spine fitting the rule's own binder data at the chain
frame gives the constructor's `FitsFrom` at the block's carrier —
the same two premises, the transports read the other way.  What it
does NOT give is `ChainFit`'s second conjunct (the index expressions'
readings ARE the tuple's components), which is RM11's `es0` against
`d.esF`. -/
theorem blockRecCtorFitsFrom {envC : Env} {mpC : EnvModelM V μ envC} {d : BlockData V}
    {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {i j K : Nat} {mem : Nat → Nat} {ψ : Name → Nat}
    {a ρ : Nat → V} {xs fs : List V} {X : Nat → V}
    (hfd : blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i
      = liftDomsK (p.toBlockShape.rulePrefixAt c - d.nP) 0 ((d.Fss (mem c) ψ).getD j []))
    (hslot : ∀ l, l < ((d.Fss (mem c) ψ).getD j []).length → ∀ bs : List V,
      SpineFit (consList (xs.take d.nP) ρ) (((d.Fss (mem c) ψ).getD j []).take l) bs →
      ((d.rss (mem c)).getD j []).getD l false = true →
      d.slotAt ψ X (mem c) j l (consList bs (consList (xs.take d.nP) ρ))
        = interp V (consList bs (consList (xs.take d.nP) ρ))
            (((d.Fss (mem c) ψ).getD j []).getD l default))
    (hxs : xs.length
      = (blockRecPdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c).length)
    (hsp : SpineFit (chainFrame K a ρ)
      (blockRecPdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c
        ++ blockRecFdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c i) (xs ++ fs)) :
    FitsFrom ((d.rss (mem c)).getD j []) (d.slotAt ψ X (mem c) j) 0
      (consList (xs.take d.nP) ρ) ((d.Fss (mem c) ψ).getD j []) fs := by
  obtain ⟨as₁, as₂, heq, h1, h2⟩ := spineFit_append_split hsp
  have hl1 : as₁.length = xs.length := by rw [h1.length_eq, hxs]
  obtain ⟨rfl, rfl⟩ := List.append_inj heq hl1.symm
  have hlenP : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
      = p.toBlockShape.rulePrefixAt c := blockRulePdomsAV_length hμ mpC h hr ψ
  have hxs' : xs.length = p.toBlockShape.rulePrefixAt c := by
    rw [hxs, blockRecPdomsK, liftDomsK_length, hlenP]
  rw [blockRecFdomsK, hlenP, hfd] at h2
  refine fitsFrom_of_spineFit (fun l hl bs hb hrb => by
      rw [Nat.zero_add] at hrb ⊢
      exact hslot l hl bs hb hrb) ?_
  exact (spineFit_liftDomsK_rule hxs').mp h2

end SpineOfChain

/-! ## 25. `hslot` — the slot IS the domain's reading (session 8)

The one piece §24 left open: at a RECURSIVE position the block's slot
(`slotSet` at the target component of the least tuple) and the
constructor's own field domain (the target member's FORMER applied to
the parameters and the field's index readings) are the same set.

It is `blockChainReal_of`'s `hrec` obligation
(`BlockRealChains.lean`) with `blockLeafApp` replaced by
`BlockModelAt.leaf` — the same two cases:

* a FINITARY recursive field has an empty telescope
  (`BlockCtorDataI.tssNone`), so `slotSet_nil` reduces the slot to
  `app (X tgt) ⟨e⃗⟩` and `recEntry` reduces the domain to the fold of
  the member's former, which `leaf` identifies;
* a REFLEXIVE field's domain is `mkPisAV` over its telescope
  (`reflEntry`), whose reading is the `piTele` the slot already is
  (`interp_mkPisAV_piTele`), with the same identification one
  telescope spine deeper.

`hEis` — the field's index readings fit the TARGET's index telescope —
is the premise this cannot own: it is `ChainFactsB.gr`'s `SlotFit` on
the stage side, and `leaf`'s second hypothesis here.  It is stated at
the frames the walk reaches, as §24's `hslot` is. -/

section SlotEntry

/-- **The slot-to-domain identity at a recursive position.** -/
theorem blockSlot_eq_entry {env : Env} {mo : EnvModel V env} {names : List Name}
    {d : BlockData V} (hM : BlockModelAt mo names d) {lps : List Name}
    {c j : Nat} {cA : ConstantVal × Nat} (hcj : (d.ctorsM c)[j]? = some cA)
    (hcf : BlockCtorFacts mo d lps c j cA)
    {ψ : Name → Nat} {ρ : Nat → V} {as bs : List V} {l : Nat}
    (hasLen : as.length = d.nP) (hps : SpineFit ρ (d.params ψ) as)
    (hl : l < cA.2) (hbs : bs.length = l) (htgt : d.tgts c j l < d.k)
    (hEis : ∀ ts : List V,
      SpineFit (consList bs (consList as ρ))
          ((((d.tlss c ψ).getD j []).getD l []).map (·.2.2)) ts →
      SpineFit (consList as ρ) (d.IdsM (d.tgts c j l) ψ)
        ((((d.Eiss c ψ).getD j []).getD l []).map
          (interp V (consList ts (consList bs (consList as ρ))))))
    (hrec : ((d.rss c).getD j []).getD l false = true) :
    d.slotAt ψ (lfpTuple (d.w ψ) d.N (d.idx ψ (consList as ρ)) (d.Φ ψ (consList as ρ))) c j l
        (consList bs (consList as ρ))
      = interp V (consList bs (consList as ρ)) (((d.Fss c ψ).getD j []).getD l default) := by
  classical
  obtain ⟨-, -, hD⟩ := hcf
  obtain ⟨hj, -⟩ := List.getElem?_eq_some_iff.mp hcj
  have hlenD : (d.dsF c j ψ).length = d.nP + cA.2 := hD.len ψ
  have hFssD : (d.Fss c ψ).getD j [] = ((d.dsF c j ψ).drop d.nP).map (·.2.2) :=
    fssOfR_fixCtorDataList_getD hcj
  have hTlD : (d.tlss c ψ).getD j [] = d.tssF c j ψ := tlssOfR_fixCtorDataList_getD hcj
  have hEiD : (d.Eiss c ψ).getD j [] = d.eissF c j ψ := eissOfR_fixCtorDataList_getD hcj
  have hksLen : (d.ksF c j).length = cA.2 := hD.ksLen
  have hkind : (d.ksF c j).getD l .ordinary = .recursive
      ∨ (d.ksF c j).getD l .ordinary = .reflexive := by
    have hrs : (d.rss c).getD j [] = rsOf (d.ksF c j) := rssOfK_getD hj
    rw [hrs] at hrec
    exact (rsOf_getD_iff (by rw [hksLen]; exact hl)).mp hrec
  -- the frame, as one list
  have hfrm : consList bs (consList as ρ) = consList (as ++ bs) ρ := (consList_append as bs ρ).symm
  have hlenAB : (as ++ bs).length = d.nP + l := by rw [List.length_append, hasLen, hbs]
  have htakeAB : (as ++ bs).take d.nP = as := by
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  -- the leaf, at a fitting index spine
  have hleaf : ∀ is : List V, SpineFit (consList as ρ) (d.IdsM (d.tgts c j l) ψ) is →
      ∀ σ : Nat → V,
      (as ++ is).foldl app (interp V σ (mo.acval (d.memberName (d.tgts c j l)) ψ))
        = app (lfpTuple (d.w ψ) d.N (d.idx ψ (consList as ρ)) (d.Φ ψ (consList as ρ))
            (d.tgts c j l)) (tupW (d.uM (d.tgts c j l) ψ) is) := by
    intro is his σ
    rw [acval_interp_closedC mo (d.memberName (d.tgts c j l)) ψ σ ρ]
    exact hM.leaf (d.tgts c j l) htgt ψ ρ as is hps his
  rw [hFssD, drop_map_getD hlenD hl, BlockData.slotAt]
  rcases hkind with hk | hk
  · -- a FINITARY recursive field: an empty telescope
    have hnone : ((d.tlss c ψ).getD j []).getD l [] = [] := by
      rw [hTlD]
      exact hD.tssNone ψ l (by rw [hk]; intro hcon; cases hcon)
    have hentry : ((d.dsF c j ψ).getD (d.nP + l) default).2.2
        = AnnotTerm.mkAppN (mo.acval (d.memberName (d.tgts c j l)) ψ)
            (paramBvarsAt d.nP (d.nP + l) ++ ((d.Eiss c ψ).getD j []).getD l []) := by
      rw [hEiD]
      exact hD.recEntry ψ l hk hl
    have hfit0 := hEis [] (by rw [hnone]; trivial)
    simp only [consList_nil] at hfit0
    rw [hentry, hnone, slotSet_nil, interp_mkAppN, foldl_app_map, List.map_append, hfrm,
      map_bvarAt_take (hD := hlenAB.symm) (by omega), htakeAB]
    exact (hleaf _ (by rw [hfrm] at hfit0; exact hfit0) _).symm
  · -- a REFLEXIVE field: the nested product of the target's family
    have hentry : ((d.dsF c j ψ).getD (d.nP + l) default).2.2
        = mkPisAV (((d.tlss c ψ).getD j []).getD l [])
            (AnnotTerm.mkAppN (mo.acval (d.memberName (d.tgts c j l)) ψ)
              (paramBvarsAt d.nP (d.nP + l + ((((d.tlss c ψ).getD j []).getD l [])).length)
                ++ ((d.Eiss c ψ).getD j []).getD l [])) := by
      rw [hEiD, hTlD]
      exact hD.reflEntry ψ l hk hl
    have hbits : ∀ dd ∈ ((d.tlss c ψ).getD j []).getD l [], (dd.2.1 = 0 ↔ d.w ψ = 0) := by
      rw [hTlD]
      exact fun dd hdd => hD.tssBits ψ l dd hdd
    rw [hentry]
    unfold slotSet
    refine (interp_mkPisAV_piTele (v := d.w ψ) (acc := []) hbits ?_).symm
    intro ts hsp
    have htsLen : ts.length = ((((d.tlss c ψ).getD j []).getD l [])).length := by
      rw [hsp.length_eq, List.length_map]
    have hfrm2 : consList ts (consList bs (consList as ρ)) = consList (as ++ bs ++ ts) ρ := by
      rw [consList_append, consList_append]
    have hlenABT : (as ++ bs ++ ts).length
        = d.nP + l + ((((d.tlss c ψ).getD j []).getD l [])).length := by
      rw [List.length_append, hlenAB, htsLen]
    have htakeABT : (as ++ bs ++ ts).take d.nP = as := by
      rw [List.take_append_of_le_length (by rw [hlenAB]; omega), htakeAB]
    have hfit := hEis ts hsp
    rw [List.nil_append, interp_mkAppN, foldl_app_map, List.map_append, hfrm2,
      map_bvarAt_take (hD := hlenABT.symm) (by rw [hlenABT]; omega), htakeABT]
    exact hleaf _ (by rw [hfrm2] at hfit; exact hfit) _

/-- **§24's `hslot`, as a function of the run**: the agreement at
every recursive position, at every frame the walk reaches.  The only
thing the frame contributes is the prefix's LENGTH — the fitting
content is `hEis`, the field's index readings landing in the target
member's index telescope. -/
theorem blockSlot_agree {env : Env} {mo : EnvModel V env} {names : List Name}
    {d : BlockData V} (hM : BlockModelAt mo names d) {lps : List Name}
    {c j : Nat} {cA : ConstantVal × Nat} (hcj : (d.ctorsM c)[j]? = some cA)
    (hcf : BlockCtorFacts mo d lps c j cA)
    {ψ : Name → Nat} {ρ : Nat → V} {as : List V}
    (hasLen : as.length = d.nP) (hps : SpineFit ρ (d.params ψ) as)
    (htgt : ∀ l, l < cA.2 → d.tgts c j l < d.k)
    (hEis : ∀ l, l < cA.2 → ∀ bs : List V, bs.length = l → ∀ ts : List V,
      SpineFit (consList bs (consList as ρ))
          ((((d.tlss c ψ).getD j []).getD l []).map (·.2.2)) ts →
      SpineFit (consList as ρ) (d.IdsM (d.tgts c j l) ψ)
        ((((d.Eiss c ψ).getD j []).getD l []).map
          (interp V (consList ts (consList bs (consList as ρ)))))) :
    ∀ l, l < ((d.Fss c ψ).getD j []).length → ∀ bs : List V, bs.length = l →
      ((d.rss c).getD j []).getD l false = true →
      d.slotAt ψ (lfpTuple (d.w ψ) d.N (d.idx ψ (consList as ρ)) (d.Φ ψ (consList as ρ))) c j l
          (consList bs (consList as ρ))
        = interp V (consList bs (consList as ρ)) (((d.Fss c ψ).getD j []).getD l default) := by
  have hnF : ((d.Fss c ψ).getD j []).length = cA.2 := by
    obtain ⟨-, -, hD⟩ := hcf
    have hFssD : (d.Fss c ψ).getD j [] = ((d.dsF c j ψ).drop d.nP).map (·.2.2) :=
      fssOfR_fixCtorDataList_getD hcj
    rw [hFssD, List.length_map, List.length_drop, hD.len ψ]
    omega
  intro l hl bs hbs hrec
  rw [hnF] at hl
  exact blockSlot_eq_entry hM hcj hcf hasLen hps hl hbs (htgt l hl) (hEis l hl bs hbs) hrec

/-- **`hspF` at the run, with `hslot` discharged** — §24's assembly
over §25's identity. -/
theorem blockRecSpF_of {envC : Env} {mpC : EnvModelM V μ envC} {names : List Name}
    {d : BlockData V} (hM : BlockModelAt mpC.base2 names d) {lps : List Name}
    {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {i j K : Nat} {mem : Nat → Nat} {ψ : Name → Nat}
    {a ρ : Nat → V} {xs fs : List V} {t : V} {cA : ConstantVal × Nat}
    (hcj : (d.ctorsM (mem c))[j]? = some cA)
    (hcf : BlockCtorFacts mpC.base2 d lps (mem c) j cA)
    (hfd : blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i
      = liftDomsK (p.toBlockShape.rulePrefixAt c - d.nP) 0 ((d.Fss (mem c) ψ).getD j []))
    (hasLen : (xs.take d.nP).length = d.nP)
    (hps : SpineFit ρ (d.params ψ) (xs.take d.nP))
    (htgt : ∀ l, l < cA.2 → d.tgts (mem c) j l < d.k)
    (hEis : ∀ l, l < cA.2 → ∀ bs : List V, bs.length = l → ∀ ts : List V,
      SpineFit (consList bs (consList (xs.take d.nP) ρ))
          ((((d.tlss (mem c) ψ).getD j []).getD l []).map (·.2.2)) ts →
      SpineFit (consList (xs.take d.nP) ρ) (d.IdsM (d.tgts (mem c) j l) ψ)
        ((((d.Eiss (mem c) ψ).getD j []).getD l []).map
          (interp V (consList ts (consList bs (consList (xs.take d.nP) ρ))))))
    (hxs : xs.length = p.toBlockShape.rulePrefixAt c)
    (hpref : SpineFit (chainFrame K a ρ)
      (blockRecPdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c) xs)
    (hfit : d.ChainFit ψ (consList (xs.take d.nP) ρ)
      (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
        (d.Φ ψ (consList (xs.take d.nP) ρ))) t (mem c) j fs) :
    SpineFit (chainFrame K a ρ)
      (blockRecPdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c
        ++ blockRecFdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c i) (xs ++ fs) :=
  blockRecSpF hμ h hr hfd
    (fun l hl bs hb hrb => blockSlot_agree hM hcj hcf hasLen hps htgt hEis l hl bs
      (by have := hb.length_eq; rw [List.length_take] at this; omega) hrb)
    hxs hpref hfit

/-- **`hctorAt`'s fit half at the run, with `hslot` discharged.** -/
theorem blockRecCtorFitsFrom_of {envC : Env} {mpC : EnvModelM V μ envC} {names : List Name}
    {d : BlockData V} (hM : BlockModelAt mpC.base2 names d) {lps : List Name}
    {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {i j K : Nat} {mem : Nat → Nat} {ψ : Name → Nat}
    {a ρ : Nat → V} {xs fs : List V} {cA : ConstantVal × Nat}
    (hcj : (d.ctorsM (mem c))[j]? = some cA)
    (hcf : BlockCtorFacts mpC.base2 d lps (mem c) j cA)
    (hfd : blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i
      = liftDomsK (p.toBlockShape.rulePrefixAt c - d.nP) 0 ((d.Fss (mem c) ψ).getD j []))
    (hasLen : (xs.take d.nP).length = d.nP)
    (hps : SpineFit ρ (d.params ψ) (xs.take d.nP))
    (htgt : ∀ l, l < cA.2 → d.tgts (mem c) j l < d.k)
    (hEis : ∀ l, l < cA.2 → ∀ bs : List V, bs.length = l → ∀ ts : List V,
      SpineFit (consList bs (consList (xs.take d.nP) ρ))
          ((((d.tlss (mem c) ψ).getD j []).getD l []).map (·.2.2)) ts →
      SpineFit (consList (xs.take d.nP) ρ) (d.IdsM (d.tgts (mem c) j l) ψ)
        ((((d.Eiss (mem c) ψ).getD j []).getD l []).map
          (interp V (consList ts (consList bs (consList (xs.take d.nP) ρ))))))
    (hxs : xs.length
      = (blockRecPdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c).length)
    (hsp : SpineFit (chainFrame K a ρ)
      (blockRecPdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c
        ++ blockRecFdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c i) (xs ++ fs)) :
    FitsFrom ((d.rss (mem c)).getD j []) (d.slotAt ψ
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) (mem c) j) 0
      (consList (xs.take d.nP) ρ) ((d.Fss (mem c) ψ).getD j []) fs :=
  blockRecCtorFitsFrom hμ h hr hfd
    (fun l hl bs hb hrb => blockSlot_agree hM hcj hcf hasLen hps htgt hEis l hl bs
      (by have := hb.length_eq; rw [List.length_take] at this; omega) hrb)
    hxs hsp

end SlotEntry

/-! ## 26. `hctorAt`'s INDEX half (session 8)

`ChainFit`'s second conjunct asks that the constructor's result index
readings BE the components of the tuple the rule picks
(`d.tup ψ (mem c) e⃗`).  Three moves, and only the first is new here:

* `projS_tupW` — the tuple's retraction, at BOTH index regimes: at
  `u ≠ 0` it is `projS_mkTower`, at `u = 0` the tuple is the point and
  every index value is the point too (`projS_pt`,
  `spineFit_pt_of_bound0`).  The tree had this only inside
  `EqAll_eqsXI`'s proof;
* `interp_liftN_rule` (§23) at the index expressions, which are single
  forms rather than a binder list;
* RM11's `es0` (`blockRuleEsAV_eq`) composed with the record's
  `Es`/`Ess` identification, a named premise here. -/

section CtorIdx

/-- **The index tuple's retraction**, at both regimes — `EqAll_eqsXI`'s
own `hproj`, as a lemma. -/
theorem projS_tupW {u : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} (hI : IdxOk u ρp Ids)
    {is : List V} (hsp : SpineFit ρp Ids is) {l : Nat} (hl : l < Ids.length) :
    projS l (tupW u is) = is.getD l pt := by
  have hislen : is.length = Ids.length := hsp.length_eq
  by_cases hu : u = 0
  · subst hu
    rw [tupW_zero, projS_pt, spineFit_pt_of_bound0 hI.2 hsp l (by omega)]
  · rw [tupW_pos hu, projS_mkTower l is (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega), Option.getD_some]

/-- **`hctorAt`'s second conjunct at the run**: the constructor's
result index readings are the components of the rule's index tuple. -/
theorem blockRecCtorIdx {envC : Env} {mpC : EnvModelM V μ envC} {d : BlockData V}
    {p : ConLeche.BlockParts}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {c i j K : Nat} {mem : Nat → Nat} {ψ : Name → Nat} {a ρ : Nat → V} {xs fs : List V}
    {cA : ConstantVal × Nat}
    (hes : blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ c i
      = ((d.Ess (mem c) ψ).getD j []).map (·.liftN (p.toBlockShape.rulePrefixAt c - d.nP) cA.2))
    (hpl : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
      = p.toBlockShape.rulePrefixAt c)
    (hfl : (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i).length = cA.2)
    (hxs : xs.length = p.toBlockShape.rulePrefixAt c) (hfs : fs.length = cA.2)
    (hEsLen : ((d.Ess (mem c) ψ).getD j []).length = (d.IdsM (mem c) ψ).length)
    (hIdx : IdxOk (d.uM (mem c) ψ) (consList (xs.take d.nP) ρ) (d.IdsM (mem c) ψ))
    (hEsFit : SpineFit (consList (xs.take d.nP) ρ) (d.IdsM (mem c) ψ)
      ((blockRecEsK K mpC.base2.acval envC p.toBlockShape rs ψ c i).map
        (interp V (consList (xs ++ fs) (chainFrame K a ρ))))) :
    ∀ l, l < (d.IdsM (mem c) ψ).length →
      interp V (consList fs (consList (xs.take d.nP) ρ))
          (((d.Ess (mem c) ψ).getD j []).getD l default)
        = projS l (d.tup ψ (mem c)
            ((blockRecEsK K mpC.base2.acval envC p.toBlockShape rs ψ c i).map
              (interp V (consList (xs ++ fs) (chainFrame K a ρ))))) := by
  intro l hl
  have hlt : l < ((d.Ess (mem c) ψ).getD j []).length := by rw [hEsLen]; exact hl
  have hmapGetD : ∀ (L : List AnnotTerm) (G : AnnotTerm → V), l < L.length →
      (L.map G).getD l pt = G (L.getD l default) := by
    intro L G hL
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hL,
      Option.map_some, Option.getD_some, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hL, Option.getD_some]
  have hEsK : blockRecEsK K mpC.base2.acval envC p.toBlockShape rs ψ c i
      = ((d.Ess (mem c) ψ).getD j []).map fun e =>
          (e.liftN (p.toBlockShape.rulePrefixAt c - d.nP) cA.2).liftN K
            (p.toBlockShape.rulePrefixAt c + cA.2) := by
    rw [blockRecEsK, hes, List.map_map, hpl, hfl]
    rfl
  rw [BlockData.tup, projS_tupW hIdx hEsFit hl, hEsK, List.map_map, hmapGetD _ _ hlt]
  exact (interp_liftN_rule (nP := d.nP) hxs hfs _).symm

end CtorIdx

end ConLeche.Model

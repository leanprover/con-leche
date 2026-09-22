module

import ConLeche.Model.Inductives.BlockRecTyping
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Annot.BitRename
import ConLeche.Model.Inductives.BlockRecOpenerRead
import ConLeche.Verify.Inductives.BlockRecInv
public import ConLeche.Semantics.Tower.BlockRecSqI
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
is graded); it is a PREMISE here, in the spelling its owners export.

Its second argument is the checker's FUEL, not a frame depth — the
audit's item 8, where the same letter `F` means the rule frame's depth
on the rule lane; the binder is `fuel` here so the two cannot be
confused when a producer meets both. -/

/-- **One rule's certificates**: everything `residueOk_blockFrame`
needs that does not mention the frame. -/
def BlockRuleCerts (V : Type w) [SetTheory V] {μ : CheckMode} {envT : Env}
    (mp : EnvModelM V μ envT) (fuel : Nat) (ψ : Name → Nat) (rP nF nR : Nat)
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
    ConLeche.inferTypeCore μ envT fuel (rP + nF + nR) bodyO = .ok ty ∧
    ConLeche.isDefEqCore μ envT fuel (rP + nF + nR) ty concl = .ok true ∧
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
    {mpC : EnvModelM V μ envC} {mp : EnvModelM V μ envT} {F : Nat}
    {s : (Name → Nat) → Nat}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {rP : Nat → Nat} {pdoms : (Name → Nat) → Nat → List AnnotTerm}
    {fdoms es ihdoms : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {mk : (Name → Nat) → Nat → Nat → AnnotTerm}
    {ihs : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {Rb Ca : (Name → Nat) → Nat → Nat → AnnotTerm}
    (hTy : ∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ c, c < rs.length →
      interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c) ∈ˢ (univ (s ψ) : V) ∧
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
      BlockRecPre V (s ψ) rs.length (blockRecTyAV mpC.base2.acval envC rs ψ)
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
    htgts ?_ hparams ?_ (fun ψ c j hj => hFssD ψ c j _ (hcAof c j hj)) ?_ hparamsC ?_ ?_
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
  -- the constructors' RESULT index readings fit the component's telescope
  · intro ψ ρ hsat c hc j hj fs hfs
    have hjc := hcAof c j hj
    have hfr := hS.frames c (by rw [← hNk]; exact hc) j _ hjc
    have hFs : SpineFit ρ (((d.dsF c j ψ).drop d.nP).map (·.2.2)) fs := by
      rw [← hFssD ψ c j _ hjc]; exact hfs
    have hq := (hfr.2 ψ ρ ((hfr.1 ψ ρ).mp ((hparams ψ c hc ρ).mp hsat))).2.2 fs hFs
    rw [show (d.Ess c ψ).getD j [] = d.esF c j ψ from essOfR_fixCtorDataList_getD hjc]
    exact hq

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
    (ihv : List V → Nat → Nat → List V → V → List V) (xs : List V) (u g : V) : V :=
  interp V
    (consList (ihv xs (tagDec K u).1 (blockDecTag K d ψ ρ mem xs u).1
        (blockDecTag K d ψ ρ mem xs u).2 g)
      (consList (xs ++ (blockDecTag K d ψ ρ mem xs u).2) ρ))
    (Rb0 (tagDec K u).1 (blockDecTag K d ψ ρ mem xs u).1)

/-- **The step at a CONSTRUCTED element**: the decomposition reads back
the constructor and the fields, so the step is the rule's residue at
the rule's own spine — the ι law's right-hand side. -/
theorem blockRecStep_at (hM : BlockModelAt mo names d) {K : Nat} {ψ : Name → Nat} {ρ : Nat → V}
    {mem : Nat → Nat} {Rb0 : Nat → Nat → AnnotTerm}
    {ihv : List V → Nat → Nat → List V → V → List V} {xs : List V} (hw : d.w ψ ≠ 0)
    {c : Nat} (hc : c < K) (hmemN : mem c < d.N) {i : V} {j : Nat} {fs : List V}
    (hj : j < (d.ctorsM (mem c)).length)
    (hfit : d.ChainFit ψ (consList (xs.take d.nP) ρ)
      (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
        (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs)
    (g : V) :
    blockRecStep K d ψ ρ mem Rb0 ihv xs (tagged c i (d.inj ψ (mem c) j fs)) g
      = interp V (consList (ihv xs c j fs g) (consList (xs ++ fs) ρ)) (Rb0 c j) := by
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
  {ihv : List V → Nat → Nat → List V → V → List V} {envT : Env} {mp : EnvModelM V μ envT} {F : Nat}
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
      SpineFit (consList (xs ++ fs) ρ) (ihdoms c j) (ihv xs c j fs g))
    (hCaB : ∀ c, c < K → SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs → ∀ g : V,
      interp V (consList (ihv xs c j fs g) (consList (xs ++ fs) ρ)) (Ca c j)
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
  {ihv : List V → Nat → Nat → List V → V → List V} {envT : Env} {mp : EnvModelM V μ envT} {F : Nat}

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
      SpineFit (consList (xs ++ fs) ρ) (ihdoms c j) (ihv xs c j fs g))
    (hCaB : ∀ xs : List V, ∀ c, c < K →
      SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs → ∀ g : V,
      interp V (consList (ihv xs c j fs g) (consList (xs ++ fs) ρ)) (Ca c j)
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
  {Rb0 : Nat → Nat → AnnotTerm} {ihv : List V → Nat → Nat → List V → V → List V}

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
        = interp V (consList (ihv xs c j fs g) (consList (xs ++ fs) ρ)) (Rb0 c j))
    (hihChain : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (famCand D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      ihv xs c j fs
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
        = interp V (consList (ihv xs c j fs g) (consList (xs ++ fs) ρ)) (Rb0 c j) := by
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
  {ihv : List V → Nat → Nat → List V → V → List V} {src : Nat → List (Option Nat)}

/-- **Regime SQ's step**: the rule's residue read at the SOURCE spine
— the fields recovered from the tagged element's INDEX, the major
being the point. -/
@[expose] noncomputable def blockSqStep (K : Nat) (d : BlockData V) (ψ : Name → Nat)
    (ρ : Nat → V) (mem : Nat → Nat) (src : Nat → List (Option Nat))
    (Rb0 : Nat → Nat → AnnotTerm) (ihv : List V → Nat → Nat → List V → V → List V) (xs : List V)
    (u g : V) : V :=
  interp V
    (consList
      (ihv xs (tagDec K u).1 0
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
      = interp V (consList (ihv xs c 0 fs g) (consList (xs ++ fs) ρ)) (Rb0 c 0) := by
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
        = interp V (consList (ihv xs c j fs g) (consList (xs ++ fs) ρ)) (Rb0 c j) := by
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
    (ihv : List V → Nat → Nat → List V → V → List V),
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
        = interp V (consList (ihv xs c j fs g) (consList (xs ++ fs) ρ)) (Rb0 c j)) ∧
    (∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (famCand D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      ihv xs c j fs
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
at the lanes' shared choice of `K`, `nCt` and `eqs`.  BOTH levels
depend on the level assignment: the family's elimination level (the
guard is `ℓ ψ`) and the CHAIN's level `s ψ` — the latter since
session 11, the audit's item 4.  One numeral for the whole block is
refutable at any level-polymorphic family (the parameters' sorts carry
the level parameter even at a `Prop` motive), and the assembly already
consumes `hpre` at `s ψ`; §21's `blockRecTy_univ_run` produces `s` in
the shape `maxLevelEval us`, a function of `ψ` only through
`Level.eval`. -/
theorem blockRecPre_hpre {envC : Env} {mpC : EnvModelM V μ envC} {s : (Name → Nat) → Nat}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {ℓ : (Name → Nat) → Nat} {rP : Nat → Nat}
    {rds : (Name → Nat) → Nat → List (Nat × Nat × AnnotTerm)}
    {concl : (Name → Nat) → Nat → AnnotTerm} {pdoms : (Name → Nat) → Nat → List AnnotTerm}
    {fdoms es : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {mk : (Name → Nat) → Nat → Nat → AnnotTerm}
    {ihs : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm}
    (hTy : ∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ c, c < rs.length →
      interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c) ∈ˢ (univ (s ψ) : V) ∧
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
      BlockRecPre V (s ψ) rs.length (blockRecTyAV mpC.base2.acval envC rs ψ)
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
  {Rb0 Ca : Nat → Nat → AnnotTerm} {ihv : List V → Nat → Nat → List V → V → List V}
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
      SpineFit (consList (xs ++ fs) ρ) (ihdoms c j) (ihv xs c j fs g))
    (hCaB : ∀ xs : List V, ∀ c, c < K →
      SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs → ∀ g : V,
      interp V (consList (ihv xs c j fs g) (consList (xs ++ fs) ρ)) (Ca c j)
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
      ihv xs c j fs
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

/-- **The family's level, as a FUNCTION of the level assignment**: the
max of the `Level`s the check inferred for the `K` recursor types.
Each `u` is a level EXPRESSION the run fixed once (ψ-independent), so
this is a function of `ψ` only through `Level.eval` — which is what
makes a consumer's `s ψ₁ = s ψ₂` (at assignments agreeing on the
block's level parameters) provable. -/
@[expose] def maxLevelEval (us : List Level) (ψ : Name → Nat) : Nat :=
  (us.map fun u => u.eval ψ).foldr Nat.max 0

theorem maxLevelEval_cons (u : Level) (us : List Level) (ψ : Name → Nat) :
    maxLevelEval (u :: us) ψ = Nat.max (u.eval ψ) (maxLevelEval us ψ) := rfl

/-- **A uniform universe for finitely many members, by cumulativity**
— at a level that is a FUNCTION of the assignment, because a
level-polymorphic family's types live at a `ψ`-dependent universe
(the audit's item 4: one numeral for the whole block is refutable at
any block with a level parameter, the parameters' sorts carrying it
even at a `Prop` motive). -/
theorem exists_uniform_univ {n : Nat} {g : (Name → Nat) → Nat → (Nat → V) → V}
    (h : ∀ c, c < n → ∃ u : Level, ∀ (ψ : Name → Nat) (ρ : Nat → V),
      g ψ c ρ ∈ˢ (univ (u.eval ψ) : V)) :
    ∃ us : List Level, ∀ c, c < n → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      g ψ c ρ ∈ˢ (univ (maxLevelEval us ψ) : V) := by
  induction n with
  | zero => exact ⟨[], fun c hc => absurd hc (Nat.not_lt_zero c)⟩
  | succ n ih =>
    obtain ⟨us₀, hs₀⟩ := ih fun c hc => h c (Nat.lt_succ_of_lt hc)
    obtain ⟨u₁, hs₁⟩ := h n (Nat.lt_succ_self n)
    refine ⟨u₁ :: us₀, fun c hc ψ ρ => ?_⟩
    rw [maxLevelEval_cons]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc' | rfl
    · exact univ_mono (Nat.le_max_right _ _) _ (hs₀ c hc' ψ ρ)
    · exact univ_mono (Nat.le_max_left _ _) _ (hs₁ ψ ρ)

/-- **`hTy` at the run, with the level the CHECK chose.**  The family's
level is the max of the `K` inferred sorts, each of them a `Level` the
run fixed; every recursor type's reading lands in it by cumulativity,
and its grading is the same run's. -/
theorem blockRecTy_univ_run {envC : Env} (hμ : μ.verifiedChecks = true)
    (mpC : EnvModelM V μ envC) {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs) :
    ∃ us : List Level, ∀ (ψ : Name → Nat) (c : Nat), c < rs.length → ∀ ρ : Nat → V,
      interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c)
          ∈ˢ (univ (maxLevelEval us ψ) : V) ∧
        WellDenoted V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c) := by
  have hmem : ∀ c, c < rs.length → ∃ u : Level, ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c) ∈ˢ (univ (u.eval ψ) : V) := by
    intro c hc
    obtain ⟨u, hru⟩ := checkBlockRecK_tyReads (V := V) hμ mpC h rs[c] (List.getElem_mem hc)
    refine ⟨u, fun ψ ρ => ?_⟩
    obtain ⟨ta, hta, -, hu⟩ := hru ψ
    rw [blockRecTyAV_eq (List.getElem?_eq_getElem hc) hta]
    exact hu ρ
  obtain ⟨us, hs⟩ := exists_uniform_univ hmem
  refine ⟨us, fun ψ c hc ρ => ⟨hs c hc ψ ρ, ?_⟩⟩
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
record's `ds`/`Fss` identification — §27's `blockRuleFdomsAV_datum`
since session 10 — and `hslot` is the slot-to-domain
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
      FitsFrom ((d.rss (mem c)).getD j []) (d.slotAt ψ X (mem c) j) 0
        (consList (xs.take d.nP) ρ) (((d.Fss (mem c) ψ).getD j []).take l) bs →
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
    (hSF : SlotFit (d.uM (d.tgts c j l) ψ) (d.w ψ) (consList as ρ) (d.IdsM (d.tgts c j l) ψ)
      (((d.tlss c ψ).getD j []).getD l []) (((d.Eiss c ψ).getD j []).getD l []) bs)
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
    have hfit0 := (hSF.2.2 [] (by rw [hnone]; trivial)).2
    simp only [List.append_nil] at hfit0
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
    have hfit := (hSF.2.2 ts hsp).2
    rw [consList_append] at hfit
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
    (hc : c < d.N) (hj : j < (d.ctorsM c).length) {_t : V}
    (ht : _t ∈ˢ d.idx ψ (consList as ρ) c)
    (hX : InTupleSpace (d.w ψ) d.N (d.idx ψ (consList as ρ))
      (lfpTuple (d.w ψ) d.N (d.idx ψ (consList as ρ)) (d.Φ ψ (consList as ρ)))) :
    ∀ l, l < ((d.Fss c ψ).getD j []).length → ∀ bs : List V,
      FitsFrom ((d.rss c).getD j [])
        (d.slotAt ψ (lfpTuple (d.w ψ) d.N (d.idx ψ (consList as ρ)) (d.Φ ψ (consList as ρ))) c j)
        0 (consList as ρ) (((d.Fss c ψ).getD j []).take l) bs →
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
  intro l hl bs hb hrec
  have hbs : bs.length = l := by
    have := hb.length_eq
    rw [List.length_take] at this
    omega
  have hSF := hM.idxFit ψ (consList as ρ) (d.satOfSpine hps) _ hX c hc _t ht j hj l hl hrec bs hb
  rw [hnF] at hl
  exact blockSlot_eq_entry hM hcj hcf hasLen hps hl hbs (htgt l hl) hSF hrec

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
    (hcN : mem c < d.N) (hj : j < (d.ctorsM (mem c)).length)
    (ht : t ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (mem c))
    (hX : InTupleSpace (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
      (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
        (d.Φ ψ (consList (xs.take d.nP) ρ))))
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
    (fun l hl bs hb hrb =>
      blockSlot_agree hM hcj hcf hasLen hps htgt hcN hj ht hX l hl bs hb hrb)
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
    (hcN : mem c < d.N) (hj : j < (d.ctorsM (mem c)).length) {t : V}
    (ht : t ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (mem c))
    (hX : InTupleSpace (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
      (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
        (d.Φ ψ (consList (xs.take d.nP) ρ))))
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
    (fun l hl bs hb hrb =>
      blockSlot_agree hM hcj hcf hasLen hps htgt hcN hj ht hX l hl bs hb hrb)
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
  `Es`/`Ess` identification, the ONE named premise left here.

Session 10: the retraction's own hypothesis — that the result index
readings FIT the member's index telescope — is no longer a premise
either.  It is `BlockModelAt.resIdxFit`, the constructor's typing read
off the representation, and it is `idxFit` one position along (§25's
is at a recursive FIELD, this one at the RESULT). -/

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
result index readings are the components of the rule's index tuple.

Since session 10 the fit of those readings in the member's own index
telescope is not a premise but `BlockModelAt.resIdxFit` — the
constructor's typing, read off the representation — so the theorem's
only named premise is RM11's `es0` (`blockRuleEsAV_eq`) composed with
the record's `Es`/`Ess` identification. -/
theorem blockRecCtorIdx {envC : Env} {mpC : EnvModelM V μ envC} {d : BlockData V}
    {names : List Name} {p : ConLeche.BlockParts}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {c i j K : Nat} {mem : Nat → Nat} {ψ : Name → Nat} {a ρ : Nat → V} {xs fs : List V}
    {cA : ConstantVal × Nat}
    (hM : BlockModelAt mpC.base2 names d)
    (hes : blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ c i
      = ((d.Ess (mem c) ψ).getD j []).map (·.liftN (p.toBlockShape.rulePrefixAt c - d.nP) cA.2))
    (hpl : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
      = p.toBlockShape.rulePrefixAt c)
    (hfl : (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i).length = cA.2)
    (hxs : xs.length = p.toBlockShape.rulePrefixAt c) (hfs : fs.length = cA.2)
    (hmem : mem c < d.N) (hjc : j < (d.ctorsM (mem c)).length)
    (hps : SpineFit ρ (d.params ψ) (xs.take d.nP))
    (hsf : SpineFit (consList (xs.take d.nP) ρ) ((d.Fss (mem c) ψ).getD j []) fs) :
    ∀ l, l < (d.IdsM (mem c) ψ).length →
      interp V (consList fs (consList (xs.take d.nP) ρ))
          (((d.Ess (mem c) ψ).getD j []).getD l default)
        = projS l (d.tup ψ (mem c)
            ((blockRecEsK K mpC.base2.acval envC p.toBlockShape rs ψ c i).map
              (interp V (consList (xs ++ fs) (chainFrame K a ρ))))) := by
  have hsat : Sat V (d.params ψ).reverse (consList (xs.take d.nP) ρ) := d.satOfSpine hps
  have hIdx : IdxOk (d.uM (mem c) ψ) (consList (xs.take d.nP) ρ) (d.IdsM (mem c) ψ) :=
    hM.idxOk ψ _ hsat (mem c) hmem
  have hres := hM.resIdxFit ψ _ hsat (mem c) hmem j hjc fs hsf
  have hEsLen : ((d.Ess (mem c) ψ).getD j []).length = (d.IdsM (mem c) ψ).length := by
    have hq := hres.length_eq
    rwa [List.length_map] at hq
  have hEsK : blockRecEsK K mpC.base2.acval envC p.toBlockShape rs ψ c i
      = ((d.Ess (mem c) ψ).getD j []).map fun e =>
          (e.liftN (p.toBlockShape.rulePrefixAt c - d.nP) cA.2).liftN K
            (p.toBlockShape.rulePrefixAt c + cA.2) := by
    rw [blockRecEsK, hes, List.map_map, hpl, hfl]
    rfl
  have hmapEq : (blockRecEsK K mpC.base2.acval envC p.toBlockShape rs ψ c i).map
        (interp V (consList (xs ++ fs) (chainFrame K a ρ)))
      = ((d.Ess (mem c) ψ).getD j []).map
          (interp V (consList fs (consList (xs.take d.nP) ρ))) := by
    rw [hEsK, List.map_map]
    exact List.map_congr_left fun e _ => interp_liftN_rule (nP := d.nP) hxs hfs e
  have hEsFit : SpineFit (consList (xs.take d.nP) ρ) (d.IdsM (mem c) ψ)
      ((blockRecEsK K mpC.base2.acval envC p.toBlockShape rs ψ c i).map
        (interp V (consList (xs ++ fs) (chainFrame K a ρ)))) := by
    rw [hmapEq]; exact hres
  intro l hl
  have hlt : l < ((d.Ess (mem c) ψ).getD j []).length := by rw [hEsLen]; exact hl
  have hmapGetD : ∀ (L : List AnnotTerm) (G : AnnotTerm → V), l < L.length →
      (L.map G).getD l pt = G (L.getD l default) := by
    intro L G hL
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hL,
      Option.map_some, Option.getD_some, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hL, Option.getD_some]
  rw [BlockData.tup, projS_tupW hIdx hEsFit hl, hEsK, List.map_map, hmapGetD _ _ hlt]
  exact (interp_liftN_rule (nP := d.nP) hxs hfs _).symm

end CtorIdx

/-! ## 27. `hfd` — the rule's field domains ARE the constructor's
(session 10)

The last named premise of §24 (and so of `hspF` and of `hctorAt`'s fit
half).  RM11's `blockRuleFdomsAV_eq` already says that the rule's
field domains are the CONSTRUCTOR's own binder readings lifted past
the recursor prefix's extra `rP − nP` binders; what it states them at
is the `BlockCtorDataI` record's `ds`, and what the consumer wants is
the datum's `d.Fss`.  The two are the same list
(`fssOfR_fixCtorDataList_getD`: the datum's field chain at
constructor `j` IS `d.dsF` dropped past the parameters), so the
composition is a rewrite.

Its inputs are the stage's: `BlockCtorsCore` supplies both the
constructor's reading record and — through the stored `ctorInfo` and
the environment's well-formedness — the fvar-freeness of its type,
which `blockRuleFdomsAV_eq` asks for and nothing else in the run
carries.  The rule's constructor and the member's are named by the
SAME `cA` (`blockRecMkK_value`'s pattern), so no equation between the
two positions `i` and `j` is needed. -/

section RuleFdoms

/-- **`hfd` at the run**: the rule's field domains are the datum's own
field chain, lifted past the recursor prefix's extra binders. -/
theorem blockRuleFdomsAV_datum {envC : Env} {mpC : EnvModelM V μ envC} {d : BlockData V}
    {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {lps : List Name} {cvTasAll : List ConstantVal} {p₁ : ConLeche.BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm}
    (hcore : BlockCtorsCore mpC.base2 d lps cvTasAll p₁ isRec A d.k)
    {mem : Nat → Nat} {j : Nat} (hmemk : mem c < d.k)
    (hcj : (d.ctorsM (mem c))[j]? = some cA)
    (hnP : p.nP ≤ p.toBlockShape.rulePrefixAt c) (hdnP : d.nP = p.nP) (ψ : Name → Nat) :
    blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i
      = liftDomsK (p.toBlockShape.rulePrefixAt c - d.nP) 0 ((d.Fss (mem c) ψ).getD j []) := by
  have hfind := (hcore.2.2.2 (mem c) hmemk j cA hcj).1
  have hCf : cA.1.type.hasFvar = false :=
    (mpC.base2.wf _ (List.mem_of_find?_eq_some hfind)).1
  have hcd := (hcore.2.2.1 (mem c) j cA hcj).2.2
  rw [hdnP] at hcd
  have hF : (d.Fss (mem c) ψ).getD j [] = ((d.dsF (mem c) j ψ).drop d.nP).map (·.2.2) :=
    fssOfR_fixCtorDataList_getD hcj
  rw [blockRuleFdomsAV_eq h hr hcA hrhs hcd hCf hnP ψ, hF, hdnP]

end RuleFdoms

/-! ## 28. The `K` lifts of §20 are the IDENTITY (audit item 5)

The guard the kit reads back (`blockRecIs_fits`, §3) is
`SpineFit ρ (pdoms c) xs` at the BASE frame, while the bridges that
discharge it (`blockRecSpF_of`, `blockRecCtorFitsFrom_of`) hold at the
CHAIN frame; §20 instantiates `pdoms := blockRecPdomsK K … =
liftDomsK K 0 (blockRulePdomsAV …)`, a form lifted past the `K` chain
binders.  `spineFit_liftDomsK` relates the chain-frame LIFTED data to
the base-frame UNLIFTED data; it says nothing about the base frame at
the lifted data.

The gap is not real, and this section says why: every rule datum is
the reading of a CLOSED expression at its own depth, so the `l`-th
binder domain mentions no variable at or above `l`
(`bvarsBelow_of_reading`), and a lift at a cutoff above a term's bound
is the identity (`AnnotTerm.liftN_eq_self`).  `liftDomsK` walks the
list raising the cutoff by one per entry, which is exactly the shape
that bound has, so the whole list is fixed.

The boundedness itself is a named premise here, in the positional
shape `liftDomsK` needs.  Its producer is the run:
`checkBlockRecK_tyPis`' binder clause reads the `l`-th opener's stored
type at DEPTH `l`, and `bvarsBelow_of_reading`
(`Model/Inductives/StructFrames.lean`) turns a reading at depth `l`
into `bvarsBelow l` — what it still wants is the openers' own scoping
facts, which the tyPis theorem does not currently return. -/

section LiftIdentity

/-- **A lift above a telescope's own bounds is the identity.**  Entry
`l` of `liftDomsK K k Ds` is lifted at the cutoff `k + l`, so a list
whose `l`-th entry is bounded below `k + l` is fixed. -/
theorem liftDomsK_eq_self_of_bounded {K : Nat} :
    ∀ (k : Nat) (Ds : List AnnotTerm),
      (∀ l, l < Ds.length → Term.bvarsBelow (k + l) ((Ds.getD l default).erase)) →
      liftDomsK K k Ds = Ds
  | _, [], _ => rfl
  | k, D :: Ds, h => by
    have h0 : Term.bvarsBelow k D.erase := by
      have hq := h 0 (Nat.succ_pos _)
      rwa [Nat.add_zero] at hq
    show AnnotTerm.liftN K D k :: liftDomsK K (k + 1) Ds = D :: Ds
    rw [AnnotTerm.liftN_eq_self D h0 K]
    refine congrArg (D :: ·) (liftDomsK_eq_self_of_bounded (k + 1) Ds fun l hl => ?_)
    have hq := h (l + 1) (by simpa using hl)
    rw [show k + (l + 1) = k + 1 + l from by omega] at hq
    simpa using hq

/-- **§20's prefix domains are the base form.**  `blockRecPdomsK` is
`blockRulePdomsAV` — the `K` lift does nothing to a telescope read at
its own depths — so the guard and the bridges are at the same data. -/
theorem blockRecPdomsK_eq {envC : Env} {mpC : EnvModelM V μ envC} {K : Nat}
    {p : ConLeche.BlockParts}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {ψ : Name → Nat} {c : Nat}
    (hb : ∀ l, l < (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length →
      Term.bvarsBelow l
        (((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).getD l default).erase)) :
    blockRecPdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c
      = blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c := by
  rw [blockRecPdomsK]
  exact liftDomsK_eq_self_of_bounded 0 _ (by simpa using hb)

/-- **`hpdE` at the run** (session 7's outstanding item): the rule
prefix's domains ARE the recursor type's first `rP c` binder domains.
Off §28's collapse, `blockRulePdomsAV`'s definition and
`List.map_take`. -/
theorem blockRecHpdE {envC : Env} {mpC : EnvModelM V μ envC} {K : Nat}
    {p : ConLeche.BlockParts}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {ψ : Name → Nat} {c : Nat}
    (hb : ∀ l, l < (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length →
      Term.bvarsBelow l
        (((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).getD l default).erase)) :
    blockRecPdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c
      = ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2)).take
          (p.toBlockShape.rulePrefixAt c) := by
  rw [blockRecPdomsK_eq hb, blockRulePdomsAV, List.map_take]

end LiftIdentity

/-! ## 29. The rule's CONCLUSION, peeled — and `hCaB` (session 12)

`BlockRuleCerts` carries `denoteMeta … concl = some Ca` with `concl`
EXISTENTIALLY quantified (session 10's finding), so no consumer can
say what `Ca` is.  `checkBlockRule` says: the recursor's TYPE
instantiated at the rule's prefix openers, the constructor's result
index arguments and the fired major
(`checkBlockRule_data`'s `instPisAtLift` clause).

**What the bundle carries is that form PAST THE PEEL.**
`denoteMeta_instPisAtLift_peel` turns the check's `instPisAtLift` into
`AnnotTerm.peelPis` of the recursor type's READING along the
arguments' readings, and those are: the prefix openers' — bvars, by
`denoteMeta`'s fvar clause at `openPisAtFvars_index`, which is
`paramBvarsAt rP (rP + nF + nR)` on the nose — the index arguments'
(`esA`) and the fired spine's (`mkA`).  Stating the peeled form makes
the producer pay for the peel's four side conditions (the arguments'
scoping, their bvar-closedness, the `DenoteMetaSpine`, the type's
reading) once, where they live, instead of making the bundle carry
them for a single consumer.

It is a SEPARATE bundle from `BlockRuleCerts` on purpose: the six
sites that STATE the certificates (the two regimes, the kit, the kit
family, `IndRegimeAt`, the WF assembly) never read the conclusion's
shape, and threading three more components through them would be the
over-quantification this lane has repaired ten times.  Both bundles
have the same producer and the same run. -/

section RuleConcl

/-- **The rule's conclusion, in the read currency.** -/
@[expose] def BlockRuleConclAt (rP nF nR : Nat) (RecTy : AnnotTerm)
    (esA : List AnnotTerm) (mkA Ca : AnnotTerm) : Prop :=
  ConLeche.Model.AnnotTerm.peelPis RecTy
    (paramBvarsAt rP (rP + nF + nR) ++ esA ++ [mkA]) = some Ca

omit [SetTheory V] in
theorem paramBvarsAt_length (nP D : Nat) : (paramBvarsAt nP D).length = nP := by
  simp [paramBvarsAt]

/-- **`hCaB`'s frame evaluation**: the rule's conclusion read at the
rule's own frame (the prefix, the fields and the `ih` openers' values)
is the recursor's conclusion read at the spine the tagged element
carries (the prefix, the index spine and the major).

Three moves, and none of them is about the block:

1. the peel, evaluated (`interp_peelPis_mkPisAV`) — the reading at the
   frame extended by the spine's VALUES;
2. those values.  The frame is
   `consList ihvals (consList (xs ++ fs) ρ) = consList (xs ++ fs ++ ihvals) ρ`
   (`consList_append`), a list of length `rP + nF + nR` whose FIRST
   entries are `xs`; so `map_bvarAt_take` (§22) reads the prefix bvars
   as `xs` with no premise at all — the ordering is what makes the
   prefix half free.  The other two are the caller's two value
   identifications;
3. the conclusion is bounded below the recursor type's binder count,
   so the frame below the spine is irrelevant (`interp_congr_below`)
   and the `ihvals`/`fs` block under it drops out. -/
theorem blockRecCa_value {rP nF nR nIdx : Nat} {RecTy Ca mkA conclC : AnnotTerm}
    {esA : List AnnotTerm} {rdsC : List (Nat × Nat × AnnotTerm)}
    (hcon : BlockRuleConclAt rP nF nR RecTy esA mkA Ca)
    (hTyE : RecTy = mkPisAV rdsC conclC)
    (hrds : rdsC.length = rP + nIdx + 1)
    (hesLen : esA.length = nIdx)
    (hconclB : Term.bvarsBelow rdsC.length conclC.erase)
    {ρ : Nat → V} {xs fs ihvals is : List V} {maj : V}
    (hxs : xs.length = rP) (hfs : fs.length = nF) (hihl : ihvals.length = nR)
    (hes : esA.map (interp V (consList ihvals (consList (xs ++ fs) ρ))) = is)
    (hmk : interp V (consList ihvals (consList (xs ++ fs) ρ)) mkA = maj) :
    interp V (consList ihvals (consList (xs ++ fs) ρ)) Ca
      = interp V (consList (xs ++ (is ++ [maj])) ρ) conclC := by
  have hL : consList ihvals (consList (xs ++ fs) ρ) = consList (xs ++ fs ++ ihvals) ρ := by
    simp only [consList_append]
  have hLlen : (xs ++ fs ++ ihvals).length = rP + nF + nR := by
    rw [List.length_append, List.length_append, hxs, hfs, hihl]
  have hisLen : is.length = nIdx := by rw [← hes, List.length_map, hesLen]
  have hWlen : (xs ++ (is ++ [maj])).length = rdsC.length := by
    rw [List.length_append, List.length_append, hxs, hisLen, List.length_singleton, hrds]
    omega
  have hvlen : (paramBvarsAt rP (rP + nF + nR) ++ esA ++ [mkA]).length = rdsC.length := by
    rw [List.length_append, List.length_append, paramBvarsAt_length, hesLen,
      List.length_singleton, hrds]
  rw [hTyE] at hcon
  rw [interp_peelPis_mkPisAV hvlen hcon]
  have hpb : (paramBvarsAt rP (rP + nF + nR)).map
        (interp V (consList ihvals (consList (xs ++ fs) ρ))) = xs := by
    rw [hL, map_bvarAt_take (nP := rP) hLlen.symm (by rw [hLlen]; omega),
      List.append_assoc, List.take_left' hxs]
  have hmap : (paramBvarsAt rP (rP + nF + nR) ++ esA ++ [mkA]).map
        (interp V (consList ihvals (consList (xs ++ fs) ρ)))
      = xs ++ (is ++ [maj]) := by
    rw [List.map_append, List.map_append, hpb, hes, List.map_cons, List.map_nil, hmk,
      List.append_assoc]
  rw [hmap]
  refine interp_congr_below (V := V) conclC rdsC.length _ _ hconclB fun i hi => ?_
  have hi' : i < (xs ++ (is ++ [maj])).length := by rw [hWlen]; exact hi
  rw [consList_getD_of_lt _ _ _ hi', consList_getD_of_lt _ _ _ hi']

/-- **A reading crosses the `ih` openers' block**: the `ih` values are
the INNERMOST binders, so a form lifted by their count at cutoff `0`
reads at the frame below them. -/
theorem interp_liftN_ihvals {ihvals : List V} {σ : Nat → V} (e : AnnotTerm) :
    interp V (consList ihvals σ) (e.liftN ihvals.length 0) = interp V σ e := by
  rw [interp_liftN]
  have h := shiftE_consList_add (V := V) ihvals 0 σ
  rw [shiftE_zero_zero, Nat.add_zero] at h
  rw [h]

/-- **`hCaB` at the run's components.**  `blockRecCa_value` with its
two value identifications taken at the PLAIN frame — which is where
§22's `blockRecMkK_value` and §26's `blockRecCtorIdx` deliver them
(both at `K := 0`, where `chainFrame` is `ρ` and the chain lift is the
identity) — and the `ih` block crossed by `interp_liftN_ihvals`.

The two syntactic identities `hmkL`/`hesL` are the PRODUCER's: the
bundle's components are the run's readings at depth `rP + nF + nR`,
and the run's own `blockRuleMkAV`/`blockRuleEsAV` are at depth
`rP + nF`; a reading at a deeper frame of the same closed-at-`rP+nF`
expression is that reading lifted at cutoff `0`. -/
theorem blockRecCa_run {rP nF nR nIdx : Nat} {RecTy Ca mkA mk0 conclC : AnnotTerm}
    {esA es0 : List AnnotTerm} {rdsC : List (Nat × Nat × AnnotTerm)}
    (hcon : BlockRuleConclAt rP nF nR RecTy esA mkA Ca)
    (hTyE : RecTy = mkPisAV rdsC conclC)
    (hrds : rdsC.length = rP + nIdx + 1)
    (hesLen : es0.length = nIdx)
    (hconclB : Term.bvarsBelow rdsC.length conclC.erase)
    {ρ : Nat → V} {xs fs ihvals is : List V} {maj : V}
    (hxs : xs.length = rP) (hfs : fs.length = nF) (hihl : ihvals.length = nR)
    (hmkL : mkA = mk0.liftN nR 0) (hesL : esA = es0.map (·.liftN nR 0))
    (hmkV : interp V (consList (xs ++ fs) ρ) mk0 = maj)
    (hesV : es0.map (interp V (consList (xs ++ fs) ρ)) = is) :
    interp V (consList ihvals (consList (xs ++ fs) ρ)) Ca
      = interp V (consList (xs ++ (is ++ [maj])) ρ) conclC := by
  refine blockRecCa_value hcon hTyE hrds (by rw [hesL, List.length_map]; exact hesLen)
    hconclB hxs hfs hihl ?_ ?_
  · rw [hesL, List.map_map, ← hesV]
    refine List.map_congr_left fun e _ => ?_
    show interp V (consList ihvals (consList (xs ++ fs) ρ)) (e.liftN nR 0) = _
    rw [← hihl]
    exact interp_liftN_ihvals e
  · rw [hmkL, ← hihl]
    rw [interp_liftN_ihvals mk0]
    exact hmkV

/-- **`hCaB` in the kit's own spelling**: the rule's conclusion at the
rule's frame IS the motive at the constructed element.  §29's frame
evaluation composed with §9's `blockRecMot_tagged`; the index spine is
the caller's `is` (the `isOfW` retraction of the rule's index tuple,
§26's business) and the major the caller's `maj` (§22's). -/
theorem blockRecHCaB {K c : Nat} (hc : c < K) {uOf nIdxOf : Nat → Nat}
    {concl : Nat → AnnotTerm} {rP nF nR nIdx : Nat} {RecTy Ca mkA mk0 : AnnotTerm}
    {esA es0 : List AnnotTerm} {rdsC : List (Nat × Nat × AnnotTerm)}
    (hcon : BlockRuleConclAt rP nF nR RecTy esA mkA Ca)
    (hTyE : RecTy = mkPisAV rdsC (concl c))
    (hrds : rdsC.length = rP + nIdx + 1)
    (hesLen : es0.length = nIdx)
    (hconclB : Term.bvarsBelow rdsC.length (concl c).erase)
    {ρ : Nat → V} {xs fs ihvals : List V} {tt maj : V}
    (hxs : xs.length = rP) (hfs : fs.length = nF) (hihl : ihvals.length = nR)
    (hmkL : mkA = mk0.liftN nR 0) (hesL : esA = es0.map (·.liftN nR 0))
    (hmkV : interp V (consList (xs ++ fs) ρ) mk0 = maj)
    (hesV : es0.map (interp V (consList (xs ++ fs) ρ)) = isOfW (uOf c) (nIdxOf c) tt) :
    interp V (consList ihvals (consList (xs ++ fs) ρ)) Ca
      = blockRecMot K concl uOf nIdxOf ρ xs (tagged c tt maj) := by
  rw [blockRecMot_tagged hc]
  exact blockRecCa_run hcon hTyE hrds hesLen hconclB hxs hfs hihl hmkL hesL hmkV hesV

/-- **The bundle's producer, at the peel.**  `checkBlockRule`'s own
`instPisAtLift` equation (`checkBlockRule_data`, through
`checkBlockRecK_ruleRun`) read at the rule's depth: the peel's four
side conditions are the run's — the recursor type and the arguments
are closed expressions scoped at the rule frame, and the arguments
read to the prefix bvars, the index readings and the fired spine.

This is where the syntactic form lives; the bundle above carries only
its output, which is the whole point of stating the bundle past the
peel. -/
theorem blockRuleConclAt_of {envT : Env} {mp : EnvModelM V μ envT} {ψ : Name → Nat}
    {rP nF nR : Nat} {recTy concl : Expr} {args : List Expr}
    {RecTy Ca mkA : AnnotTerm} {esA : List AnnotTerm}
    (hpr : ConLeche.Expr.instPisAtLift args recTy = some concl)
    (hw : Expr.WScoped (rP + nF + nR) recTy)
    (ha : ∀ a ∈ args, Expr.WScoped (rP + nF + nR) a ∧ a.looseBVarsBounded 0 = true)
    (hty : denoteMeta mp.base2.acval envT ψ (rP + nF + nR) recTy = some RecTy)
    (hsp : DenoteMetaSpine mp.base2.acval envT ψ (rP + nF + nR) args
      (paramBvarsAt rP (rP + nF + nR) ++ esA ++ [mkA]))
    (hCa : denoteMeta mp.base2.acval envT ψ (rP + nF + nR) concl = some Ca) :
    BlockRuleConclAt rP nF nR RecTy esA mkA Ca := by
  obtain ⟨restA, hrest, hpeel⟩ := denoteMeta_instPisAtLift_peel
    mp.base2.acval_closed (acval_inst_self mp.base2) args hpr hw ha hty hsp
  obtain rfl : restA = Ca := Option.some.inj (hrest.symm.trans hCa)
  exact hpeel

/-- **The prefix openers read to `paramBvarsAt`.**  `openPisAtFvars`
at index `0` produces `fvar k`s in order, and `denoteMeta` reads
`fvar k` at depth `D` as `bvar (D - 1 - k)` — which is `paramBvarsAt`
by definition.  The producer's first spine segment. -/
theorem denoteMetaSpine_prefFvs {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {D rP : Nat} {e : Expr} {fvs : List Expr} {body : Expr}
    (hop : ConLeche.openPisAtFvars rP e 0 = some (fvs, body)) (hlen : fvs.length = rP) :
    DenoteMetaSpine acval env φ D fvs (paramBvarsAt rP D) := by
  have h := ConLeche.Model.denoteMetaSpine_fvars (acval := acval) (env := env) (φ := φ) D fvs 0
    (fun k x hx => ConLeche.openPisAtFvars_index _ _ _ hop k x hx)
  rw [hlen] at h
  simpa [paramBvarsAt] using h

end RuleConcl

/-! ## 30. The `ih` openers' VALUES — `ihv` defined, and `hihChain`
(session 13)

Until this section `ihv` was a PARAMETER of the kit, of the abstract
arm and of `KitRegimeAt`, and the two facts about it (`hihF`, the
values fit the ih openers' domains; `hihChain`, they ARE the ih terms'
readings at the chain frame) were premises.  `ihv` is now DEFINED, and
it may not mention the recursor: the kit's step is what the recursion
theorem is being handed, so the only thing an ih value may be built
from is the GRAPH `g` the step receives.

**The design** (`M5M-pre-REPORT` §S6.4 item 2).  A rule's `ih` opener
for a guarded call `rec_{c'} x⃗ e⃗_i(a⃗) (f_i a⃗)` is valued at the
CURRIED λ-tower over the field's telescope (F3's finding 2: the ih's
domain is the telescope, not the predecessor set) whose body is the
graph at that call's PREDECESSOR — `blockRecIhvAt`.  The ih TERMS are
the same towers spelled syntactically under the `K` chain binders
(`ihFunAV`, whose head is the chain's component) — `blockRecIhsAt`,
the single definition of `ihs` the two lanes share (the audit's item
9).

`hihChain` is then a TOWER congruence: the two towers run over the
same binder data at two frames that agree below the rule's own depth,
and at a leaf the graph-built body is the call's value
(`blockRecIhCall`: `app_graph` at the predecessor and `famCand_fold`
at the candidate) while the syntactic one folds to the same thing
(`interp_ihFunAV_body`, `ihFunAV_fold`'s core stated at the BODY
rather than at the fold). -/

section IhValues

/-! ### The tower congruence -/

/-- A frame built by `consList` does not see the environment below it. -/
theorem consList_below_indep (L : List V) (ρ₁ ρ₂ : Nat → V) :
    ∀ i, i < L.length → consList L ρ₁ i = consList L ρ₂ i := by
  intro i hi
  rw [consList_getD_of_lt _ _ _ hi, consList_getD_of_lt _ _ _ hi]

/-- **A λ-tower congruence at two frames**: towers over the SAME
binder data agree when the frames agree below the depth the data are
bounded at — entry `l` at `N + l`, the shape a telescope's own bound
has (§28's finding) — and their bodies agree at every leaf frame the
walk reaches. -/
theorem lamTowerA_congr_below {m : Nat} {g₁ g₂ : List V → (Nat → V) → V} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {N : Nat} {ρ₁ ρ₂ : Nat → V} {acc : List V},
      (∀ i, i < N → ρ₁ i = ρ₂ i) →
      (∀ l, l < ds.length → Term.bvarsBelow (N + l) ((ds.getD l default).2.2).erase) →
      (∀ bs : List V, bs.length = ds.length →
        g₁ (acc ++ bs) (consList bs ρ₁) = g₂ (acc ++ bs) (consList bs ρ₂)) →
      lamTowerA m ρ₁ acc ds g₁ = lamTowerA m ρ₂ acc ds g₂
  | [], _, _, _, acc, _, _, hbody => by
    have h := hbody [] rfl
    simpa [lamTowerA] using h
  | dd :: ds, N, ρ₁, ρ₂, acc, hag, hb, hbody => by
    have hdom : interp V ρ₁ dd.2.2 = interp V ρ₂ dd.2.2 := by
      refine interp_congr_below (V := V) dd.2.2 N ρ₁ ρ₂ ?_ hag
      have h0 := hb 0 (by simp)
      simpa using h0
    show lamR m (interp V ρ₁ dd.2.2) (fun a => lamTowerA m (cons a ρ₁) (acc ++ [a]) ds g₁)
      = lamR m (interp V ρ₂ dd.2.2) (fun a => lamTowerA m (cons a ρ₂) (acc ++ [a]) ds g₂)
    rw [← hdom]
    refine lamR_congr fun a _ => ?_
    refine lamTowerA_congr_below (N := N + 1) (fun i hi => ?_) (fun l hl => ?_) (fun bs hbs => ?_)
    · cases i with
      | zero => rfl
      | succ i => exact hag i (by omega)
    · have h := hb (l + 1) (by simpa using hl)
      rw [show N + 1 + l = N + (l + 1) from by omega]
      simpa using h
    · have h := hbody (a :: bs) (by simpa using hbs)
      simpa [List.append_assoc] using h

/-! ### The ih term's body -/

/-- **`ihFunAV_fold`'s core, at the BODY**: the guarded call's spine
read at a leaf frame of the field's telescope — the chain's component
folded along the rule's prefix, the field's index readings and the
applied field.  `ihFunAV_fold` is this plus `lamTowerA_fold`; the
congruence needs the body, not the fold. -/
theorem interp_ihFunAV_body {K c' rP nF : Nat} {tl : List (Nat × Nat × AnnotTerm)}
    {eis : List AnnotTerm} {fap : AnnotTerm} {σ : Nat → V} {R : V}
    (hR : σ (K - 1 - c') = R) {xs fs as : List V}
    (hxl : xs.length = rP) (hfl : fs.length = nF) (hal : as.length = tl.length) :
    interp V (consList as (consList (xs ++ fs) σ))
        (AnnotTerm.mkAppN (.bvar (tl.length + nF + rP + (K - 1 - c')))
          (prefVarsAV rP (nF + tl.length) ++ eis ++ [fap]))
      = (xs ++ (eis ++ [fap]).map (interp V (consList as (consList (xs ++ fs) σ)))).foldl
          SetTheory.app R := by
  have hfr : consList as (consList (xs ++ fs) σ) = consList (xs ++ (fs ++ as)) σ := by
    rw [consList_append, consList_append, consList_append]
  rw [hfr, interp_mkAppN, foldl_app_map]
  have hlen : (xs ++ (fs ++ as)).length = nF + tl.length + rP := by
    rw [List.length_append, List.length_append, hxl, hfl, hal]; omega
  have hhead : interp V (consList (xs ++ (fs ++ as)) σ)
      (.bvar (tl.length + nF + rP + (K - 1 - c'))) = R := by
    show consList (xs ++ (fs ++ as)) σ (tl.length + nF + rP + (K - 1 - c')) = R
    rw [show tl.length + nF + rP + (K - 1 - c')
          = (K - 1 - c') + (xs ++ (fs ++ as)).length from by rw [hlen]; omega,
      consList_apply_add, hR]
  have hpre : (prefVarsAV rP (nF + tl.length)).map (interp V (consList (xs ++ (fs ++ as)) σ))
      = xs := by
    have h := interp_prefVarsAV (V := V) (rP := rP) (xs := xs) (bs := fs ++ as) (ρ := σ) hxl
    rw [List.length_append, hfl, hal] at h
    exact h
  rw [hhead]
  simp only [List.map_append, hpre, List.append_assoc]

/-! ### The two lists -/

/-- **The `ih` openers' TERMS**, one per key: the design's curried
λ-tower of the guarded call, spelled under the `K` chain binders.
This is the `ihs` BOTH lanes state their facts at (the audit's item
9); its per-key syntactic data are the rule lane's
(`ihNodeVal_blockRec`'s `hihv`: `ihTeleAtR`, the `ihIdxAtM`-moved index
readings and the applied field). -/
@[expose] def blockRecIhsAt (ℓ K rP nF : Nat) (ihKeys : List (Nat × Nat))
    (tlA : Nat → List (Nat × Nat × AnnotTerm)) (eisA : Nat → List AnnotTerm)
    (fapA : Nat → AnnotTerm) : List AnnotTerm :=
  ihKeys.map fun key => ihFunAV ℓ K key.2 rP nF (tlA key.1) (eisA key.1) (fapA key.1)

omit [SetTheory V] in
@[simp] theorem blockRecIhsAt_length (ℓ K rP nF : Nat) (ihKeys : List (Nat × Nat))
    (tlA : Nat → List (Nat × Nat × AnnotTerm)) (eisA : Nat → List AnnotTerm)
    (fapA : Nat → AnnotTerm) :
    (blockRecIhsAt ℓ K rP nF ihKeys tlA eisA fapA).length = ihKeys.length := by
  simp [blockRecIhsAt]

/-- **The `ih` openers' VALUES**, built from the recursion GRAPH `g`
alone: per key the λ-tower over the field's telescope whose body is
`g` at the PREDECESSOR the guarded call names — the field applied to
the telescope spine, tagged with its class and its index tuple. -/
@[expose] noncomputable def blockRecIhvAt (ℓ : Nat) (tup : Nat → List V → V) (σ : Nat → V)
    (ihKeys : List (Nat × Nat)) (tlA : Nat → List (Nat × Nat × AnnotTerm))
    (eisA : Nat → List AnnotTerm) (fapA : Nat → AnnotTerm) (g : V) : List V :=
  ihKeys.map fun key =>
    lamTowerA ℓ σ [] (tlA key.1) fun _ τ =>
      app g (tagged key.2 (tup key.2 ((eisA key.1).map (interp V τ)))
        (interp V τ (fapA key.1)))

@[simp] theorem blockRecIhvAt_length (ℓ : Nat) (tup : Nat → List V → V) (σ : Nat → V)
    (ihKeys : List (Nat × Nat)) (tlA : Nat → List (Nat × Nat × AnnotTerm))
    (eisA : Nat → List AnnotTerm) (fapA : Nat → AnnotTerm) (g : V) :
    (blockRecIhvAt ℓ tup σ ihKeys tlA eisA fapA g).length = ihKeys.length := by
  simp [blockRecIhvAt]

/-! ### The graph at a predecessor IS the candidate's fold -/

/-- **The guarded call's value, from the kit's graph.**  At a
PREDECESSOR of the element the step is running at, the kit's graph is
the kit's own recursor (`app_graph`, the graph being a function's
graph over `pred u`), and the candidate folded along the call's spine
is that recursor (`famCand_fold`).  This is the one fact `hihChain`
needs of the recursion, and it is not about the block. -/
theorem blockRecIhCall {ℓ K : Nat} {rP : Nat → Nat}
    {rds : Nat → List (Nat × Nat × AnnotTerm)} {concl : Nat → AnnotTerm} {ρ : Nat → V}
    (D : RecFamData V ℓ K rP rds concl ρ) (hℓ : ℓ ≠ 0) {c' : Nat}
    {xs is : List V} {maj u : V} (hxl : xs.length = rP c')
    (hsp : SpineFit ρ ((rds c').map (·.2.2)) (xs ++ (is ++ [maj])))
    (hpred : (tagged c' (D.tupOf c' is) maj : V) ∈ˢ (D.kit xs).pred u) :
    app (kitGraphAt (D.kit xs) u) (tagged c' (D.tupOf c' is) maj)
      = (xs ++ (is ++ [maj])).foldl SetTheory.app (famCand D c') := by
  rw [famCand_fold D hℓ hxl hsp, kitGraphAt, app_graph hpred]
  rfl

/-! ### `hihChain`, at the tower level -/

/-- **`hihChain` at the tower level**: the graph-built values ARE the
ih terms' readings at the chain frame.

Three inputs, and only the third is about the recursion: the callees
are classes of the block (`hkey`), the telescopes are bounded at their
own depth (`htlB` — the premise `liftDomsK_eq_self_of_bounded` asks
too, §28), and at every telescope spine the graph at the call's
predecessor is the candidate folded along the call's spine (`hcall`,
`blockRecIhCall` at the run). -/
theorem blockRecIhvAt_eq {ℓ K rP nF N : Nat} {a ρ : Nat → V} {xs fs : List V} {g : V}
    {tup : Nat → List V → V} {ihKeys : List (Nat × Nat)}
    {tlA : Nat → List (Nat × Nat × AnnotTerm)} {eisA : Nat → List AnnotTerm}
    {fapA : Nat → AnnotTerm}
    (hxl : xs.length = rP) (hfl : fs.length = nF) (hN : N = (xs ++ fs).length)
    (hkey : ∀ key ∈ ihKeys, key.2 < K)
    (htlB : ∀ key ∈ ihKeys, ∀ l, l < (tlA key.1).length →
      Term.bvarsBelow (N + l) (((tlA key.1).getD l default).2.2).erase)
    (hcall : ∀ key ∈ ihKeys, ∀ bs : List V, bs.length = (tlA key.1).length →
      app g (tagged key.2
          (tup key.2 ((eisA key.1).map (interp V (consList bs (consList (xs ++ fs) ρ)))))
          (interp V (consList bs (consList (xs ++ fs) ρ)) (fapA key.1)))
        = (xs ++ ((eisA key.1) ++ [fapA key.1]).map
            (interp V (consList bs (consList (xs ++ fs) (chainFrame K a ρ))))).foldl
              SetTheory.app (a key.2)) :
    blockRecIhvAt ℓ tup (consList (xs ++ fs) ρ) ihKeys tlA eisA fapA g
      = (blockRecIhsAt ℓ K rP nF ihKeys tlA eisA fapA).map
          (interp V (consList (xs ++ fs) (chainFrame K a ρ))) := by
  rw [blockRecIhvAt, blockRecIhsAt, List.map_map]
  refine List.map_congr_left fun key hkm => ?_
  show lamTowerA ℓ (consList (xs ++ fs) ρ) [] (tlA key.1) _
    = interp V (consList (xs ++ fs) (chainFrame K a ρ))
        (ihFunAV ℓ K key.2 rP nF (tlA key.1) (eisA key.1) (fapA key.1))
  rw [ihFunAV, interp_mkLamsC_A (acc := ([] : List V))]
  refine lamTowerA_congr_below (N := N) (fun i hi => ?_) (htlB key hkm) (fun bs hbs => ?_)
  · exact consList_below_indep (xs ++ fs) ρ (chainFrame K a ρ) i (by rw [← hN]; exact hi)
  · have hbody := interp_ihFunAV_body (V := V) (K := K) (c' := key.2) (tl := tlA key.1)
      (eis := eisA key.1) (fap := fapA key.1) (σ := chainFrame K a ρ)
      (chainFrame_apply (hkey key hkm) a ρ) hxl hfl hbs
    show app g _ = interp V (consList bs (consList (xs ++ fs) (chainFrame K a ρ))) _
    rw [hbody, ← hcall key hkm bs hbs]

/-! ### The call's arguments, across the two frames -/

/-- The two towers' LEAF frames agree below the rule's own depth plus
the telescope's: both are `consList` of the same entries. -/
theorem consList_chain_agree_leaf {K N : Nat} {a ρ : Nat → V} {ws bs : List V}
    (hN : N = ws.length) :
    ∀ i, i < N + bs.length →
      consList bs (consList ws ρ) i = consList bs (consList ws (chainFrame K a ρ)) i := by
  intro i hi
  rw [← consList_append, ← consList_append]
  exact consList_below_indep _ _ _ i (by rw [List.length_append]; omega)

/-- A form bounded at the leaf frame's depth reads the same under the
base frame and under the chain frame. -/
theorem interp_leaf_chain {K N : Nat} {a ρ : Nat → V} {ws bs : List V} {e : AnnotTerm}
    (hN : N = ws.length) (hb : Term.bvarsBelow (N + bs.length) e.erase) :
    interp V (consList bs (consList ws ρ)) e
      = interp V (consList bs (consList ws (chainFrame K a ρ))) e :=
  interp_congr_below (V := V) e (N + bs.length) _ _ hb (consList_chain_agree_leaf hN)

/-- **`blockRecIhvAt_eq`'s `hcall`, at the run.**  `blockRecIhCall`
with the call's arguments read at the BASE frame — where the ih VALUES
live — rather than at the chain frame, where the ih TERMS do; the two
readings agree because the arguments are bounded at the leaf frame's
depth (`heisB`, `hfapB`), which is the same premise `htlB` is. -/
theorem blockRecIhCall_run {ℓ K N : Nat} {rP : Nat → Nat}
    {rds : Nat → List (Nat × Nat × AnnotTerm)} {concl : Nat → AnnotTerm} {ρ : Nat → V}
    (D : RecFamData V ℓ K rP rds concl ρ) (hℓ : ℓ ≠ 0)
    {c' : Nat} {xs fs bs : List V} {u : V} {eis : List AnnotTerm} {fap : AnnotTerm}
    (hN : N = (xs ++ fs).length)
    (heisB : ∀ e ∈ eis, Term.bvarsBelow (N + bs.length) e.erase)
    (hfapB : Term.bvarsBelow (N + bs.length) fap.erase)
    (hxl : xs.length = rP c')
    (hsp : SpineFit ρ ((rds c').map (·.2.2))
      (xs ++ (eis.map (interp V (consList bs (consList (xs ++ fs)
            (chainFrame K (famCand D) ρ))))
        ++ [interp V (consList bs (consList (xs ++ fs) (chainFrame K (famCand D) ρ))) fap])))
    (hpred : (tagged c'
        (D.tupOf c' (eis.map (interp V (consList bs (consList (xs ++ fs)
          (chainFrame K (famCand D) ρ))))))
        (interp V (consList bs (consList (xs ++ fs) (chainFrame K (famCand D) ρ))) fap) : V)
      ∈ˢ (D.kit xs).pred u) :
    app (kitGraphAt (D.kit xs) u)
        (tagged c' (D.tupOf c' (eis.map (interp V (consList bs (consList (xs ++ fs) ρ)))))
          (interp V (consList bs (consList (xs ++ fs) ρ)) fap))
      = (xs ++ (eis ++ [fap]).map
          (interp V (consList bs (consList (xs ++ fs) (chainFrame K (famCand D) ρ))))).foldl
            SetTheory.app (famCand D c') := by
  have hes : eis.map (interp V (consList bs (consList (xs ++ fs) ρ)))
      = eis.map (interp V (consList bs (consList (xs ++ fs) (chainFrame K (famCand D) ρ)))) :=
    List.map_congr_left fun e he => interp_leaf_chain hN (heisB e he)
  rw [hes, interp_leaf_chain (K := K) (a := famCand D) hN hfapB,
    List.map_append, List.map_cons, List.map_nil]
  exact blockRecIhCall D hℓ hxl hsp hpred

end IhValues

/-! ## 31. The two lanes' `eqs` are ONE term (the audit's item 7)

This lane states `hpre` at `iotaEqsAV` instantiated at §20's
components; the rule lane states `hnew` at `blockIotaEqsAV`, which is
the same instantiation written once.  Since §28 the two agree
everywhere except in the RESIDUE's cutoff: this lane writes the
LIFTED prefix and field domains' lengths (they come out of its own
`pdoms`/`fdoms` parameters) and the rule lane the unlifted ones.
`liftDomsK_length` is a theorem, not `rfl` — a recursion on the list —
so the two do not typecheck against each other without this. -/

section EqsIdent

/-- **The identification.** -/
theorem iotaEqsAV_eq_blockIotaEqsAV {K : Nat} {nCt : Nat → Nat}
    {pdoms0 : Nat → List AnnotTerm} {fdoms0 es0 ihs : Nat → Nat → List AnnotTerm}
    {mk0 Rb0 : Nat → Nat → AnnotTerm} :
    iotaEqsAV K nCt (fun c => liftDomsK K 0 (pdoms0 c))
        (fun c j => liftDomsK K (pdoms0 c).length (fdoms0 c j))
        (fun c j => (es0 c j).map fun e =>
          e.liftN K ((pdoms0 c).length + (fdoms0 c j).length))
        (fun c j => (mk0 c j).liftN K ((pdoms0 c).length + (fdoms0 c j).length))
        ihs
        (fun c j => (Rb0 c j).liftN K
          ((liftDomsK K 0 (pdoms0 c)).length
            + (liftDomsK K (pdoms0 c).length (fdoms0 c j)).length + (ihs c j).length))
      = blockIotaEqsAV K nCt pdoms0 fdoms0 es0 ihs mk0 Rb0 := by
  have hRb : (fun c j => (Rb0 c j).liftN K
        ((liftDomsK K 0 (pdoms0 c)).length
          + (liftDomsK K (pdoms0 c).length (fdoms0 c j)).length + (ihs c j).length))
      = (fun c j => (Rb0 c j).liftN K
        ((pdoms0 c).length + (fdoms0 c j).length + (ihs c j).length)) := by
    funext c j
    rw [liftDomsK_length, liftDomsK_length]
  rw [hRb, blockIotaEqsAV]

end EqsIdent

/-! ## 32. The `ih` openers' DOMAINS — `hihF` (session 13)

`hihF` says the graph-built towers FIT the `ih` openers' domains.  The
domain of opener `r` is the reading of `blockIhPis`' `l = r` entry:
the Π-tower over the field's telescope of the CALLEE's recursor TYPE
instantiated at the rule's prefix, the field's index expressions and
the applied field — no constant in sight, so it is §29's
`BlockRuleConclAt` one telescope deeper, and the SAME peel produces
it.

Two things make this cheap.

* **The opener's `l`-shift is a `liftN r 0` of the `l = 0` form.**
  `ihIdxAtM_shift`, `fieldApp_shift`, `prefVars_shift` and
  `teleVarsAV_liftN` (`BlockRecRule.lean`) say so entry by entry, and
  a `mkPisAV` lifted at cutoff `0` lifts entry `k` at cutoff `k` and
  its body at the telescope's length — exactly the shape.  The fit
  walk reads opener `r` under the `r` earlier ih VALUES, and
  `interp_liftN_ihvals` (§29) cancels the two: the domain's reading at
  the walk's frame IS the `l = 0` tower's reading at the rule's frame,
  which is where the ih VALUE lives.  **No congruence between two
  different binder-data lists is needed**, which is what the shift
  first looked like it would cost.
* **The leaf obligation is `blockRecHCaB` at the PREDECESSOR.**  The
  peel's prefix arguments are `prefVarsAV rP (nF + m)`, which is
  `paramBvarsAt rP (rP + nF + m)` on the nose, so §29's
  `blockRecCa_value` applies verbatim with the telescope spine in the
  `ih` block's place: the opener's conclusion reads to the motive at
  the predecessor, and the graph is motive-valued there. -/

section IhDomains

/-- A spine fits when every entry fits at the frame the walk reaches
it in — the index form of `SpineFit`'s walk. -/
theorem spineFit_of_getD {σ : Nat → V} :
    ∀ {Ds : List AnnotTerm} {as : List V}, as.length = Ds.length →
      (∀ r, r < Ds.length →
        as.getD r pt ∈ˢ interp V (consList (as.take r) σ) (Ds.getD r default)) →
      SpineFit σ Ds as
  | [], [], _, _ => trivial
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | D :: Ds, a :: as, hl, h => by
    refine ⟨?_, ?_⟩
    · have h0 := h 0 (by simp)
      simpa using h0
    · refine spineFit_of_getD (by simpa using hl) fun r hr => ?_
      have hr' := h (r + 1) (by simpa using hr)
      simpa using hr'

/-- **`hihF` at ONE opener**: the graph-built tower inhabits the ih
opener's Π-tower.  `lamTowerA_mem` at the walk built from the fits
(`towerWalkA_of_spines_body`); the leaf obligation is the graph's
value at the PREDECESSOR lying in the opener's conclusion. -/
theorem blockRecIhv_mem {ℓ c' : Nat} {tl : List (Nat × Nat × AnnotTerm)} {Cih : AnnotTerm}
    {tup : Nat → List V → V} {σ : Nat → V} {g : V}
    {eis : List AnnotTerm} {fap : AnnotTerm} (hℓ : ℓ ≠ 0)
    (hbits : ∀ dd ∈ tl, (ℓ = 0 ↔ dd.2.1 = 0))
    (hleaf : ∀ bs : List V, SpineFit σ (tl.map (·.2.2)) bs →
      app g (tagged c' (tup c' (eis.map (interp V (consList bs σ))))
          (interp V (consList bs σ) fap))
        ∈ˢ interp V (consList bs σ) Cih) :
    lamTowerA ℓ σ [] tl
        (fun _ τ => app g (tagged c' (tup c' (eis.map (interp V τ))) (interp V τ fap)))
      ∈ˢ interp V σ (mkPisAV tl Cih) :=
  lamTowerA_mem hbits (towerWalkA_of_spines_body fun ys hsp =>
    ⟨hleaf ys hsp, fun h0 => absurd h0 hℓ⟩)

/-- **`hihF` at the whole opener list**: `blockRecIhvAt` fits
`ihdoms`, given that opener `r`'s domain IS the `l = 0` Π-tower lifted
past the `r` earlier openers (`hdom`), the telescope carries the
family's bit (`hbits`) and the graph is motive-valued at every
predecessor the openers name (`hleaf`). -/
theorem blockRecIhvAt_fit {ℓ : Nat} {tup : Nat → List V → V} {σ : Nat → V} {g : V}
    {ihKeys : List (Nat × Nat)} {tlA : Nat → List (Nat × Nat × AnnotTerm)}
    {eisA : Nat → List AnnotTerm} {fapA : Nat → AnnotTerm}
    {ihdoms : List AnnotTerm} {Cih : Nat → AnnotTerm} (hℓ : ℓ ≠ 0)
    (hlen : ihdoms.length = ihKeys.length)
    (hdom : ∀ r, r < ihKeys.length →
      ihdoms.getD r default
        = (mkPisAV (tlA (ihKeys.getD r (0, 0)).1) (Cih r)).liftN r 0)
    (hbits : ∀ r, r < ihKeys.length →
      ∀ dd ∈ tlA (ihKeys.getD r (0, 0)).1, (ℓ = 0 ↔ dd.2.1 = 0))
    (hleaf : ∀ r, r < ihKeys.length → ∀ bs : List V,
      SpineFit σ ((tlA (ihKeys.getD r (0, 0)).1).map (·.2.2)) bs →
      app g (tagged (ihKeys.getD r (0, 0)).2
          (tup (ihKeys.getD r (0, 0)).2
            ((eisA (ihKeys.getD r (0, 0)).1).map (interp V (consList bs σ))))
          (interp V (consList bs σ) (fapA (ihKeys.getD r (0, 0)).1)))
        ∈ˢ interp V (consList bs σ) (Cih r)) :
    SpineFit σ ihdoms (blockRecIhvAt ℓ tup σ ihKeys tlA eisA fapA g) := by
  refine spineFit_of_getD (by rw [blockRecIhvAt_length, hlen]) fun r hr => ?_
  have hrk : r < ihKeys.length := by rw [← hlen]; exact hr
  have hk : ihKeys[r]? = some (ihKeys.getD r (0, 0)) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrk]
    rfl
  have hval : (blockRecIhvAt ℓ tup σ ihKeys tlA eisA fapA g).getD r pt
      = lamTowerA ℓ σ [] (tlA (ihKeys.getD r (0, 0)).1)
          (fun _ τ => app g (tagged (ihKeys.getD r (0, 0)).2
            (tup (ihKeys.getD r (0, 0)).2
              ((eisA (ihKeys.getD r (0, 0)).1).map (interp V τ)))
            (interp V τ (fapA (ihKeys.getD r (0, 0)).1)))) := by
    rw [blockRecIhvAt, List.getD_eq_getElem?_getD, List.getElem?_map, hk]
    rfl
  have htk : ((blockRecIhvAt ℓ tup σ ihKeys tlA eisA fapA g).take r).length = r := by
    rw [List.length_take, blockRecIhvAt_length]
    omega
  have hcancel : interp V (consList ((blockRecIhvAt ℓ tup σ ihKeys tlA eisA fapA g).take r) σ)
        ((mkPisAV (tlA (ihKeys.getD r (0, 0)).1) (Cih r)).liftN r 0)
      = interp V σ (mkPisAV (tlA (ihKeys.getD r (0, 0)).1) (Cih r)) := by
    have h := interp_liftN_ihvals (V := V)
      (ihvals := (blockRecIhvAt ℓ tup σ ihKeys tlA eisA fapA g).take r) (σ := σ)
      (mkPisAV (tlA (ihKeys.getD r (0, 0)).1) (Cih r))
    rw [htk] at h
    exact h
  rw [hval, hdom r hrk, hcancel]
  exact blockRecIhv_mem hℓ (hbits r hrk) (hleaf r hrk)

end IhDomains

/-! ## 33. THE PREDECESSOR — the one fact `hihChain` and `hihF` share
(session 14)

§30 and §32 both end at the same obligation: the guarded call's
argument — the recursive field applied along a fitting telescope
spine — is a PREDECESSOR of the constructed element, i.e. it lies in
`tcPred (unionSet K Is Cr) u`.  `mem_tcPred` splits that in two, and
the block's data decide both:

* **in the UNION**: the value lies in the TARGET member's carrier at
  the call's index tuple, which is what the recursive SLOT says
  (`slotSet` is the nested product over the field's telescope of the
  target component at the index tuple — `piTele_fold` at a fitting
  telescope spine), and the tuple lies in that member's index set by
  `BlockModelAt.idxFit`'s `SlotFit` plus `tupW_mem`.  The class's
  guard is `SpineFit ρ (pdoms c') xs` — **at the CALLEE's class**;
* **∈-BELOW**: `blockData_mkDepth` at a finitary field,
  `blockData_mkDepth_app` at a reflexive one (`BlockRecRegimes.lean`).

**`pdoms c = pdoms c'` is a PREMISE, and it has no producer**
(`hpdU` below).  `checkBlockRecTys` (`Kernel/Inductives/BlockInstall.lean:439`)
compares the first `nP` binder domains of a recursor's type with the
block's parameters binder by binder and states, in as many words,
that "the binders `nP … rP-1` are ARBITRARY — the stretch official
fills with the motives and the minor premises is never looked
inside".  So two recursors of one block may carry different motive
and minor telescopes of the same LENGTH (`blockIhKeys`' filter pins
only the length, `pairIdxOf_blockIhKeys_rP`), and nothing in the
recursor stage makes the rule's prefix values fit the CALLEE's
prefix.  See §S14.2 for the two ways out; the premise is stated here,
where its run-level consumer is. -/

section Predecessor

variable {env : Env} {mo : EnvModel V env} {names : List Name} {d : BlockData V}

/-- **The tagged predecessor**, from the two memberships and the
depth.  The guard is read at the CALLEE's class `c'`. -/
theorem blockRecPred_of {K c' : Nat} {ψ : Name → Nat} {ρ : Nat → V} {mem : Nat → Nat}
    {pdoms : Nat → List AnnotTerm} {xs : List V} {t x u : V}
    (hc' : c' < K)
    (hparFit : SpineFit ρ (d.params ψ) (xs.take d.nP))
    (hpref' : SpineFit ρ (pdoms c') xs)
    (ht : t ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (mem c'))
    (hx : x ∈ˢ app (blockRecCr d ψ ρ mem xs c') t)
    (hdep : x ∈ˢ ConLeche.SetTheory.tc (tagVal u)) :
    (tagged c' t x : V)
      ∈ˢ tcPred (unionSet K (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs)) u := by
  refine mem_tcPred.mpr ⟨tagged_mem_unionSet hc' ?_ hx, ?_⟩
  · rw [blockRecIs_pos hparFit hpref']
    exact ht
  · rw [tagVal_tagged]
    exact hdep

/-- **The two memberships, from the recursive SLOT.**  A recursive
field's value is the nested product over the field's telescope of the
target component at the call's index tuple, so folding it along a
fitting telescope spine lands in that component at that tuple
(`piTele_fold`); and the tuple is in the component's index set by
`BlockModelAt.idxFit` (its `SlotFit`'s third conjunct is exactly the
index readings' fit) through `tupW_mem`. -/
theorem blockRecSlot_pred {ψ : Name → Nat} {ρp : Nat → V} {X : Nat → V} {c j i : Nat}
    {t f : V} {as bs : List V}
    (hM : BlockModelAt mo names d) (hw : d.w ψ ≠ 0)
    (hsat : Sat V (d.params ψ).reverse ρp)
    (hX : InTupleSpace (d.w ψ) d.N (d.idx ψ ρp) X)
    (hc : c < d.N) (ht : t ∈ˢ d.idx ψ ρp c) (hj : j < (d.ctorsM c).length)
    (hi : i < ((d.Fss c ψ).getD j []).length)
    (hrec : ((d.rss c).getD j []).getD i false = true)
    (hpre : FitsFrom ((d.rss c).getD j []) (d.slotAt ψ X c j) 0 ρp
      (((d.Fss c ψ).getD j []).take i) as)
    (hf : f ∈ˢ d.slotAt ψ X c j i (consList as ρp))
    (hbs : SpineFit (consList as ρp) ((((d.tlss c ψ).getD j []).getD i []).map (·.2.2)) bs) :
    d.tup ψ (d.tgts c j i)
        ((((d.Eiss c ψ).getD j []).getD i []).map (interp V (consList bs (consList as ρp))))
      ∈ˢ d.idx ψ ρp (d.tgts c j i) ∧
    bs.foldl SetTheory.app f
      ∈ˢ app (X (d.tgts c j i))
        (d.tup ψ (d.tgts c j i)
          ((((d.Eiss c ψ).getD j []).getD i []).map
            (interp V (consList bs (consList as ρp))))) := by
  have hslotFit := hM.idxFit ψ ρp hsat X hX c hc t ht j hj i hi hrec as hpre
  have hidx := (hslotFit.2.2 bs hbs).2
  rw [consList_append] at hidx
  refine ⟨tupW_mem hidx, ?_⟩
  have hfold := piTele_fold (V := V) hw (B := fun ys =>
      app (X (d.tgts c j i))
        (tupW (d.uM (d.tgts c j i) ψ)
          ((((d.Eiss c ψ).getD j []).getD i []).map (interp V (consList ys (consList as ρp))))))
    (acc := ([] : List V)) hf (fitsS_teleOfFields.mpr hbs)
  rw [List.nil_append] at hfold
  exact hfold

end Predecessor

/-! ## 34. `hpref'` — the guard at the CALLEE's class (session 15)

§33's premise `hpref' : SpineFit ρ (pdoms c') xs` is what the ruling
of 2026-09-22 buys.  The kernel now checks that a family's recursors
share their whole rule prefix (`checkBlockRecPrefixAgree`, stage (b'),
`Kernel/Inductives/BlockInstall.lean`), and the run exports it as a
per-position `isDefEq` between the two openings
(`checkBlockRecK_prefixAgree`, `BlockRecMem.lean`).

Two steps take that to the premise, and only the first is semantic:

* **the readings agree** — `DefEqClaim` at the stage's own
  `isDefEqCore` calls.  It is the ONE step still owed, and it is the
  standard certified hop (`BlockRecTyping.lean` §1 runs it for the
  rule stage's own `isDefEq`); its side conditions are the openings'
  `CtxOk`/`WScoped`/`LeavesBounded`, which `opening_vars` and
  `checkBlockRecK_tyBounds`' inputs already carry;
* **a fitting spine transfers** — `spineFit_congr_readings`, below,
  which is a plain induction on the walk. -/

section CalleeGuard

/-- **A fitting spine transfers along equal READINGS**: `SpineFit`
mentions the domains only through `interp`, so two domain lists whose
entries read the same at every frame have the same fitting spines.

**Its premise is not payable at the run** (§S16.1): a certified
`isDefEq` yields equal readings at the frames satisfying the
opening's CONTEXT and at no others.  §35's `spineFit_congr_walk` is
the version the run can feed — the domains agree at the frames the
WALK reaches — and `blockRecHpref_run` is the producer.  This one
stays as the special case, and as the record of what the shape looked
like before the currency was checked. -/
theorem spineFit_congr_readings :
    ∀ {Fs Gs : List AnnotTerm} {ρ : Nat → V} {as : List V},
      Fs.length = Gs.length →
      (∀ l, l < Fs.length → ∀ σ : Nat → V,
        interp V σ (Fs.getD l default) = interp V σ (Gs.getD l default)) →
      SpineFit ρ Fs as → SpineFit ρ Gs as
  | [], [], _, [], _, _, _ => trivial
  | [], _ :: _, _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, _, hl, _, _ => by simp at hl
  | _ :: _, _ :: _, _, [], _, _, hf => hf.elim
  | F :: Fs, G :: Gs, ρ, a :: as, hl, hag, hf => by
    have h0 := hag 0 (by simp) ρ
    simp only [List.getD_cons_zero] at h0
    refine ⟨h0 ▸ hf.1, ?_⟩
    refine spineFit_congr_readings (by simpa using hl) (fun l hll σ => ?_) hf.2
    have := hag (l + 1) (by simpa using hll) σ
    simpa using this

/-- **`hpref'`, from the family's shared prefix**: the guard at
recursor `c` is the guard at recursor `c'` once their domains read the
same.  §33's consumer takes it at exactly this shape — but through
§35's `blockRecHpref_run`/`_runK`, which are the RUN-level producers;
this theorem's `hdoms` quantifies over all frames and nothing at the
run can supply it (§S16.1). -/
theorem blockRecHpref {pdoms : Nat → List AnnotTerm} {c c' : Nat} {ρ : Nat → V} {xs : List V}
    (hlen : (pdoms c).length = (pdoms c').length)
    (hdoms : ∀ l, l < (pdoms c).length → ∀ σ : Nat → V,
      interp V σ ((pdoms c).getD l default) = interp V σ ((pdoms c').getD l default))
    (hfit : SpineFit ρ (pdoms c) xs) :
    SpineFit ρ (pdoms c') xs :=
  spineFit_congr_readings hlen hdoms hfit

end CalleeGuard


/-! ## 35. THE CERTIFIED HOP — `hpref'` from the run (session 16)

§34 turns EQUAL domain readings into §33's `hpref'`; what it left open
is the hop from stage (b')'s `isDefEq` to those readings, and this
section is that hop, end to end.  Four steps, and only the third is
about the checker:

* **the two openings meet** (A) — stage (b') opens a recursor's stored
  type at the RULE PREFIX, O-2 at the full `mI + 1` binders, so the
  shorter opening has to be the longer one's prefix
  (`openPisAtFvars_split`, `openPisAtFvars_add`'s converse);
* **the walk pays for less than §34 asked** (B) — `SpineFit` reads
  entry `l` at the spine's own first `l` values, so the domains need
  only agree THERE (`spineFit_congr_walk`).  §34's all-frames premise
  is not payable: `DefEqClaim` concludes at the frames satisfying the
  opening's context and at no others;
* **`CtxOk` at the OTHER opening's context** (C/E) — `CtxOk`'s per-leaf
  obligation is an EQUATION between the leaf annotation's reading and
  the context entry, not a syntactic identity
  (`ctxOk_of_openers_congr`), and an opener at `l` mentions only
  openers below `l`, so the second recursor's `l`-th domain can be read
  against the FIRST one's context using only the agreement already
  proved at the earlier positions.  That is what makes the induction
  on the position go through;
* **the run** (G) — the openings' readings ARE `blockRulePdomsAV`'s
  entries, the gradings come off the recursor type's own `.pi` tower
  (`piTeleAV_graded`), and `blockRecHpref_run` chains the two hops
  `c → 0 → c'` through the reference recursor.  The two hops run in
  OPPOSITE orientations of one `isDefEq`, which is why the hop takes
  its comparison as a disjunction — `DefEqClaim` concludes an
  EQUATION, and the check supplies only the one order.

§28's own premise falls out on the way (`blockRulePdomsAV_bounded`,
`blockRecPdomsK_run`): the boundedness it asked for is
`checkBlockRecK_tyBounds`' first conjunct at the prefix, so the kit's
lifted guard and the base form are one term at the run and
`blockRecHpref_runK` is the kit's own spelling. -/

/-! ## A. Two openings of one type: the shorter is a prefix -/

/-- **An opening splits**: `openPisAtFvars_add`'s converse. -/
theorem openPisAtFvars_split :
    ∀ (n : Nat) {m : Nat} {e : Expr} {d : Nat} {F : List Expr} {o' : Expr},
      openPisAtFvars (n + m) e d = some (F, o') →
      ∃ (fvs fvs' : List Expr) (o : Expr),
        openPisAtFvars n e d = some (fvs, o) ∧
        openPisAtFvars m o (d + n) = some (fvs', o') ∧ F = fvs ++ fvs'
  | 0, _, e, d, F, o', h => ⟨[], F, e, rfl, by simpa using h, rfl⟩
  | n + 1, m, e, d, F, o', h => by
    rw [show n + 1 + m = n + m + 1 from by omega] at h
    match e, h with
    | .forallE dom body mb, h =>
      simp only [openPisAtFvars] at h
      split at h
      · next fvs₁ e₁ h₁ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨fvs, fvs', o, hA, hB, hF⟩ := openPisAtFvars_split n h₁
        refine ⟨Expr.fvar d dom :: fvs, fvs', o, ?_, ?_, by rw [hF]; rfl⟩
        · simp only [openPisAtFvars, hA]
        · rw [show d + (n + 1) = d + 1 + n from by omega]; exact hB
      · exact nomatch h
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [openPisAtFvars] at h

/-- **The shorter opening's openers are the longer one's prefix.** -/
theorem openPisAtFvars_prefix_getElem {n N : Nat} {e : Expr} {d : Nat}
    {F fvs : List Expr} {o o' : Expr} (hle : n ≤ N)
    (hlong : openPisAtFvars N e d = some (F, o'))
    (hshort : openPisAtFvars n e d = some (fvs, o)) :
    ∀ l, l < n → F[l]? = fvs[l]? := by
  obtain ⟨m, rfl⟩ : ∃ m, N = n + m := ⟨N - n, by omega⟩
  obtain ⟨fvs₀, fvs', o₀, hA, -, rfl⟩ := openPisAtFvars_split n hlong
  obtain ⟨rfl, -⟩ : fvs₀ = fvs ∧ o₀ = o := by
    have := Option.some.inj (hA.symm.trans hshort)
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  intro l hl
  exact List.getElem?_append_left (by rw [ConLeche.Verify.openPisAtFvars_length _ hshort]; exact hl)

/-! ## B. A fitting spine transfers along the WALK's own readings -/

/-- **`spineFit_congr_readings` at the walk's own frames**: the domains
have to agree only at the frames the walk actually reaches — entry `l`
under the spine's own first `l` values.  §34's all-frames version is
the special case, and this one is what a run-level agreement (proved
at the opening's satisfying frames, never at all of them) can pay. -/
theorem spineFit_congr_walk :
    ∀ {Fs Gs : List AnnotTerm} {ρ : Nat → V} {as : List V},
      Fs.length = Gs.length →
      (∀ l, l < Fs.length →
        interp V (consList (as.take l) ρ) (Fs.getD l default)
          = interp V (consList (as.take l) ρ) (Gs.getD l default)) →
      SpineFit ρ Fs as → SpineFit ρ Gs as
  | [], [], _, [], _, _, _ => trivial
  | [], _ :: _, _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, _, hl, _, _ => by simp at hl
  | _ :: _, _ :: _, _, [], _, _, hf => hf.elim
  | F :: Fs, G :: Gs, ρ, a :: as, hl, hag, hf => by
    have h0 := hag 0 (by simp)
    simp only [List.take_zero, consList_nil, List.getD_cons_zero] at h0
    refine ⟨h0 ▸ hf.1, ?_⟩
    refine spineFit_congr_walk (by simpa using hl) (fun l hll => ?_) hf.2
    have h := hag (l + 1) (by simpa using hll)
    simpa [List.take_succ_cons, consList_cons] using h

/-! ## C. `CtxOk` at an opening whose entries only AGREE with the
context's -/

/-- **`ctxOk_of_openers` with the context's entries only SEMANTICALLY
equal to the openers' own readings.**  `CtxOk`'s per-leaf obligation is
an EQUATION between the leaf annotation's reading and the context
entry, not a syntactic identity, so an opening may correlate with
another opening's context as soon as the two agree at the satisfying
frames — which is exactly what a `checkBlockDefEqList` between the two
buys.  With `Ba := Aa` and `hagree := rfl` this is `ctxOk_of_openers`. -/
theorem ctxOk_of_openers_congr {env : Env} {m : EnvModel V env} {φ : Name → Nat}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (m.acval n ψ).liftN 1 k = m.acval n ψ)
    {k : Nat} {fvs : List Expr} {Aa Ba : Nat → AnnotTerm} {Δa : List AnnotTerm}
    (hΔlen : Δa.length = k)
    (hshape : ∀ (i : Nat) (x : Expr), fvs[i]? = some x → ∃ ty, x = Expr.fvar i ty)
    (hws : ∀ x ∈ fvs, Expr.WScoped k x)
    (hdoms : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      denoteMeta m.acval env φ i (Expr.fvarTypeD x) = some (Ba i))
    {e : Expr} {n : Nat}
    (hleaf : ∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs)
    (hltE : ∀ l ∈ e.fvarLeaves, l.1 < n)
    (hent : ∀ i, i < n → Δa[k - 1 - i]? = some (Aa i))
    (hagree : ∀ i, i < n → i < k → ∀ ρ : Nat → V, Sat V Δa ρ →
      interp V (shiftE (k - i) 0 ρ) (Ba i) = interp V (shiftE (k - i) 0 ρ) (Aa i))
    (hokB : ∀ i, i < n → i < k → ∀ ρ : Nat → V, Sat V Δa ρ →
      WellDenotedV V (shiftE (k - i) 0 ρ) (Ba i)) :
    CtxOk m φ k Δa e := by
  refine ⟨hΔlen, ?_⟩
  intro l hl
  have hmem := hleaf l hl
  obtain ⟨pos, hpos⟩ := List.getElem?_of_mem hmem
  obtain ⟨ty, hx⟩ := hshape pos _ hpos
  obtain ⟨h1, h2⟩ : l.1 = pos ∧ l.2 = ty := by
    injection hx with a b
    exact ⟨a, b⟩
  subst h1 h2
  have hlt : l.1 < n := hltE l hl
  have hw := hws _ (List.mem_of_getElem? hpos)
  have hwty : l.1 < k ∧ Expr.WScoped l.1 l.2 := by
    simpa [Expr.WScoped] using hw
  refine ⟨hwty.1, hwty.2.fvarsBelow, (Ba l.1).liftN (k - l.1) 0, Aa l.1,
    ?_, hent l.1 hlt, ?_, ?_⟩
  · have hd1 := hdoms l.1 _ hpos
    rw [show Expr.fvarTypeD (Expr.fvar l.1 l.2) = l.2 from rfl] at hd1
    rw [denoteMeta_lift hacl hwty.2 k (by omega), hd1]
    rfl
  · intro ρ hρ
    rw [interp_liftN, hagree l.1 hlt hwty.1 ρ hρ, shiftE_zero]
    congr 1
    funext j
    congr 1
    omega
  · intro ρ hρ
    refine (WellDenotedV_liftN V (k - l.1) (Ba l.1) 0 ρ).mpr ?_
    exact hokB l.1 hlt hwty.1 ρ hρ

/-! ## D. Small list/frame helpers -/

omit [SetTheory V] in
/-- The frame `rP - j` slots up from a spine's own is the spine's first
`j` values. -/
theorem shiftE_consList_take {xs : List V} {ρ₀ : Nat → V} {rP : Nat} (j : Nat)
    (hxlen : xs.length = rP) :
    shiftE (rP - j) 0 (consList xs ρ₀) = consList (xs.take j) ρ₀ := by
  have h1 : (xs.drop j).length = rP - j := by rw [List.length_drop, hxlen]
  have h2 : consList xs ρ₀ = consList (xs.drop j) (consList (xs.take j) ρ₀) := by
    rw [← consList_append, List.take_append_drop]
  rw [h2, ← h1, shiftE_consList]

omit [SetTheory V] in
theorem getD_take_of_lt {L : List AnnotTerm} {j i : Nat} (h : j < i) :
    (L.take i).getD j default = L.getD j default := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rw [List.getElem?_take, if_pos h]

omit [SetTheory V] in
theorem getElem?_reverse_entry {L : List AnnotTerm} {n i : Nat}
    (hlen : L.length = n) (hi : i < n) :
    L.reverse[n - 1 - i]? = some (L.getD i default) := by
  rw [List.getElem?_reverse (by rw [hlen]; omega), hlen,
    show n - 1 - (n - 1 - i) = i from by omega,
    List.getElem?_eq_getElem (by rw [hlen]; exact hi),
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact hi)]
  rfl

/-! ## E. `CtxOk` at one opener's annotation -/

/-- An opener's annotation mentions only openers. -/
theorem openerType_leaves {rP : Nat} {ty : Expr} {fvs : List Expr} {o : Expr}
    (hop : openPisAtFvars rP ty 0 = some (fvs, o)) (hw0 : Expr.WScoped 0 ty)
    {l : Nat} {x : Expr} (hx : fvs[l]? = some x) :
    ∀ lf ∈ (Expr.fvarTypeD x).fvarLeaves, Expr.fvar lf.1 lf.2 ∈ fvs := by
  intro lf hlf
  obtain ⟨ty', hty'⟩ := openPisAtFvars_index rP ty 0 hop l x hx
  have hxx : lf ∈ x.fvarLeaves := by
    rw [hty'] at hlf ⊢
    simp only [Expr.fvarTypeD] at hlf
    simp only [Expr.fvarLeaves]
    exact List.mem_cons_of_mem _ hlf
  rcases openPisAtFvars_leaves rP hop lf (Or.inr ⟨x, List.mem_of_getElem? hx, hxx⟩) with h | h
  · exact absurd (Expr.fvarLeaves_lt_of_wscoped hw0 lf h) (Nat.not_lt_zero _)
  · exact h

/-- **An opener's annotation correlates with a context of the SAME
length whose entries agree with the opening's own readings below the
opener's index.**  The opener at `l` mentions only openers below `l`,
so nothing above `l` is consulted — which is what lets the SECOND
recursor's domain be read against the FIRST one's context while the
agreement is still being proved position by position. -/
theorem ctxOk_openerType {envT : Env} {m : EnvModel V envT} {φ : Name → Nat} {rP : Nat}
    {ty : Expr} {fvs : List Expr} {o : Expr}
    (hop : openPisAtFvars rP ty 0 = some (fvs, o))
    (hwty : Expr.WScoped 0 ty)
    {doms Δa : List AnnotTerm} {Aa : Nat → AnnotTerm}
    (hΔlen : Δa.length = rP)
    (hd : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      denoteMeta m.acval envT φ i (Expr.fvarTypeD x) = some (doms.getD i default))
    (hent : ∀ i, i < rP → Δa[rP - 1 - i]? = some (Aa i))
    {l : Nat} (hl : l < rP) {x : Expr} (hx : fvs[l]? = some x)
    (hagree : ∀ i, i < l → ∀ ρ : Nat → V, Sat V Δa ρ →
      interp V (shiftE (rP - i) 0 ρ) (doms.getD i default)
        = interp V (shiftE (rP - i) 0 ρ) (Aa i))
    (hok : ∀ i, i < l → ∀ ρ : Nat → V, Sat V Δa ρ →
      WellDenotedV V (shiftE (rP - i) 0 ρ) (doms.getD i default)) :
    CtxOk m φ rP Δa (Expr.fvarTypeD x) := by
  have hleaf := openerType_leaves hop hwty hx
  have hltE : ∀ lf ∈ (Expr.fvarTypeD x).fvarLeaves, lf.1 < l := by
    intro lf hlf
    have hw := openPisAtFvars_typeWScoped rP hop hwty l x hx
    rw [Nat.zero_add] at hw
    exact Expr.fvarLeaves_lt_of_wscoped hw lf hlf
  refine ctxOk_of_openers_congr m.acval_closed (Aa := Aa)
    (Ba := fun i => doms.getD i default) hΔlen
    (by simpa using openPisAtFvars_index rP ty 0 hop)
    (by simpa using (openPisAtFvars_WScoped rP ty 0 hop hwty).1)
    hd hleaf hltE (fun i hi => hent i (by omega))
    (fun i hi _ ρ hρ => hagree i hi ρ hρ) (fun i hi _ ρ hρ => hok i hi ρ hρ)

/-! ## F. The certified hop -/

/-- Every frame satisfying a domain list's context IS a fitting
spine's frame. -/
theorem sat_reverse_cases {doms : List AnnotTerm} {rP : Nat} (hlen : doms.length = rP)
    {ρ : Nat → V} (h : Sat V doms.reverse ρ) :
    ∃ (ρ₁ : Nat → V) (ys : List V),
      ys.length = rP ∧ SpineFit ρ₁ doms ys ∧ ρ = consList ys ρ₁ := by
  have h' : Sat V (doms.reverse ++ []) ρ := by simpa using h
  have hsp := spineFit_of_sat (Ds := doms) (Δ₀ := []) h'
  refine ⟨fun j => ρ (j + doms.length), (List.range doms.length).reverse.map ρ, ?_, hsp, ?_⟩
  · simp [hlen]
  · rw [← frameIdx_eq_reverse_map]
    have := consList_frameIdx doms.length ρ
    rw [shiftE_zero] at this
    exact this.symm

/-- **THE CERTIFIED HOP** — a fitting spine of the FIRST opening's
domains fits the SECOND's, as soon as the check compared the two
openings' binder domains position by position.

`DefEqClaim` is at the opening's OWN depth `rP`, so its conclusion is
an equation between the two readings LIFTED to that depth, at the
frames satisfying the first opening's context; `interp_liftN` turns
that into the equation the walk consumes — entry `l` at the spine's
first `l` values (`spineFit_congr_walk`).

The induction is on the position, and it has to be: `CtxOk` for the
SECOND opening's `l`-th domain reads its leaves — openers below `l` —
against the FIRST opening's context, which is exactly the agreement at
the earlier positions (`ctxOk_openerType`). -/
theorem prefixDoms_spineFit {envT : Env} (hμ : μ.verifiedChecks = true)
    (mp : EnvModelM V μ envT) {ψ : Name → Nat} {fuel rP : Nat}
    {tyA tyB : Expr} {fvsA fvsB : List Expr} {oA oB : Expr}
    (hopA : openPisAtFvars rP tyA 0 = some (fvsA, oA))
    (hopB : openPisAtFvars rP tyB 0 = some (fvsB, oB))
    (hwA : Expr.WScoped 0 tyA) (hwB : Expr.WScoped 0 tyB)
    (hbA : tyA.looseBVarsBounded 0 = true) (hbB : tyB.looseBVarsBounded 0 = true)
    {domsA domsB : List AnnotTerm}
    (hlenA : domsA.length = rP) (hlenB : domsB.length = rP)
    (hdA : ∀ (i : Nat) (x : Expr), fvsA[i]? = some x →
      denoteMeta mp.base2.acval envT ψ i (Expr.fvarTypeD x) = some (domsA.getD i default))
    (hdB : ∀ (i : Nat) (x : Expr), fvsB[i]? = some x →
      denoteMeta mp.base2.acval envT ψ i (Expr.fvarTypeD x) = some (domsB.getD i default))
    (hokA : ∀ i, i < rP → ∀ (ρ : Nat → V) (ys : List V),
      SpineFit ρ (domsA.take i) ys → WellDenotedV V (consList ys ρ) (domsA.getD i default))
    (hokB : ∀ i, i < rP → ∀ (ρ : Nat → V) (ys : List V),
      SpineFit ρ (domsB.take i) ys → WellDenotedV V (consList ys ρ) (domsB.getD i default))
    (hdeq : ∀ i, i < rP →
      ConLeche.isDefEqCore μ envT fuel rP ((fvsA.map Expr.fvarTypeD).getD i default)
          ((fvsB.map Expr.fvarTypeD).getD i default) = .ok true ∨
        ConLeche.isDefEqCore μ envT fuel rP ((fvsB.map Expr.fvarTypeD).getD i default)
          ((fvsA.map Expr.fvarTypeD).getD i default) = .ok true)
    {ρ₀ : Nat → V} {xs : List V} (hfit : SpineFit ρ₀ domsA xs) :
    SpineFit ρ₀ domsB xs := by
  obtain ⟨-, -, ihd, -⟩ := checkSoundAt (V := V) hμ (Rules.RulesInputs.ofSem mp ψ) fuel
  have hlA : fvsA.length = rP := ConLeche.Verify.openPisAtFvars_length _ hopA
  have hlB : fvsB.length = rP := ConLeche.Verify.openPisAtFvars_length _ hopB
  have hlbA := (ConLeche.Verify.openPisAtFvars_bounded _ hopA hbA).2
  have hlbB := (ConLeche.Verify.openPisAtFvars_bounded _ hopB hbB).2
  have hentA : ∀ i, i < rP → domsA.reverse[rP - 1 - i]? = some (domsA.getD i default) :=
    fun i hi => getElem?_reverse_entry hlenA hi
  -- the agreement, position by position, at every fitting spine's frame
  have key : ∀ l, l < rP → ∀ (ρ₁ : Nat → V) (ys : List V), SpineFit ρ₁ domsA ys →
      interp V (consList (ys.take l) ρ₁) (domsA.getD l default)
        = interp V (consList (ys.take l) ρ₁) (domsB.getD l default) := by
    intro l
    induction l using Nat.strongRecOn with
    | _ l IH =>
      intro hl ρ₁ ys hfitY
      have hylen : ys.length = rP := by rw [SpineFit.length_eq hfitY, hlenA]
      -- the agreements below `l`, at every context-satisfying frame
      have hbelow : ∀ i, i < l → ∀ ρ : Nat → V, Sat V domsA.reverse ρ →
          interp V (shiftE (rP - i) 0 ρ) (domsA.getD i default)
            = interp V (shiftE (rP - i) 0 ρ) (domsB.getD i default) := by
        intro i hi ρ hρ
        obtain ⟨ρ₂, zs, hzlen, hfitZ, rfl⟩ := sat_reverse_cases hlenA hρ
        rw [shiftE_consList_take i hzlen]
        exact IH i hi (by omega) ρ₂ zs hfitZ
      have hokAf : ∀ i, i < l → ∀ ρ : Nat → V, Sat V domsA.reverse ρ →
          WellDenotedV V (shiftE (rP - i) 0 ρ) (domsA.getD i default) := by
        intro i hi ρ hρ
        obtain ⟨ρ₂, zs, hzlen, hfitZ, rfl⟩ := sat_reverse_cases hlenA hρ
        rw [shiftE_consList_take i hzlen]
        exact hokA i (by omega) ρ₂ (zs.take i) (spineFit_take_any hfitZ i)
      have hokBf : ∀ i, i < l → ∀ ρ : Nat → V, Sat V domsA.reverse ρ →
          WellDenotedV V (shiftE (rP - i) 0 ρ) (domsB.getD i default) := by
        intro i hi ρ hρ
        obtain ⟨ρ₂, zs, hzlen, hfitZ, rfl⟩ := sat_reverse_cases hlenA hρ
        rw [shiftE_consList_take i hzlen]
        refine hokB i (by omega) ρ₂ (zs.take i) ?_
        refine spineFit_congr_walk (by rw [List.length_take, List.length_take, hlenA, hlenB]) ?_
          (spineFit_take_any hfitZ i)
        intro j hj
        rw [List.length_take, hlenA] at hj
        have hji : j < i := by omega
        rw [getD_take_of_lt hji, getD_take_of_lt hji, List.take_take,
          show min j i = j from by omega]
        exact IH j (by omega) (by omega) ρ₂ zs hfitZ
      -- the two subjects
      obtain ⟨xA, hxA⟩ : ∃ x, fvsA[l]? = some x :=
        ⟨fvsA[l]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨xB, hxB⟩ : ∃ x, fvsB[l]? = some x :=
        ⟨fvsB[l]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      have hsubA : (fvsA.map Expr.fvarTypeD).getD l default = Expr.fvarTypeD xA := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, hxA]; rfl
      have hsubB : (fvsB.map Expr.fvarTypeD).getD l default = Expr.fvarTypeD xB := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, hxB]; rfl
      -- `CtxOk` for both, at the FIRST opening's context
      have hctxA : CtxOk mp.base2 ψ rP domsA.reverse (Expr.fvarTypeD xA) :=
        ctxOk_openerType hopA hwA (by simp [hlenA]) hdA hentA hl hxA
          (fun i hi ρ hρ => rfl) hokAf
      have hctxB : CtxOk mp.base2 ψ rP domsA.reverse (Expr.fvarTypeD xB) :=
        ctxOk_openerType hopB hwB (by simp [hlenA]) hdB hentA hl hxB
          (fun i hi ρ hρ => (hbelow i hi ρ hρ).symm) hokBf
      -- the readings at the opening's own depth
      have hwsA : Expr.WScoped rP (Expr.fvarTypeD xA) := by
        have := openPisAtFvars_typeWScoped rP hopA hwA l xA hxA
        rw [Nat.zero_add] at this
        exact this.mono (by omega)
      have hwsB : Expr.WScoped rP (Expr.fvarTypeD xB) := by
        have := openPisAtFvars_typeWScoped rP hopB hwB l xB hxB
        rw [Nat.zero_add] at this
        exact this.mono (by omega)
      have hrdA : denoteMeta mp.base2.acval envT ψ rP (Expr.fvarTypeD xA)
          = some ((domsA.getD l default).liftN (rP - l) 0) := by
        have hw := openPisAtFvars_typeWScoped rP hopA hwA l xA hxA
        rw [Nat.zero_add] at hw
        rw [denoteMeta_lift mp.base2.acval_closed hw rP (by omega), hdA l xA hxA]
        rfl
      have hrdB : denoteMeta mp.base2.acval envT ψ rP (Expr.fvarTypeD xB)
          = some ((domsB.getD l default).liftN (rP - l) 0) := by
        have hw := openPisAtFvars_typeWScoped rP hopB hwB l xB hxB
        rw [Nat.zero_add] at hw
        rw [denoteMeta_lift mp.base2.acval_closed hw rP (by omega), hdB l xB hxB]
        rfl
      -- the gradings at the opening's own depth
      have hokAl : ∀ ρ : Nat → V, Sat V domsA.reverse ρ →
          WellDenotedV V ρ ((domsA.getD l default).liftN (rP - l) 0) := by
        intro ρ hρ
        refine (WellDenotedV_liftN V (rP - l) _ 0 ρ).mpr ?_
        obtain ⟨ρ₂, zs, hzlen, hfitZ, rfl⟩ := sat_reverse_cases hlenA hρ
        rw [shiftE_consList_take l hzlen]
        exact hokA l hl ρ₂ (zs.take l) (spineFit_take_any hfitZ l)
      have hokBl : ∀ ρ : Nat → V, Sat V domsA.reverse ρ →
          WellDenotedV V ρ ((domsB.getD l default).liftN (rP - l) 0) := by
        intro ρ hρ
        refine (WellDenotedV_liftN V (rP - l) _ 0 ρ).mpr ?_
        obtain ⟨ρ₂, zs, hzlen, hfitZ, rfl⟩ := sat_reverse_cases hlenA hρ
        rw [shiftE_consList_take l hzlen]
        refine hokB l hl ρ₂ (zs.take l) ?_
        refine spineFit_congr_walk (by rw [List.length_take, List.length_take, hlenA, hlenB]) ?_
          (spineFit_take_any hfitZ l)
        intro j hj
        rw [List.length_take, hlenA] at hj
        have hjl : j < l := by omega
        rw [getD_take_of_lt hjl, getD_take_of_lt hjl, List.take_take,
          show min j l = j from by omega]
        exact IH j hjl (by omega) ρ₂ zs hfitZ
      -- the hop
      have hlbAx := hlbA xA (List.mem_of_getElem? hxA)
      have hlbBx := hlbB xB (List.mem_of_getElem? hxB)
      have hLA := leavesBounded_of_openers hlbA (openerType_leaves hopA hwA hxA)
      have hLB := leavesBounded_of_openers hlbB (openerType_leaves hopB hwB hxB)
      have hsat : Sat V domsA.reverse (consList ys ρ₁) := by
        simpa using sat_of_spineFit (Sat_nil V ρ₁) hfitY
      have heq : interp V (consList ys ρ₁) ((domsA.getD l default).liftN (rP - l) 0)
          = interp V (consList ys ρ₁) ((domsB.getD l default).liftN (rP - l) 0) := by
        rcases hdeq l hl with hd | hd
        · exact ihd (hsubA ▸ hsubB ▸ hd) hwsA hlbAx hLA hwsB hlbBx hLB
            hctxA hctxB hrdA hrdB hokAl hokBl (consList ys ρ₁) hsat
        · exact (ihd (hsubA ▸ hsubB ▸ hd) hwsB hlbBx hLB hwsA hlbAx hLA
            hctxB hctxA hrdB hrdA hokBl hokAl (consList ys ρ₁) hsat).symm
      rw [interp_liftN, interp_liftN, shiftE_consList_take l hylen] at heq
      exact heq
  exact spineFit_congr_walk (by rw [hlenA, hlenB]) (fun l hl => key l (by omega) ρ₀ xs hfit) hfit

/-! ## G. The run's side -/

section Run

variable {envC : Env} {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}

/-- **A stored recursor type is CLOSED** — the two scoping facts
`prefixDoms_spineFit` asks of an opening's subject, at the run.
`checkBlockRecK_tyBounds` derives them inline; they are named here
because the hop needs them on their own. -/
theorem checkBlockRecK_tyClosed
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {i : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[i]? = some r) :
    Expr.WScoped 0 r.1.type ∧ r.1.type.looseBVarsBounded 0 = true := by
  obtain ⟨⟨cv, hcv⟩, -, -, -⟩ := checkBlockRecK_tyShape h hr
  obtain ⟨-, -, -, -, hlb0, hfv0, tyA, -, -, hann, -, -, -, -, hcv'⟩ :=
    ConLeche.checkConstantVal_inv hcv
  have hrty : r.1.type = tyA := by rw [hcv']
  exact ⟨by
      rw [hrty]
      exact ConLeche.annotateCore_WScoped _ _ hann (Expr.WScoped.of_not_hasFvar hfv0),
    by rw [hrty]; exact ConLeche.annotateCore_looseBVars _ _ hann hlb0⟩

/-- **The rule PREFIX opening's readings are `blockRulePdomsAV`'s
entries.**  Stage (b') opens the stored type at the rule prefix alone;
O-2 reads it at the full `mI + 1` binders.  The shorter opening is the
longer one's prefix (`openPisAtFvars_prefix_getElem`), so the two名 the
same annotations at every position below `rP`. -/
theorem blockRulePdomsAV_reads (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {i : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[i]? = some r) (ψ : Name → Nat) {fvs : List Expr} {o : Expr}
    (hop : openPisAtFvars (p.toBlockShape.rulePrefixAt i) r.1.type 0 = some (fvs, o)) :
    ∀ (l : Nat) (x : Expr), fvs[l]? = some x →
      denoteMeta mpC.base2.acval envC ψ l (Expr.fvarTypeD x)
        = some ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ i).getD l default) := by
  intro l x hx
  have hlfvs : fvs.length = p.toBlockShape.rulePrefixAt i :=
    ConLeche.Verify.openPisAtFvars_length _ hop
  have hl : l < p.toBlockShape.rulePrefixAt i := by
    have := (List.getElem?_eq_some_iff.mp hx).1
    omega
  have hle := blockRecHrPle (p := p) h (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨fvsL, concl, hopL, -, -, -, -, hbind, -, -⟩ := checkBlockRecK_tyPis hμ mpC h hr ψ
  have hpre := openPisAtFvars_prefix_getElem (by omega) hopL hop l hl
  obtain ⟨pd, hpd, -, hread⟩ := hbind l x (by rw [hpre]; exact hx)
  rw [hread]
  congr 1
  rw [blockRulePdomsAV, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_take, if_pos hl, hpd]
  rfl

/-- **A `.pi` tower's PREFIX domains are graded along their own fitting
spines** — `piTeleAV_graded` read back at the peel's entries. -/
theorem prefixDoms_graded_of_tower {rds : List (Nat × Nat × AnnotTerm)} {cc : AnnotTerm}
    {rP : Nat} (hrP : rP ≤ rds.length)
    (hwd : ∀ ρ : Nat → V, WellDenotedV V ρ (mkPisAV rds cc))
    {l : Nat} (hl : l < rP) {ρ : Nat → V} {ys : List V}
    (hys : SpineFit ρ (((rds.take rP).map (·.2.2)).take l) ys) :
    WellDenotedV V (consList ys ρ) (((rds.take rP).map (·.2.2)).getD l default) := by
  have hlk : l < rds.length := by omega
  have htele := piTeleAV_of_stripPisAV (stripPisAV_mkPisAV rds cc)
  obtain ⟨okΓ, -⟩ := piTeleAV_graded (V := V) htele (Δ₀ := []) (fun ρ' _ => hwd ρ')
  simp only [List.append_nil] at okΓ
  obtain ⟨pd, hpd⟩ : ∃ pd, rds[l]? = some pd :=
    ⟨rds[l]'hlk, List.getElem?_eq_getElem hlk⟩
  have hentΓ : ((rds.map (·.2.2)).reverse).getD (rds.length - 1 - l) default = pd.2.2 :=
    getD_reverse_of_peel rfl hlk hpd
  have hpdoms : ((rds.take rP).map (·.2.2)).getD l default = pd.2.2 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take, if_pos hl, hpd]
    rfl
  have htk : ((rds.take rP).map (·.2.2)).take l = (rds.take l).map (·.2.2) := by
    rw [← List.map_take, List.take_take, show min l rP = l from by omega]
  have hdropΓ : ((rds.map (·.2.2)).reverse).drop (rds.length - l)
      = ((rds.take l).map (·.2.2)).reverse := by
    rw [reverse_map_take_drop rds l,
      List.drop_append_of_le_length (by simp),
      List.drop_eq_nil_of_le (by simp), List.nil_append]
  have hsat : Sat V (((rds.map (·.2.2)).reverse).drop (rds.length - l)) (consList ys ρ) := by
    rw [hdropΓ, ← htk]
    simpa using sat_of_spineFit (Sat_nil V ρ) hys
  have hres := okΓ l hlk (consList ys ρ) hsat
  rw [hentΓ] at hres
  rw [hpdoms]
  exact hres

/-- **The rule prefix's domains are GRADED at the run.** -/
theorem blockRulePdomsAV_graded (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {i : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[i]? = some r) (ψ : Name → Nat) :
    ∀ l, l < p.toBlockShape.rulePrefixAt i → ∀ (ρ : Nat → V) (ys : List V),
      SpineFit ρ ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ i).take l) ys →
      WellDenotedV V (consList ys ρ)
        ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ i).getD l default) := by
  intro l hl ρ ys hys
  have hle := blockRecHrPle (p := p) h (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨-, -, -, -, hmk, hlenRds, -, -, -, hwdTy⟩ := checkBlockRecK_tyPis hμ mpC h hr ψ
  refine prefixDoms_graded_of_tower (cc := blockRecConclAV mpC.base2.acval envC
      p.toBlockShape rs ψ i) (by omega) (fun ρ' => by rw [← hmk]; exact hwdTy ρ') hl hys

/-- **`hpref'`, FROM THE RUN** (§33's premise, discharged): a spine
fitting recursor `c`'s rule-prefix domains fits recursor `c'`'s.

The reference is recursor `0` — stage (b') compares every other
recursor's opened prefix against it — so the transfer is two hops,
`c → 0 → c'`, and the two run in OPPOSITE orientations of the same
`isDefEq` (which is why `prefixDoms_spineFit` takes its comparison as
a disjunction: `DefEqClaim`'s conclusion is an equation, and the check
supplies only the one order). -/
theorem blockRecHpref_run (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (ψ : Name → Nat) {c c' : Nat}
    {rc rc' : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hrc : rs[c]? = some rc) (hrc' : rs[c']? = some rc')
    {ρ : Nat → V} {xs : List V}
    (hfit : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) xs) :
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c') xs := by
  have hcl : c < rs.length := (List.getElem?_eq_some_iff.mp hrc).1
  obtain ⟨r0, hr0⟩ : ∃ r0, rs[0]? = some r0 :=
    ⟨rs[0]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨fvs0, o0, hop0, hall⟩ := checkBlockRecK_prefixAgree h hr0
  have hl0 : fvs0.length = p.toBlockShape.rulePrefixAt 0 :=
    ConLeche.Verify.openPisAtFvars_length _ hop0
  have hlen0 : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ 0).length
      = p.toBlockShape.rulePrefixAt 0 := blockRulePdomsAV_length hμ mpC h hr0 ψ
  have hd0 := blockRulePdomsAV_reads hμ mpC h hr0 ψ hop0
  have hok0 := blockRulePdomsAV_graded hμ mpC h hr0 ψ
  obtain ⟨hw0, hb0⟩ := checkBlockRecK_tyClosed h hr0
  -- one hop, in both orientations
  have hop : ∀ (i : Nat) (ri : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[i]? = some ri → ∀ (σ : Nat → V) (zs : List V),
        (SpineFit σ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ i) zs →
          SpineFit σ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ 0) zs) ∧
        (SpineFit σ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ 0) zs →
          SpineFit σ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ i) zs) := by
    intro i ri hri σ zs
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · obtain rfl : ri = r0 := Option.some.inj (hri.symm.trans hr0)
      exact ⟨id, id⟩
    obtain ⟨hrP, fvsI, oI, hopI, hlenEq, hdeqI⟩ := hall i ri hri hipos
    have hlI : fvsI.length = p.toBlockShape.rulePrefixAt 0 := by
      rw [← hlenEq]; exact hl0
    have hopI' : openPisAtFvars (p.toBlockShape.rulePrefixAt i) ri.1.type 0 = some (fvsI, oI) := by
      rw [hrP]; exact hopI
    have hlenI : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ i).length
        = p.toBlockShape.rulePrefixAt 0 := by
      rw [blockRulePdomsAV_length hμ mpC h hri ψ, hrP]
    have hdI := blockRulePdomsAV_reads hμ mpC h hri ψ hopI'
    have hokI := blockRulePdomsAV_graded hμ mpC h hri ψ
    obtain ⟨hwI, hbI⟩ := checkBlockRecK_tyClosed h hri
    have hdeq0I : ∀ l, l < p.toBlockShape.rulePrefixAt 0 →
        ConLeche.isDefEqCore μ envC F (p.toBlockShape.rulePrefixAt 0)
          ((fvs0.map Expr.fvarTypeD).getD l default)
          ((fvsI.map Expr.fvarTypeD).getD l default) = .ok true :=
      fun l hl => hdeqI l (by omega)
    -- BOTH openings are passed at recursor `0`'s prefix count, which is
    -- what stage (b') compares at; `hrP` is the run's own equation and
    -- the ONLY thing that identifies it with recursor `i`'s (the two are
    -- definitionally equal only while the route's `k = 1` gate is down).
    constructor
    · intro hz
      exact prefixDoms_spineFit hμ mpC hopI hop0 hwI hw0 hbI hb0 hlenI hlen0 hdI hd0
        (fun l hl σ' ys hys => hokI l (by omega) σ' ys hys)
        (fun l hl σ' ys hys => hok0 l (by omega) σ' ys hys)
        (fun l hl => Or.inr (hdeq0I l hl)) hz
    · intro hz
      exact prefixDoms_spineFit hμ mpC hop0 hopI hw0 hwI hb0 hbI hlen0 hlenI hd0 hdI
        (fun l hl σ' ys hys => hok0 l (by omega) σ' ys hys)
        (fun l hl σ' ys hys => hokI l (by omega) σ' ys hys)
        (fun l hl => Or.inl (hdeq0I l hl)) hz
  exact (hop c' rc' hrc' ρ xs).2 ((hop c rc hrc ρ xs).1 hfit)

/-- **§28's boundedness premise, at the run**: the rule prefix's
domains are bounded at their own depths, so `blockRecPdomsK`'s `K`
lift is the identity.  `checkBlockRecK_tyBounds` says it of the whole
binder list; the prefix is its `take`. -/
theorem blockRulePdomsAV_bounded (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {i : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[i]? = some r) (ψ : Name → Nat) :
    ∀ l, l < (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ i).length →
      Term.bvarsBelow l
        (((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ i).getD l default).erase) := by
  intro l hl
  have hlp : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ i).length
      = p.toBlockShape.rulePrefixAt i := blockRulePdomsAV_length hμ mpC h hr ψ
  have hle := blockRecHrPle (p := p) h (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨-, -, -, -, -, hlenRds, -, -, -, -⟩ := checkBlockRecK_tyPis hμ mpC h hr ψ
  obtain ⟨hbnd, -⟩ := checkBlockRecK_tyBounds hμ mpC h hr ψ
  have hlk : l < (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ i).length := by omega
  obtain ⟨pd, hpd⟩ : ∃ pd, (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ i)[l]?
      = some pd :=
    ⟨_, List.getElem?_eq_getElem hlk⟩
  have heq : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ i).getD l default
      = pd.2.2 := by
    rw [blockRulePdomsAV, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_take, if_pos (by omega), hpd]
    rfl
  have hq := hbnd l hlk
  rw [List.getD_eq_getElem?_getD, hpd, Option.getD_some] at hq
  rw [heq]
  exact hq

/-- **§20's guard is the base form, at the run** — `blockRecPdomsK_eq`
with its premise discharged. -/
theorem blockRecPdomsK_run (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {i : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[i]? = some r) (ψ : Name → Nat) (K : Nat) :
    blockRecPdomsK K mpC.base2.acval envC p.toBlockShape rs ψ i
      = blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ i :=
  blockRecPdomsK_eq (blockRulePdomsAV_bounded hμ mpC h hr ψ)

/-- **`hpref'` at the KIT's own spelling** — `blockRecHpref_run`
through §28's collapse. -/
theorem blockRecHpref_runK (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (ψ : Name → Nat) (K : Nat) {c c' : Nat}
    {rc rc' : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hrc : rs[c]? = some rc) (hrc' : rs[c']? = some rc')
    {ρ : Nat → V} {xs : List V}
    (hfit : SpineFit ρ (blockRecPdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c) xs) :
    SpineFit ρ (blockRecPdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c') xs := by
  rw [blockRecPdomsK_run hμ mpC h hrc' ψ K]
  rw [blockRecPdomsK_run hμ mpC h hrc ψ K] at hfit
  exact blockRecHpref_run hμ mpC h ψ hrc hrc' hfit

end Run


/-! ## 36. REGIME SQ's KIT — the recursion theorem at `w = 0` (session 18)

The last structural hole of the three regimes.  At `w = 0` every
injection is the point (`BlockModelAt.mkZero`), so regime WF's
predecessor map is not merely different but DEGENERATE: `tcPred` reads
the payload's ∈-subterms and every payload is the point, so it is
empty and the recursion it carries is the trivial one.  Regime SQ's
predecessors are the INDEX tuples of the lone constructor's recursive
calls at the element's SOURCE spine (`blockSqPred`), and its
accessibility argument is the block's OWN lfp induction — which is why
session 14 made the recursion theorem `UnionRecKitC`'s field rather
than deriving it from an `Acc` witness.

Four steps:

* `blockSqPred` and `blockSqSpine` — the map, at the source spine the
  subsingleton criterion recovers from the index;
* `blockSqExu` — `UnionRecKitC.exu` by `lfpTuple_induction` on the
  block's representation, with `recGraph_singleton_of_preds`
  (`SetModel/RecGraph.lean`) at each step.  The step's obligation is
  that every predecessor's fibre is already a singleton, and the
  SEPARATED tuple is what carries it: a recursive field's value at the
  constructed element lies in the separated tuple at the call's index
  tuple (`blockSqPred_sep`, off `mem_piTele_zero` — the `w = 0` branch
  of `slotSet_fold_mem`, which needs no `hX`);
* `blockSqStep_hst` and `blockSqKit` — the kit, at §9's motive and
  §14's step;
* `blockSqKitFam`, `blockSqData`, `blockKitRegime_sq` — the family at
  every prefix spine and the dispatch's `KitRegimeAt`, fed by
  `blockSqStep_at_rule` (§14).

**The route taken, and why.**  `sqGraph_singleton`
(`Semantics/Tower/FixSquashI.lean`) proves the same theorem for the
FIX route, over `fixFamI` — a CONSTRUCTION — while the block's carrier
is `d.Φ`, characterised only up to `BlockModelAt.fibre`.  There is no
equation between them to transport along, so the transport kit of
session 17 (`recGraph_transport`, `recGraph_restrict`) is not what
closes this: the induction is re-run at the block datum, exactly as
`blockIndPt` (§17) re-runs it for the conclusion.  §S18.1 records
what that means for the transport lemmas.
-/

/-- **A fit, read at ONE position**: the walk's prefix and the entry
there.  `FitsFrom` is a walk and every consumer that wants a single
field has been restating it; this is the projection. -/
theorem FitsFrom.at_pos {rs : List Bool} {slot : Nat → (Nat → V) → V} :
    ∀ {i : Nat} {ρ : Nat → V} {Fs : List AnnotTerm} {as : List V},
      FitsFrom rs slot i ρ Fs as → ∀ l, l < Fs.length →
        FitsFrom rs slot i ρ (Fs.take l) (as.take l) ∧
        as.getD l pt ∈ˢ (if rs.getD (i + l) false then slot (i + l) (consList (as.take l) ρ)
          else interp V (consList (as.take l) ρ) (Fs.getD l default))
  | _, _, [], [], _, l, hl => by simp at hl
  | _, _, [], _ :: _, h, _, _ => h.elim
  | _, _, _ :: _, [], h, _, _ => h.elim
  | i, ρ, F :: Fs, a :: as, h, 0, _ => by
    refine ⟨trivial, ?_⟩
    simpa using h.1
  | i, ρ, F :: Fs, a :: as, h, l + 1, hl => by
    obtain ⟨h1, h2⟩ := FitsFrom.at_pos h.2 l (by simpa using hl)
    refine ⟨⟨h.1, h1⟩, ?_⟩
    simp only [List.take_succ_cons, consList_cons, List.getD_cons_succ]
    rw [show i + (l + 1) = i + 1 + l from by omega]
    exact h2

/-! ## Regime SQ's kit -/

section SqKit

variable {env : Env} {mo : EnvModel V env} {names : List Name} {d : BlockData V}
  {ℓ : Nat} {ψ : Name → Nat} {ρ ρp : Nat → V} {mem : Nat → Nat}
  {pdoms : Nat → List AnnotTerm} {xs : List V} {src : List (Option Nat)}

/-- **The SOURCE spine at a tagged element**: the lone constructor's
fields recovered from the element's index tuple (the subsingleton
criterion, `srcVals`). -/
@[expose] noncomputable def blockSqSpine (d : BlockData V) (ψ : Name → Nat) (mem : Nat → Nat)
    (src : List (Option Nat)) (u : V) : List V :=
  srcVals (isOfW (d.uM (mem 0) ψ) (d.nIdxAt (mem 0)) (tagIdx u)) src

@[simp] theorem blockSqSpine_tagged (c : Nat) (i x : V) :
    blockSqSpine d ψ mem src (tagged c i x)
      = srcVals (isOfW (d.uM (mem 0) ψ) (d.nIdxAt (mem 0)) i) src := by
  rw [blockSqSpine, tagIdx_tagged]

/-- **Regime SQ's predecessor map at the union**: the index tuples of
the lone constructor's recursive calls at the element's SOURCE spine.

Regime WF's `tcPred` is not available here and not merely different:
at `w = 0` every payload is the point (`mkZero`), so `tcPred` — the
payload's ∈-subterms inside the union — is EMPTY and the recursion it
carries is the trivial one.  The SQ recursion runs on the INDEX. -/
@[expose] noncomputable def blockSqPred (d : BlockData V) (ψ : Name → Nat) (ρp : Nat → V)
    (mem : Nat → Nat) (src : List (Option Nat)) (U u : V) : V :=
  sep U fun v => ∃ i, i < ((d.Fss (mem 0) ψ).getD 0 []).length ∧
    ((d.rss (mem 0)).getD 0 []).getD i false = true ∧
    ∃ bs : List V,
      SpineFit (consList ((blockSqSpine d ψ mem src u).take i) ρp)
        ((((d.tlss (mem 0) ψ).getD 0 []).getD i []).map (·.2.2)) bs ∧
      tagIdx v = d.tup ψ (d.tgts (mem 0) 0 i)
        ((((d.Eiss (mem 0) ψ).getD 0 []).getD i []).map
          (interp V (consList bs (consList ((blockSqSpine d ψ mem src u).take i) ρp))))

theorem blockSqPred_subset (U u : V) :
    blockSqPred d ψ ρp mem src U u ⊆ˢ U := sep_subset

/-- The induction's property: the recursor's graph is a SINGLETON at
the tagged element. -/
@[expose] def SqSingleton (ℓ : Nat) (U : V) (pr B : V → V) (st : V → V → V)
    (_m : Nat) (i y : V) : Prop :=
  (∃ v, v ∈ˢ app (recGraph ℓ U pr B st) (tagged 0 i y)) ∧
  ∀ v v', v ∈ˢ app (recGraph ℓ U pr B st) (tagged 0 i y) →
    v' ∈ˢ app (recGraph ℓ U pr B st) (tagged 0 i y) → v = v'

/-- **A recursive field's call lands in the tuple** (`w = 0`): the
field's value folded along its telescope inhabits the tuple's target
component at the call's index tuple.  Stated with the tuple `X` a
VARIABLE, which is what keeps the `w = 0` rewrite off it. -/
theorem blockSqPred_sep {X : Nat → V} {fs bs : List V} {i' : Nat}
    (hw : d.w ψ = 0) (htgt0 : d.tgts 0 0 i' = 0)
    (hf : fs.getD i' pt ∈ˢ d.slotAt ψ X 0 0 i' (consList (fs.take i') ρp))
    (hbs : SpineFit (consList (fs.take i') ρp)
      ((((d.tlss 0 ψ).getD 0 []).getD i' []).map (·.2.2)) bs) :
    ∃ y, y ∈ˢ app (X 0) (d.tup ψ 0 ((((d.Eiss 0 ψ).getD 0 []).getD i' []).map
      (interp V (consList bs (consList (fs.take i') ρp))))) := by
  rw [BlockData.slotAt, htgt0, slotSet, hw] at hf
  have h := mem_piTele_zero hf bs (fitsS_teleOfFields.mpr hbs)
  rw [List.nil_append] at h
  exact h

/-- **`UnionRecKitC.exu` for regime SQ**: the recursion theorem at the
block's TAGGED UNION, by the block's OWN lfp induction.

At `w = 0` accessibility is not available — `tcPred` is empty and the
∈-order says nothing — so the singleton property is proved the way
`sqGraph_singleton` proves it for the fix route: by `lfpTuple_induction`
on the block's representation, with `recGraph_singleton_of_preds` at
each step.  The step's obligation is that every predecessor's fibre is
already a singleton, and the SEPARATED tuple is what carries it: a
recursive field's value at the constructed element lies in the
separated tuple at the call's index tuple, which is the property at
that tuple.

The block is the SQ guard's: one class (`K = 1`), one component
(`d.N = 1`), one constructor, every recursive field targeting the lone
member, and the subsingleton criterion (`hsrcAt`) saying the fields are
a function of the index. -/
theorem blockSqExu (hM : BlockModelAt mo names d) (hw : d.w ψ = 0)
    (hN : d.N = 1) (hmem0 : mem 0 = 0) (hnCt1 : (d.ctorsM 0).length = 1)
    (htgt : ∀ i, d.tgts 0 0 i = 0)
    (hsrcAt : ∀ X, InTupleSpace (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ)) X →
      ∀ t, t ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) 0 → ∀ fs,
        d.ChainFit ψ (consList (xs.take d.nP) ρ) X t 0 0 fs →
        fs = srcVals (isOfW (d.uM 0 ψ) (d.nIdxAt 0) t) src)
    {B : V → V} {st : V → V → V}
    (hB : ∀ u, u ∈ˢ unionSet 1 (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs) →
      B u ∈ˢ (univ ℓ : V))
    (hst : ∀ u, u ∈ˢ unionSet 1 (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs) →
      ∀ g, g ∈ˢ piSet
          (blockSqPred d ψ (consList (xs.take d.nP) ρ) mem src
            (unionSet 1 (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs)) u)
          (fun j => app (recGraph ℓ
            (unionSet 1 (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs))
            (blockSqPred d ψ (consList (xs.take d.nP) ρ) mem src
              (unionSet 1 (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs)))
            B st) j) →
        st u g ∈ˢ B u) :
    ∀ u, u ∈ˢ unionSet 1 (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs) →
      (∃ v, v ∈ˢ app (recGraph ℓ
        (unionSet 1 (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs))
        (blockSqPred d ψ (consList (xs.take d.nP) ρ) mem src
          (unionSet 1 (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs))) B st) u) ∧
      ∀ v v', v ∈ˢ app (recGraph ℓ
          (unionSet 1 (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs))
          (blockSqPred d ψ (consList (xs.take d.nP) ρ) mem src
            (unionSet 1 (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs))) B st) u →
        v' ∈ˢ app (recGraph ℓ
          (unionSet 1 (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs))
          (blockSqPred d ψ (consList (xs.take d.nP) ρ) mem src
            (unionSet 1 (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs))) B st) u →
        v = v' := by
  intro u hu
  obtain ⟨c, hc, t, ht, x, hx, rfl⟩ := mem_unionSet.mp hu
  obtain rfl : c = 0 := by omega
  obtain ⟨hparFit, hprefFit⟩ := blockRecIs_fits ht
  have hsat := d.satOfSpine hparFit
  have hmemN : (0 : Nat) < d.N := by omega
  obtain ⟨hmono, hmaps, hcl⟩ := hM.functor ψ (consList (xs.take d.nP) ρ) hsat
  have huz : (univ (d.w ψ) : V) = univZero := by rw [hw, univ_zero]
  rw [blockRecIs_pos hparFit hprefFit, hmem0] at ht
  rw [blockRecCr, hmem0] at hx
  refine lfpTuple_induction hcl hmono
    (SqSingleton ℓ (unionSet 1 (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs))
      (blockSqPred d ψ (consList (xs.take d.nP) ρ) mem src
        (unionSet 1 (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs))) B st)
    ?_ 0 hmemN t ht x hx
  -- THE STEP
  intro m hm i hi y hy
  obtain rfl : m = 0 := by omega
  have hXsp := sepTuple_mem (V := V) (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
    (d.Φ ψ (consList (xs.take d.nP) ρ))
    (SqSingleton ℓ (unionSet 1 (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs))
      (blockSqPred d ψ (consList (xs.take d.nP) ρ) mem src
        (unionSet 1 (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs))) B st)
  obtain ⟨j, fs, hj, hfit, rfl⟩ :=
    (hM.fibre ψ (consList (xs.take d.nP) ρ) hsat _ hXsp 0 hmemN i hi y).mp hy
  obtain rfl : j = 0 := by omega
  -- the element is the point, and it is in the carrier
  have hyl : d.inj ψ 0 0 fs ∈ˢ app (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
      (d.Φ ψ (consList (xs.take d.nP) ρ)) 0) i :=
    lfpTuple_closed hcl hmono 0 hmemN i hi _
      (hmono _ _ hXsp (lfpTuple_mem _ _ _ _) (sepTuple_le _ _ _ _ _) 0 hmemN i hi _ hy)
  have hpt : d.inj ψ 0 0 fs = (pt : V) := hM.mkZero ψ hw 0 0 fs
  have huU : tagged 0 i (d.inj ψ 0 0 fs)
      ∈ˢ unionSet 1 (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs) := by
    refine tagged_mem_unionSet (by omega) ?_ ?_
    · rw [blockRecIs_pos hparFit hprefFit, hmem0]; exact hi
    · rw [blockRecCr, hmem0]; exact hyl
  show SqSingleton ℓ _ _ B st 0 i (d.inj ψ 0 0 fs)
  refine recGraph_singleton_of_preds hB (fun v _ => blockSqPred_subset _ v) huU
    (hst _ huU) ?_
  -- THE PREDECESSORS
  intro v hv
  obtain ⟨hvU, i', hi'F, hi'r, bs, hbs, htag⟩ := mem_sep.mp hv
  rw [hmem0] at hi'F hi'r hbs htag
  rw [htgt i'] at htag
  obtain ⟨c', hc', t', ht', x', hx', rfl⟩ := mem_unionSet.mp hvU
  obtain rfl : c' = 0 := by omega
  obtain ⟨hparFit', hprefFit'⟩ := blockRecIs_fits ht'
  rw [blockRecIs_pos hparFit' hprefFit', hmem0] at ht'
  rw [blockRecCr, hmem0] at hx'
  -- the payload is the point
  have hx'pt : x' = (pt : V) := by
    have hmf : app (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
        (d.Φ ψ (consList (xs.take d.nP) ρ)) 0) t' ∈ˢ (univ (d.w ψ) : V) :=
      famSpace_app (lfpTuple_mem _ _ _ _ 0 hmemN) ht'
    rw [huz] at hmf
    exact eq_pt_of_mem_univZero hmf hx'
  subst hx'pt
  rw [tagIdx_tagged] at htag
  -- the source spine at the constructed element IS the rule's fields
  have hspine : blockSqSpine d ψ mem src (tagged 0 i (d.inj ψ 0 0 fs)) = fs := by
    rw [blockSqSpine_tagged, hmem0]
    exact (hsrcAt _ hXsp i hi fs hfit).symm
  rw [hspine] at hbs htag
  -- the recursive field's value, folded along its telescope
  obtain ⟨hpre, hentry⟩ := FitsFrom.at_pos hfit.1 i' hi'F
  rw [Nat.zero_add, if_pos hi'r] at hentry
  obtain ⟨z, hz⟩ := blockSqPred_sep hw (htgt i') hentry hbs
  rw [← htag] at hz
  rw [sepTuple, app_graph ht', mem_sep] at hz
  have hzpt : z = (pt : V) := by
    have hmf : app (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
        (d.Φ ψ (consList (xs.take d.nP) ρ)) 0) t' ∈ˢ (univ (d.w ψ) : V) :=
      famSpace_app (lfpTuple_mem _ _ _ _ 0 hmemN) ht'
    rw [huz] at hmf
    exact eq_pt_of_mem_univZero hmf hz.1
  rw [hzpt] at hz
  exact hz.2

section SqStep

variable {nCt rP : Nat → Nat} {concl : Nat → AnnotTerm}
  {fdoms ihdoms : Nat → Nat → List AnnotTerm} {Rb0 Ca : Nat → Nat → AnnotTerm}
  {ihv : List V → Nat → Nat → List V → V → List V} {srcs : Nat → List (Option Nat)}
  {envT : Env} {mp : EnvModelM V μ envT} {F : Nat}

/-- **The graph's values are bounded, at an ARBITRARY predecessor
map** — `app_mem_B_of_piSet` (§11) with `tcPred` generalised.  Regime
SQ's map is not `tcPred`, and unifying a variable map against
`tcPred`'s `sep` is what makes the elaborator unfold the union. -/
theorem app_mem_B_of_piSet_pred {ℓ : Nat} {U : V} {pred B : V → V} {st : V → V → V} {u g : V}
    (hB : ∀ i, i ∈ˢ U → B i ∈ˢ (univ ℓ : V))
    (hsub : ∀ i, i ∈ˢ U → pred i ⊆ˢ U)
    (hg : g ∈ˢ piSet (pred u) (fun v => app (recGraph ℓ U pred B st) v))
    {v : V} (hv : v ∈ˢ pred u) (hvU : v ∈ˢ U) : app g v ∈ˢ B v := by
  have h1 := app_mem_of_mem_piSet hg hv
  rw [app_recGraph_eq hB hsub hvU] at h1
  exact (mem_recGraphFibre.mp h1).1

/-- **Regime SQ's `hst`**: the step lands in the motive.  The
predecessor map is a PARAMETER — the obligation reads it only through
`hihF`'s bound on the graph — so this serves whatever map the kit is
built at. -/
theorem blockSqStep_hst {pr : V → V} (hμ : μ.verifiedChecks = true)
    (hM : BlockModelAt mo names d)
    (hsub : ∀ i, i ∈ˢ unionSet 1 (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs) →
      pr i ⊆ˢ unionSet 1 (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs))
    (hmemN : ∀ c, c < 1 → mem c < d.N)
    (hnCt1 : ∀ c, c < 1 → (d.ctorsM (mem c)).length = 1)
    (hnCt : ∀ c, c < 1 → nCt c = 1)
    (hsrcL : ∀ c, c < 1 → SpineFit ρ (d.params ψ) (xs.take d.nP) →
      ∀ i : V, i ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (mem c) → ∀ fs : List V,
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) 0 fs →
      srcVals (isOfW (d.uM (mem c) ψ) (d.nIdxAt (mem c)) i) (srcs c) = fs)
    (hconclTy : ∀ c, c < 1 → ∀ i, i ∈ˢ blockRecIs d ψ ρ pdoms mem xs c →
      ∀ x, x ∈ˢ app (blockRecCr d ψ ρ mem xs c) i →
      interp V
          (consList (xs ++ (isOfW (d.uM (mem c) ψ) (d.nIdxAt (mem c)) i ++ [x])) ρ) (concl c)
        ∈ˢ (univ ℓ : V))
    (hcerts : ∀ c, c < 1 → ∀ j, j < nCt c →
      BlockRuleCerts V mp F ψ (rP c) (fdoms c j).length (ihdoms c j).length
        (pdoms c) (fdoms c j) (ihdoms c j) (Rb0 c j) (Ca c j))
    (hspF : ∀ c, c < 1 → SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs →
      SpineFit ρ (pdoms c ++ fdoms c j) (xs ++ fs))
    (hihF : ∀ c, c < 1 → SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs → ∀ g : V,
      (∀ v, v ∈ˢ pr (tagged c i (d.inj ψ (mem c) j fs)) →
        app g v ∈ˢ blockRecMot 1 concl (fun c' => d.uM (mem c') ψ)
          (fun c' => d.nIdxAt (mem c')) ρ xs v) →
      SpineFit (consList (xs ++ fs) ρ) (ihdoms c j) (ihv xs c j fs g))
    (hCaB : ∀ c, c < 1 → SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs → ∀ g : V,
      interp V (consList (ihv xs c j fs g) (consList (xs ++ fs) ρ)) (Ca c j)
        = blockRecMot 1 concl (fun c' => d.uM (mem c') ψ) (fun c' => d.nIdxAt (mem c')) ρ xs
            (tagged c i (d.inj ψ (mem c) j fs))) :
    ∀ u, u ∈ˢ unionSet 1 (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs) → ∀ g : V,
      g ∈ˢ piSet (pr u)
        (fun j => app (recGraph ℓ
          (unionSet 1 (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs)) pr
          (blockRecMot 1 concl (fun c' => d.uM (mem c') ψ) (fun c' => d.nIdxAt (mem c')) ρ xs)
          (blockSqStep 1 d ψ ρ mem srcs Rb0 ihv xs)) j) →
      blockSqStep 1 d ψ ρ mem srcs Rb0 ihv xs u g
        ∈ˢ blockRecMot 1 concl (fun c' => d.uM (mem c') ψ) (fun c' => d.nIdxAt (mem c')) ρ xs u := by
  intro u hu g hg
  obtain ⟨c, hc, i, hi, x, hx, rfl⟩ := mem_unionSet.mp hu
  obtain ⟨hparFit, hprefFit⟩ := blockRecIs_fits hi
  rw [blockRecIs_pos hparFit hprefFit] at hi
  obtain ⟨j, fs, hj, hfit, rfl⟩ :=
    blockCarrier_case hM (d.satOfSpine hparFit) (hmemN c hc) hi hx
  obtain rfl : j = 0 := by
    have := hnCt1 c hc
    omega
  have hjn : (0 : Nat) < nCt c := by rw [hnCt c hc]; omega
  have hgB : ∀ v, v ∈ˢ pr (tagged c i (d.inj ψ (mem c) 0 fs)) →
      app g v ∈ˢ blockRecMot 1 concl (fun c' => d.uM (mem c') ψ)
        (fun c' => d.nIdxAt (mem c')) ρ xs v :=
    fun v hv => app_mem_B_of_piSet_pred (blockRecMot_mem_univ hconclTy) hsub hg hv
      (hsub _ hu v hv)
  have hres := (hcerts c hc 0 hjn).residueOk hμ
    (hspF c hc hparFit hprefFit 0 hjn i fs hfit)
    (hihF c hc hparFit hprefFit 0 hjn i fs hfit g hgB)
  rw [blockSqStep_at hc (hsrcL c hc hparFit i hi fs hfit) g,
    ← hCaB c hc hparFit hprefFit 0 hjn i fs hfit g]
  exact hres.2

/-- **Regime SQ's kit at a prefix spine**: a `UnionRecKitC` whose
`pred` is `blockSqPred` and whose `exu` is the block's own lfp
induction.  It is a `UnionRecKitC` DIRECTLY and not a `WfRecKit`: the
accessibility route is unavailable at `w = 0`, which is why session
14 made the recursion theorem the kit's field. -/
noncomputable def blockSqKit (hμ : μ.verifiedChecks = true)
    (hM : BlockModelAt mo names d) (hw : d.w ψ = 0)
    (hN : d.N = 1) (hmem0 : mem 0 = 0)
    (hnCt1 : ∀ c, c < 1 → (d.ctorsM (mem c)).length = 1)
    (hnCt : ∀ c, c < 1 → nCt c = 1)
    (htgt : ∀ i, d.tgts 0 0 i = 0)
    (hmemN : ∀ c, c < 1 → mem c < d.N)
    (hsrcAt : ∀ X, InTupleSpace (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ)) X →
      ∀ t, t ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) 0 → ∀ fs,
        d.ChainFit ψ (consList (xs.take d.nP) ρ) X t 0 0 fs →
        fs = srcVals (isOfW (d.uM 0 ψ) (d.nIdxAt 0) t) (srcs 0))
    (hconclTy : ∀ c, c < 1 → ∀ i, i ∈ˢ blockRecIs d ψ ρ pdoms mem xs c →
      ∀ x, x ∈ˢ app (blockRecCr d ψ ρ mem xs c) i →
      interp V
          (consList (xs ++ (isOfW (d.uM (mem c) ψ) (d.nIdxAt (mem c)) i ++ [x])) ρ) (concl c)
        ∈ˢ (univ ℓ : V))
    (hcerts : ∀ c, c < 1 → ∀ j, j < nCt c →
      BlockRuleCerts V mp F ψ (rP c) (fdoms c j).length (ihdoms c j).length
        (pdoms c) (fdoms c j) (ihdoms c j) (Rb0 c j) (Ca c j))
    (hspF : ∀ c, c < 1 → SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs →
      SpineFit ρ (pdoms c ++ fdoms c j) (xs ++ fs))
    (hihF : ∀ c, c < 1 → SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs → ∀ g : V,
      (∀ v, v ∈ˢ blockSqPred d ψ (consList (xs.take d.nP) ρ) mem (srcs 0)
            (unionSet 1 (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs))
            (tagged c i (d.inj ψ (mem c) j fs)) →
        app g v ∈ˢ blockRecMot 1 concl (fun c' => d.uM (mem c') ψ)
          (fun c' => d.nIdxAt (mem c')) ρ xs v) →
      SpineFit (consList (xs ++ fs) ρ) (ihdoms c j) (ihv xs c j fs g))
    (hCaB : ∀ c, c < 1 → SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs → ∀ g : V,
      interp V (consList (ihv xs c j fs g) (consList (xs ++ fs) ρ)) (Ca c j)
        = blockRecMot 1 concl (fun c' => d.uM (mem c') ψ) (fun c' => d.nIdxAt (mem c')) ρ xs
            (tagged c i (d.inj ψ (mem c) j fs))) :
    UnionRecKitC ℓ 1 (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs) :=
  have hsrcL : ∀ c, c < 1 → SpineFit ρ (d.params ψ) (xs.take d.nP) →
      ∀ i : V, i ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (mem c) → ∀ fs : List V,
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) 0 fs →
      srcVals (isOfW (d.uM (mem c) ψ) (d.nIdxAt (mem c)) i) (srcs c) = fs := by
    intro c hc _ i hi fs hfit
    obtain rfl : c = 0 := by omega
    rw [hmem0] at hi hfit ⊢
    exact (hsrcAt _ (lfpTuple_mem _ _ _ _) i hi fs hfit).symm
  have hstP := blockSqStep_hst
    (pr := blockSqPred d ψ (consList (xs.take d.nP) ρ) mem (srcs 0)
      (unionSet 1 (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs)))
    (nCt := nCt) (rP := rP) (concl := concl) (fdoms := fdoms) (ihdoms := ihdoms)
    (Rb0 := Rb0) (Ca := Ca) (ihv := ihv) (srcs := srcs) (mp := mp) (F := F)
    hμ hM (fun i _ => blockSqPred_subset _ i) hmemN hnCt1 hnCt hsrcL hconclTy hcerts hspF
    hihF hCaB
  { pred := blockSqPred d ψ (consList (xs.take d.nP) ρ) mem (srcs 0)
      (unionSet 1 (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs))
    B := blockRecMot 1 concl (fun c' => d.uM (mem c') ψ) (fun c' => d.nIdxAt (mem c')) ρ xs
    st := blockSqStep 1 d ψ ρ mem srcs Rb0 ihv xs
    predSub := fun u _ => blockSqPred_subset _ u
    hB := blockRecMot_mem_univ hconclTy
    hst := hstP
    exu := blockSqExu hM hw hN hmem0 (by have := hnCt1 0 (by omega); rwa [hmem0] at this)
      htgt hsrcAt (blockRecMot_mem_univ hconclTy) hstP }

end SqStep

/-! ## The kit family, the data, and `KitRegimeAt` -/

section SqFam

variable {nCt rP : Nat → Nat} {rds : Nat → List (Nat × Nat × AnnotTerm)}
  {concl RecTy : Nat → AnnotTerm} {fdoms es ihdoms : Nat → Nat → List AnnotTerm}
  {mk : Nat → Nat → AnnotTerm} {ihs : Nat → Nat → List AnnotTerm}
  {Rb0 Ca : Nat → Nat → AnnotTerm} {ihv : List V → Nat → Nat → List V → V → List V}
  {srcs : Nat → List (Option Nat)} {envT : Env} {mp : EnvModelM V μ envT} {F : Nat}

/-- **Regime SQ's data**: `RecFamData` at the block's own index sets
and carriers, with a `UnionRecKitC` per prefix spine.  The WF regime's
`blockWfData` goes through `wfData` because its kit is a `WfRecKit`;
regime SQ's is a class kit already, so this is the structure. -/
@[expose] noncomputable def blockSqData (d : BlockData V)
    (kitC : ∀ xs : List V,
      UnionRecKitC ℓ 1 (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs))
    (hsplit : ∀ c, c < 1 → ∀ ys, SpineFit ρ ((rds c).map (·.2.2)) ys →
      (prefOf (rP c) ys).length = rP c ∧
      ys = prefOf (rP c) ys ++ (idxOf (rP c) ys ++ [majOf ys]) ∧
      d.tup ψ (mem c) (idxOf (rP c) ys) ∈ˢ blockRecIs d ψ ρ pdoms mem (prefOf (rP c) ys) c ∧
      majOf ys ∈ˢ app (blockRecCr d ψ ρ mem (prefOf (rP c) ys) c)
        (d.tup ψ (mem c) (idxOf (rP c) ys)))
    (hconcl : ∀ c, c < 1 → ∀ ys, SpineFit ρ ((rds c).map (·.2.2)) ys →
      (kitC (prefOf (rP c) ys)).B
          (tagged c (d.tup ψ (mem c) (idxOf (rP c) ys)) (majOf ys))
        = interp V (consList ys ρ) (concl c)) :
    RecFamData V ℓ 1 rP rds concl ρ where
  Is := blockRecIs d ψ ρ pdoms mem
  Cr := blockRecCr d ψ ρ mem
  tupOf := fun c is => d.tup ψ (mem c) is
  kit := kitC
  hsplit := hsplit
  hconcl := hconcl

/-- **The kit at EVERY prefix spine** (M5m's O-3), regime SQ's: the
guard sits in `blockRecIs`, so a non-fitting prefix carries empty
classes and every obligation is vacuous there. -/
noncomputable def blockSqKitFam (hμ : μ.verifiedChecks = true)
    (hM : BlockModelAt mo names d) (hw : d.w ψ = 0)
    (hN : d.N = 1) (hmem0 : mem 0 = 0)
    (hnCt1 : ∀ c, c < 1 → (d.ctorsM (mem c)).length = 1)
    (hnCt : ∀ c, c < 1 → nCt c = 1)
    (htgt : ∀ i, d.tgts 0 0 i = 0)
    (hmemN : ∀ c, c < 1 → mem c < d.N)
    (hsrcAt : ∀ xs : List V, ∀ X,
      InTupleSpace (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ)) X →
      ∀ t, t ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) 0 → ∀ fs,
        d.ChainFit ψ (consList (xs.take d.nP) ρ) X t 0 0 fs →
        fs = srcVals (isOfW (d.uM 0 ψ) (d.nIdxAt 0) t) (srcs 0))
    (hconclTy : ∀ xs : List V, ∀ c, c < 1 → ∀ i, i ∈ˢ blockRecIs d ψ ρ pdoms mem xs c →
      ∀ x, x ∈ˢ app (blockRecCr d ψ ρ mem xs c) i →
      interp V
          (consList (xs ++ (isOfW (d.uM (mem c) ψ) (d.nIdxAt (mem c)) i ++ [x])) ρ) (concl c)
        ∈ˢ (univ ℓ : V))
    (hcerts : ∀ c, c < 1 → ∀ j, j < nCt c →
      BlockRuleCerts V mp F ψ (rP c) (fdoms c j).length (ihdoms c j).length
        (pdoms c) (fdoms c j) (ihdoms c j) (Rb0 c j) (Ca c j))
    (hspF : ∀ xs : List V, ∀ c, c < 1 →
      SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs →
      SpineFit ρ (pdoms c ++ fdoms c j) (xs ++ fs))
    (hihF : ∀ xs : List V, ∀ c, c < 1 →
      SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs → ∀ g : V,
      (∀ v, v ∈ˢ blockSqPred d ψ (consList (xs.take d.nP) ρ) mem (srcs 0)
            (unionSet 1 (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs))
            (tagged c i (d.inj ψ (mem c) j fs)) →
        app g v ∈ˢ blockRecMot 1 concl (fun c' => d.uM (mem c') ψ)
          (fun c' => d.nIdxAt (mem c')) ρ xs v) →
      SpineFit (consList (xs ++ fs) ρ) (ihdoms c j) (ihv xs c j fs g))
    (hCaB : ∀ xs : List V, ∀ c, c < 1 →
      SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs → ∀ g : V,
      interp V (consList (ihv xs c j fs g) (consList (xs ++ fs) ρ)) (Ca c j)
        = blockRecMot 1 concl (fun c' => d.uM (mem c') ψ) (fun c' => d.nIdxAt (mem c')) ρ xs
            (tagged c i (d.inj ψ (mem c) j fs)))
    (xs : List V) :
    UnionRecKitC ℓ 1 (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs) :=
  blockSqKit (nCt := nCt) (rP := rP) (ihdoms := ihdoms) (Ca := Ca) (ihv := ihv) (srcs := srcs)
    hμ hM hw hN hmem0 hnCt1 hnCt htgt hmemN (hsrcAt xs) (hconclTy xs) hcerts (hspF xs)
    (hihF xs) (hCaB xs)

theorem blockSqKitFam_B (hμ : μ.verifiedChecks = true) (hM : BlockModelAt mo names d)
    (hw : d.w ψ = 0) (hN) (hmem0) (hnCt1) (hnCt) (htgt) (hmemN) (hsrcAt) (hconclTy) (hcerts)
    (hspF) (hihF) (hCaB) (xs : List V) :
    (blockSqKitFam (V := V) (ℓ := ℓ) (ρ := ρ) (mem := mem) (nCt := nCt) (rP := rP)
        (concl := concl) (pdoms := pdoms) (fdoms := fdoms) (ihdoms := ihdoms) (Rb0 := Rb0)
        (Ca := Ca) (ihv := ihv) (srcs := srcs) (mp := mp) (F := F)
        hμ hM hw hN hmem0 hnCt1 hnCt htgt hmemN hsrcAt hconclTy hcerts hspF hihF hCaB xs).B
      = blockRecMot 1 concl (fun c' => d.uM (mem c') ψ) (fun c' => d.nIdxAt (mem c')) ρ xs := by
  rfl

theorem blockSqKitFam_st (hμ : μ.verifiedChecks = true) (hM : BlockModelAt mo names d)
    (hw : d.w ψ = 0) (hN) (hmem0) (hnCt1) (hnCt) (htgt) (hmemN) (hsrcAt) (hconclTy) (hcerts)
    (hspF) (hihF) (hCaB) (xs : List V) :
    (blockSqKitFam (V := V) (ℓ := ℓ) (ρ := ρ) (mem := mem) (nCt := nCt) (rP := rP)
        (concl := concl) (pdoms := pdoms) (fdoms := fdoms) (ihdoms := ihdoms) (Rb0 := Rb0)
        (Ca := Ca) (ihv := ihv) (srcs := srcs) (mp := mp) (F := F)
        hμ hM hw hN hmem0 hnCt1 hnCt htgt hmemN hsrcAt hconclTy hcerts hspF hihF hCaB xs).st
      = blockSqStep 1 d ψ ρ mem srcs Rb0 ihv xs := by
  rfl

/-- **`KitRegimeAt` at the SQ regime** (`ℓ ≠ 0 ∧ w = 0`), from the
representation, the certificates and the same reading bridges the WF
arm takes — with `tcPred` replaced by `blockSqPred` in `hihF`, and the
subsingleton criterion in two places: at the carrier's case analysis
(`hsrcAt`, which the kit's `exu` and `hst` consume) and at a rule's own
spine (`hsrcRule`, which `blockSqStep_at_rule` consumes). -/
theorem blockKitRegime_sq (hμ : μ.verifiedChecks = true) (hM : BlockModelAt mo names d)
    (hw : d.w ψ = 0) (hmemK : ∀ c, c < 1 → mem c < d.k)
    (hN : d.N = 1) (hmem0 : mem 0 = 0)
    (hnCt1 : ∀ c, c < 1 → (d.ctorsM (mem c)).length = 1)
    (hnCt : ∀ c, c < 1 → nCt c = 1)
    (htgt : ∀ i, d.tgts 0 0 i = 0)
    (hlenIds : ∀ c, c < 1 → (d.IdsM (mem c) ψ).length = d.nIdxAt (mem c))
    (hsplitR : BlockRecSplitAt V mo d ψ 1 rP mem rds ρ)
    (hpdE : ∀ c, c < 1 → pdoms c = ((rds c).map (·.2.2)).take (rP c))
    (hsrcAt : ∀ xs : List V, ∀ X,
      InTupleSpace (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ)) X →
      ∀ t, t ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) 0 → ∀ fs,
        d.ChainFit ψ (consList (xs.take d.nP) ρ) X t 0 0 fs →
        fs = srcVals (isOfW (d.uM 0 ψ) (d.nIdxAt 0) t) (srcs 0))
    (hconclTy : ∀ xs : List V, ∀ c, c < 1 → ∀ i, i ∈ˢ blockRecIs d ψ ρ pdoms mem xs c →
      ∀ x, x ∈ˢ app (blockRecCr d ψ ρ mem xs c) i →
      interp V
          (consList (xs ++ (isOfW (d.uM (mem c) ψ) (d.nIdxAt (mem c)) i ++ [x])) ρ) (concl c)
        ∈ˢ (univ ℓ : V))
    (hcerts : ∀ c, c < 1 → ∀ j, j < nCt c →
      BlockRuleCerts V mp F ψ (rP c) (fdoms c j).length (ihdoms c j).length
        (pdoms c) (fdoms c j) (ihdoms c j) (Rb0 c j) (Ca c j))
    (hspF : ∀ xs : List V, ∀ c, c < 1 →
      SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs →
      SpineFit ρ (pdoms c ++ fdoms c j) (xs ++ fs))
    (hihF : ∀ xs : List V, ∀ c, c < 1 →
      SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs → ∀ g : V,
      (∀ v, v ∈ˢ blockSqPred d ψ (consList (xs.take d.nP) ρ) mem (srcs 0)
            (unionSet 1 (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs))
            (tagged c i (d.inj ψ (mem c) j fs)) →
        app g v ∈ˢ blockRecMot 1 concl (fun c' => d.uM (mem c') ψ)
          (fun c' => d.nIdxAt (mem c')) ρ xs v) →
      SpineFit (consList (xs ++ fs) ρ) (ihdoms c j) (ihv xs c j fs g))
    (hCaB : ∀ xs : List V, ∀ c, c < 1 →
      SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs → ∀ g : V,
      interp V (consList (ihv xs c j fs g) (consList (xs ++ fs) ρ)) (Ca c j)
        = blockRecMot 1 concl (fun c' => d.uM (mem c') ψ) (fun c' => d.nIdxAt (mem c')) ρ xs
            (tagged c i (d.inj ψ (mem c) j fs)))
    (hTyE : ∀ c, c < 1 → RecTy c = mkPisAV (rds c) (concl c))
    (hbits : OneElimLevel ℓ 1 rds) (hpl : ∀ c, c < 1 → (pdoms c).length = rP c)
    (hrule : ∀ (D : RecFamData V ℓ 1 rP rds concl ρ), ∀ c, c < 1 → ∀ j, j < nCt c →
      ∀ xs fs : List V, xs.length = (pdoms c).length →
      SpineFit (chainFrame 1 (famCand D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      SpineFit ρ ((rds c).map (·.2.2))
        (xs ++ ((es c j).map (interp V (consList (xs ++ fs) (chainFrame 1 (famCand D) ρ)))
          ++ [interp V (consList (xs ++ fs) (chainFrame 1 (famCand D) ρ)) (mk c j)])))
    (hsrcRule : ∀ (D : RecFamData V ℓ 1 rP rds concl ρ), ∀ c, c < 1 → ∀ j, j < nCt c →
      ∀ xs fs : List V, xs.length = (pdoms c).length →
      SpineFit (chainFrame 1 (famCand D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      j = 0 ∧
        srcVals
            (isOfW (d.uM (mem c) ψ) (d.nIdxAt (mem c))
              (D.tupOf c
                ((es c j).map (interp V (consList (xs ++ fs) (chainFrame 1 (famCand D) ρ))))))
            (srcs c)
          = fs)
    (hihChain : ∀ (D : RecFamData V ℓ 1 rP rds concl ρ), ∀ c, c < 1 → ∀ j, j < nCt c →
      ∀ xs fs : List V, xs.length = (pdoms c).length →
      SpineFit (chainFrame 1 (famCand D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      ihv xs c j fs
          (kitGraphAt (D.kit xs)
            (tagged c
              (D.tupOf c
                ((es c j).map (interp V (consList (xs ++ fs) (chainFrame 1 (famCand D) ρ)))))
              (interp V (consList (xs ++ fs) (chainFrame 1 (famCand D) ρ)) (mk c j))))
        = (ihs c j).map (interp V (consList (xs ++ fs) (chainFrame 1 (famCand D) ρ)))) :
    KitRegimeAt V ℓ 1 rP nCt rds concl RecTy pdoms fdoms es mk ihs Rb0 ρ := by
  have hmemN : ∀ c, c < 1 → mem c < d.N :=
    fun c hc => Nat.lt_of_lt_of_le (hmemK c hc) (Nat.le_add_right _ _)
  refine ⟨blockSqData (rds := rds) (concl := concl) (rP := rP) (ρ := ρ) d
      (blockSqKitFam (ihdoms := ihdoms) (Ca := Ca) (ihv := ihv) (rP := rP) (nCt := nCt)
        (srcs := srcs) hμ hM hw hN hmem0 hnCt1 hnCt htgt hmemN hsrcAt hconclTy hcerts hspF
        hihF hCaB)
      (blockWf_hsplit hM hpdE hmemK hsplitR) ?_,
    blockSqStep 1 d ψ ρ mem srcs Rb0 ihv, ihv, ?_, hTyE, hbits, hpl, ?_, ?_, ?_⟩
  · intro c hc ys hfit
    rw [blockSqKitFam_B]
    exact blockWf_hconcl hM hmemN hlenIds hsplitR c hc ys hfit
  · intro xs
    rfl
  · exact hrule _
  · exact blockSqStep_at_rule _ (hsrcRule _)
  · exact hihChain _

end SqFam

end SqKit


/-! ## 37. THE IND ARM'S STEP — `blockIndPt`'s `hstep` (session 18)

§17 reduces regime IND's induction principle to "the conclusion is
inhabited at every fitting spine" and leaves the STEP — the conclusion
at a CONSTRUCTED major, with the property already available at the
recursive fields — as a premise.  This section is that step, from the
rules' certificates.

The assembly is short because everything it needs already exists: the
spine splits (`BlockRecSplitAt`), the major decomposes at the
SEPARATED tuple (`BlockModelAt.fibre` — the separated tuple, not the
lfp, which is what makes the recursive fields carry the property), and
`BlockRuleCerts.residueOk` types the residue at the frame.  At `ℓ = 0`
the conclusion's reading is a TRUTH VALUE (`hT`), so the residue's
value there IS the point and the conclusion is inhabited.

**What is a premise, and why.**  `hih` — the `ih` openers' fit at the
frame — is the induction hypothesis itself: at `ℓ = 0` the openers'
domains are truth values whose inhabitation is the motive at the
PREDECESSORS, which the separated tuple carries (§33 puts the
predecessor there, and §35's `hpref'` is what made §33 run).  Turning
that into the fit needs the openers' domain READING — the per-key
identification `ihdoms.getD r = (mkPisAV (tlA i) (Cih r)).liftN r 0`
with `Cih r` the peel of the CALLEE's conclusion — which is lane
RM19's export and is not landed.  It is named here, consumed at the
run level in the same section, and becomes an `exact` when RM19's
`hconcl` lands.  `hT` and `hCaE` are §29's `blockRecCa_run` at
`ℓ = 0`, in the shape the regime states them. -/

section IndStep

variable {env : Env} {mo : EnvModel V env} {names : List Name} {d : BlockData V}
  {K : Nat} {ψ : Name → Nat} {ρ : Nat → V} {mem nCt rP : Nat → Nat}
  {rds : Nat → List (Nat × Nat × AnnotTerm)} {concl : Nat → AnnotTerm}
  {pdoms : Nat → List AnnotTerm} {fdoms ihdoms : Nat → Nat → List AnnotTerm}
  {ihs : Nat → Nat → List AnnotTerm} {Rb0 Ca : Nat → Nat → AnnotTerm}
  {envT : Env} {mp : EnvModelM V μ envT} {F : Nat}
  {ihvals : Nat → Nat → List V}

/-- Every entry of a `pt` replication is the point — the IND regime's
`ih` VALUES, at every position. -/
theorem getD_replicate_pt (n r : Nat) : (List.replicate n (pt : V)).getD r pt = pt := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

/-- **The `ih` openers' fit AT `ℓ = 0`** — `blockRecIhvAt_fit`'s twin
at the zero level, and the half of the IND arm's `hih` that is not
about the block.

At `ℓ = 0` every opener's domain is a `Prop` Π-tower over the field's
telescope (`hbits`, `OneElimLevel` at the family's level), so the
point inhabits it exactly when its BODY is inhabited at every fitting
telescope spine (`pt_mem_mkPisAV_zero`, §16); and the ih VALUES are
the point there, which is the one thing the `ℓ ≠ 0` route cannot say.
The domain shape `hdom` is the per-key identification `blockIhPis`
produces (opener `r`'s domain is the `l = 0` tower lifted past the `r`
earlier openers, §32), and its BODY `Cih r` is the CALLEE's
conclusion peeled at the call's prefix, index expressions and target
— the component `blockRuleHconcl_of` (`BlockRecOpenerRead.lean`) now
exports beside the reading.

What is left over after this lemma is `hleaf`: that peel IS the
motive at the PREDECESSOR (§29's `blockRecCa_value` at the callee's
class `c'`) and the motive holds there (`blockIndP`, §33's
predecessor with §35's `hpref'`). -/
theorem spineFit_ihdoms_zero {σ : Nat → V} {ihKeys : List (Nat × Nat)}
    {tlA : Nat → List (Nat × Nat × AnnotTerm)} {Cih : Nat → AnnotTerm}
    {ihdoms : List AnnotTerm} {ihvals : List V}
    (hlen : ihdoms.length = ihKeys.length) (hvlen : ihvals.length = ihKeys.length)
    (hvals : ∀ r, r < ihKeys.length → ihvals.getD r pt = (pt : V))
    (hdom : ∀ r, r < ihKeys.length →
      ihdoms.getD r default
        = (mkPisAV (tlA (ihKeys.getD r (0, 0)).1) (Cih r)).liftN r 0)
    (hbits : ∀ r, r < ihKeys.length →
      ∀ dd ∈ tlA (ihKeys.getD r (0, 0)).1, dd.2.1 = 0)
    (hleaf : ∀ r, r < ihKeys.length → ∀ bs : List V,
      SpineFit σ ((tlA (ihKeys.getD r (0, 0)).1).map (·.2.2)) bs →
      (pt : V) ∈ˢ interp V (consList bs σ) (Cih r)) :
    SpineFit σ ihdoms ihvals := by
  refine spineFit_of_getD (by rw [hvlen, hlen]) fun r hr => ?_
  have hrk : r < ihKeys.length := by rw [← hlen]; exact hr
  have htk : (ihvals.take r).length = r := by
    rw [List.length_take, hvlen]
    omega
  have hcancel : interp V (consList (ihvals.take r) σ)
        ((mkPisAV (tlA (ihKeys.getD r (0, 0)).1) (Cih r)).liftN r 0)
      = interp V σ (mkPisAV (tlA (ihKeys.getD r (0, 0)).1) (Cih r)) := by
    have hq := interp_liftN_ihvals (V := V) (ihvals := ihvals.take r) (σ := σ)
      (mkPisAV (tlA (ihKeys.getD r (0, 0)).1) (Cih r))
    rw [htk] at hq
    exact hq
  rw [hvals r hrk, hdom r hrk, hcancel]
  exact pt_mem_mkPisAV_zero _ σ _ (hbits r hrk) (hleaf r hrk)

/-- **A tuple-space component is graded at EVERY index**: on its own
index set by `famSpace_app`, and off it a family is junk
(`app_off_dom_of_mem_piSet`), which lies in every universe.  This is
what `slotSet_fold_mem` asks of the target component, and it is the
reason the fold needs no `w ≠ 0` split. -/
theorem inTupleSpace_app_univ {w N : Nat} {Is X : Nat → V}
    (hX : InTupleSpace w N Is X) {m : Nat} (hm : m < N) (t : V) :
    SetTheory.app (X m) t ∈ˢ (univ w : V) := by
  by_cases ht : t ∈ˢ Is m
  · exact famSpace_app (hX m hm) ht
  · rw [app_off_dom_of_mem_piSet (hX m hm) ht]
    exact empty_mem_univ w

/-- **The recursive field's PREDECESSOR data, at the SEPARATED
tuple** — §33's composition, in the shape the IND step reaches it.

`FitsFrom.at_pos` reads the constructor's walk at the field's
position, the representation's `idxFit` carries the call's index
readings into the TARGET member's index telescope (`SlotFit`'s third
clause), and `slotSet_fold_mem` folds the field along a fitting
telescope spine into the target component at the call's index tuple
— at ANY `w`, which is why this is not `blockRecSlot_pred`'s
`piTele_fold`.

At the separated tuple that component is a `sep` of the carrier, so
one membership gives BOTH halves the `ih` opener needs: the call's
major lies in the carrier (through `BlockModelAt.leaf`, at the
caller) and the motive holds at it. -/
theorem blockIndPred_of (hM : BlockModelAt mo names d) {ψ : Name → Nat} {ρp : Nat → V}
    {P : Nat → V → V → Prop} {c j i : Nat} {t : V} {fs bs : List V}
    (hsat : Sat V (d.params ψ).reverse ρp)
    (hc : c < d.N) (ht : t ∈ˢ d.idx ψ ρp c) (hj : j < (d.ctorsM c).length)
    (hfit : d.ChainFit ψ ρp (sepTuple (d.w ψ) d.N (d.idx ψ ρp) (d.Φ ψ ρp) P) t c j fs)
    (hi : i < ((d.Fss c ψ).getD j []).length)
    (hrec : ((d.rss c).getD j []).getD i false = true)
    (htgtN : d.tgts c j i < d.N)
    (hbs : SpineFit (consList (fs.take i) ρp)
      ((((d.tlss c ψ).getD j []).getD i []).map (·.2.2)) bs) :
    SpineFit ρp (d.IdsM (d.tgts c j i) ψ)
        ((((d.Eiss c ψ).getD j []).getD i []).map
          (interp V (consList bs (consList (fs.take i) ρp)))) ∧
      bs.foldl SetTheory.app (fs.getD i pt)
        ∈ˢ SetTheory.app
          (lfpTuple (d.w ψ) d.N (d.idx ψ ρp) (d.Φ ψ ρp) (d.tgts c j i))
          (d.tup ψ (d.tgts c j i)
            ((((d.Eiss c ψ).getD j []).getD i []).map
              (interp V (consList bs (consList (fs.take i) ρp))))) ∧
      P (d.tgts c j i)
        (d.tup ψ (d.tgts c j i)
          ((((d.Eiss c ψ).getD j []).getD i []).map
            (interp V (consList bs (consList (fs.take i) ρp)))))
        (bs.foldl SetTheory.app (fs.getD i pt)) := by
  have hXmem := sepTuple_mem (d.w ψ) d.N (d.idx ψ ρp) (d.Φ ψ ρp) P
  obtain ⟨hpre, hf⟩ := hfit.1.at_pos i hi
  rw [Nat.zero_add, hrec, if_pos rfl] at hf
  have hslotFit := hM.idxFit ψ ρp hsat _ hXmem c hc t ht j hj i hi hrec (fs.take i) hpre
  have hidxfit := (hslotFit.2.2 bs hbs).2
  rw [consList_append] at hidxfit
  have htup : tupW (d.uM (d.tgts c j i) ψ)
      ((((d.Eiss c ψ).getD j []).getD i []).map
        (interp V (consList bs (consList (fs.take i) ρp))))
      ∈ˢ d.idx ψ ρp (d.tgts c j i) := tupW_mem hidxfit
  have hmem := slotSet_fold_mem (inTupleSpace_app_univ hXmem htgtN) hf hbs
  rw [show (sepTuple (d.w ψ) d.N (d.idx ψ ρp) (d.Φ ψ ρp) P) (d.tgts c j i)
        = graph (fun i' => sep (SetTheory.app
            (lfpTuple (d.w ψ) d.N (d.idx ψ ρp) (d.Φ ψ ρp) (d.tgts c j i)) i')
          (P (d.tgts c j i) i')) (d.idx ψ ρp (d.tgts c j i)) from rfl,
    app_graph htup, mem_sep] at hmem
  exact ⟨hidxfit, hmem.1, hmem.2⟩

/-- **The `ih` opener's CONCLUSION is inhabited** — `hihLeaf` at one
key, and the second half of the IND arm's `hih`.

The opener's body `CihR` is the peel of the CALLEE's recursor type at
the guarded call's spine (`BlockRuleConclAt` with the field's
TELESCOPE spine in the `ih` block's place — §32: the peel's prefix
arguments are `prefVarsAV rP (nF + m)`, which is
`paramBvarsAt rP (rP + nF + m)` on the nose), so §29's
`blockRecCa_value` evaluates it to the callee's stored conclusion at
the spine `(x⃗, e⃗(a⃗), f_i a⃗)` — and the motive at the PREDECESSOR is
exactly `blockIndP` there.

Both of the block's own facts are the caller's: the spine FITS the
callee's recursor type (`hfitC'`, the converse of `BlockRecSplitAt`
at the callee's class) and the predecessor carries the property
(`hP`, the separated tuple's second component). -/
theorem blockIndIhLeaf_of {RecTy : Nat → AnnotTerm} {c' : Nat} (hc' : c' < K)
    {nF nIdx m : Nat} {eisA : List AnnotTerm} {fapA CihR : AnnotTerm}
    {as xs fs bs is : List V} {maj : V}
    (hcon : BlockRuleConclAt (rP c') nF m (RecTy c') eisA fapA CihR)
    (hTyE : RecTy c' = mkPisAV (rds c') (concl c'))
    (hrds : (rds c').length = rP c' + nIdx + 1)
    (hesLen : eisA.length = nIdx)
    (hconclB : Term.bvarsBelow (rds c').length (concl c').erase)
    (hxs : xs.length = rP c') (hfs : fs.length = nF) (hbs : bs.length = m)
    (hes : eisA.map (interp V (consList bs (consList (xs ++ fs) ρ))) = is)
    (hmk : interp V (consList bs (consList (xs ++ fs) ρ)) fapA = maj)
    (hfitC' : SpineFit ρ ((rds c').map (·.2.2)) (xs ++ (is ++ [maj])))
    (htake : xs.take d.nP = as)
    (hP : blockIndP d ψ ρ K rP mem rds concl as (mem c') (d.tup ψ (mem c') is) maj) :
    (pt : V) ∈ˢ interp V (consList bs (consList (xs ++ fs) ρ)) CihR := by
  rw [blockRecCa_value hcon hTyE hrds hesLen hconclB hxs hfs hbs hes hmk]
  refine hP c' hc' rfl (xs ++ (is ++ [maj])) hfitC' ?_ ?_ ?_
  · rw [prefOf_split hxs]; exact htake
  · rw [idxOf_split hxs]
  · rw [majOf_split]

/-- **`hihLeaf` AT ONE KEY, from the block** — §33's composition
finished: the separated tuple's two halves (`blockIndPred_of`), the
major's carrier form (`BlockModelAt.leaf`, read backwards), the
callee's spine assembled (`hjoin`, the converse of
`BlockRecSplitAt` — the recursor type's binders past the rule prefix
ARE the member's index telescope and its former) and the peel
evaluated at it (`blockIndIhLeaf_of`).

Three premises are the OTHER lanes' and are named in the shape they
deliver: `hpref'` (the guard at the CALLEE's class, §35's
`blockRecHpref_run`), `hjoin` and `hpdE` (the recursor stage's, the
two directions of one type-shape fact), and the TWO-FRAME bridge
`hesB`/`hmkB` — the guarded call's index readings and its applied
field, read at the RULE's frame (`prefix ++ fields`) against the
block's (`parameters ++ earlier fields`).  That bridge is the rule
lane's `blockRecIhvAt_eq`-shaped fact and the only genuinely new
content left in the IND arm's `hih`. -/
theorem blockIndIhLeaf_pred {RecTy : Nat → AnnotTerm} (hM : BlockModelAt mo names d)
    {c' cc j i nF nIdx m : Nat} {as xs fs bs : List V} {t : V}
    {eisA : List AnnotTerm} {fapA CihR : AnnotTerm}
    (hc' : c' < K) (hmk' : mem c' < d.k)
    (hpar : SpineFit ρ (d.params ψ) as)
    (hccN : cc < d.N) (ht : t ∈ˢ d.idx ψ (consList as ρ) cc)
    (hj : j < (d.ctorsM cc).length)
    (hfit : d.ChainFit ψ (consList as ρ)
      (sepTuple (d.w ψ) d.N (d.idx ψ (consList as ρ)) (d.Φ ψ (consList as ρ))
        (blockIndP d ψ ρ K rP mem rds concl as)) t cc j fs)
    (hiF : i < ((d.Fss cc ψ).getD j []).length)
    (hrec : ((d.rss cc).getD j []).getD i false = true)
    (htgt : d.tgts cc j i = mem c')
    (hbsB : SpineFit (consList (fs.take i) (consList as ρ))
      ((((d.tlss cc ψ).getD j []).getD i []).map (·.2.2)) bs)
    (hesB : (((d.Eiss cc ψ).getD j []).getD i []).map
        (interp V (consList bs (consList (fs.take i) (consList as ρ))))
      = eisA.map (interp V (consList bs (consList (xs ++ fs) ρ))))
    (hmkB : bs.foldl SetTheory.app (fs.getD i pt)
      = interp V (consList bs (consList (xs ++ fs) ρ)) fapA)
    (hpdE : pdoms c' = ((rds c').map (·.2.2)).take (rP c'))
    (hpref' : SpineFit ρ (pdoms c') xs)
    (htake : xs.take d.nP = as)
    (hjoin : ∀ (is : List V) (maj : V),
      SpineFit (consList as ρ) (d.IdsM (mem c') ψ) is →
      maj ∈ˢ (as ++ is).foldl SetTheory.app
        (interp V ρ (mo.acval (d.memberName (mem c')) ψ)) →
      SpineFit (consList xs ρ) (((rds c').map (·.2.2)).drop (rP c')) (is ++ [maj]))
    (hcon : BlockRuleConclAt (rP c') nF m (RecTy c') eisA fapA CihR)
    (hTyE : RecTy c' = mkPisAV (rds c') (concl c'))
    (hrds : (rds c').length = rP c' + nIdx + 1)
    (hesLen : eisA.length = nIdx)
    (hconclB : Term.bvarsBelow (rds c').length (concl c').erase)
    (hxs : xs.length = rP c') (hfs : fs.length = nF) (hbsl : bs.length = m) :
    (pt : V) ∈ˢ interp V (consList bs (consList (xs ++ fs) ρ)) CihR := by
  have htgtN : d.tgts cc j i < d.N := by
    rw [htgt]
    exact Nat.lt_of_lt_of_le hmk' (Nat.le_add_right _ _)
  obtain ⟨hidx, hcar, hP⟩ :=
    blockIndPred_of hM (d.satOfSpine hpar) hccN ht hj hfit hiF hrec htgtN hbsB
  rw [htgt] at hidx hcar hP
  rw [← hM.leaf (mem c') hmk' ψ ρ as _ hpar hidx] at hcar
  have hfitC' : SpineFit ρ ((rds c').map (·.2.2))
      (xs ++ ((((d.Eiss cc ψ).getD j []).getD i []).map
          (interp V (consList bs (consList (fs.take i) (consList as ρ))))
        ++ [bs.foldl SetTheory.app (fs.getD i pt)])) := by
    rw [← List.take_append_drop (rP c') ((rds c').map (·.2.2))]
    exact SpineFit.append (hpdE ▸ hpref') (hjoin _ _ hidx hcar)
  exact blockIndIhLeaf_of hc' hcon hTyE hrds hesLen hconclB hxs hfs hbsl hesB.symm hmkB.symm
    hfitC' htake hP

/-- **The IND arm's step**, `blockIndPt`'s `hstep`. -/
theorem blockIndStep (hμ : μ.verifiedChecks = true) (hM : BlockModelAt mo names d)
    (hnCt : ∀ c, c < K → (d.ctorsM (mem c)).length = nCt c)
    (hcerts : ∀ c, c < K → ∀ j, j < nCt c →
      BlockRuleCerts V mp F ψ (rP c) (fdoms c j).length (ihdoms c j).length
        (pdoms c) (fdoms c j) (ihdoms c j) (Rb0 c j) (Ca c j))
    (hspF : ∀ c, c < K → ∀ ys : List V, SpineFit ρ ((rds c).map (·.2.2)) ys →
      ∀ j, j < nCt c → ∀ fs : List V,
      d.ChainFit ψ (consList ((prefOf (rP c) ys).take d.nP) ρ)
        (sepTuple (d.w ψ) d.N (d.idx ψ (consList ((prefOf (rP c) ys).take d.nP) ρ))
          (d.Φ ψ (consList ((prefOf (rP c) ys).take d.nP) ρ))
          (blockIndP d ψ ρ K rP mem rds concl ((prefOf (rP c) ys).take d.nP)))
        (d.tup ψ (mem c) (idxOf (rP c) ys)) (mem c) j fs →
      SpineFit ρ (pdoms c ++ fdoms c j) (prefOf (rP c) ys ++ fs))
    (hih : ∀ c, c < K → ∀ ys : List V, SpineFit ρ ((rds c).map (·.2.2)) ys →
      ∀ j, j < nCt c → ∀ fs : List V,
      d.ChainFit ψ (consList ((prefOf (rP c) ys).take d.nP) ρ)
        (sepTuple (d.w ψ) d.N (d.idx ψ (consList ((prefOf (rP c) ys).take d.nP) ρ))
          (d.Φ ψ (consList ((prefOf (rP c) ys).take d.nP) ρ))
          (blockIndP d ψ ρ K rP mem rds concl ((prefOf (rP c) ys).take d.nP)))
        (d.tup ψ (mem c) (idxOf (rP c) ys)) (mem c) j fs →
      SpineFit (consList (prefOf (rP c) ys ++ fs) ρ) (ihdoms c j) (ihvals c j))
    (hT : ∀ c, c < K → ∀ ys : List V, SpineFit ρ ((rds c).map (·.2.2)) ys →
      ∀ j, j < nCt c → ∀ fs : List V,
      interp V (consList (ihvals c j) (consList (prefOf (rP c) ys ++ fs) ρ)) (Ca c j)
        ∈ˢ (univZero : V))
    (hCaE : ∀ c, c < K → ∀ ys : List V, SpineFit ρ ((rds c).map (·.2.2)) ys →
      ∀ j, j < nCt c → ∀ fs : List V,
      majOf ys = d.inj ψ (mem c) j fs →
      interp V (consList (ihvals c j) (consList (prefOf (rP c) ys ++ fs) ρ)) (Ca c j)
        = interp V (consList ys ρ) (concl c)) :
    ∀ as : List V, SpineFit ρ (d.params ψ) as →
      ∀ m, m < d.N → ∀ i, i ∈ˢ d.idx ψ (consList as ρ) m → ∀ x,
        x ∈ˢ app (d.Φ ψ (consList as ρ)
            (sepTuple (d.w ψ) d.N (d.idx ψ (consList as ρ)) (d.Φ ψ (consList as ρ))
              (blockIndP d ψ ρ K rP mem rds concl as)) m) i →
        blockIndP d ψ ρ K rP mem rds concl as m i x := by
  intro as hpar m hm i hi x hx c hc hmc ys hys htk hti hmaj
  subst hmc
  subst htk
  subst hti
  subst hmaj
  obtain ⟨j, fs, hj, hfit, hxinj⟩ :=
    (hM.fibre ψ (consList ((prefOf (rP c) ys).take d.nP) ρ) (d.satOfSpine hpar) _
      (sepTuple_mem _ _ _ _ _) (mem c) hm _ hi (majOf ys)).mp hx
  have hjn : j < nCt c := by rw [← hnCt c hc]; exact hj
  have hres := (hcerts c hc j hjn).residueOk hμ
    (hspF c hc ys hys j hjn fs hfit) (hih c hc ys hys j hjn fs hfit)
  have hTv := hT c hc ys hys j hjn fs
  rw [← hCaE c hc ys hys j hjn fs hxinj] at *
  exact (eq_pt_of_mem_univZero hTv hres.2) ▸ hres.2

/-- **`IndRegimeAt` FROM THE RUN**, the dispatch's `ℓ = 0` arm: §17's
induction with its step discharged (`blockIndStep`), the rules'
certificates, and the regime's own two premises at the CHAIN frame.

The step's premises are at the BASE frame and the regime's at the
chain frame; they are genuinely two obligations (the induction is a
statement about the block's carrier, the ι equations' about the
chain), which is why both appear. -/
theorem blockIndRegime_run {RecTy : Nat → AnnotTerm} {Rb : Nat → Nat → AnnotTerm}
    {ihKeys : Nat → Nat → List (Nat × Nat)}
    {tlA : Nat → Nat → Nat → List (Nat × Nat × AnnotTerm)}
    {Cih : Nat → Nat → Nat → AnnotTerm}
    (hμ : μ.verifiedChecks = true) (hM : BlockModelAt mo names d)
    (hmemK : ∀ c, c < K → mem c < d.k)
    (hnCt : ∀ c, c < K → (d.ctorsM (mem c)).length = nCt c)
    (hsplitR : BlockRecSplitAt V mo d ψ K rP mem rds ρ)
    (hbits : OneElimLevel 0 K rds)
    (hTyE : ∀ c, c < K → RecTy c = mkPisAV (rds c) (concl c))
    (hcerts : ∀ c, c < K → ∀ j, j < nCt c →
      BlockRuleCerts V mp F ψ (rP c) (fdoms c j).length (ihdoms c j).length
        (pdoms c) (fdoms c j) (ihdoms c j) (Rb c j) (Ca c j))
    (hspF : ∀ c, c < K → ∀ ys : List V, SpineFit ρ ((rds c).map (·.2.2)) ys →
      ∀ j, j < nCt c → ∀ fs : List V,
      d.ChainFit ψ (consList ((prefOf (rP c) ys).take d.nP) ρ)
        (sepTuple (d.w ψ) d.N (d.idx ψ (consList ((prefOf (rP c) ys).take d.nP) ρ))
          (d.Φ ψ (consList ((prefOf (rP c) ys).take d.nP) ρ))
          (blockIndP d ψ ρ K rP mem rds concl ((prefOf (rP c) ys).take d.nP)))
        (d.tup ψ (mem c) (idxOf (rP c) ys)) (mem c) j fs →
      SpineFit ρ (pdoms c ++ fdoms c j) (prefOf (rP c) ys ++ fs))
    (hihLen : ∀ c, c < K → ∀ j, j < nCt c → (ihdoms c j).length = (ihKeys c j).length)
    (hihDom : ∀ c, c < K → ∀ j, j < nCt c → ∀ r, r < (ihKeys c j).length →
      (ihdoms c j).getD r default
        = (mkPisAV (tlA c j ((ihKeys c j).getD r (0, 0)).1) (Cih c j r)).liftN r 0)
    (hihBits : ∀ c, c < K → ∀ j, j < nCt c → ∀ r, r < (ihKeys c j).length →
      ∀ dd ∈ tlA c j ((ihKeys c j).getD r (0, 0)).1, dd.2.1 = 0)
    (hihLeaf : ∀ c, c < K → ∀ ys : List V, SpineFit ρ ((rds c).map (·.2.2)) ys →
      ∀ j, j < nCt c → ∀ fs : List V,
      d.ChainFit ψ (consList ((prefOf (rP c) ys).take d.nP) ρ)
        (sepTuple (d.w ψ) d.N (d.idx ψ (consList ((prefOf (rP c) ys).take d.nP) ρ))
          (d.Φ ψ (consList ((prefOf (rP c) ys).take d.nP) ρ))
          (blockIndP d ψ ρ K rP mem rds concl ((prefOf (rP c) ys).take d.nP)))
        (d.tup ψ (mem c) (idxOf (rP c) ys)) (mem c) j fs →
      ∀ r, r < (ihKeys c j).length → ∀ bs : List V,
      SpineFit (consList (prefOf (rP c) ys ++ fs) ρ)
        ((tlA c j ((ihKeys c j).getD r (0, 0)).1).map (·.2.2)) bs →
      (pt : V) ∈ˢ interp V (consList bs (consList (prefOf (rP c) ys ++ fs) ρ)) (Cih c j r))
    (hTStep : ∀ c, c < K → ∀ ys : List V, SpineFit ρ ((rds c).map (·.2.2)) ys →
      ∀ j, j < nCt c → ∀ fs : List V,
      interp V
          (consList (List.replicate (ihdoms c j).length (pt : V))
            (consList (prefOf (rP c) ys ++ fs) ρ)) (Ca c j)
        ∈ˢ (univZero : V))
    (hCaE : ∀ c, c < K → ∀ ys : List V, SpineFit ρ ((rds c).map (·.2.2)) ys →
      ∀ j, j < nCt c → ∀ fs : List V,
      majOf ys = d.inj ψ (mem c) j fs →
      interp V
          (consList (List.replicate (ihdoms c j).length (pt : V))
            (consList (prefOf (rP c) ys ++ fs) ρ)) (Ca c j)
        = interp V (consList ys ρ) (concl c))
    (hihReg : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (fun _ => (pt : V)) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      SpineFit (consList (xs ++ fs) (chainFrame K (fun _ => (pt : V)) ρ)) (ihdoms c j)
        ((ihs c j).map
          (interp V (consList (xs ++ fs) (chainFrame K (fun _ => (pt : V)) ρ)))))
    (hTReg : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (fun _ => (pt : V)) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      interp V
          (consList
            ((ihs c j).map
              (interp V (consList (xs ++ fs) (chainFrame K (fun _ => (pt : V)) ρ))))
            (consList (xs ++ fs) (chainFrame K (fun _ => (pt : V)) ρ))) (Ca c j)
        ∈ˢ (univZero : V)) :
    IndRegimeAt V μ K nCt rP ψ RecTy pdoms fdoms ihs Rb ρ :=
  ⟨envT, mp, F, ihdoms, Ca, hμ,
    hind_of_spines hbits hTyE
      (blockIndPt hM hmemK hsplitR
        (blockIndStep (ihvals := fun c j => List.replicate (ihdoms c j).length (pt : V))
          hμ hM hnCt hcerts hspF
          (fun c hc ys hys j hjn fs hfit =>
            spineFit_ihdoms_zero (hihLen c hc j hjn)
              (by rw [List.length_replicate]; exact hihLen c hc j hjn)
              (fun r _ => getD_replicate_pt _ _)
              (fun r hr => hihDom c hc j hjn r hr) (fun r hr => hihBits c hc j hjn r hr)
              (fun r hr bs hbs => hihLeaf c hc ys hys j hjn fs hfit r hr bs hbs))
          hTStep hCaE)),
    hcerts, hihReg, hTReg⟩

end IndStep


/-! ## 38. THE BITS LAW — a Π-tower's binder data follows its
CONCLUSION's sort

`blockRecOneElimLevel` (§4) takes `hbits` — every binder numeral of
recursor `c`'s binder data is zero exactly when its elimination level
is — as a premise, and the audit's §2.6 lists it UNOWNED.  This is its
producer.

**It is a law of the CHECK, not of the annotation pass.**  `annotPwPi`
(`Kernel/Core.lean`) answers most binders from the head-symbol reader
(`typeSortPW`) and only falls back to inference, so an annotation-side
law would have to carry the reader's soundness; `inferBody`'s ∀ clause
VALIDATES the datum it finds against the codomain sort it infers
(`(forall-cod)`), which at a verified mode pins every `BinderMeta.pw`
of a tower with nothing but that clause's own `unless`.

Three steps:

* `inferTypeCore_forallE_peel` — one ∀ binder of a successful
  inference: the codomain's sort `v`, the datum `mb.pw = zeronessOf v`
  and the node's own sort `imax u v`;
* `inferTypeCore_openPis_sortZ` — the tower's inferred sort has the
  CONCLUSION's zero-ness (`zeronessOf (imax u v) = zeronessOf v` is
  the whole content, carried down the openers);
* `stripPisAV_denoteMeta_pw` — every binder numeral of the READING is
  `pwBit ψ` of that one `PropWhen`, `denoteMeta`'s own
  `.pi 0 (pwBit φ mb.pw)` composed with the two above.

All three take the conclusion's inference at a SECOND fuel `G ≥ F`:
the check runs it twice — once inside the tower's own recursion, at
the fuel left after the peel, and once on its own
(`checkBlockRecTys`) — and fuel monotonicity (`inferTypeCore_mono`,
`Verify/Mono.lean`) is what identifies the two. -/

section BitsLaw

/-- `ensureSort` on a BUILT sort — `whnf_sort` at the two fuel steps
the reduction pays. -/
theorem ensureSortCore_sort (envK : Env) {G : Nat} (d : Nat) (u : Level) (hG : 2 ≤ G) :
    ConLeche.ensureSortCore μ envK G d (.sort u) = .ok u := by
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 2 := ⟨G - 2, by omega⟩
  show ConLeche.ensureSort (ConLeche.pureFns μ envK (G' + 2)) envK d (.sort u) = .ok u
  unfold ConLeche.ensureSort
  rw [show (ConLeche.pureFns μ envK (G' + 2)).whnf d (Expr.sort u)
      = ConLeche.whnf μ envK (G' + 2) d (.sort u) from rfl, ConLeche.whnf_sort]
  rfl

/-- A successful inference at fuel `0` is impossible. -/
theorem inferTypeCore_pos {envK : Env} {d : Nat} {e r : Expr} {F : Nat}
    (h : ConLeche.inferTypeCore μ envK F d e = .ok r) : 1 ≤ F := by
  cases F with
  | zero =>
    rw [ConLeche.inferTypeCore_zero] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ _ => omega

/-- **One ∀ binder of a successful inference, peeled.**  The ∀ clause's
own witnesses: the codomain's sort `v`, the node's validated datum and
the node's own sort. -/
theorem inferTypeCore_forallE_peel (hμ : μ.verifiedChecks = true) {envK : Env}
    {d F : Nat} {ty bd s : Expr} {mb : ConLeche.BinderMeta}
    (h : ConLeche.inferTypeCore μ envK F d (.forallE ty bd mb) = .ok s) :
    ∃ (F₀ : Nat) (udom v : Level) (bt₁ : Expr),
      F = F₀ + 1 ∧ 1 ≤ F₀ ∧
      ConLeche.inferTypeCore μ envK F₀ (d + 1) (bd.instantiate1 (.fvar d ty)) = .ok bt₁ ∧
      ConLeche.ensureSortCore μ envK F₀ (d + 1) bt₁ = .ok v ∧
      Level.zeronessOf v = mb.pw ∧ s = .sort (.imax udom v) := by
  cases F with
  | zero =>
    rw [ConLeche.inferTypeCore_zero] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ F₀ =>
    rw [ConLeche.inferTypeCore_forallE_eq] at h
    obtain ⟨tty, htty, h⟩ := ConLeche.exceptBind_ok h
    obtain ⟨w0, hw0, h⟩ := ConLeche.exceptBind_ok h
    clear htty hw0
    cases w0 with
    | sort udom =>
      obtain ⟨bt₁, hbt₁, h⟩ := ConLeche.exceptBind_ok h
      obtain ⟨v, hv, h⟩ := ConLeche.exceptBind_ok h
      simp only [hμ, if_true, bind, Except.bind] at h
      by_cases hz : (Level.zeronessOf v == mb.pw) = true
      · rw [hz] at h
        refine ⟨F₀, udom, v, bt₁, rfl, inferTypeCore_pos hbt₁, hbt₁, hv,
          by simpa using hz, ?_⟩
        simpa [pure, Except.pure] using h.symm
      · simp only [hz] at h
        simp [throw, throwThe, MonadExceptOf.throw] at h
    | _ => simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **A Π-tower's inferred sort has its CONCLUSION's zero-ness.** -/
theorem inferTypeCore_openPis_sortZ (hμ : μ.verifiedChecks = true) {envK : Env} :
    ∀ (n : Nat) {d F G : Nat} {e : Expr} {fvs : List Expr} {o s bt : Expr} {u : Level},
      F ≤ G → openPisAtFvars n e d = some (fvs, o) →
      ConLeche.inferTypeCore μ envK F d e = .ok s →
      ConLeche.inferTypeCore μ envK G (d + n) o = .ok bt →
      ConLeche.ensureSortCore μ envK G (d + n) bt = .ok u →
      ∃ w, ConLeche.ensureSortCore μ envK G d s = .ok w ∧
        Level.zeronessOf w = Level.zeronessOf u
  | 0, d, F, G, e, fvs, o, s, bt, u, hFG, hop, hinf, hcon, hsort => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨-, rfl⟩ := hop
    rw [Nat.add_zero] at hcon hsort
    obtain rfl : bt = s := by
      have hh := hcon.symm.trans (ConLeche.inferTypeCore_mono hFG hinf)
      simpa using hh
    exact ⟨u, hsort, rfl⟩
  | n + 1, d, F, G, e, fvs, o, s, bt, u, hFG, hop, hinf, hcon, hsort => by
    match e, hop with
    | .forallE ty bd mb, hop =>
      simp only [openPisAtFvars] at hop
      split at hop
      · next fvs' o' hop' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨-, rfl⟩ := hop
        obtain ⟨F₀, udom, v, bt₁, rfl, hF₀, hbt₁, hv, hpw, rfl⟩ :=
          inferTypeCore_forallE_peel hμ hinf
        have hcon' : ConLeche.inferTypeCore μ envK G (d + 1 + n) o' = .ok bt := by
          rw [show d + 1 + n = d + (n + 1) from by omega]; exact hcon
        have hsort' : ConLeche.ensureSortCore μ envK G (d + 1 + n) bt = .ok u := by
          rw [show d + 1 + n = d + (n + 1) from by omega]; exact hsort
        obtain ⟨w', hw', hzw'⟩ :=
          inferTypeCore_openPis_sortZ hμ n (by omega) hop' hbt₁ hcon' hsort'
        obtain rfl : w' = v := by
          have hh := hw'.symm.trans (ConLeche.ensureSortCore_mono (f := F₀) (f' := G)
            (by omega) hv)
          simpa using hh
        exact ⟨.imax udom w', ensureSortCore_sort envK d _ (by omega), hzw'⟩
      · exact nomatch hop
    | .bvar _, hop => nomatch hop
    | .fvar _ _, hop => nomatch hop
    | .sort _, hop => nomatch hop
    | .const _ _, hop => nomatch hop
    | .app _ _, hop => nomatch hop
    | .lam _ _ _, hop => nomatch hop
    | .letE _ _ _, hop => nomatch hop
    | .proj _ _ _, hop => nomatch hop
    | .lit _, hop => nomatch hop

/-- **The bits law.**  Every binder numeral of a checked Π-tower's
READING is `pwBit φ` of the tower's conclusion's sort. -/
theorem stripPisAV_denoteMeta_pw {acval : Name → (Name → Nat) → AnnotTerm} {env envK : Env}
    {φ : Name → Nat} (hμ : μ.verifiedChecks = true) :
    ∀ (n : Nat) {d F G : Nat} {e : Expr} {fvs : List Expr} {o s bt : Expr} {u : Level}
      {ea : AnnotTerm} {pps : List (Nat × Nat × AnnotTerm)} {b : AnnotTerm},
      F ≤ G → openPisAtFvars n e d = some (fvs, o) →
      denoteMeta acval env φ d e = some ea →
      stripPisAV n ea = some (pps, b) →
      ConLeche.inferTypeCore μ envK F d e = .ok s →
      ConLeche.inferTypeCore μ envK G (d + n) o = .ok bt →
      ConLeche.ensureSortCore μ envK G (d + n) bt = .ok u →
      ∀ p ∈ pps, p.2.1 = pwBit φ (Level.zeronessOf u)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hst, _, _, _ => by
    simp only [stripPisAV, Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, -⟩ := hst
    exact fun _ h => nomatch h
  | n + 1, d, F, G, e, fvs, o, s, bt, u, ea, pps, b, hFG, hop, hr, hst, hinf, hcon, hsort => by
    match e, hop with
    | .forallE ty bd mb, hop =>
      obtain ⟨ta, ba, -, hba, rfl⟩ := denoteMeta_forallE_inv hr
      simp only [openPisAtFvars] at hop
      split at hop
      · next fvs' o' hop' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨-, rfl⟩ := hop
        obtain ⟨F₀, udom, v, bt₁, rfl, hF₀, hbt₁, hv, hpw, rfl⟩ :=
          inferTypeCore_forallE_peel hμ hinf
        have hcon' : ConLeche.inferTypeCore μ envK G (d + 1 + n) o' = .ok bt := by
          rw [show d + 1 + n = d + (n + 1) from by omega]; exact hcon
        have hsort' : ConLeche.ensureSortCore μ envK G (d + 1 + n) bt = .ok u := by
          rw [show d + 1 + n = d + (n + 1) from by omega]; exact hsort
        -- the head binder's datum: the tail's own inferred sort
        obtain ⟨w', hw', hzw'⟩ :=
          inferTypeCore_openPis_sortZ hμ n (μ := μ) (by omega) hop' hbt₁ hcon' hsort'
        obtain rfl : w' = v := by
          have hh := hw'.symm.trans (ConLeche.ensureSortCore_mono (f := F₀) (f' := G)
            (by omega) hv)
          simpa using hh
        simp only [stripPisAV] at hst
        cases hst' : stripPisAV n ba with
        | none => rw [hst'] at hst; exact nomatch hst
        | some q =>
          rw [hst'] at hst
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hst
          obtain ⟨rfl, -⟩ := hst
          intro p hp
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · show pwBit φ mb.pw = pwBit φ (Level.zeronessOf u)
            rw [← hpw, hzw']
          · exact stripPisAV_denoteMeta_pw hμ n (by omega) hop' hba hst' hbt₁ hcon' hsort' p hp
      · exact nomatch hop
    | .bvar _, hop => nomatch hop
    | .fvar _ _, hop => nomatch hop
    | .sort _, hop => nomatch hop
    | .const _ _, hop => nomatch hop
    | .app _ _, hop => nomatch hop
    | .lam _ _ _, hop => nomatch hop
    | .letE _ _ _, hop => nomatch hop
    | .proj _ _ _, hop => nomatch hop
    | .lit _, hop => nomatch hop

end BitsLaw

/-! ### 38.1 The run: stage (b)'s two CONCLUSION runs, and `hbits`

`checkBlockRecTys_inv` (`Verify/Inductives/BlockWF.lean`) and
`checkBlockRecTys_open` (`BlockRecMem.lean`) both discard the stage's
own sort computation on the opened conclusion — `ops.inferType`
followed by `ops.ensureSort`, whose level IS the recursor's stored
elimination level.  Those two runs are the bits law's premises, so the
peel is widened here (a sixth inversion of that stage; if the Verify
lane ever keeps the runs, this is its corollary and should go). -/

section ElimRun

local syntax "close_throw" term : tactic
local macro_rules
  | `(tactic| close_throw $h:term) =>
    `(tactic| first
        | exact nomatch $h
        | exact absurd $h (by
            simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
            exact fun hh => nomatch hh)
        | exact absurd $h
            (by simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]))

/-- **Stage (b)'s inversion, WIDENED to the conclusion's SORT**: the
recursor's opened conclusion is inferred and `ensureSort`ed at the
stage's own fuel, and the level that comes back is the entry's third
component — the elimination level D-d compares. -/
theorem checkBlockRecTys_elim {env : Env}
    {p : ConLeche.BlockShape} {nested : Bool} {cvTas : List ConstantVal} {F : Nat} :
    ∀ {recs : List ConLeche.RecShape} {ri : Nat}
      {cvRus : List (ConstantVal × Nat × Level)},
      ConLeche.checkBlockRecTys (ConLeche.fueledOps μ F) env p nested cvTas recs ri
          = .ok cvRus →
      ∀ i, i < recs.length → ∃ (cvRi : ConstantVal) (nIdx : Nat) (u : Level)
        (fvs : List Expr) (concl sty : Expr),
        cvRus[i]? = some (cvRi, nIdx, u) ∧
        ConLeche.openPisAtFvars (p.majorIdxAt (ri + i) + 1) cvRi.type 0
          = some (fvs, concl) ∧
        ConLeche.inferTypeCore μ env F (p.majorIdxAt (ri + i) + 1) concl = .ok sty ∧
        ConLeche.ensureSortCore μ env F (p.majorIdxAt (ri + i) + 1) sty = .ok u
  | [], _, cvRus, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | rc :: rest, ri, cvRus, h, i, hi => by
    unfold ConLeche.checkBlockRecTys at h
    obtain ⟨ms, _, h⟩ := ConLeche.exceptBind_ok h
    obtain ⟨cvTa, _, h⟩ := ConLeche.exceptBind_ok h
    obtain ⟨cvRi, _, h⟩ := ConLeche.exceptBind_ok h
    by_cases hle : p.nP ≤ p.rulePrefixAt ri
    case neg => rw [if_neg hle] at h; close_throw h
    rw [if_pos hle] at h
    by_cases hle2 : (p.majorIdxAt ri == p.rulePrefixAt ri + ms.nIdx) = true
    case neg => rw [if_neg hle2] at h; close_throw h
    rw [if_pos hle2] at h
    obtain ⟨x1, hx1, h⟩ := ConLeche.exceptBind_ok h
    obtain ⟨fvs, concl⟩ := x1
    have hop : ConLeche.openPisAtFvars (p.majorIdxAt ri + 1) cvRi.type 0
        = some (fvs, concl) := ConLeche.unwrapOr_ok hx1
    obtain ⟨x2, _, h⟩ := ConLeche.exceptBind_ok h; obtain ⟨_, _⟩ := x2
    obtain ⟨_, _, h⟩ := ConLeche.exceptBind_ok h
    obtain ⟨maj, _, h⟩ := ConLeche.exceptBind_ok h
    by_cases hmaj : (maj.fvarTypeD.getAppFn ==
          Expr.const ms.cvT.name (p.lps.map .param) &&
        maj.fvarTypeD.getAppArgs.length == p.nP + ms.nIdx &&
        maj.fvarTypeD.getAppArgs.take p.nP == fvs.take p.nP &&
        maj.fvarTypeD.getAppArgs.drop p.nP ==
          (fvs.drop (p.rulePrefixAt ri)).take ms.nIdx) = true
    case neg => rw [if_neg hmaj] at h; close_throw h
    rw [if_pos hmaj] at h
    obtain ⟨sty, hsty, h⟩ := ConLeche.exceptBind_ok h
    obtain ⟨u, hu, h⟩ := ConLeche.exceptBind_ok h
    have key : ∀ {rs' : List (ConstantVal × Nat × Level)},
        ConLeche.checkBlockRecTys (ConLeche.fueledOps μ F) env p nested cvTas rest
            (ri + 1) = .ok rs' →
        cvRus = (cvRi, ms.nIdx, u) :: rs' →
        ∃ (cvRi' : ConstantVal) (nIdx : Nat) (u' : Level)
          (fvs' : List Expr) (concl' sty' : Expr),
          cvRus[i]? = some (cvRi', nIdx, u') ∧
          ConLeche.openPisAtFvars (p.majorIdxAt (ri + i) + 1) cvRi'.type 0
            = some (fvs', concl') ∧
          ConLeche.inferTypeCore μ env F (p.majorIdxAt (ri + i) + 1) concl' = .ok sty' ∧
          ConLeche.ensureSortCore μ env F (p.majorIdxAt (ri + i) + 1) sty' = .ok u' := by
      intro rs' hrest hcv
      subst hcv
      cases i with
      | zero =>
        refine ⟨cvRi, ms.nIdx, u, fvs, concl, sty, rfl, ?_, ?_, ?_⟩
        · rw [Nat.add_zero]; exact hop
        · rw [Nat.add_zero]; exact hsty
        · rw [Nat.add_zero]; exact hu
      | succ i =>
        obtain ⟨cvRi', nIdx, u', fvs', concl', sty', hcu, hop', hsty', hu'⟩ :=
          checkBlockRecTys_elim hrest i (by simpa using hi)
        refine ⟨cvRi', nIdx, u', fvs', concl', sty', by simpa using hcu, ?_, ?_, ?_⟩
        · rw [show ri + (i + 1) = ri + 1 + i from by omega]; exact hop'
        · rw [show ri + (i + 1) = ri + 1 + i from by omega]; exact hsty'
        · rw [show ri + (i + 1) = ri + 1 + i from by omega]; exact hu'
    by_cases hlarge : ConLeche.blockLargeElimAllowed p nested = true
    case pos =>
      rw [if_pos hlarge] at h
      obtain ⟨rs', hrest, h⟩ := ConLeche.exceptBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact key hrest h.symm
    case neg =>
      rw [if_neg hlarge] at h
      obtain ⟨b, _, h⟩ := ConLeche.exceptBind_ok h
      by_cases hb : b = true
      case neg => rw [if_neg hb] at h; close_throw h
      rw [if_pos hb] at h
      obtain ⟨rs', hrest, h⟩ := ConLeche.exceptBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact key hrest h.symm

/-- **Stage (b) and D-d, off `checkBlockRecK`**: the type stage's own
list, with its elimination-level verdict. -/
theorem checkBlockRecK_elimList {envC : Env} {p : ConLeche.BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs) :
    ∃ cvRus : List (ConstantVal × Nat × Level),
      ConLeche.checkBlockRecTys (ConLeche.fueledOps μ F) envC p.toBlockShape
          (ConLeche.blockNested p.kinds) cvTas p.recs 0 = .ok cvRus ∧
      ConLeche.checkBlockRecElimAgree (m := ConLeche.CheckM) (cvRus.map (·.2.2)) = .ok () ∧
      rs.length = p.recs.length ∧
      ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
        rs[i]? = some r → (cvRus.map (·.1))[i]? = some r.1 := by
  unfold ConLeche.checkBlockRecK at h
  obtain ⟨-, -, h⟩ := ConLeche.exceptBind_ok h
  obtain ⟨cvRus, htys, h⟩ := ConLeche.exceptBind_ok h
  obtain ⟨uf, hfam, h⟩ := ConLeche.exceptBind_ok h
  obtain ⟨-, hallT⟩ := ConLeche.checkBlockRecTys_inv htys
  obtain ⟨hlenR, hallR⟩ := ConLeche.checkBlockRecsRules_facts h
  rw [ConLeche.checkBlockRecFamilyAgree] at hfam
  obtain ⟨u0, helim, hrest0⟩ := ConLeche.exceptBind_ok hfam
  clear hrest0
  refine ⟨cvRus, htys, ?_, hlenR, ?_⟩
  · cases u0; exact helim
  intro i r hr
  have hil : i < p.recs.length := by
    have := (List.getElem?_eq_some_iff.mp hr).1
    omega
  obtain ⟨-, r', -, hr', hcvRa, -⟩ := hallR i hil
  obtain rfl := Option.some.inj (hr.symm.trans hr')
  obtain ⟨-, cvRi, nIdx, u', -, hcu, -, -, -⟩ := hallT i hil
  have hcvRa' : (cvRus.map (fun q => (q.1, q.2.1)))[i]? = some (cvRi, nIdx) := by
    rw [List.getElem?_map, hcu]; rfl
  have hr1 : r.1 = cvRi := by
    have hq := hcvRa
    rw [Nat.zero_add] at hq
    exact congrArg Prod.fst (Option.some.inj (hq.symm.trans hcvRa'))
  rw [List.getElem?_map, hcu, hr1]
  rfl

end ElimRun

/-- **`hbits` AND `hmem`, FROM THE RUN** — the audit's §2.6 item
`blockRecOneElimLevel`'s premise, discharged.  The binder numerals of
recursor `c`'s binder data are `pwBit ψ` of the `PropWhen` the ∀
clause validated at every binder of its stored type, and that datum is
`zeronessOf` the level stage (b) read off the CONCLUSION — the
recursor's elimination level. -/
theorem blockRecElimLevel_run (hμ : μ.verifiedChecks = true) {envC : Env}
    (mpC : EnvModelM V μ envC) {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs) :
    ∃ (us : List Level) (uOf : Nat → Level),
      ConLeche.checkBlockRecElimAgree (m := ConLeche.CheckM) us = .ok () ∧
      (∀ c, c < rs.length → uOf c ∈ us) ∧
      ∀ (ψ : Name → Nat) (c : Nat), c < rs.length →
        ∀ b ∈ blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c,
          (b.2.1 = 0 ↔ (uOf c).eval ψ = 0) := by
  obtain ⟨cvRus, htys, helim, hlenR, hbridge⟩ := checkBlockRecK_elimList h
  have hlenT : cvRus.length = p.recs.length := (ConLeche.checkBlockRecTys_inv htys).1
  refine ⟨cvRus.map (·.2.2), fun c => ((cvRus.map (·.2.2)).getD c .zero), helim, ?_, ?_⟩
  · intro c hc
    have hlt : c < (cvRus.map (·.2.2)).length := by rw [List.length_map, hlenT]; omega
    have hg : (cvRus.map (·.2.2)).getD c .zero = (cvRus.map (·.2.2))[c] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl
    show ((cvRus.map (·.2.2)).getD c .zero) ∈ cvRus.map (·.2.2)
    rw [hg]
    exact List.getElem_mem hlt
  · intro ψ c hc b hb
    obtain ⟨r, hr⟩ : ∃ r, rs[c]? = some r := ⟨rs[c]'hc, List.getElem?_eq_getElem hc⟩
    have hcp : c < p.recs.length := by omega
    obtain ⟨cvRi, nIdx, u, fvs', concl', sty, hcu, hop', hsty, hu⟩ :=
      checkBlockRecTys_elim htys c hcp
    rw [Nat.zero_add] at hop' hsty hu
    -- the stored recursor IS the type stage's checked constant
    have hr1 : r.1 = cvRi := by
      have h' := hbridge c r hr
      rw [List.getElem?_map, hcu] at h'
      simp only [Option.map_some, Option.some.injEq] at h'
      exact h'.symm
    -- the level the theorem hands back IS stage (b)'s
    have huOf : ((cvRus.map (·.2.2)).getD c .zero) = u := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, hcu]; rfl
    -- the type's own inference (`checkConstantVal`'s second run)
    obtain ⟨-, hallT2⟩ := ConLeche.checkBlockRecTys_inv htys
    obtain ⟨rcC, cvRiB, nIdxB, uB, -, hcuB, hcvB, -, -⟩ := hallT2 c hcp
    have hcvEq : cvRiB = cvRi := congrArg Prod.fst (Option.some.inj (hcuB.symm.trans hcu))
    obtain ⟨-, -, -, -, -, -, tyA, stype, -, -, -, -, hinfTy, -, hcv'⟩ :=
      ConLeche.checkConstantVal_inv hcvB
    have htyA : cvRi.type = tyA := by rw [← hcvEq, hcv']
    -- the reading, and its Π-peel
    obtain ⟨fvs, concl, hop, hta, hmk, hlenRds, -, -, -, -⟩ := checkBlockRecK_tyPis hμ mpC h hr ψ
    rw [← hr1] at hop'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hop.symm.trans hop'))
    -- the reading's Π-peel IS the run's own binder data (O-2's identification)
    have hst : stripPisAV (p.toBlockShape.majorIdxAt c + 1)
        (blockRecTyAV mpC.base2.acval envC rs ψ c)
        = some (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c,
            blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ c) := by
      rw [hmk, ← hlenRds]
      exact stripPisAV_mkPisAV _ _
    have hinfTy' : ConLeche.inferTypeCore μ envC F 0 r.1.type = .ok stype := by
      rw [hr1, htyA]; exact hinfTy
    show b.2.1 = 0 ↔ Level.eval ψ ((cvRus.map (·.2.2)).getD c .zero) = 0
    rw [huOf, stripPisAV_denoteMeta_pw (envK := envC) hμ _ (Nat.le_refl F) hop hta hst
      hinfTy' (by rw [Nat.zero_add]; exact hsty) (by rw [Nat.zero_add]; exact hu) b hb]
    exact pwBit_zeronessOf ψ u

/-- **`OneElimLevel` FROM THE RUN** — §4's theorem with BOTH its
premises discharged.  The level is the family's shared one: the sort
`checkBlockRecTys` read off the first recursor's conclusion, at `ψ`.
This is the shape every regime's `hbits` takes
(`BlockRecRegimes.lean`, and §37's IND arm at `ℓ = 0`). -/
theorem blockRecOneElimLevel_run (hμ : μ.verifiedChecks = true) {envC : Env}
    (mpC : EnvModelM V μ envC) {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (ψ : Name → Nat) :
    ∃ ℓ : Nat, OneElimLevel ℓ rs.length
      (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) := by
  obtain ⟨us, uOf, helim, hmem, hbits⟩ := blockRecElimLevel_run (V := V) hμ mpC h
  exact ⟨(us.headD .zero).eval ψ, blockRecOneElimLevel helim ψ hmem (hbits ψ)⟩

/-! ## 39. `BlockRuleCerts`' FRAME SEAM — `hdoms` and `hokΔ` from the
three segments

`BlockRuleCerts` (§1) states its two frame premises at the REVERSED
context `ihdoms.reverse ++ (pdoms ++ fdoms).reverse`, because that is
the order `CtxOk`/`Sat` read a frame in; the three owners state their
readings and gradings SEGMENT by segment, at the frame's ascending
depths.  These two theorems are the whole distance between the two
spellings, and they are pure index algebra: the reversed context IS
`(pdoms ++ fdoms ++ ihdoms).reverse`, and `L - 1 - i` undoes the
reversal.

The premise shapes are the owners' own:

* the PREFIX segment is `blockRulePdomsAV_reads` / `_graded` (§35)
  verbatim;
* the FIELD segment is `denoteMeta_openPis`' per-binder output at the
  constructor telescope's opening (what `readOpenedDoms_shift`'s proof
  obtains and `blockRuleFdomsAV_eq` then folds into a list equation);
* the `ih` segment is `denoteMeta_blockIhOpenerTy`
  (`BlockRecOpenerRead.lean`) at the opener's own `ih` level — its
  depth `nP + o + nF + r` IS `rP + nF + r`.

None of the three is quantified past its own segment, and each names
the ONE environment its reading ran at. -/

section FrameSeam

/-- **The reversed frame context, read at an ASCENDING index**: the
entry `BlockRuleCerts` names at `L - 1 - i` is the `i`-th of the
frame's own three segments in order. -/
theorem blockFrameCtx_getD {pdoms fdoms ihdoms : List AnnotTerm} {rP nF nR : Nat}
    (hp : pdoms.length = rP) (hf : fdoms.length = nF) (hidx : ihdoms.length = nR)
    {i : Nat} (hlt : i < rP + nF + nR) :
    (ihdoms.reverse ++ (pdoms ++ fdoms).reverse).getD (rP + nF + nR - 1 - i) default
      = (pdoms ++ fdoms ++ ihdoms).getD i default := by
  have hL : (pdoms ++ fdoms ++ ihdoms).length = rP + nF + nR := by
    rw [List.length_append, List.length_append, hp, hf, hidx]
  rw [← List.reverse_append, List.getD_eq_getElem?_getD,
    List.getElem?_reverse (by rw [hL]; omega), hL,
    show rP + nF + nR - 1 - (rP + nF + nR - 1 - i) = i from by omega,
    ← List.getD_eq_getElem?_getD]

/-- The frame's three segments, at an index in the FIRST. -/
theorem blockFrameCtx_left {pdoms fdoms ihdoms : List AnnotTerm} {rP : Nat}
    (hp : pdoms.length = rP) {i : Nat} (hi : i < rP) :
    (pdoms ++ fdoms ++ ihdoms).getD i default = pdoms.getD i default := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by rw [List.length_append, hp]; omega),
    List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]

/-- The frame's three segments, at an index in the SECOND. -/
theorem blockFrameCtx_mid {pdoms fdoms ihdoms : List AnnotTerm} {rP nF : Nat}
    (hp : pdoms.length = rP) (hf : fdoms.length = nF) {l : Nat} (hl : l < nF) :
    (pdoms ++ fdoms ++ ihdoms).getD (rP + l) default = fdoms.getD l default := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by rw [List.length_append, hp, hf]; omega),
    List.getElem?_append_right (by rw [hp]; omega), hp,
    show rP + l - rP = l from by omega, ← List.getD_eq_getElem?_getD]

/-- The frame's three segments, at an index in the THIRD. -/
theorem blockFrameCtx_right {pdoms fdoms ihdoms : List AnnotTerm} {rP nF : Nat}
    (hp : pdoms.length = rP) (hf : fdoms.length = nF) (l : Nat) :
    (pdoms ++ fdoms ++ ihdoms).getD (rP + nF + l) default = ihdoms.getD l default := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by rw [List.length_append, hp, hf]; omega)]
  simp only [List.length_append, hp, hf]
  rw [show rP + nF + l - (rP + nF) = l from by omega, ← List.getD_eq_getElem?_getD]

/-- **`hdoms`, FROM THE THREE SEGMENTS.**  Each opener's stored type
reads to the frame entry `BlockRuleCerts` names for it. -/
theorem blockRuleHdoms_of {envT : Env} {acval : Name → (Name → Nat) → AnnotTerm}
    {ψ : Name → Nat} {rP nF nR : Nat}
    {pdoms fdoms ihdoms : List AnnotTerm} {fvsPref fvsF fvsIh : List Expr}
    (hp : pdoms.length = rP) (hf : fdoms.length = nF) (hidx : ihdoms.length = nR)
    (hlp : fvsPref.length = rP) (hlf : fvsF.length = nF) (hli : fvsIh.length = nR)
    (hP : ∀ (l : Nat) (x : Expr), fvsPref[l]? = some x →
      denoteMeta acval envT ψ l (Expr.fvarTypeD x) = some (pdoms.getD l default))
    (hF : ∀ (l : Nat) (x : Expr), fvsF[l]? = some x →
      denoteMeta acval envT ψ (rP + l) (Expr.fvarTypeD x) = some (fdoms.getD l default))
    (hI : ∀ (l : Nat) (x : Expr), fvsIh[l]? = some x →
      denoteMeta acval envT ψ (rP + nF + l) (Expr.fvarTypeD x)
        = some (ihdoms.getD l default)) :
    ∀ (i : Nat) (x : Expr), (fvsPref ++ fvsF ++ fvsIh)[i]? = some x →
      denoteMeta acval envT ψ i (Expr.fvarTypeD x)
        = some ((ihdoms.reverse ++ (pdoms ++ fdoms).reverse).getD
            (rP + nF + nR - 1 - i) default) := by
  intro i x hx
  have hlenF : (fvsPref ++ fvsF ++ fvsIh).length = rP + nF + nR := by
    rw [List.length_append, List.length_append, hlp, hlf, hli]
  have hlt : i < rP + nF + nR := by
    have := (List.getElem?_eq_some_iff.mp hx).1
    omega
  rw [blockFrameCtx_getD hp hf hidx hlt]
  rcases Nat.lt_or_ge i rP with hi | hi
  · rw [blockFrameCtx_left hp hi]
    refine hP i x ?_
    rw [List.getElem?_append_left (by rw [List.length_append, hlp, hlf]; omega),
      List.getElem?_append_left (by omega)] at hx
    exact hx
  rcases Nat.lt_or_ge i (rP + nF) with hi2 | hi2
  · obtain ⟨l, rfl⟩ : ∃ l, i = rP + l := ⟨i - rP, by omega⟩
    rw [blockFrameCtx_mid hp hf (by omega)]
    refine hF l x ?_
    rw [List.getElem?_append_left (by rw [List.length_append, hlp, hlf]; omega),
      List.getElem?_append_right (by rw [hlp]; omega), hlp,
      show rP + l - rP = l from by omega] at hx
    exact hx
  · obtain ⟨l, rfl⟩ : ∃ l, i = rP + nF + l := ⟨i - (rP + nF), by omega⟩
    rw [blockFrameCtx_right hp hf]
    refine hI l x ?_
    rw [List.getElem?_append_right (by rw [List.length_append, hlp, hlf]; omega)] at hx
    simp only [List.length_append, hlp, hlf] at hx
    rw [show rP + nF + l - (rP + nF) = l from by omega] at hx
    exact hx

/-- **`hokΔ`, FROM THE THREE SEGMENTS.**  The frame's context is
GRADED — each entry well-denoted under the entries standing before it
— which at `Sat` is the statement `residueOk_blockFrame` consumes.

Each segment is stated in the `SpineFit`-of-its-own-prefix shape the
owners prove it in (`blockRulePdomsAV_graded`'s), and `spineFit_of_sat`
is the one bridge: a satisfying frame restricts to a fitting spine at
every prefix of the ascending context. -/
theorem blockRuleHokΔ_of {rP nF nR : Nat} {pdoms fdoms ihdoms : List AnnotTerm}
    (hp : pdoms.length = rP) (hf : fdoms.length = nF) (hidx : ihdoms.length = nR)
    (hok : ∀ l, l < rP + nF + nR → ∀ (σ : Nat → V) (ys : List V),
      SpineFit σ ((pdoms ++ fdoms ++ ihdoms).take l) ys →
      WellDenotedV V (consList ys σ) ((pdoms ++ fdoms ++ ihdoms).getD l default)) :
    ∀ i, i < rP + nF + nR →
      ∀ ρ : Nat → V, Sat V (ihdoms.reverse ++ (pdoms ++ fdoms).reverse) ρ →
        WellDenotedV V (fun j => ρ (j + (rP + nF + nR - 1 - i) + 1))
          ((ihdoms.reverse ++ (pdoms ++ fdoms).reverse).getD
            (rP + nF + nR - 1 - i) default) := by
  intro i hi ρ hsat
  have hL : (pdoms ++ fdoms ++ ihdoms).length = rP + nF + nR := by
    rw [List.length_append, List.length_append, hp, hf, hidx]
  have hcat : ihdoms.reverse ++ (pdoms ++ fdoms).reverse
      = (pdoms ++ fdoms ++ ihdoms).reverse := by rw [← List.reverse_append]
  rw [blockFrameCtx_getD hp hf hidx hi]
  rw [hcat] at hsat
  -- the frame beyond this entry satisfies the ASCENDING prefix, reversed
  have htl : (pdoms ++ fdoms ++ ihdoms).length - i = rP + nF + nR - i := by rw [hL]
  have hdropEq : ((pdoms ++ fdoms ++ ihdoms).reverse).drop (rP + nF + nR - i)
      = ((pdoms ++ fdoms ++ ihdoms).take i).reverse := by
    have hsplit : (pdoms ++ fdoms ++ ihdoms).reverse
        = ((pdoms ++ fdoms ++ ihdoms).drop i).reverse
          ++ ((pdoms ++ fdoms ++ ihdoms).take i).reverse := by
      rw [← List.reverse_append, List.take_append_drop]
    rw [hsplit,
      List.drop_append_of_le_length (by rw [List.length_reverse, List.length_drop, hL]; omega),
      List.drop_eq_nil_of_le (by rw [List.length_reverse, List.length_drop, hL]; omega),
      List.nil_append]
  have hsatT : Sat V (((pdoms ++ fdoms ++ ihdoms).take i).reverse ++ [])
      (fun j => ρ (j + (rP + nF + nR - i))) := by
    rw [List.append_nil, ← hdropEq]
    exact Sat_drop hsat (rP + nF + nR - i)
  have hys := spineFit_of_sat (V := V) hsatT
  have hti : ((pdoms ++ fdoms ++ ihdoms).take i).length = i := by
    rw [List.length_take, hL]; omega
  rw [hti] at hys
  -- the outer valuation is the one the entry's grading is stated at
  have hfun : (fun j => ρ (j + i + (rP + nF + nR - i))) = fun j => ρ (j + (rP + nF + nR)) := by
    funext j; congr 1; omega
  rw [hfun] at hys
  have hcons := consList_range_reverse (V := V) i (fun j => ρ (j + (rP + nF + nR - i)))
  rw [hfun] at hcons
  have := hok i hi (fun j => ρ (j + (rP + nF + nR))) _ hys
  rw [hcons] at this
  have hval : (fun j => ρ (j + (rP + nF + nR - 1 - i) + 1))
      = fun j => ρ (j + (rP + nF + nR - i)) := by
    funext j; congr 1; omega
  rw [hval]
  exact this

/-! ### 39.1 The bundle, from the segments

`BlockRuleCerts.of_segments` is the bundle's INTRODUCTION rule in the
spelling its producers export: the three openings and the two typing
runs come from stage (c)'s peel (`checkBlockRule_data`), the frame's
readings and grading come SEGMENT by segment (§39), and the residue's
and conclusion's own readings are the rule lane's.  Nothing here is
quantified past the rule it is about, and every semantic premise names
`envT` — the CONSTRUCTORS' environment, where the check ran — and no
other. -/

/-- **`BlockRuleCerts`, from its segments.**  What is left to own,
after this, is exactly the list of its arguments. -/
theorem BlockRuleCerts.of_segments {envT : Env} (mp : EnvModelM V μ envT)
    {ψ : Name → Nat} {fuel rP nF nR : Nat}
    {recTy crest ihTele : Expr} {fvsPref fvsF fvsIh : List Expr}
    {o₁ o₂ o₃ bodyO ty concl : Expr}
    {pdoms fdoms ihdoms : List AnnotTerm} {Rb Ca : AnnotTerm}
    (h₁ : openPisAtFvars rP recTy 0 = some (fvsPref, o₁))
    (h₂ : openPisAtFvars nF crest rP = some (fvsF, o₂))
    (h₃ : openPisAtFvars nR ihTele (rP + nF) = some (fvsIh, o₃))
    (hw₁ : Expr.WScoped 0 recTy) (hw₂ : Expr.WScoped rP crest)
    (hw₃ : Expr.WScoped (rP + nF) ihTele)
    (hlbF : ∀ x ∈ fvsPref ++ fvsF ++ fvsIh, (Expr.fvarTypeD x).looseBVarsBounded 0 = true)
    (hp : pdoms.length = rP) (hf : fdoms.length = nF) (hidx : ihdoms.length = nR)
    (hP : ∀ (l : Nat) (x : Expr), fvsPref[l]? = some x →
      denoteMeta mp.base2.acval envT ψ l (Expr.fvarTypeD x) = some (pdoms.getD l default))
    (hF : ∀ (l : Nat) (x : Expr), fvsF[l]? = some x →
      denoteMeta mp.base2.acval envT ψ (rP + l) (Expr.fvarTypeD x)
        = some (fdoms.getD l default))
    (hI : ∀ (l : Nat) (x : Expr), fvsIh[l]? = some x →
      denoteMeta mp.base2.acval envT ψ (rP + nF + l) (Expr.fvarTypeD x)
        = some (ihdoms.getD l default))
    (hokA : ∀ l, l < rP + nF + nR → ∀ (σ : Nat → V) (ys : List V),
      SpineFit σ ((pdoms ++ fdoms ++ ihdoms).take l) ys →
      WellDenotedV V (consList ys σ) ((pdoms ++ fdoms ++ ihdoms).getD l default))
    (hinf : ConLeche.inferTypeCore μ envT fuel (rP + nF + nR) bodyO = .ok ty)
    (hdeq : ConLeche.isDefEqCore μ envT fuel (rP + nF + nR) ty concl = .ok true)
    (hbR : bodyO.looseBVarsBounded 0 = true) (hbC : concl.looseBVarsBounded 0 = true)
    (hleafR : ∀ l ∈ bodyO.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF ++ fvsIh)
    (hleafC : ∀ l ∈ concl.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF ++ fvsIh)
    (hRb : denoteMeta mp.base2.acval envT ψ (rP + nF + nR) bodyO = some Rb)
    (hCa : denoteMeta mp.base2.acval envT ψ (rP + nF + nR) concl = some Ca)
    (hokC : ∀ ρ : Nat → V, Sat V (ihdoms.reverse ++ (pdoms ++ fdoms).reverse) ρ →
      WellDenotedV V ρ Ca) :
    BlockRuleCerts V mp fuel ψ rP nF nR pdoms fdoms ihdoms Rb Ca :=
  ⟨recTy, crest, ihTele, fvsPref, fvsF, fvsIh, o₁, o₂, o₃, bodyO, ty, concl,
    h₁, h₂, h₃, hw₁, hw₂, hw₃, hlbF, hp, hf, hidx,
    blockRuleHdoms_of hp hf hidx (ConLeche.Verify.openPisAtFvars_length _ h₁)
      (ConLeche.Verify.openPisAtFvars_length _ h₂)
      (ConLeche.Verify.openPisAtFvars_length _ h₃) hP hF hI,
    blockRuleHokΔ_of hp hf hidx hokA,
    hinf, hdeq, hbR, hbC, hleafR, hleafC, hRb, hCa, hokC⟩

end FrameSeam

/-! ## 40. `BlockRuleCerts`' PRODUCER — the owed arguments, at the run

§39.1 reduced the bundle to a list of named arguments; this section
owns that list.  The arguments split in three:

* the **scoping** half (`hw₂`, `hw₃`, `hlbF`, `hbR`, `hbC`, `hleafR`,
  `hleafC`, the three lengths) — plumbing over the frame's three
  openings, closed here against premises the run supplies;
* the **reading** half (`hP`, `hF`, `hI`) — the openers' stored types
  read to the frame's entries.  `hP` is §35's; `hF` and `hI` are
  closed here, and both go through `readOpenedDoms_reads` below: the
  SPELLING `readOpenedDoms` is a reading-by-construction, so a
  segment's own entries need only the readings to EXIST;
* the **grading** half (`hokA`, `hokC`), which is where the audit's
  §2.6 gap lives — see §40.5.

The generated `ih` opener tower is the one place where the CHECK
supplies nothing: `blockIhPis` builds `ihTele` and the kernel never
types it, so its two syntactic facts (`hasFvar = false`, and
`looseBVarsBounded (rP + nF)`) are premises here exactly as they are
on the opener lane (`blockRuleHopener_of`'s `hihfv`). -/

section CertsArgs

open ConLeche (openPisAtFvars)

/-! ### 40.1 The scoping arguments -/

/-- An opener is a free variable, so it is bvar-closed whatever its
annotation is (`looseBVarsBounded` does not descend into an `fvar`'s
stored type). -/
theorem openPisAtFvars_fvars_closed {k : Nat} {e : Expr} {d : Nat} {fvs : List Expr}
    {body : Expr} (hop : openPisAtFvars k e d = some (fvs, body)) :
    ∀ x ∈ fvs, x.looseBVarsBounded 0 = true := by
  intro x hx
  obtain ⟨q, hq⟩ := List.getElem?_of_mem hx
  obtain ⟨ty, rfl⟩ := ConLeche.openPisAtFvars_index _ _ _ hop q x hq
  rfl

/-- **`hw₂`** — the constructor's telescope at the rule's parameters is
scoped at the rule prefix.  The subject is a STORED constructor type
(fvar-free); the arguments are the prefix openers, which the frame's
first opening puts below `rP`. -/
theorem blockRuleHw2_of {rP nP : Nat} {recTy cty crest o₁ : Expr} {fvsPref cpref : List Expr}
    (h₁ : openPisAtFvars rP recTy 0 = some (fvsPref, o₁))
    (hw₁ : Expr.WScoped 0 recTy) (hCf : cty.hasFvar = false)
    (hinst : ConLeche.Expr.instPisAt (fvsPref.take nP) cty = some (cpref, crest)) :
    Expr.WScoped rP crest := by
  have hfv := (openPisAtFvars_WScoped rP recTy 0 h₁ hw₁).1
  rw [Nat.zero_add] at hfv
  exact (instPisAt_WScoped (d := rP) _ cty hinst (Expr.WScoped.of_not_hasFvar hCf)
    (fun a ha => hfv a (List.mem_of_mem_take ha))).2

/-- **`hw₃`** — the GENERATED `ih` tower, opened at the rule frame's
own variables, is scoped there.  The tower mentions no free variable
(it is built from stored types and de Bruijn spines), so the opening
list alone bounds it. -/
theorem blockRuleHw3_of {E : Nat} {ihTele : Expr} {L : List Expr}
    (hL : FvarList E L) (hihfv : ihTele.hasFvar = false) :
    Expr.WScoped E (ihTele.instantiateList L) :=
  wscoped_instantiateList hL ihTele hihfv 0

/-- **The generated tower, opened, is bvar-closed** — `hbR`'s and
`hlbF`'s `ih` segment.  `hihlb` is the one fact the CHECK does not
supply: `blockIhPis`' output is bounded at the rule frame's depth. -/
theorem blockRuleIhTeleClosed {rP nF : Nat} {ihTele : Expr} {L : List Expr}
    (hL : FvarList (rP + nF) L) (hLcl : ∀ x ∈ L, x.looseBVarsBounded 0 = true)
    (hihlb : ihTele.looseBVarsBounded (rP + nF) = true) (hE : 0 < rP + nF) :
    (ihTele.instantiateList L).looseBVarsBounded 0 = true := by
  rw [instantiateList_eq_instSeq_of_fvarList hL hE]
  refine looseBVarsBounded_instSeq L.reverse (rP + nF - 1)
    (fun s hs => hLcl s (List.mem_reverse.mp hs))
    (by rw [List.length_reverse, hL.1]; omega) ?_
  rw [show rP + nF - 1 + 1 = rP + nF from by omega]
  exact hihlb

/-- **`hlbF`, `hbR` and `hbC`** — the frame's openers carry bvar-closed
annotations, and the opened residue is bvar-closed, as soon as the
three SUBJECTS are (`openPisAtFvars_bounded`, three times). -/
theorem blockRuleHlbF_of {rP nF nR : Nat} {recTy crest ihTele' o₁ o₂ o₃ : Expr}
    {fvsPref fvsF fvsIh : List Expr}
    (h₁ : openPisAtFvars rP recTy 0 = some (fvsPref, o₁))
    (h₂ : openPisAtFvars nF crest rP = some (fvsF, o₂))
    (h₃ : openPisAtFvars nR ihTele' (rP + nF) = some (fvsIh, o₃))
    (hb₁ : recTy.looseBVarsBounded 0 = true) (hb₂ : crest.looseBVarsBounded 0 = true)
    (hb₃ : ihTele'.looseBVarsBounded 0 = true) :
    (∀ x ∈ fvsPref ++ fvsF ++ fvsIh, (Expr.fvarTypeD x).looseBVarsBounded 0 = true) ∧
      o₃.looseBVarsBounded 0 = true := by
  obtain ⟨-, hl₁⟩ := openPisAtFvars_bounded rP h₁ hb₁
  obtain ⟨-, hl₂⟩ := openPisAtFvars_bounded nF h₂ hb₂
  obtain ⟨hbo, hl₃⟩ := openPisAtFvars_bounded nR h₃ hb₃
  refine ⟨fun x hx => ?_, hbo⟩
  rcases List.mem_append.mp hx with hx' | hx'
  · rcases List.mem_append.mp hx' with hx'' | hx''
    · exact hl₁ x hx''
    · exact hl₂ x hx''
  · exact hl₃ x hx'

/-- **`hleafR` and `hleafC`** — every free-variable leaf of a term
built over the frame is one of the frame's openers, as soon as the
three subjects are closed (`openPisAtFvars_leaves`, three times: a
leaf of the residue is a leaf of the generated tower or an `ih`
opener, and so on outwards). -/
theorem blockRuleHleaf_of {rP nF nR : Nat} {ihTele' o₃ : Expr}
    {fvsPref fvsF fvsIh : List Expr}
    (h₃ : openPisAtFvars nR ihTele' (rP + nF) = some (fvsIh, o₃))
    (hf₃ : ∀ l ∈ ihTele'.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF) :
    ∀ l ∈ o₃.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF ++ fvsIh := by
  intro l hl
  rcases openPisAtFvars_leaves nR h₃ l (Or.inl hl) with h' | h'
  · exact List.mem_append_left _ (hf₃ l h')
  · exact List.mem_append_right _ h'

/-! ### 40.2 The reading arguments — `hF` and `hI`

`hP` is §35's (`blockRulePdomsAV_reads`).  The other two segments are
spelled with `readOpenedDoms` (`BlockRecData.lean`), which is a
reading BY CONSTRUCTION: its `l`-th entry IS the `l`-th opener's
reading whenever that reading exists at all.  So both segments reduce
to an EXISTENCE statement, which is the shape their owners already
prove — `denoteMeta_openPis`' per-binder output for the fields, and
the `ih` opener battery's `_exists` form for the openers.

`readOpenedDoms`' own equations do not leave its module (the
proof-tier `def` trap, §S20.2), so the bridge is `readOpenedDoms_eq`
at a witness list built from the readings themselves. -/

section Readings

variable {acval : Name → (Name → Nat) → AnnotTerm} {envC : Env} {ψ : Name → Nat}

omit [SetTheory V] in
/-- **A segment's entries, from the readings' EXISTENCE alone.** -/
theorem readOpenedDoms_reads {d : Nat} {fvs : List Expr}
    (hex : ∀ (l : Nat) (x : Expr), fvs[l]? = some x →
      ∃ A, denoteMeta acval envC ψ (d + l) (Expr.fvarTypeD x) = some A) :
    ∀ (l : Nat) (x : Expr), fvs[l]? = some x →
      denoteMeta acval envC ψ (d + l) (Expr.fvarTypeD x)
        = some ((readOpenedDoms acval envC ψ d fvs).getD l default) := by
  have hb : ∀ (l : Nat) (x : Expr), fvs[l]? = some x →
      ∃ pd, ((List.range fvs.length).map fun q =>
            ((0 : Nat), (0 : Nat),
              (denoteMeta acval envC ψ (d + q)
                (Expr.fvarTypeD (fvs.getD q default))).getD default))[l]? = some pd ∧
        denoteMeta acval envC ψ (d + l) (Expr.fvarTypeD x) = some pd.2.2 := by
    intro l x hx
    have hl : l < fvs.length := (List.getElem?_eq_some_iff.mp hx).1
    obtain ⟨A, hA⟩ := hex l x hx
    have hgd : fvs.getD l default = x := by rw [List.getD_eq_getElem?_getD, hx]; rfl
    refine ⟨(0, 0, (denoteMeta acval envC ψ (d + l)
      (Expr.fvarTypeD (fvs.getD l default))).getD default), ?_, ?_⟩
    · rw [List.getElem?_map, List.getElem?_range hl]
      rfl
    · rw [hgd, hA, Option.getD_some]
  have heq := readOpenedDoms_eq (acval := acval) (envC := envC) (ψ := ψ) fvs _ d
    (by rw [List.length_map, List.length_range]) hb
  intro l x hx
  obtain ⟨pd, hpd, hread⟩ := hb l x hx
  rw [heq, List.getD_eq_getElem?_getD, List.getElem?_map, hpd]
  exact hread

end Readings

/-- **`hF` generically** — the rule's FIELD openers read to
`blockRuleFdomsAV`'s entries.  `readOpenedDoms_shift` folds the same
`denoteMeta_openPis` output into a list equation; this keeps the
per-opener readings, which is what the bundle's argument is. -/
theorem readOpenedDoms_shift_reads {envC : Env} {m : EnvModel V envC} {ψ : Name → Nat}
    {crest crest' : Expr} {ds : List (Nat × Nat × AnnotTerm)} {bodyC : AnnotTerm}
    {nP nF o : Nat}
    (hread : denoteMeta m.acval envC ψ nP crest = some (mkPisAV (ds.drop nP) bodyC))
    (hw : Expr.WScoped nP crest) (hlenD : ds.length = nP + nF)
    (heq : Expr.ErasedEq crest crest')
    {fvsF : List Expr} {cbody : Expr}
    (hop : ConLeche.openPisAtFvars nF crest' (nP + o) = some (fvsF, cbody)) :
    ∀ (l : Nat) (x : Expr), fvsF[l]? = some x →
      denoteMeta m.acval envC ψ (nP + o + l) (Expr.fvarTypeD x)
        = some ((readOpenedDoms m.acval envC ψ (nP + o) fvsF).getD l default) := by
  have hread' : denoteMeta m.acval envC ψ (nP + o) crest'
      = some (mkPisAV (liftDoms o 0 (ds.drop nP)) (bodyC.liftN o nF)) := by
    rw [← denoteMeta_erasedEq heq]
    exact ctorResidual_read_lift hread hw hlenD o
  obtain ⟨pps, b, hst, hb, hlen, hbind⟩ := denoteMeta_openPis nF hop hread'
  refine readOpenedDoms_reads (fun l x hx => ?_)
  obtain ⟨q, hq, -, hd⟩ := hbind l x hx
  exact ⟨q.2.2, hd⟩

/-- **`hI`'s existence half, at the run**: every `ih` opener's STORED
type has a reading AT ITS OWN DEPTH `rP + nF + r`.

This is `blockRuleHopener_of`'s part (4) with no shift: that lemma
reads the same openers at the WALK's depth (`F + nR + d`, where the
tower lands at `ih` level `nR + d`), which is what the fit's opener
premise asks; the bundle's `hI` asks at the opener's own depth, where
`denoteMeta_blockIhOpenerTy` applies at `d := r` directly.

The keys are named by `getElem?` rather than by `pairIdxOf?` — the
premise's content depends only on the FIELD index, and the check's
key list is what the run hands over; `pairIdxOf?_getElem?` turns the
opener lane's spelling into this one. -/
theorem blockRuleIhOpenerReads_of {envT : Env} {mT : EnvModel V envT} {ψ : Name → Nat}
    {fr : ConLeche.BlockRuleFrame} {o : Nat}
    {cty : Expr} {fvs0 : List Expr} {crest : Expr}
    {tlF : Nat → List (Nat × Nat × AnnotTerm)} {EisF : Nat → List AnnotTerm}
    {recTyOf : Nat → Expr} {body ihTele bodyO : Expr}
    {fvsPref fvsF fvsIh : List Expr}
    (ho : fr.rP - fr.nP = o) (hrP : fr.nP + o = fr.rP)
    (hop0 : ConLeche.openPisAtFvars (fr.nP + fr.nF) cty 0 = some (fvs0, crest))
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hstripC : (cty.stripPis (fr.nP + fr.nF)).isSome = true)
    (htele : fr.teleOf = ConLeche.structFieldTeleOf cty fr.nP fr.nF)
    (hfld : ∀ i c' r : Nat, fr.ihKeys[r]? = some (i, c') →
      i < fr.nF ∧ FieldReadAt mT ψ fr.nP fr.nF i cty fvs0 (tlF i) (EisF i))
    (hpis : ConLeche.blockIhPis fr.nP fr.rP fr.nF fr.pw recTyOf fr.teleOf fr.idxOf
      fr.ihKeys 0 body = some ihTele)
    (hihfv : ihTele.hasFvar = false)
    (hLpf : FvarList (fr.rP + fr.nF) (fvsPref ++ fvsF).reverse)
    (hopen : ConLeche.openPisAtFvars fr.ihKeys.length
      (ihTele.instantiateList (fvsPref ++ fvsF).reverse) (fr.rP + fr.nF) = some (fvsIh, bodyO))
    (hconcl : ∀ (i c' r : Nat) (concl : Expr) (as1 : List Expr),
      fr.ihKeys[r]? = some (i, c') →
      Expr.instPisAtLift
          (ConLeche.blockRulePrefixVars fr.rP fr.nF (r + (fr.teleOf i).length) ++
            (fr.idxOf i).map (ConLeche.structIdxAt fr.nF o i r (fr.teleOf i).length) ++
            [Expr.mkAppN (.bvar (fr.nF - 1 - i + r + (fr.teleOf i).length))
              (ConLeche.structTeleVars (fr.teleOf i).length)])
          (recTyOf c') = some concl →
      FvarList (fr.nP + o + fr.nF + r) as1 →
      ∃ conclA, denoteMeta mT.acval envT ψ
          (fr.nP + o + fr.nF + r + (ConLeche.structFieldTeleOf cty fr.nP fr.nF i).length)
          (concl.instantiateList ((openFvars (fr.nP + o + fr.nF + r)
            (ConLeche.structFieldTeleOf cty fr.nP fr.nF i).length).reverse ++ as1) 0)
        = some conclA) :
    ∀ (r : Nat) (x : Expr), fvsIh[r]? = some x →
      ∃ A, denoteMeta mT.acval envT ψ (fr.rP + fr.nF + r) (Expr.fvarTypeD x) = some A := by
  intro r x hx
  have hrlt : r < fvsIh.length := (List.getElem?_eq_some_iff.mp hx).1
  have hIhlen : fvsIh.length = fr.ihKeys.length := openPisAtFvars_length _ hopen
  obtain ⟨key, hkey⟩ : ∃ k, fr.ihKeys[r]? = some k :=
    ⟨fr.ihKeys[r]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨i, c'⟩ := key
  obtain ⟨hiF, hfr⟩ := hfld i c' r hkey
  obtain ⟨concl, hconclRun, hstored, hFv1⟩ :=
    blockIhOpener_stored hpis hLpf hihfv hopen hkey hx
  rw [ho] at hconclRun hstored
  rw [show fr.rP + fr.nF + r = fr.nP + o + fr.nF + r from by omega] at hFv1
  obtain ⟨B, hB⟩ := denoteMeta_blockIhOpenerTy_exists (pw := fr.pw) hop0 hCf hCb hstripC hiF hfr
    hFv1 (hconcl i c' r concl _ hkey hconclRun hFv1)
  refine ⟨mkPisAV (ihTeleAtR fr.nF o i r (rebit (pwBit ψ fr.pw) (tlF i))) B, ?_⟩
  rw [show fr.rP + fr.nF + r = fr.nP + o + fr.nF + r from by omega, hstored, htele]
  exact hB

/-! ### 40.3 The bundle, from the frame's three openings

`BlockRuleCerts.of_segments` (§39.1) takes the bundle's arguments in
the producers' spelling; this is the same bundle at the spelling the
RUN hands over — the three opener LISTS — with every syntactic
argument discharged by §40.1 and the two owed segment readings
discharged by §40.2 from their existence alone.

What is left as a premise here is exactly what the check does not
supply: the frame's GRADING (`hokA`) and the conclusion's
well-denotedness (`hokC`), which are the audit's §2.6 item, plus the
two runs and the two term readings, which are stage (c)'s own. -/

omit [SetTheory V] in
/-- A segment's length is its opener list's, whenever the readings
exist (the same witness list as `readOpenedDoms_reads`). -/
theorem readOpenedDoms_length {acval : Name → (Name → Nat) → AnnotTerm} {envC : Env}
    {ψ : Name → Nat} {d : Nat} {fvs : List Expr}
    (hex : ∀ (l : Nat) (x : Expr), fvs[l]? = some x →
      ∃ A, denoteMeta acval envC ψ (d + l) (Expr.fvarTypeD x) = some A) :
    (readOpenedDoms acval envC ψ d fvs).length = fvs.length := by
  have hb : ∀ (l : Nat) (x : Expr), fvs[l]? = some x →
      ∃ pd, ((List.range fvs.length).map fun q =>
            ((0 : Nat), (0 : Nat),
              (denoteMeta acval envC ψ (d + q)
                (Expr.fvarTypeD (fvs.getD q default))).getD default))[l]? = some pd ∧
        denoteMeta acval envC ψ (d + l) (Expr.fvarTypeD x) = some pd.2.2 := by
    intro l x hx
    have hl : l < fvs.length := (List.getElem?_eq_some_iff.mp hx).1
    obtain ⟨A, hA⟩ := hex l x hx
    have hgd : fvs.getD l default = x := by rw [List.getD_eq_getElem?_getD, hx]; rfl
    refine ⟨(0, 0, (denoteMeta acval envC ψ (d + l)
      (Expr.fvarTypeD (fvs.getD l default))).getD default), ?_, ?_⟩
    · rw [List.getElem?_map, List.getElem?_range hl]
      rfl
    · rw [hgd, hA, Option.getD_some]
  rw [readOpenedDoms_eq (acval := acval) (envC := envC) (ψ := ψ) fvs _ d
    (by rw [List.length_map, List.length_range]) hb, List.length_map, List.length_map,
    List.length_range]

/-- **`BlockRuleCerts` from the frame's openings.**  The bundle's
domains are the openers' own readings (`readOpenedDoms`), so the
producer owes, per segment, only that those readings EXIST. -/
theorem blockRuleCerts_of_openings {envT : Env} (mp : EnvModelM V μ envT)
    {ψ : Name → Nat} {fuel rP nF nR : Nat}
    {recTy crest ihTele' : Expr} {fvsPref fvsF fvsIh : List Expr}
    {o₁ o₂ bodyO ty concl : Expr} {Rb Ca : AnnotTerm}
    (h₁ : ConLeche.openPisAtFvars rP recTy 0 = some (fvsPref, o₁))
    (h₂ : ConLeche.openPisAtFvars nF crest rP = some (fvsF, o₂))
    (h₃ : ConLeche.openPisAtFvars nR ihTele' (rP + nF) = some (fvsIh, bodyO))
    (hw₁ : Expr.WScoped 0 recTy) (hw₂ : Expr.WScoped rP crest)
    (hw₃ : Expr.WScoped (rP + nF) ihTele')
    (hb₁ : recTy.looseBVarsBounded 0 = true) (hb₂ : crest.looseBVarsBounded 0 = true)
    (hb₃ : ihTele'.looseBVarsBounded 0 = true)
    (hfv₃ : ∀ l ∈ ihTele'.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF)
    (hexP : ∀ (l : Nat) (x : Expr), fvsPref[l]? = some x →
      ∃ A, denoteMeta mp.base2.acval envT ψ (0 + l) (Expr.fvarTypeD x) = some A)
    (hexF : ∀ (l : Nat) (x : Expr), fvsF[l]? = some x →
      ∃ A, denoteMeta mp.base2.acval envT ψ (rP + l) (Expr.fvarTypeD x) = some A)
    (hexI : ∀ (l : Nat) (x : Expr), fvsIh[l]? = some x →
      ∃ A, denoteMeta mp.base2.acval envT ψ (rP + nF + l) (Expr.fvarTypeD x) = some A)
    (hinf : ConLeche.inferTypeCore μ envT fuel (rP + nF + nR) bodyO = .ok ty)
    (hdeq : ConLeche.isDefEqCore μ envT fuel (rP + nF + nR) ty concl = .ok true)
    (hbC : concl.looseBVarsBounded 0 = true)
    (hleafC : ∀ l ∈ concl.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF ++ fvsIh)
    (hRb : denoteMeta mp.base2.acval envT ψ (rP + nF + nR) bodyO = some Rb)
    (hCa : denoteMeta mp.base2.acval envT ψ (rP + nF + nR) concl = some Ca)
    (hokA : ∀ l, l < rP + nF + nR → ∀ (σ : Nat → V) (ys : List V),
      SpineFit σ ((readOpenedDoms mp.base2.acval envT ψ 0 fvsPref
        ++ readOpenedDoms mp.base2.acval envT ψ rP fvsF
        ++ readOpenedDoms mp.base2.acval envT ψ (rP + nF) fvsIh).take l) ys →
      WellDenotedV V (consList ys σ)
        ((readOpenedDoms mp.base2.acval envT ψ 0 fvsPref
          ++ readOpenedDoms mp.base2.acval envT ψ rP fvsF
          ++ readOpenedDoms mp.base2.acval envT ψ (rP + nF) fvsIh).getD l default))
    (hokC : ∀ ρ : Nat → V,
      Sat V ((readOpenedDoms mp.base2.acval envT ψ (rP + nF) fvsIh).reverse
        ++ (readOpenedDoms mp.base2.acval envT ψ 0 fvsPref
          ++ readOpenedDoms mp.base2.acval envT ψ rP fvsF).reverse) ρ →
      WellDenotedV V ρ Ca) :
    BlockRuleCerts V mp fuel ψ rP nF nR
      (readOpenedDoms mp.base2.acval envT ψ 0 fvsPref)
      (readOpenedDoms mp.base2.acval envT ψ rP fvsF)
      (readOpenedDoms mp.base2.acval envT ψ (rP + nF) fvsIh) Rb Ca := by
  obtain ⟨hlbF, hbR⟩ := blockRuleHlbF_of h₁ h₂ h₃ hb₁ hb₂ hb₃
  refine BlockRuleCerts.of_segments mp h₁ h₂ h₃ hw₁ hw₂ hw₃ hlbF
    (by rw [readOpenedDoms_length hexP, ConLeche.Verify.openPisAtFvars_length _ h₁])
    (by rw [readOpenedDoms_length hexF, ConLeche.Verify.openPisAtFvars_length _ h₂])
    (by rw [readOpenedDoms_length hexI, ConLeche.Verify.openPisAtFvars_length _ h₃])
    (fun l x hx => ?_) (fun l x hx => readOpenedDoms_reads hexF l x hx)
    (fun l x hx => readOpenedDoms_reads hexI l x hx)
    hokA hinf hdeq hbR hbC (blockRuleHleaf_of h₃ hfv₃) hleafC hRb hCa hokC
  have := readOpenedDoms_reads hexP l x hx
  rwa [Nat.zero_add] at this

/-! ### 40.4 `hokA`, segment by segment

`hokA` is stated at the ASCENDING frame, so its three segments are a
`take` split and nothing else — but the split must be taken on the
ascending side (§S20.7's finding: a `take`-shaped reading of the
REVERSED context lands on the wrong valuation).  Each segment is
stated at its own frame: the prefix at the bare `σ`, the fields under
the prefix's values, the `ih` openers under both — which is the shape
each owner proves its grading in, and the only shape in which the
premise is bounded by the fact that produces it. -/

/-- **`hokA` from the three segments.** -/
theorem blockRuleHokA_of_segments {P F I : List AnnotTerm} {rP nF nR : Nat}
    (hp : P.length = rP) (hf : F.length = nF) (_hidx : I.length = nR)
    (hPseg : ∀ l, l < rP → ∀ (σ : Nat → V) (ys : List V),
      SpineFit σ (P.take l) ys → WellDenotedV V (consList ys σ) (P.getD l default))
    (hFseg : ∀ q, q < nF → ∀ (σ : Nat → V) (xs ys : List V),
      SpineFit σ P xs → SpineFit (consList xs σ) (F.take q) ys →
      WellDenotedV V (consList ys (consList xs σ)) (F.getD q default))
    (hIseg : ∀ q, q < nR → ∀ (σ : Nat → V) (xs fs ys : List V),
      SpineFit σ P xs → SpineFit (consList xs σ) F fs →
      SpineFit (consList fs (consList xs σ)) (I.take q) ys →
      WellDenotedV V (consList ys (consList fs (consList xs σ))) (I.getD q default)) :
    ∀ l, l < rP + nF + nR → ∀ (σ : Nat → V) (ys : List V),
      SpineFit σ ((P ++ F ++ I).take l) ys →
      WellDenotedV V (consList ys σ) ((P ++ F ++ I).getD l default) := by
  intro l hl σ ys hys
  rcases Nat.lt_or_ge l rP with hlP | hlP
  · -- the PREFIX segment
    have htk : (P ++ F ++ I).take l = P.take l := by
      rw [List.take_append_of_le_length (by rw [List.length_append, hp]; omega),
        List.take_append_of_le_length (by rw [hp]; omega)]
    have hgd : (P ++ F ++ I).getD l default = P.getD l default := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [List.length_append, hp]; omega),
        List.getElem?_append_left (by rw [hp]; omega)]
    rw [hgd]
    exact hPseg l hlP σ ys (by rw [← htk]; exact hys)
  rcases Nat.lt_or_ge l (rP + nF) with hlF | hlF
  · -- the FIELD segment
    have htk : (P ++ F ++ I).take l = P ++ F.take (l - rP) := by
      rw [List.take_append_of_le_length (by rw [List.length_append, hp, hf]; omega),
        List.take_append, List.take_of_length_le (by rw [hp]; omega), hp]
    rw [htk] at hys
    obtain ⟨xs, zs, rfl, hxs, hzs⟩ := spineFit_append_inv hys
    have hgd : (P ++ F ++ I).getD l default = F.getD (l - rP) default := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [List.length_append, hp, hf]; omega),
        List.getElem?_append_right (by rw [hp]; omega), hp]
    rw [hgd, consList_append]
    exact hFseg (l - rP) (by omega) σ xs zs hxs hzs
  · -- the `ih` segment
    have htk : (P ++ F ++ I).take l = P ++ F ++ I.take (l - (rP + nF)) := by
      rw [List.take_append,
        List.take_of_length_le (by rw [List.length_append, hp, hf]; omega),
        List.length_append, hp, hf,
        show l - (rP + nF) = l - (rP + nF) from rfl]
    rw [htk] at hys
    obtain ⟨xfs, zs, rfl, hxfs, hzs⟩ := spineFit_append_inv hys
    obtain ⟨xs, fs, rfl, hxs, hfs⟩ := spineFit_append_inv hxfs
    have hgd : (P ++ F ++ I).getD l default = I.getD (l - (rP + nF)) default := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by rw [List.length_append, hp, hf]; omega),
        List.length_append, hp, hf]
    rw [consList_append] at hzs
    rw [hgd, consList_append, consList_append]
    exact hIseg (l - (rP + nF)) (by omega) σ xs fs zs hxs hfs hzs

/-! ### 40.5 The prefix segment, at the run's spelling

`blockRuleCerts_of_openings` states the bundle's domains as the
openers' own readings; §35's `blockRulePdomsAV` is the same list read
off O-2's binder data.  The identification is `readOpenedDoms_eq` at
that data, and it is what lets the bundle's consumers keep the
spelling they already use (`blockRecHpref_run`, `BlockRuleDataAt`). -/

theorem blockRulePdomsAV_eq_readOpenedDoms {envC : Env} {p : ConLeche.BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {i : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[i]? = some r) (ψ : Name → Nat) {fvs : List Expr} {o : Expr}
    (hop : ConLeche.openPisAtFvars (p.toBlockShape.rulePrefixAt i) r.1.type 0 = some (fvs, o)) :
    readOpenedDoms mpC.base2.acval envC ψ 0 fvs
      = blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ i := by
  have hlfvs : fvs.length = p.toBlockShape.rulePrefixAt i :=
    ConLeche.Verify.openPisAtFvars_length _ hop
  have hle := blockRecHrPle (p := p) h (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨-, -, -, -, -, hlenRds, -, -, -, -⟩ := checkBlockRecK_tyPis hμ mpC h hr ψ
  have hreads := blockRulePdomsAV_reads hμ mpC h hr ψ hop
  have hlenTake : ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ i).take
      (p.toBlockShape.rulePrefixAt i)).length = p.toBlockShape.rulePrefixAt i := by
    rw [List.length_take, hlenRds]; omega
  rw [readOpenedDoms_eq (acval := mpC.base2.acval) (envC := envC) (ψ := ψ) fvs
    ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ i).take
      (p.toBlockShape.rulePrefixAt i)) 0 (by rw [hlfvs, hlenTake]) ?_]
  · rfl
  · intro l x hx
    have hl : l < p.toBlockShape.rulePrefixAt i := by
      have := (List.getElem?_eq_some_iff.mp hx).1; omega
    obtain ⟨pd, hpd⟩ : ∃ pd, ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ i).take
        (p.toBlockShape.rulePrefixAt i))[l]? = some pd :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlenTake]; exact hl)⟩
    refine ⟨pd, hpd, ?_⟩
    rw [Nat.zero_add, hreads l x hx, blockRulePdomsAV, List.getD_eq_getElem?_getD,
      List.getElem?_map, hpd]
    rfl

/-! ### 40.6 The CONCLUSION's two scoping arguments

`hbC` and `hleafC` are about the term the rule's residue is compared
against — the recursor's stored type instantiated at the rule's
prefix openers, the constructor's result index arguments and the
fired major.  Every one of those arguments is built from the frame's
openers over two STORED (fvar-free) types, so both arguments come off
`instPisAt`'s two batteries once the spine's entries are known to be
bvar-closed. -/

/-- **`hbC` and `hleafC`, from the run's own conclusion equation.** -/
theorem blockRuleConclClosed_of {nP rP nF : Nat}
    {recTy cty crest cbody o₁ concl : Expr} {fvsPref fvsF cpref : List Expr}
    {cname : Name} {lvls : List Level}
    (h₁ : ConLeche.openPisAtFvars rP recTy 0 = some (fvsPref, o₁))
    (h₂ : ConLeche.openPisAtFvars nF crest rP = some (fvsF, cbody))
    (hf₁ : recTy.hasFvar = false) (hCf : cty.hasFvar = false)
    (hb₁ : recTy.looseBVarsBounded 0 = true) (hb₂ : crest.looseBVarsBounded 0 = true)
    (hinstC : ConLeche.Expr.instPisAt (fvsPref.take nP) cty = some (cpref, crest))
    (hpr : ConLeche.Expr.instPisAtLift
        (fvsPref ++ cbody.getAppArgs.drop nP
          ++ [Expr.mkAppN (.const cname lvls) (fvsPref.take nP ++ fvsF)]) recTy = some concl) :
    concl.looseBVarsBounded 0 = true ∧
      ∀ l ∈ concl.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF := by
  have hrecNil : recTy.fvarLeaves = [] := ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hf₁
  have hctyNil : cty.fvarLeaves = [] := ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hCf
  have hcb : cbody.looseBVarsBounded 0 = true := (openPisAtFvars_bounded nF h₂ hb₂).1
  -- an opener's own leaves are openers
  have hlP : ∀ a ∈ fvsPref, ∀ l ∈ a.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref := by
    intro a ha l hl
    rcases openPisAtFvars_leaves rP h₁ l (Or.inr ⟨a, ha, hl⟩) with h' | h'
    · rw [hrecNil] at h'; exact nomatch h'
    · exact h'
  have hcrestLeaf : ∀ l ∈ crest.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref := by
    intro l hl
    rcases ConLeche.instPisAt_fvarLeaves _ cty hinstC l hl with h' | ⟨a, ha, hla⟩
    · rw [hctyNil] at h'; exact nomatch h'
    · exact hlP a (List.mem_of_mem_take ha) l hla
  have hlF : ∀ a ∈ fvsF, ∀ l ∈ a.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF := by
    intro a ha l hl
    rcases openPisAtFvars_leaves nF h₂ l (Or.inr ⟨a, ha, hl⟩) with h' | h'
    · exact List.mem_append_left _ (hcrestLeaf l h')
    · exact List.mem_append_right _ h'
  have hcbLeaf : ∀ l ∈ cbody.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF := by
    intro l hl
    rcases openPisAtFvars_leaves nF h₂ l (Or.inl hl) with h' | h'
    · exact List.mem_append_left _ (hcrestLeaf l h')
    · exact List.mem_append_right _ h'
  -- the spine's entries are bvar-closed
  have hargs : ∀ a ∈ fvsPref ++ cbody.getAppArgs.drop nP
      ++ [Expr.mkAppN (.const cname lvls) (fvsPref.take nP ++ fvsF)],
      a.looseBVarsBounded 0 = true := by
    intro a ha
    rcases List.mem_append.mp ha with ha' | ha'
    · rcases List.mem_append.mp ha' with ha'' | ha''
      · exact openPisAtFvars_fvars_closed h₁ a ha''
      · exact ConLeche.looseBVarsBounded_getAppArgs hcb a (List.mem_of_mem_drop ha'')
    · rw [List.mem_singleton] at ha'
      subst ha'
      refine ConLeche.looseBVarsBounded_mkAppN rfl (fun x hx => ?_)
      rcases List.mem_append.mp hx with hx' | hx'
      · exact openPisAtFvars_fvars_closed h₁ x (List.mem_of_mem_take hx')
      · exact openPisAtFvars_fvars_closed h₂ x hx'
  -- the lift IS the plain instantiation at those arguments
  rw [ConLeche.instPisAtLift_eq_instPisAt hargs, Option.map_eq_some_iff] at hpr
  obtain ⟨pr, hinst, rfl⟩ := hpr
  obtain ⟨ds, res⟩ := pr
  refine ⟨ConLeche.instPisAt_looseBVars _ recTy hinst hb₁ hargs, fun l hl => ?_⟩
  rcases ConLeche.instPisAt_fvarLeaves _ recTy hinst l hl with h' | ⟨a, ha, hla⟩
  · rw [hrecNil] at h'; exact nomatch h'
  rcases List.mem_append.mp ha with ha' | ha'
  · rcases List.mem_append.mp ha' with ha'' | ha''
    · exact List.mem_append_left _ (hlP a ha'' l hla)
    · exact hcbLeaf l (ConLeche.fvarLeaves_getAppArgs (List.mem_of_mem_drop ha'') l hla)
  · rw [List.mem_singleton] at ha'
    subst ha'
    rcases ConLeche.fvarLeaves_mkAppN hla with h' | ⟨x, hx, hlx⟩
    · simp [Expr.fvarLeaves] at h'
    rcases List.mem_append.mp hx with hx' | hx'
    · exact List.mem_append_left _ (hlP x (List.mem_of_mem_take hx') l hlx)
    · exact hlF x hx' l hlx

end CertsArgs

end ConLeche.Model

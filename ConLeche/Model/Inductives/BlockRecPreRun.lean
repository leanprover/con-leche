module

import ConLeche.Verify.Inductives.RecStage
import ConLeche.Model.Inductives.BlockRecTyping
public import ConLeche.Semantics.Tower.BlockRecGraphI
import ConLeche.Model.Annot.BitInst
import ConLeche.Verify.Inductives.BlockRecInv
import ConLeche.Model.Inductives.BlockRecRead
public import ConLeche.Model.Inductives.BlockRecData

public section

/-!
# The recursor model's run-level library

`blockRecPre_graph` (`Model/Inductives/BlockRecGraph.lean`) produces the
recursor stage's semantic seam

```
hpre : ∀ ψ ρ, BlockRecPre V s K (blockRecTyAV mpC.base2.acval envC rs ψ) (eqs ψ) ρ
```

from the graph kit.  This file holds what that producer reads at the
run, in the order it composes:

* **§1 the rule's certificates, bundled** (`BlockRuleCerts`): every
  run-level argument of `residueOk_blockFrame` (`BlockRecTyping.lean`)
  except the frame, so the kit's typing obligation consumes ONE
  hypothesis per rule and instantiates it at its own decoding;
* **§2 the carrier's case analysis** (`blockCarrier_case`,
  `blockCarrier_case_unique` — `mkInj`, one arm of the kit's `huniq`);
* **§3 the classes at a prefix spine** (`blockRecIs`, `blockRecCr`,
  `blockRec_hsplit`): the class's index set is the member's index-tuple
  set and its carrier the least pre-fixed tuple's component, i.e. the
  member's former at the prefix frame (`BlockModelAt.leaf`);
* **§4 `OneElimLevel` from the check** (`blockRecOneElimLevel`);
* **§9 the bound** (`blockRecMot`, `blockRec_hconcl`);
* **§20 onward**: the rule data's components at the run's spelling,
  the `ih` values and terms, the certified hop, the certificates'
  producer and the ι equations' grading.
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

The bundle is the rule stage's typing output plus the two frame
premises (`hdoms`, `hokΔ`: the openers' stored types read to the
context's entries, and the context is graded).

Its second argument is the checker's FUEL, not a frame depth: elsewhere
the letter `F` names the rule frame's depth, so the binder is `fuel`
here and the two cannot be confused where both meet. -/

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
    (∀ x ∈ fvsPref ++ fvsF ++ fvsIh, ConstsBound envT x) ∧
    (∀ x ∈ fvsPref ++ fvsF ++ fvsIh, ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF ++ fvsIh) ∧
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
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h₁, h₂, h₃, hw₁, hw₂, hw₃, hlbF, _, _,
    hp, hf, hidx, hdoms, hokΔ, hinf, hdeq, hbR, hbC, hleafR, hleafC, hRb, hCa, hokC⟩ := h
  exact residueOk_blockFrame hμ mp h₁ h₂ h₃ hw₁ hw₂ hw₃ hlbF hp hf hidx hdoms hokΔ
    hinf hdeq hbR hbC hleafR hleafC hRb hCa hokC hsp hih

/-! ## 2. The carrier's case analysis

An element of a component's carrier is the injection of the
constructor that built it.  `BlockModelAt.fibre` says that at the
OPERATOR: component `c`'s fibre of `Φ X` at `t` consists exactly of
the injections of the spines fitting one of `c`'s constructors.  The
carrier is the least pre-fixed TUPLE, and the fixed-point equation
(`app_lfpTuple_eq`, off the clause's own `functor`) moves the
statement onto it.

At a `Type`-valued block (`w ψ ≠ 0`) the decomposition is UNIQUE
(`mkInj`) — the graph kit's `huniq` above `Prop`
(`blockGraphUniq_run`). -/

/-- A fitting field spine is as long as the constructor's field
list. -/
theorem BlockData.StoredFit.length_eq {d : BlockData V} {ψ : Name → Nat} {ρp : Nat → V}
    {t : V} {c j : Nat} {fs : List V} (h : d.StoredFit ψ ρp t c j fs) :
    fs.length = ((d.Fss c ψ).getD j []).length :=
  h.2.1.length_eq

/-- **The carrier's case analysis**: an element of component `c`'s
carrier at the index tuple `t` is the injection of a spine fitting one
of `c`'s constructors AS STORED at `t`.  `BlockModelAt.fibre` through
the fixed-point equation gives the hole fit at the carrier, which is
the stored fit (`BlockModelAt.carrier`, the override law). -/
theorem blockCarrier_case {env : Env} {mo : EnvModel V env} {names : List Name}
    {d : BlockData V} (hM : BlockModelAt mo names d) {ψ : Name → Nat} {ρp : Nat → V}
    (hsat : Sat V (d.params ψ).reverse ρp) {c : Nat} (hc : c < d.N) {t : V}
    (ht : t ∈ˢ d.idx ψ ρp c) {x : V}
    (hx : x ∈ˢ app (lfpTuple (d.w ψ) d.N (d.idx ψ ρp) (d.Φ ψ ρp) c) t) :
    ∃ j fs, d.StoredFit ψ ρp t c j fs ∧ x = d.inj ψ c j fs := by
  obtain ⟨hmono, hmaps, hcl⟩ := hM.functor ψ ρp hsat
  rw [← app_lfpTuple_eq hcl hmono hmaps hc ht] at hx
  obtain ⟨j, fs, hf, rfl⟩ := (hM.fibre ψ ρp hsat _ (lfpTuple_mem _ _ _ _) c hc t ht x).mp hx
  exact ⟨j, fs, (hM.carrier ψ ρp hsat c hc t ht j fs).mp hf, rfl⟩

/-- **The decomposition is unique** at a `Type`-valued block: two
fitting spines of the same component with the same injection are the
same constructor and the same spine (`mkInj`, whose length side
conditions are the stored fit's own). -/
theorem blockCarrier_case_unique {env : Env} {mo : EnvModel V env} {names : List Name}
    {d : BlockData V} (hM : BlockModelAt mo names d) {ψ : Name → Nat} {ρp : Nat → V}
    (hw : d.w ψ ≠ 0) {c : Nat} (hc : c < d.N) {t : V} {j j' : Nat} {fs fs' : List V}
    (hfit : d.StoredFit ψ ρp t c j fs) (hfit' : d.StoredFit ψ ρp t c j' fs')
    (heq : d.inj ψ c j fs = d.inj ψ c j' fs') : j = j' ∧ fs = fs' :=
  hM.mkInj ψ hw c hc j fs j' fs' hfit.1 hfit'.1 hfit.length_eq hfit'.length_eq heq

/-! ## 3. The recursor classes at the block's own carriers

`GraphFamData` (`Semantics/Tower/BlockRecGraphI.lean`) asks, per PREFIX
SPINE, for the classes' index sets and ORDINARY carriers, the index
tuple, a graph kit, and the two readings the recursors' TYPES fix.
For a block the first three are not a choice:

* the prefix spine's first `nP` values ARE the block's parameters (the
  recursor's rule prefix begins with them, `checkBlockRecTys`), so the
  parameter frame is `consList (xs.take nP) ρ`;
* class `c` eliminates the member `mem c`, so its index set is that
  component's index-tuple set and its carrier the least pre-fixed
  tuple's component — which is the member's FORMER at the parameter
  frame, by `BlockModelAt.leaf`.

That last identification is the whole content of `blockRec_hsplit`: the
major's binder domain is the member's former applied, the clause's
`leaf` turns the fold into `app (lfpTuple …) ⟨ı⃗⟩`, and the index
tuple lands in the index set by `tupW_mem`. -/

section ClassData

variable {env : Env} {mo : EnvModel V env} {names : List Name} {d : BlockData V}

/-- Class `c`'s index set at a prefix spine: the eliminated
component's own index-tuple set, at the parameter frame — and EMPTY
at a prefix that does not FIT: the kit is total over prefix spines,
and at a spine that fits nothing the class carriers are empty and
every obligation is vacuous.

**The guard is the WHOLE rule prefix, not only its parameters**: the
kit's step instantiates the rule's certificates at
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

/-- **The reading facts about a recursor's binder data**: a fitting spine
of `rec_c`'s type is the rule prefix, the eliminated member's indices
and the major; the prefix begins with the block's parameters; the
index values fit the member's own index telescope there; and the
major lies in the member's former applied to both.  Every conjunct is
a statement about the STORED type's reading, none about the
recursion. -/
@[expose] def BlockRecSplitOne (V : Type w) [SetTheory V] {env : Env} (mo : EnvModel V env)
    (d : BlockData V) (ψ : Name → Nat) (rP mem : Nat → Nat)
    (rds : Nat → List (Nat × Nat × AnnotTerm)) (ρ : Nat → V) (c : Nat) : Prop :=
  ∀ ys : List V, SpineFit ρ ((rds c).map (·.2.2)) ys →
    (prefOf (rP c) ys).length = rP c ∧
    ys = prefOf (rP c) ys ++ (idxOf (rP c) ys ++ [majOf ys]) ∧
    SpineFit ρ (d.params ψ) ((prefOf (rP c) ys).take d.nP) ∧
    SpineFit (consList ((prefOf (rP c) ys).take d.nP) ρ) (d.IdsM (mem c) ψ)
      (idxOf (rP c) ys) ∧
    majOf ys ∈ˢ ((prefOf (rP c) ys).take d.nP ++ idxOf (rP c) ys).foldl app
      (interp V ρ (mo.acval (d.memberName (mem c)) ψ))


/-- **`GraphFamData.hsplit` at ONE member class** (lane NESTIND). -/
theorem blockRec_hsplit_at (hM : BlockModelAt mo names d) {ψ : Name → Nat} {ρ : Nat → V}
    {rP mem : Nat → Nat} {rds : Nat → List (Nat × Nat × AnnotTerm)}
    {pdoms : Nat → List AnnotTerm} {c : Nat}
    (hpdE : pdoms c = ((rds c).map (·.2.2)).take (rP c))
    (hmem : mem c < d.k)
    (hsplit : BlockRecSplitOne V mo d ψ rP mem rds ρ c) :
    ∀ ys, SpineFit ρ ((rds c).map (·.2.2)) ys →
      (prefOf (rP c) ys).length = rP c ∧
      ys = prefOf (rP c) ys ++ (idxOf (rP c) ys ++ [majOf ys]) ∧
      d.tup ψ (mem c) (idxOf (rP c) ys) ∈ˢ blockRecIs d ψ ρ pdoms mem (prefOf (rP c) ys) c ∧
      majOf ys ∈ˢ app (blockRecCr d ψ ρ mem (prefOf (rP c) ys) c)
        (d.tup ψ (mem c) (idxOf (rP c) ys)) := by
  intro ys hfit
  obtain ⟨hlen, hdec, hpar, hidx, hmaj⟩ := hsplit ys hfit
  have hpref : SpineFit ρ (pdoms c) (prefOf (rP c) ys) := by
    rw [hpdE]
    exact spineFit_take_any hfit _
  rw [blockRecIs_pos hpar hpref]
  refine ⟨hlen, hdec, tupW_mem hidx, ?_⟩
  rw [blockRecCr, ← hM.leaf (mem c) hmem ψ ρ ((prefOf (rP c) ys).take d.nP)
    (idxOf (rP c) ys) hpar hidx]
  exact hmaj


end ClassData

/-! ## 4. `OneElimLevel` from the check

D-d — one elimination level per family — follows from the
elimination-level PIN (`checkBlockRecElimPin`: every conclusion sort is
equivalent to the generated `structElimLevel p.elim p.large`), and
`blockRecElimPin_run` (§38.1) turns it into equalities of
`Level.eval` at a ground assignment.  What the candidate's λ-tower
needs (`famCandG_hCand`'s `hbits`) is the ZERONESS bit of every binder
of every class's binder data, and that is the same bit once each
class's binder numerals follow its own conclusion's sort — the
reading's fact, taken here as `hbits`. -/

/-- **D-d, in the shape the candidate consumes**: at the family's
single level `ℓ` — every recursor's own level evaluates to it (the
pin, `blockRecElimPin_run`) — every binder numeral of every class's
binder data is zero exactly when `ℓ` is. -/
theorem blockRecOneElimLevel {ℓ : Nat} (ψ : Name → Nat) {K : Nat}
    {rds : Nat → List (Nat × Nat × AnnotTerm)} {uOf : Nat → Level}
    (hpin : ∀ c, c < K → (uOf c).eval ψ = ℓ)
    (hbits : ∀ c, c < K → ∀ b ∈ rds c, (b.2.1 = 0 ↔ (uOf c).eval ψ = 0)) :
    OneElimLevel ℓ K rds :=
  fun c hc b hb => by rw [hbits c hc b hb, hpin c hc]

/-! ## 6. The rule count -/

/-- **The `c`-th recursor's RULE COUNT** — the `nCt` every regime is
stated at: what `sumRules` enumerates. -/
@[expose] def blockRecNCt
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))) (c : Nat) : Nat :=
  (rs.getD c default).2.2.2.length

/-! ## 7.–8. `BlockModelAt` from the stages' three records

Moved to `BlockModelRecords.lean` (lane ENVLFP): the install records
the block's lfp clause at its constructors' environment, upstream of
this file (`blockModelAt_of_records`). -/

/-! ## 9. The WF kit's MOTIVE

The kit's bound `B` is a function of the TAGGED element alone, so the motive
must recover the spine the conclusion is read at: the class, the index
tuple and the major.  `tagged` is injective (`tagged_inj`), so below
`K` the decoding is unique and `tagDec` is it as a function; the index
SPINE comes back out of its tuple by `isOfW` (`isOfW_tupW`, at the
member's own index telescope).

With that the two clauses the kit and the family data owe about the
motive are one rewrite each: `hconcl` (`GraphFamData`'s) says the motive
at the tagged index IS the conclusion's reading at the fitting spine,
and `hB` (the kit's) says it is a set of the family's level, which is
the conclusion's reading fact restated at the decoded data. -/

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
the conclusion's reading fact (it reads to a set of level `ℓ` at
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

/-- **`GraphFamData.hconcl` at the block's motive**: the motive at the
tagged index IS the conclusion's reading at the fitting spine.  The
index spine comes back out of its tuple at the member's own index
telescope (`isOfW_tupW`, whose `IdxOk` is the representation's own
`idxOk` clause), and the spine is the frame by `hsplit`'s
decomposition.  This is it at ONE member class (lane NESTIND), the
motive read at the member's own universe and index count. -/
theorem blockRec_hconcl_at {env : Env} {mo : EnvModel V env} {names : List Name}
    {d : BlockData V} (hM : BlockModelAt mo names d) {ψ : Name → Nat} {ρ : Nat → V} {K : Nat}
    {rP mem : Nat → Nat} {rds : Nat → List (Nat × Nat × AnnotTerm)} {concl : Nat → AnnotTerm}
    {uX nIdxX : Nat → Nat} {c : Nat} (hc : c < K)
    (huX : uX c = d.uM (mem c) ψ) (hnX : nIdxX c = d.nIdxAt (mem c))
    (hmem : mem c < d.N)
    (hlenIds : (d.IdsM (mem c) ψ).length = d.nIdxAt (mem c))
    (hsplit : BlockRecSplitOne V mo d ψ rP mem rds ρ c) :
    ∀ ys, SpineFit ρ ((rds c).map (·.2.2)) ys →
      blockRecMot K concl uX nIdxX ρ
          (prefOf (rP c) ys) (tagged c (d.tup ψ (mem c) (idxOf (rP c) ys)) (majOf ys))
        = interp V (consList ys ρ) (concl c) := by
  intro ys hfit
  obtain ⟨-, hdec, hpar, hidx, -⟩ := hsplit ys hfit
  have hIdx : IdxOk (d.uM (mem c) ψ) (consList ((prefOf (rP c) ys).take d.nP) ρ)
      (d.IdsM (mem c) ψ) := hM.idxOk ψ _ (d.satOfSpine hpar) (mem c) hmem
  have hret : isOfW (uX c) (nIdxX c)
      (d.tup ψ (mem c) (idxOf (rP c) ys)) = idxOf (rP c) ys := by
    rw [huX, hnX, ← hlenIds]
    exact isOfW_tupW hIdx hidx
  rw [blockRecMot_tagged hc, hret, ← hdec]


/-! ## 13. The residue across the chain frame

The graph producer's ι law reads the kit's step (the BASE-frame
residue) against the ι equation's right-hand side (the residue lifted
past the `K` chain binders); `interp_Rb_chain` is that frame move. -/

section ChainRb

variable {env : Env} {mo : EnvModel V env} {names : List Name} {d : BlockData V}
  {ℓ s K : Nat} {ψ : Name → Nat} {ρ : Nat → V} {mem nCt rP : Nat → Nat}
  {rds : Nat → List (Nat × Nat × AnnotTerm)} {concl RecTy : Nat → AnnotTerm}
  {pdoms : Nat → List AnnotTerm} {fdoms es : Nat → Nat → List AnnotTerm}
  {mk : Nat → Nat → AnnotTerm} {ihs : Nat → Nat → List AnnotTerm}
  {Rb0 : Nat → Nat → AnnotTerm} {ihv : List V → Nat → Nat → List V → V → List V}

/-- **The residue crosses the chain frame**: the base-frame residue
lifted past the `K` Σ' binders at its own depth reads the same under
the rule's binders and the ih block (`interp_liftN_chainFrame` at the
rule's frame). -/
theorem interp_Rb_chain {K : Nat} {a ρ : Nat → V} {ws ihvals : List V} {Rb0 : AnnotTerm} :
    interp V (consList ihvals (consList ws (chainFrame K a ρ)))
        (Rb0.liftN K (ws.length + ihvals.length))
      = interp V (consList ihvals (consList ws ρ)) Rb0 := by
  have h := interp_liftN_chainFrame (V := V) (K := K) (a := a) (ρ := ρ) (ws ++ ihvals) Rb0
  rw [List.length_append] at h
  rw [← consList_append, ← consList_append]
  exact h

end ChainRb

/-! ## 20. The components at the RUN's spelling

The rule data's syntactic components are functions of the run
(`BlockRecData.lean`): `blockRulePdomsAV`
(the recursor type's first `rP` binder domains),
`blockRuleFdomsAV`/`blockRuleEsAV`/`blockRuleMkAV` (the constructor's
field domains, index expressions and fired spine, read at the rule's
frame), with `blockRuleData_run` identifying them with what the check
actually opened.  The ι equations are stated at those components
LIFTED past the `K` chain binders at their own cutoffs
(`blockIotaEqsAV`).

These definitions are that instantiation, so every premise of §19
reads at those names; `hpl` — the rule's prefix domains are as
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

end RunComponents

/-! ## 21. The family's LEVEL, and `hTy` without pinning any bit

**The reading's binder numerals are not pinned.**  The
level a recursor's type lives at is the one the CHECK inferred — its
`ensureSort` names it, and that level already accounts for the
binders' levels, so the Π-tower's membership needs no per-binder
hypothesis at all.  `checkConstantVal_reads` (`BlockRecRead.lean`)
returns it: the same claims that grade the reading
place it in `univ (u.eval ψ)`, one component further into the
`InferClaim`/`WhnfClaim` pair (`sortSemAt_of_claims`, at
`ensureSortCore_inv`).

The family's level is then the MAX over the `K` recursors, and each
type's membership rises to it by cumulativity (`univ_mono`).  That is
`blockRecTy_univ_run`, and with it `BlockRecPre.hTy` is a theorem off
the run alone, with no hypothesis on the binders' levels. -/

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
(one numeral for the whole block is refutable at any block with a
level parameter, the parameters' sorts carrying it even at a `Prop`
motive). -/
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
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR) :
    ∃ us : List Level, ∀ (ψ : Name → Nat) (c : Nat), c < rs.length → ∀ ρ : Nat → V,
      interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c)
          ∈ˢ (univ (maxLevelEval us ψ) : V) ∧
        WellDenoted V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c) := by
  have hmem : ∀ c, c < rs.length → ∃ u : Level, ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c) ∈ˢ (univ (u.eval ψ) : V) := by
    intro c hc
    obtain ⟨u, hru⟩ := recStage_tyReads (V := V) hμ mpC h rs[c] (List.getElem_mem hc)
    refine ⟨u, fun ψ ρ => ?_⟩
    obtain ⟨ta, hta, -, hu⟩ := hru ψ
    rw [blockRecTyAV_eq (List.getElem?_eq_getElem hc) hta]
    exact hu ρ
  obtain ⟨us, hs⟩ := exists_uniform_univ hmem
  refine ⟨us, fun ψ c hc ρ => ⟨hs c hc ψ ρ, ?_⟩⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hwd⟩ :=
    recStage_tyPis hμ mpC h (List.getElem?_eq_getElem hc) ψ
  exact (hwd ρ).1

end FamilyLevel

/-! ## 22. `hctorAt` (b) — the fired spine's VALUE at the rule's frame

`blockRuleMkAV_eq` identifies the fired spine's reading as the
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
  fitting parameter spine (the constructor's value is parameter-blind). -/

section FiredSpine

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
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hm : memR c) (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
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
    blockRuleMkAV_eq (hm := hm) h hr hcA hrhs hfind hlps hnP ψ, interp_mkAppN, foldl_app_map,
    List.map_append]
  -- (2) the bvars read the frame's entries
  rw [map_bvarAt_take (hD := by rw [hlenL]) (by rw [hlenL]; omega),
    map_fieldBvars hxs hfs, List.take_append_of_le_length (by omega)]
  -- (3) the constant's leaf does not see the frame
  rw [acval_interp_closedC mpC.base2 cA.1.name _ (consList (xs ++ fs) ρ) ρ,
    Level.substFn_param_self ψ p.lps]
  exact hM.ctor (mem c) hmemN j cA hcj ψ ρ (xs.take p.nP) fs hps hfp

end FiredSpine

/-! ## 23. The lifting transport at an ARBITRARY insertion

`interp_liftN_chainFrame`/`spineFit_liftDomsK` transport a
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
ARBITRARY insertion (the chain version is this one at
`us := (List.range K).map a`). -/
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

/-! ## 24. `hspF` at the run — the rule's spine fits

`hspF` is the kit's step passing `BlockRuleCerts.residueOk` its
`SpineFit ρ (pdoms c ++ fdoms c j) (x⃗ ++ f⃗)`, and it splits exactly
where `SpineFit.append` does:

* the PREFIX half is the guard — an inhabited class
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
spelling: `hfd` is `blockRuleFdomsAV_eq` composed with the record's
`ds`/`Fss` identification — §27's `blockRuleFdomsAV_datum` — and
`hslot` is the slot-to-domain
step at the block's own carrier (`BlockCtorDataI.recEntry`/`.reflEntry`
through `BlockModelAt.leaf`, the shape `blockChainReal_of` already
discharges against the stage's tower).

`hslot` is quantified at the frames the walk actually REACHES —
`consList b⃗ ρp` for a prefix that already fits — and not at every
`σ`: the identity is `BlockModelAt.leaf`, whose hypotheses are fits,
so at an arbitrary frame the fold of the member's former and the slot
are unrelated and the `∀ σ` form of the premise is FALSE. -/

section SpineOfChain

/-- **`hspF` at the run.**  With the prefix's fit (the guard), a field
spine fitting the constructor's stored fields fits the rule's own
binder data at the chain frame. -/
theorem blockRecSpF {envC : Env} {mpC : EnvModelM V μ envC} {d : BlockData V}
    {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (hμ : μ.verifiedChecks = true)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {i j K : Nat} {mem : Nat → Nat} {ψ : Name → Nat}
    {a ρ : Nat → V} {xs fs : List V}
    (hfd : blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i
      = liftDomsK (p.toBlockShape.rulePrefixAt c - d.nP) 0 ((d.Fss (mem c) ψ).getD j []))
    (hxs : xs.length = p.toBlockShape.rulePrefixAt c)
    (hpref : SpineFit (chainFrame K a ρ)
      (blockRecPdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c) xs)
    (hbase : SpineFit (consList (xs.take d.nP) ρ) ((d.Fss (mem c) ψ).getD j []) fs) :
    SpineFit (chainFrame K a ρ)
      (blockRecPdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c
        ++ blockRecFdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c i) (xs ++ fs) := by
  refine SpineFit.append hpref ?_
  have hlenP : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
      = p.toBlockShape.rulePrefixAt c := blockRulePdomsAV_length hμ mpC h hr ψ
  rw [blockRecFdomsK, hlenP, hfd]
  exact (spineFit_liftDomsK_rule hxs).mpr hbase


end SpineOfChain

/-! ## 26. `hctorAt`'s INDEX half

`ChainFit`'s second conjunct asks that the constructor's result index
readings BE the components of the tuple the rule picks
(`d.tup ψ (mem c) e⃗`).  Three moves, and only the first is new here:

* `projS_tupW` — the tuple's retraction, at BOTH index regimes: at
  `u ≠ 0` it is `projS_mkTower`, at `u = 0` the tuple is the point and
  every index value is the point too (`projS_pt`,
  `spineFit_pt_of_bound0`);
* `interp_liftN_rule` (§23) at the index expressions, which are single
  forms rather than a binder list;
* `es0` (`blockRuleEsAV_eq`) composed with the record's `Es`/`Ess`
  identification, the ONE named premise left here.

The retraction's own hypothesis — that the result index readings FIT
the member's index telescope — is not a premise: it is
`BlockModelAt.resIdxFit`, the constructor's typing read
off the representation, and it is `idxFit` one position along (§25's
is at a recursive FIELD, this one at the RESULT). -/

section CtorIdx

/-- **`hctorAt`'s second conjunct at the run**: the constructor's
result index readings are the components of the rule's index tuple.

The fit of those readings in the member's own index telescope is not
a premise but `BlockModelAt.resIdxFit` — the constructor's typing,
read off the representation — so the theorem's only named premise is
`es0` (`blockRuleEsAV_eq`) composed with the record's `Es`/`Ess`
identification. -/
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

/-! ### 26b The rule's index readings ARE the SPLIT's index values

§26 says the constructor's result index readings are the components of
the RULE's index tuple; the fibre's `ChainFit` says the same readings
are the components of the SPLIT's tuple `d.tup ψ (mem c) is`.  Two
tuples with the same components at every position of a telescope both
spines fit are the same list (`projS_tupW` at each side), so

> **`is` IS the rule's index reading**, and the motive's split data is
> not an independent quantification after all.

This is what makes `hCaE` payable at the split data, and it is the
whole reason that premise carries the `ChainFit`: without it `is`
ranges over every fit of the member's index telescope while the rule's
readings do not move (refutable at any indexed family). -/

section CtorIdxSplit

/-- **The rule's index readings are the split's index values.** -/
theorem blockRecEsK_eq_is {envC : Env} {mpC : EnvModelM V μ envC} {d : BlockData V}
    {names : List Name} {p : ConLeche.BlockParts}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {c i j K : Nat} {mem : Nat → Nat} {ψ : Name → Nat} {a ρ : Nat → V}
    {xs fs is : List V} {cA : ConstantVal × Nat}
    (hM : BlockModelAt mpC.base2 names d)
    (hes : blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ c i
      = ((d.Ess (mem c) ψ).getD j []).map
          (·.liftN (p.toBlockShape.rulePrefixAt c - d.nP) cA.2))
    (hpl : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
      = p.toBlockShape.rulePrefixAt c)
    (hfl : (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i).length = cA.2)
    (hxs : xs.length = p.toBlockShape.rulePrefixAt c) (hfs : fs.length = cA.2)
    (hmem : mem c < d.N) (hjc : j < (d.ctorsM (mem c)).length)
    (hps : SpineFit ρ (d.params ψ) (xs.take d.nP))
    (hsf : SpineFit (consList (xs.take d.nP) ρ) ((d.Fss (mem c) ψ).getD j []) fs)
    (hIs : SpineFit (consList (xs.take d.nP) ρ) (d.IdsM (mem c) ψ) is)
    (hfit : d.StoredFit ψ (consList (xs.take d.nP) ρ) (d.tup ψ (mem c) is) (mem c) j fs) :
    (blockRecEsK K mpC.base2.acval envC p.toBlockShape rs ψ c i).map
        (interp V (consList (xs ++ fs) (chainFrame K a ρ))) = is := by
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
  rw [hmapEq]
  refine List.ext_getElem (by rw [List.length_map, hEsLen, hIs.length_eq]) fun l h1 h2 => ?_
  have hl : l < (d.IdsM (mem c) ψ).length := by
    rw [List.length_map, hEsLen] at h1; exact h1
  have hlt : l < ((d.Ess (mem c) ψ).getD j []).length := by rw [hEsLen]; exact hl
  have key : interp V (consList fs (consList (xs.take d.nP) ρ))
        (((d.Ess (mem c) ψ).getD j []).getD l default) = is.getD l pt := by
    rw [hfit.2.2 l hl, BlockData.tup, projS_tupW hIdx hIs hl]
  rw [List.getElem_map, List.getElem_eq_getD (default : AnnotTerm), key,
    List.getElem_eq_getD (pt : V)]

end CtorIdxSplit

/-! ## 27. `hfd` — the rule's field domains ARE the constructor's

The last named premise of §24 (and so of `hspF` and of `hctorAt`'s fit
half).  `blockRuleFdomsAV_eq` already says that the rule's
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
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hm : memR c) (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
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
  have hcd := (hcore.2.2.1 (mem c) j cA hcj).2.2.1
  rw [hdnP] at hcd
  have hF : (d.Fss (mem c) ψ).getD j [] = ((d.dsF (mem c) j ψ).drop d.nP).map (·.2.2) :=
    fssOfR_fixCtorDataList_getD hcj
  rw [(blockRuleFdomsAV_eq (hm := hm) h hr hcA hrhs hcd hCf hnP ψ).1, hF, hdnP]

/-- **THE `fdoms` SPELLING, at the DATUM.**  §40.8 and §40.10 state
the FIELD and `ih` segments over `(liftDoms o 0 (ds.drop nP)).map
(·.2.2)`; the bundle states its own `fdoms` as `blockRuleFdomsAV`, the
field OPENERS' readings.  `blockRuleFdomsAV_eq_liftDoms`
(`BlockRecData.lean`) is that identity at a `BlockCtorDataI`; this is
it at the BLOCK DATUM, which is the record the recursor stage's
consumers carry — `blockRuleFdomsAV_datum`'s extraction (the record
out of `BlockCtorsCore`, the type's fvar-freeness out of the
environment's well-formedness) with the spelling step DELEGATED
upstream rather than repeated. -/
theorem blockRuleFdomsAV_liftDoms {envC : Env} {mpC : EnvModelM V μ envC} {d : BlockData V}
    {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hm : memR c) (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {lps : List Name} {cvTasAll : List ConstantVal} {p₁ : ConLeche.BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm}
    (hcore : BlockCtorsCore mpC.base2 d lps cvTasAll p₁ isRec A d.k)
    {mem : Nat → Nat} {j : Nat} (hmemk : mem c < d.k)
    (hcj : (d.ctorsM (mem c))[j]? = some cA)
    (hnP : p.nP ≤ p.toBlockShape.rulePrefixAt c) (hdnP : d.nP = p.nP) {o : Nat}
    (ho : p.toBlockShape.rulePrefixAt c = p.nP + o) (ψ : Name → Nat) :
    blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i
      = (liftDoms o 0 ((d.dsF (mem c) j ψ).drop p.nP)).map (·.2.2) := by
  have hfind := (hcore.2.2.2 (mem c) hmemk j cA hcj).1
  have hCf : cA.1.type.hasFvar = false :=
    (mpC.base2.wf _ (List.mem_of_find?_eq_some hfind)).1
  have hcd := (hcore.2.2.1 (mem c) j cA hcj).2.2.1
  rw [hdnP] at hcd
  exact blockRuleFdomsAV_eq_liftDoms (hm := hm) h hr hcA hrhs hcd hCf hnP (by omega) ψ

end RuleFdoms

/-! ## 28. The `K` lifts of §20 are the IDENTITY

The guard the kit reads back (`blockRecIs_fits`, §3) is
`SpineFit ρ (pdoms c) xs` at the BASE frame, while the bridges that
discharge it (`blockRecSpF_of`, `blockRecCtorFitsFrom_of`) hold at the
CHAIN frame; §20 instantiates `pdoms := blockRecPdomsK K … =
liftDomsK K 0 (blockRulePdomsAV …)`, a form lifted past the `K` chain
binders.  `spineFit_liftDomsK` relates the chain-frame LIFTED data to
the base-frame UNLIFTED data; it says nothing about the base frame at
the lifted data.

The gap is not real: every rule datum is
the reading of a CLOSED expression at its own depth, so the `l`-th
binder domain mentions no variable at or above `l`
(`bvarsBelow_of_reading`), and a lift at a cutoff above a term's bound
is the identity (`AnnotTerm.liftN_eq_self`).  `liftDomsK` walks the
list raising the cutoff by one per entry, which is exactly the shape
that bound has, so the whole list is fixed.

The boundedness itself is a named premise here, in the positional
shape `liftDomsK` needs; §35 discharges it at the run
(`blockRulePdomsAV_bounded`, off `recStage_tyBounds`). -/

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

end LiftIdentity

/-! ## 29. The rule's CONCLUSION, peeled — and `hCaB`

`BlockRuleCerts` carries `denoteMeta … concl = some Ca` with `concl`
EXISTENTIALLY quantified, so no consumer can say what `Ca` is.
`checkBlockRule` says: the recursor's TYPE
instantiated at the rule's prefix openers, the constructor's result
index arguments and the fired major
(`RuleRun.hconcl`, the `instPisAtLift` clause).

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

It is a SEPARATE bundle from `BlockRuleCerts` on purpose: the sites
that STATE the certificates (the graph kit and its family) never read
the conclusion's shape, and threading three more components through
them would only widen their premises.  Both bundles have the same producer and the same
run. -/

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

/-! ### 29b `hCaE` AT THE SPLIT DATA

§29 evaluates the rule's conclusion at the rule's own components; §26b
identifies those components' INDEX readings with the split's `is`.
Together they are `hCaE` — the rule's conclusion as the bound at the
constructed element (`blockKitCaB_run`'s core) — at the split data, with no index clause inverted and no `w` or `ℓ` guard:
`blockRecMkK_value` and `blockRecEsK_eq_is` are both unguarded, and
the fibre's `ChainFit` (which `hCaE` carries for exactly this reason)
is what pins the index values.

The `++` re-association at the end is the only bookkeeping: §29 states
its frame as `xs ++ (is ++ [maj])` and the regime states it as
`as ++ ms ++ is ++ [x]`, which is `((as ++ ms) ++ is) ++ [x]`. -/

section CaESplit

/-- **`hCaE` at ONE rule, from the run.** -/
theorem blockIndCaE_of_run {envC : Env} {mpC : EnvModelM V μ envC} {d : BlockData V}
    {names : List Name} {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (hμ : μ.verifiedChecks = true) (hM : BlockModelAt mpC.base2 names d)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hm : memR c) (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {ci : ConstantInfo} (hfind : envC.find? cA.1.name = some ci)
    (hlps : ci.toConstantVal.levelParams = p.lps)
    (hnP : p.nP ≤ p.toBlockShape.rulePrefixAt c) (hnPd : d.nP = p.nP)
    {mem : Nat → Nat} {j : Nat} (hmemN : mem c < d.N)
    (hcj : (d.ctorsM (mem c))[j]? = some cA) (hjc : j < (d.ctorsM (mem c)).length)
    (ψ : Name → Nat) {nF nR : Nat} {esA : List AnnotTerm} {mkA Ca : AnnotTerm}
    -- the bundle's peel, and its components at the run's own spellings
    (hcon : BlockRuleConclAt (p.toBlockShape.rulePrefixAt c) nF nR
      (blockRecTyAV mpC.base2.acval envC rs ψ c) esA mkA Ca)
    (hmkL : mkA
      = (blockRecMkK 0 mpC.base2.acval envC p.toBlockShape rs ψ c i).liftN nR 0)
    (hesL : esA
      = (blockRecEsK 0 mpC.base2.acval envC p.toBlockShape rs ψ c i).map (·.liftN nR 0))
    -- the run's components against the datum
    (hes : blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ c i
      = ((d.Ess (mem c) ψ).getD j []).map
          (·.liftN (p.toBlockShape.rulePrefixAt c - d.nP) cA.2))
    (hpl : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
      = p.toBlockShape.rulePrefixAt c)
    (hfl : (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i).length = cA.2)
    (hrds : (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
      = p.toBlockShape.rulePrefixAt c + (d.IdsM (mem c) ψ).length + 1)
    (hnFe : cA.2 = nF)
    -- the SPLIT data
    {ρ : Nat → V} {xs fs ihvals is : List V} {x : V}
    (hxs : xs.length = p.toBlockShape.rulePrefixAt c) (hfs : fs.length = cA.2)
    (hihl : ihvals.length = nR)
    (hps : SpineFit ρ (d.params ψ) (xs.take d.nP))
    (hsf : SpineFit (consList (xs.take d.nP) ρ) ((d.Fss (mem c) ψ).getD j []) fs)
    (hIs : SpineFit (consList (xs.take d.nP) ρ) (d.IdsM (mem c) ψ) is)
    (hfit : d.StoredFit ψ (consList (xs.take d.nP) ρ) (d.tup ψ (mem c) is) (mem c) j fs)
    (hxinj : x = d.inj ψ (mem c) j fs) :
    interp V (consList ihvals (consList (xs ++ fs) ρ)) Ca
      = interp V (consList (xs ++ is ++ [x]) ρ)
          (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ c) := by
  -- the index readings ARE the split's values (§26b)
  have hesV : (blockRecEsK 0 mpC.base2.acval envC p.toBlockShape rs ψ c i).map
      (interp V (consList (xs ++ fs) ρ)) = is :=
    blockRecEsK_eq_is (K := 0) (a := fun _ => (pt : V)) hM hes hpl hfl hxs hfs hmemN hjc
      hps hsf hIs hfit
  have hesLen : (blockRecEsK 0 mpC.base2.acval envC p.toBlockShape rs ψ c i).length
      = (d.IdsM (mem c) ψ).length := by
    have hq := congrArg List.length hesV
    rw [List.length_map] at hq
    rw [hq, hIs.length_eq]
  -- the fired major IS the injection (§22)
  rw [hnPd] at hps hsf
  have hmkV : interp V (consList (xs ++ fs) ρ)
      (blockRecMkK 0 mpC.base2.acval envC p.toBlockShape rs ψ c i) = x := by
    rw [hxinj]
    exact blockRecMkK_value (hm := hm) (K := 0) (a := fun _ => (pt : V)) hM h hr hcA hrhs hfind hlps
      hnP hmemN hcj ψ hxs hfs (by rw [hpl, hfl, hxs, hfs]) hps hsf
  obtain ⟨-, -, -, -, hTyE, -, -, -, -, -⟩ := recStage_tyPis hμ mpC h hr ψ
  have hq := blockRecCa_run (nIdx := (d.IdsM (mem c) ψ).length) hcon hTyE hrds hesLen
    (recStage_tyBounds (V := V) hμ mpC h hr ψ).2 hxs (by rw [hfs, hnFe]) hihl
    hmkL hesL hmkV hesV
  rw [← List.append_assoc] at hq
  exact hq

end CaESplit

/-! ## 30. The `ih` openers' VALUES — `ihv` defined, and `hihChain`

The ih values `ihv` the graph kit consumes are DEFINED here, and they may not mention the recursor: the kit's
step is what the recursion theorem is being handed, so the only thing
an ih value may be built from is the GRAPH `g` the step receives.  The
two facts about them are `hihF` (the values fit the ih openers'
domains, §32) and `hihChain` (they ARE the ih terms' readings at the
chain frame).

A rule's `ih` opener for a guarded call `rec_{c'} x⃗ e⃗_i(a⃗) (f_i a⃗)`
is valued at the CURRIED λ-tower over the field's telescope (the ih's
domain is the telescope, not the predecessor set) whose body is the
graph at that call's PREDECESSOR — `blockRecIhvAt`.  The ih TERMS are
the same towers spelled syntactically under the `K` chain binders
(`ihFunAV`, whose head is the chain's component) — `blockRecIhsAt`,
the one definition of `ihs` both the kit and the rule data use.

`hihChain` is then a TOWER congruence: the two towers run over the
same binder data at two frames that agree below the rule's own depth,
and at a leaf the graph-built body is the call's value (`app_graph` at
the call target and `famCandG_fold` at the candidate) while the
syntactic one folds to the same thing (`interp_ihFunAV_body`,
`ihFunAV_fold`'s core stated at the BODY rather than at the fold). -/

section IhValues

/-! ### The tower congruence -/

/-- A frame built by `consList` does not see the environment below it. -/
theorem consList_below_indep (L : List V) (ρ₁ ρ₂ : Nat → V) :
    ∀ i, i < L.length → consList L ρ₁ i = consList L ρ₂ i := by
  intro i hi
  rw [consList_getD_of_lt _ _ _ hi, consList_getD_of_lt _ _ _ hi]

/-! ### The ih term's body -/

/-! ### The two lists -/

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

/-! ### The call's arguments, across the two frames -/

end IhValues

/-! ## 31. The two spellings of `eqs` are ONE term

`hpre` is stated at `iotaEqsAV` instantiated at §20's components; the
rule data's `hnew` at `blockIotaEqsAV`, which is the same instantiation
written once.  By §28 the two agree everywhere except in the RESIDUE's
cutoff: the former writes the LIFTED prefix and field domains' lengths
(they come out of its `pdoms`/`fdoms` parameters), the latter the
unlifted ones.  `liftDomsK_length` is a theorem, not `rfl` — a
recursion on the list — so the two do not typecheck against each other
without this. -/

section EqsIdent


end EqsIdent

/-! ## 32. The `ih` openers' DOMAINS — `hihF`

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
  different binder-data lists is needed.**
* **The leaf obligation is `hCaB` at the PREDECESSOR.**  The
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

end IhDomains

/-! ## 35. THE CERTIFIED HOP — `hpref'` from the run

A guarded call's argument is a PREDECESSOR of the constructed element:
it lies in the TARGET member's carrier at the call's
index tuple (the recursive slot, with `BlockModelAt.idxFit`'s `SlotFit`
and `tupW_mem`) and ∈-below it (the block's `mkDepth`).  Membership in
the callee's class is guarded by `SpineFit ρ (pdoms c') xs` — at the
CALLEE's class `c'` — while the rule supplies the fit at its own class
`c`.  `hpref'` bridges the two: a spine fitting recursor `c`'s
rule-prefix domains fits recursor `c'`'s.

Stage (b) alone never gives it: `checkBlockRecTys` compares only the
first `nP` binder domains with the block's parameters and never looks
inside the binders `nP … rP-1` (the motives and minor premises), so two
recursors of one block could carry different telescopes of the same
LENGTH.  Stage (b') `checkBlockRecPrefixAgree`
(`Kernel/Inductives/BlockInstall.lean`) requires a family's recursors
to share their whole rule prefix, and the run exports it as a
per-position `isDefEq` between the two openings
(`recStage_prefixAgree`, `BlockRecMem.lean`).  This section is
the hop from that `isDefEq` to the fit, in four steps; only the third
is about the checker:

* **the two openings meet** (A) — stage (b') opens a recursor's stored
  type at the RULE PREFIX, its reading opens it at the full `mI + 1`
  binders, so the shorter opening has to be the longer one's prefix
  (`openPisAtFvars_split`, `openPisAtFvars_add`'s converse);
* **the walk pays for little** (B) — `SpineFit` reads entry `l` at the
  spine's own first `l` values, so the domains need only agree THERE
  (`spineFit_congr_walk`).  Agreement at ALL frames is not payable:
  `DefEqClaim` concludes at the frames satisfying the opening's context
  and at no others;
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

§28's premise falls out on the way (`blockRulePdomsAV_bounded`,
`blockRecPdomsK_run`): the boundedness it asks for is
`recStage_tyBounds`' first conjunct at the prefix, so the kit's
lifted guard and the base form are one term at the run. -/

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
under the spine's own first `l` values.  Agreement at all frames is
the special case; this one is what a run-level agreement (proved at
the opening's satisfying frames, never at all of them) can pay. -/
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

/-- **The certified hop's READING half**: the two openings'
domains read the same at every position, at the frames the FIRST
opening's fitting spines reach — `prefixDoms_spineFit`'s induction,
exported, because a consumer comparing a THIRD telescope against the
first (stage (b'')'s index pass, `BlockRecIdxConv.lean`) needs the
readings and not the fit. -/
theorem prefixDoms_agree {envT : Env} (hμ : μ.verifiedChecks = true)
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
    :
    ∀ l, l < rP → ∀ (ρ₁ : Nat → V) (ys : List V), SpineFit ρ₁ domsA ys →
      interp V (consList (ys.take l) ρ₁) (domsA.getD l default)
        = interp V (consList (ys.take l) ρ₁) (domsB.getD l default) := by
  obtain ⟨-, -, ihd, -⟩ := checkSoundAt (V := V) hμ (Rules.RulesInputs.ofSem mp ψ) fuel
  have hlA : fvsA.length = rP := ConLeche.Verify.openPisAtFvars_length _ hopA
  have hlB : fvsB.length = rP := ConLeche.Verify.openPisAtFvars_length _ hopB
  have hlbA := (ConLeche.Verify.openPisAtFvars_bounded _ hopA hbA).2
  have hlbB := (ConLeche.Verify.openPisAtFvars_bounded _ hopB hbB).2
  have hentA : ∀ i, i < rP → domsA.reverse[rP - 1 - i]? = some (domsA.getD i default) :=
    fun i hi => getElem?_reverse_entry hlenA hi
  -- the agreement, position by position, at every fitting spine's frame
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
    SpineFit ρ₀ domsB xs :=
  spineFit_congr_walk (by rw [hlenA, hlenB])
    (fun l hl => prefixDoms_agree hμ mp hopA hopB hwA hwB hbA hbB hlenA hlenB hdA hdB hokA hokB
      hdeq l (by omega) ρ₀ xs hfit) hfit

/-! ## G. The run's side -/

section Run

variable {envC : Env} {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}

/-- **A stored recursor type is CLOSED** — the two scoping facts
`prefixDoms_spineFit` asks of an opening's subject, at the run.
`recStage_tyBounds` derives them inline; they are named here
because the hop needs them on their own. -/
theorem recStage_tyClosed
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {i : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[i]? = some r) :
    Expr.WScoped 0 r.1.type ∧ r.1.type.looseBVarsBounded 0 = true := by
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.recStageG_tyGen h hr
  obtain ⟨-, -, -, -, hlb0, hfv0, tyA, -, -, hann, -, -, -, -, hcv'⟩ :=
    ConLeche.checkConstantVal_inv TE.hcv
  have hrty : r.1.type = tyA := by rw [hcv']
  exact ⟨by
      rw [hrty]
      exact ConLeche.annotateCore_WScoped _ _ hann (Expr.WScoped.of_not_hasFvar hfv0),
    by rw [hrty]; exact ConLeche.annotateCore_looseBVars _ _ hann hlb0⟩

/-- **The rule PREFIX opening's readings are `blockRulePdomsAV`'s
entries.**  Stage (b') opens the stored type at the rule prefix alone;
its reading opens it at the full `mI + 1` binders.  The shorter opening
is the longer one's prefix (`openPisAtFvars_prefix_getElem`), so the two
carry the same annotations at every position below `rP`. -/
theorem blockRulePdomsAV_reads (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
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
  obtain ⟨fvsL, concl, hopL, -, -, -, -, hbind, -, -⟩ := recStage_tyPis hμ mpC h hr ψ
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
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {i : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[i]? = some r) (ψ : Name → Nat) :
    ∀ l, l < p.toBlockShape.rulePrefixAt i → ∀ (ρ : Nat → V) (ys : List V),
      SpineFit ρ ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ i).take l) ys →
      WellDenotedV V (consList ys ρ)
        ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ i).getD l default) := by
  intro l hl ρ ys hys
  have hle := blockRecHrPle (p := p) h (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨-, -, -, -, hmk, hlenRds, -, -, -, hwdTy⟩ := recStage_tyPis hμ mpC h hr ψ
  refine prefixDoms_graded_of_tower (cc := blockRecConclAV mpC.base2.acval envC
      p.toBlockShape rs ψ i) (by omega) (fun ρ' => by rw [← hmk]; exact hwdTy ρ') hl hys

/-- **`hpref'`, FROM THE RUN**: a spine
fitting recursor `c`'s rule-prefix domains fits recursor `c'`'s.

The reference is recursor `0` — stage (b') compares every other
recursor's opened prefix against it — so the transfer is two hops,
`c → 0 → c'`, and the two run in OPPOSITE orientations of the same
`isDefEq` (which is why `prefixDoms_spineFit` takes its comparison as
a disjunction: `DefEqClaim`'s conclusion is an equation, and the check
supplies only the one order). -/
theorem blockRecHpref_run (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    (ψ : Name → Nat) {c c' : Nat}
    {rc rc' : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hrc : rs[c]? = some rc) (hrc' : rs[c']? = some rc')
    {ρ : Nat → V} {xs : List V}
    (hfit : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) xs) :
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c') xs := by
  have hcl : c < rs.length := (List.getElem?_eq_some_iff.mp hrc).1
  obtain ⟨r0, hr0⟩ : ∃ r0, rs[0]? = some r0 :=
    ⟨rs[0]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨fvs0, o0, hop0, hall⟩ := recStage_prefixAgree h hr0
  have hl0 : fvs0.length = p.toBlockShape.rulePrefixAt 0 :=
    ConLeche.Verify.openPisAtFvars_length _ hop0
  have hlen0 : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ 0).length
      = p.toBlockShape.rulePrefixAt 0 := blockRulePdomsAV_length hμ mpC h hr0 ψ
  have hd0 := blockRulePdomsAV_reads hμ mpC h hr0 ψ hop0
  have hok0 := blockRulePdomsAV_graded hμ mpC h hr0 ψ
  obtain ⟨hw0, hb0⟩ := recStage_tyClosed h hr0
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
    obtain ⟨hwI, hbI⟩ := recStage_tyClosed h hri
    have hdeq0I : ∀ l, l < p.toBlockShape.rulePrefixAt 0 →
        ConLeche.isDefEqCore μ envC F (p.toBlockShape.rulePrefixAt 0)
          ((fvs0.map Expr.fvarTypeD).getD l default)
          ((fvsI.map Expr.fvarTypeD).getD l default) = .ok true :=
      fun l hl => hdeqI l (by omega)
    -- BOTH openings are passed at recursor `0`'s prefix count, which is
    -- what stage (b') compares at; `hrP` is the run's own equation and
    -- the ONLY thing that identifies it with recursor `i`'s.
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
lift is the identity.  `recStage_tyBounds` says it of the whole
binder list; the prefix is its `take`. -/
theorem blockRulePdomsAV_bounded (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {i : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[i]? = some r) (ψ : Name → Nat) :
    ∀ l, l < (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ i).length →
      Term.bvarsBelow l
        (((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ i).getD l default).erase) := by
  intro l hl
  have hlp : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ i).length
      = p.toBlockShape.rulePrefixAt i := blockRulePdomsAV_length hμ mpC h hr ψ
  have hle := blockRecHrPle (p := p) h (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨-, -, -, -, -, hlenRds, -, -, -, -⟩ := recStage_tyPis hμ mpC h hr ψ
  obtain ⟨hbnd, -⟩ := recStage_tyBounds hμ mpC h hr ψ
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
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {i : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[i]? = some r) (ψ : Name → Nat) (K : Nat) :
    blockRecPdomsK K mpC.base2.acval envC p.toBlockShape rs ψ i
      = blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ i :=
  blockRecPdomsK_eq (blockRulePdomsAV_bounded hμ mpC h hr ψ)

end Run

/-! ## 37. A recursive field's PREDECESSOR at the separated tuple

The graph route's induction (`blockGraphInd_run`, `BlockRecGraph.lean`)
reads the block's lfp clause at a SEPARATED tuple: a recursive field
folded along a fitting telescope spine lies in the separated tuple's
target component at the call's index tuple, so the property holds
there.  These two lemmas are that reading. -/


/-! ## 38. THE BITS LAW — a Π-tower's binder data follows its
CONCLUSION's sort

`blockRecOneElimLevel` (§4) takes `hbits` — every binder numeral of
recursor `c`'s binder data is zero exactly when its elimination level
is — as a premise.  This is its producer.

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

The stage's own sort computation on the opened conclusion —
`ops.inferType` followed by `ops.ensureSort`, whose level IS the
recursor's stored elimination level — is the type record's
`hsty`/`hu` (`RecTyEntry`, `Verify/Inductives/BlockRecRun.lean`); those
two runs are the bits law's premises. -/

section ElimRun

/-! ### The COUNTING guard, read off the verdict

`blockLargeElimAllowed` is a disjunction whose first arm
(`resSort.isNeverZero`) is refuted at a `Prop` block — `d.w ψ = 0`,
i.e. the result sort evaluates to zero at this `ψ` — so at `w = 0` the
verdict IS the counting guard's
four facts, and all of them at once:

* `large = true`, which is what the constructors' stage keys its
  SUBSINGLETON clause on (`CtorDataI.srcProp`) and therefore what
  `blockRuleChainFit_sq`'s `hlarge` asks for;
* `k = 1`, which is the dispatch's `hK1`;
* `nested = false`;
* `numCtors ≤ 1`, which is `hct1` once the member's own count is read
  off the block's (at `k = 1` the two are the same number).

They are one theorem because they are one `&&`: stating them
separately would mean reading the same guard three times, and the
reason the arm may read it at all is the same in each case.

**The pass is the licence; this theorem is the reading.**  The
antecedent `blockLargeElimAllowed = true` is produced by the counting
pass: `checkBlockRecSmallElim` (`Kernel/Inductives/BlockInstall.lean`)
states `blockLargeElimAllowed p nested || every level is zero` — the
CHECKER's own predicate — so at a non-zero elimination level the
antecedent falls out (`blockRecCounting_run`,
`Model/Inductives/BlockRecPreHpre.lean`).  (Stage (b)'s inversion alone
hands back only the guard's DISJUNCTION, and refuting its second arm
would need an inversion of `isDefEq` through `whnf` to the sort case.)

The elimination-level pin's route to `large = true` is not a duplicate:
it needs no `Prop`-valued hypothesis, so it says something at a `Type`
block where this one says nothing; `blockRecLarge_run`'s docstring says
which to reach for. -/

/-- **The counting guard's four facts, from the verdict at a `Prop`
result.** -/
theorem blockLargeElim_counting {q : ConLeche.BlockShape} {nested : Bool}
    (hallow : ConLeche.blockLargeElimAllowed q nested = true)
    {ψ : Name → Nat} (hz : q.resSort.eval ψ = 0) :
    q.large = true ∧ q.k = 1 ∧ nested = false ∧ q.numCtors ≤ 1 := by
  rw [ConLeche.blockLargeElimAllowed, Bool.or_eq_true] at hallow
  rcases hallow with hnz | hrest
  · exact absurd hz (ConLeche.Level.isNeverZero_sound ψ _ hnz)
  · rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hrest
    obtain ⟨⟨⟨hl, hk⟩, hn⟩, hc⟩ := hrest
    refine ⟨hl, by simpa using hk, by simpa using hn, ?_⟩
    rcases (Bool.or_eq_true _ _).mp hc with hc' | hc' <;>
      · rw [beq_iff_eq] at hc'; omega

end ElimRun

/-- **`hbits` AND `hmem`, FROM THE RUN** —
`blockRecOneElimLevel`'s premise, discharged.  The binder numerals of
recursor `c`'s binder data are `pwBit ψ` of the `PropWhen` the ∀
clause validated at every binder of its stored type, and that datum is
`zeronessOf` the level stage (b) read off the CONCLUSION — the
recursor's elimination level. -/
theorem blockRecElimLevel_run (hμ : μ.verifiedChecks = true) {envC : Env}
    (mpC : EnvModelM V μ envC) {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR) :
    ∃ uOf : Nat → Level,
      (∀ (ψ : Name → Nat) (c : Nat), c < rs.length →
        ∀ b ∈ blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c,
          (b.2.1 = 0 ↔ (uOf c).eval ψ = 0)) ∧
      ∀ c, c < rs.length → ∃ (fvs : List Expr) (conclE sty : Expr),
        ConLeche.openPisAtFvars (p.toBlockShape.majorIdxAt c + 1)
            (rs.getD c default).1.type 0 = some (fvs, conclE) ∧
        ConLeche.inferTypeCore μ envC F (p.toBlockShape.majorIdxAt c + 1) conclE = .ok sty ∧
        ConLeche.ensureSortCore μ envC F (p.toBlockShape.majorIdxAt c + 1) sty
          = .ok (uOf c) := by
  obtain ⟨R⟩ := id h
  have huOf : ∀ {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
      {u : Level}, R.cvRus[c]? = some (r.1, r.2.2.1, u) →
      ((R.cvRus.map (·.2.2)).getD c .zero) = u := by
    intro c r u hcu
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hcu]; rfl
  refine ⟨fun c => ((R.cvRus.map (·.2.2)).getD c .zero), ?_, ?_⟩
  · intro ψ c hc b hb
    obtain ⟨r, hr⟩ : ∃ r, rs[c]? = some r := ⟨rs[c]'hc, List.getElem?_eq_getElem hc⟩
    obtain ⟨rc, u, -, hcu, ⟨E⟩⟩ := R.tyGenAt hr
    -- the type's own inference (`checkConstantVal`'s second run)
    obtain ⟨-, -, -, -, -, -, tyA, stype, -, -, -, -, hinfTy, -, hcv'⟩ :=
      ConLeche.checkConstantVal_inv E.hcv
    have htyA : r.1.type = tyA := by rw [hcv']
    -- the reading, and its Π-peel
    obtain ⟨fvs, concl, hop, hta, hmk, hlenRds, -, -, -, -⟩ := recStage_tyPis hμ mpC h hr ψ
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hop.symm.trans E.hopen))
    -- the reading's Π-peel IS the run's own binder data (the reading's identification)
    have hst : stripPisAV (p.toBlockShape.majorIdxAt c + 1)
        (blockRecTyAV mpC.base2.acval envC rs ψ c)
        = some (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c,
            blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ c) := by
      rw [hmk, ← hlenRds]
      exact stripPisAV_mkPisAV _ _
    have hinfTy' : ConLeche.inferTypeCore μ envC F 0 r.1.type = .ok stype := by
      rw [htyA]; exact hinfTy
    show b.2.1 = 0 ↔ Level.eval ψ ((R.cvRus.map (·.2.2)).getD c .zero) = 0
    rw [huOf hcu, stripPisAV_denoteMeta_pw (envK := envC) hμ _ (Nat.le_refl F) hop hta hst
      hinfTy' (by rw [Nat.zero_add]; exact E.hsty) (by rw [Nat.zero_add]; exact E.hu) b hb]
    exact pwBit_zeronessOf ψ u
  · -- **the conclusion's two runs**, at the SAME level the bits law reads
    intro c hc
    obtain ⟨r, hr⟩ : ∃ r, rs[c]? = some r := ⟨rs[c]'hc, List.getElem?_eq_getElem hc⟩
    obtain ⟨rc, u, -, hcu, ⟨E⟩⟩ := R.tyGenAt hr
    have hrd : rs.getD c default = r := by rw [List.getD_eq_getElem?_getD, hr]; rfl
    refine ⟨E.fvs, E.concl, E.sty, by rw [hrd]; exact E.hopen, E.hsty, ?_⟩
    show ConLeche.ensureSortCore μ envC F (p.toBlockShape.majorIdxAt c + 1) E.sty
      = .ok ((R.cvRus.map (·.2.2)).getD c .zero)
    rw [huOf hcu]
    exact E.hu

/-- **The package's `uOf c` IS stage (b)'s own level**, for every
recursor of the list: `blockRecElimLevel_run` hands the level back
existentially, but its runs pin it — `inferTypeCore`/`ensureSortCore`
are functions — so a fact about the KERNEL's level list is read at
`uOf`. -/
theorem blockRecUOf_run {envC : Env} {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {uOf : Nat → Level} {memR : Nat → Prop} (R : ConLeche.RecStage μ F envC p cvTas ctorsAs rs memR)
    (hruns : ∀ c, c < rs.length → ∃ (fvs : List Expr) (conclE sty : Expr),
      ConLeche.openPisAtFvars (p.toBlockShape.majorIdxAt c + 1)
          (rs.getD c default).1.type 0 = some (fvs, conclE) ∧
        ConLeche.inferTypeCore μ envC F (p.toBlockShape.majorIdxAt c + 1) conclE = .ok sty ∧
        ConLeche.ensureSortCore μ envC F (p.toBlockShape.majorIdxAt c + 1) sty = .ok (uOf c))
    {c : Nat} (hc : c < rs.length) : uOf c ∈ R.cvRus.map (·.2.2) := by
  obtain ⟨r0, hr0⟩ : ∃ r, rs[c]? = some r := ⟨rs[c]'hc, List.getElem?_eq_getElem hc⟩
  obtain ⟨rc, u, -, hcu, ⟨E⟩⟩ := R.tyGenAt hr0
  obtain ⟨fvs', conclE', sty', hop', hsty', hu'⟩ := hruns c hc
  have hrd : rs.getD c default = r0 := by rw [List.getD_eq_getElem?_getD, hr0]; rfl
  rw [hrd] at hop'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hop'.symm.trans E.hopen))
  obtain rfl : sty' = E.sty := Except.ok.inj (hsty'.symm.trans E.hsty)
  have huu : uOf c = u := Except.ok.inj (hu'.symm.trans E.hu)
  have hg : (R.cvRus.map (·.2.2))[c]? = some u := by rw [List.getElem?_map, hcu]; rfl
  obtain ⟨hlt, hEq⟩ := List.getElem?_eq_some_iff.mp hg
  rw [huu]
  exact hEq ▸ List.getElem_mem hlt

/-- **THE LEVEL CURRENCY**: every recursor of the family eliminates at
the CHECKED elimination level `structElimLevel p.elim p.large`, at
every `ψ` — the elimination-level pin (`RecFamRun.pin`) read at the
package's `uOf`. -/
theorem blockRecElimPin_run {envC : Env} {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {uOf : Nat → Level}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    (hruns : ∀ c, c < rs.length → ∃ (fvs : List Expr) (conclE sty : Expr),
      ConLeche.openPisAtFvars (p.toBlockShape.majorIdxAt c + 1)
          (rs.getD c default).1.type 0 = some (fvs, conclE) ∧
        ConLeche.inferTypeCore μ envC F (p.toBlockShape.majorIdxAt c + 1) conclE = .ok sty ∧
        ConLeche.ensureSortCore μ envC F (p.toBlockShape.majorIdxAt c + 1) sty = .ok (uOf c))
    (ψ : Name → Nat) {c : Nat} (hc : c < rs.length) :
    Level.eval ψ (uOf c)
      = Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) := by
  obtain ⟨R⟩ := id h
  exact ConLeche.Level.isEquiv_sound (R.fam.pin _ (blockRecUOf_run R hruns hc)) ψ

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
runs come from stage (c)'s record (`RuleRun`), the frame's
readings and grading come SEGMENT by segment (§39), and the residue's
and conclusion's own readings are the rule stage's.  Nothing here is
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
    (hcbF : ∀ x ∈ fvsPref ++ fvsF ++ fvsIh, ConstsBound envT x)
    (hclF : ∀ x ∈ fvsPref ++ fvsF ++ fvsIh, ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF ++ fvsIh)
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
    h₁, h₂, h₃, hw₁, hw₂, hw₃, hlbF, hcbF, hclF, hp, hf, hidx,
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
* the **grading** half (`hokA`, `hokC`), segment by segment from
  §40.4 on.

The generated `ih` opener tower is the one place where the CHECK
supplies nothing: `blockIhPis` builds `ihTele` and the kernel never
types it, so its two syntactic facts (`hasFvar = false`, and
`looseBVarsBounded (rP + nF)`) are premises of §40.1 exactly as they
are of `blockRuleHopener_of` (`hihfv`); §40.7 proves them. -/

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

/-- An opener's own leaf set contains its stored type's — an opener
IS a free variable, so its leaves are itself and its type's. -/
theorem openPisAtFvars_typeLeaves {k : Nat} {e : Expr} {d : Nat} {fvs : List Expr}
    {body : Expr} (hop : openPisAtFvars k e d = some (fvs, body)) :
    ∀ x ∈ fvs, ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves, l ∈ x.fvarLeaves := by
  intro x hx l hl
  obtain ⟨q, hq⟩ := List.getElem?_of_mem hx
  obtain ⟨ty, rfl⟩ := ConLeche.openPisAtFvars_index _ _ _ hop q x hq
  simp only [Expr.fvarTypeD] at hl
  simp only [Expr.fvarLeaves, List.mem_cons]
  exact Or.inr hl

/-- **`hcbF`** — the frame's openers carry consts-bounded annotations
as soon as the three SUBJECTS do (`openPisAtFvars_constsBound`, three
times).  The bundle carries this for the rule's frame predicate
(§1). -/
theorem blockRuleHcbF_of {envT : Env} {rP nF nR : Nat} {recTy crest ihTele' o₁ o₂ o₃ : Expr}
    {fvsPref fvsF fvsIh : List Expr}
    (h₁ : openPisAtFvars rP recTy 0 = some (fvsPref, o₁))
    (h₂ : openPisAtFvars nF crest rP = some (fvsF, o₂))
    (h₃ : openPisAtFvars nR ihTele' (rP + nF) = some (fvsIh, o₃))
    (hc₁ : ConstsBound envT recTy) (hc₂ : ConstsBound envT crest)
    (hc₃ : ConstsBound envT ihTele') :
    ∀ x ∈ fvsPref ++ fvsF ++ fvsIh, ConstsBound envT x := by
  intro x hx
  rcases List.mem_append.mp hx with hx' | hx'
  · rcases List.mem_append.mp hx' with hx'' | hx''
    · exact (openPisAtFvars_constsBound rP hc₁ h₁).1 x hx''
    · exact (openPisAtFvars_constsBound nF hc₂ h₂).1 x hx''
  · exact (openPisAtFvars_constsBound nR hc₃ h₃).1 x hx'

/-- **`hclF`** — the frame is LEAF-CLOSED: every leaf of an opener's
stored type is itself an opener.  Each of the three openings is
`openPisAtFvars_leaves` at its own subject, and the three subjects'
leaves are openers of the openings before it: the recursor type is
fvar-free, the constructor's telescope was instantiated at the prefix
openers (`instPisAt_fvarLeaves` at an fvar-free stored type), and the
generated tower's leaves are `hfv₃`'s. -/
theorem blockRuleHclF_of {rP nF nR : Nat}
    {recTy crest ihTele' o₁ o₂ o₃ : Expr} {fvsPref fvsF fvsIh : List Expr}
    (h₁ : openPisAtFvars rP recTy 0 = some (fvsPref, o₁))
    (h₂ : openPisAtFvars nF crest rP = some (fvsF, o₂))
    (h₃ : openPisAtFvars nR ihTele' (rP + nF) = some (fvsIh, o₃))
    (hf₁ : recTy.hasFvar = false)
    -- the constructor's telescope draws its leaves from the prefix (lane NESTIND: at an
    -- outside major it is instantiated at the major's parameters, not the prefix openers)
    (hcrestLeaf : ∀ l ∈ crest.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref)
    (hfv₃ : ∀ l ∈ ihTele'.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF) :
    ∀ x ∈ fvsPref ++ fvsF ++ fvsIh, ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF ++ fvsIh := by
  have hrecNil : recTy.fvarLeaves = [] := ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hf₁
  have hlP : ∀ a ∈ fvsPref, ∀ l ∈ a.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref := by
    intro a ha l hl
    rcases openPisAtFvars_leaves rP h₁ l (Or.inr ⟨a, ha, hl⟩) with h' | h'
    · rw [hrecNil] at h'; exact nomatch h'
    · exact h'
  intro x hx l hl
  rcases List.mem_append.mp hx with hx' | hx'
  · rcases List.mem_append.mp hx' with hx'' | hx''
    · exact List.mem_append_left _ (List.mem_append_left _
        (hlP x hx'' l (openPisAtFvars_typeLeaves h₁ x hx'' l hl)))
    · rcases openPisAtFvars_leaves nF h₂ l
        (Or.inr ⟨x, hx'', openPisAtFvars_typeLeaves h₂ x hx'' l hl⟩) with h' | h'
      · exact List.mem_append_left _ (List.mem_append_left _ (hcrestLeaf l h'))
      · exact List.mem_append_left _ (List.mem_append_right _ h')
  · rcases openPisAtFvars_leaves nR h₃ l
      (Or.inr ⟨x, hx', openPisAtFvars_typeLeaves h₃ x hx' l hl⟩) with h' | h'
    · exact List.mem_append_left _ (hfv₃ l h')
    · exact List.mem_append_right _ h'

/-! ### 40.2 The reading arguments — `hF` and `hI`

`hP` is §35's (`blockRulePdomsAV_reads`).  The other two segments are
spelled with `readOpenedDoms` (`BlockRecData.lean`), which is a
reading BY CONSTRUCTION: its `l`-th entry IS the `l`-th opener's
reading whenever that reading exists at all.  So both segments reduce
to an EXISTENCE statement, which is the shape their owners already
prove — `denoteMeta_openPis`' per-binder output for the fields, and
the `ih` opener battery's `_exists` form for the openers.

`readOpenedDoms`' own equations do not leave its module (a proof-tier
`def`'s body is private under the module system), so the bridge is
`readOpenedDoms_eq` at a witness list built from the readings
themselves. -/


/-! ### 40.4 `hokA`, segment by segment

`hokA` is stated at the ASCENDING frame, so its three segments are a
`take` split and nothing else — but the split must be taken on the
ascending side (a `take`-shaped reading of the REVERSED context
lands on the wrong valuation).  Each segment is
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
off the recursor type's binder data.  The identification is `readOpenedDoms_eq` at
that data, and it is what lets the bundle's consumers keep the
spelling they already use (`blockRecHpref_run`, `BlockRuleDataAt`). -/

/-! ### 40.6 The CONCLUSION's two scoping arguments

`hbC` and `hleafC` are about the term the rule's residue is compared
against — the recursor's stored type instantiated at the rule's
prefix openers, the constructor's result index arguments and the
fired major.  Every one of those arguments is built from the frame's
openers over two STORED (fvar-free) types, so both arguments come off
`instPisAt`'s two batteries once the spine's entries are known to be
bvar-closed. -/

/-- **A prefix opener's leaves are prefix openers** (the recursor type is
fvar-free). -/
theorem prefLeaves_of_open {rP : Nat} {recTy o₁ : Expr} {fvsPref : List Expr}
    (h₁ : ConLeche.openPisAtFvars rP recTy 0 = some (fvsPref, o₁))
    (hf₁ : recTy.hasFvar = false) :
    ∀ a ∈ fvsPref, ∀ l ∈ a.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref := by
  have hrecNil : recTy.fvarLeaves = [] := ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hf₁
  intro a ha l hl
  rcases openPisAtFvars_leaves rP h₁ l (Or.inr ⟨a, ha, hl⟩) with h' | h'
  · rw [hrecNil] at h'; exact nomatch h'
  · exact h'

/-- **The constructor's telescope, instantiated at arguments drawing their
leaves from the prefix, draws its leaves from the prefix.** -/
theorem crestLeaf_of_inst {cty crest : Expr} {fvsPref ds cpref : List Expr}
    (hCf : cty.hasFvar = false)
    (hinst : ConLeche.Expr.instPisAt ds cty = some (cpref, crest))
    (hdsL : ∀ a ∈ ds, ∀ l ∈ a.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref) :
    ∀ l ∈ crest.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref := by
  have hctyNil : cty.fvarLeaves = [] := ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hCf
  intro l hl
  rcases ConLeche.instPisAt_fvarLeaves _ cty hinst l hl with h' | ⟨a, ha, hla⟩
  · rw [hctyNil] at h'; exact nomatch h'
  · exact hdsL a ha l hla

/-- **`hbC` and `hleafC`, from the run's own conclusion equation**: the
rule's conclusion is bvar-closed and draws its leaves from the
frame (lane NESTIND: at any major — the fired constructor at the
major's parameters `ds`, which draw their leaves from the prefix, and
the index arguments past the major's parameter count `nPc`). -/
theorem blockRuleConclClosed_of {nPc rP nF : Nat}
    {recTy crest cbody o₁ concl : Expr} {fvsPref fvsF ds : List Expr}
    {cname : Name} {lvls : List Level}
    (h₁ : ConLeche.openPisAtFvars rP recTy 0 = some (fvsPref, o₁))
    (h₂ : ConLeche.openPisAtFvars nF crest rP = some (fvsF, cbody))
    (hf₁ : recTy.hasFvar = false)
    (hb₁ : recTy.looseBVarsBounded 0 = true) (hb₂ : crest.looseBVarsBounded 0 = true)
    (hcrestLeaf : ∀ l ∈ crest.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref)
    (hdsB : ∀ a ∈ ds, a.looseBVarsBounded 0 = true)
    (hdsL : ∀ a ∈ ds, ∀ l ∈ a.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref)
    (hpr : ConLeche.Expr.instPisAtLift
        (fvsPref ++ cbody.getAppArgs.drop nPc
          ++ [Expr.mkAppN (.const cname lvls) (ds ++ fvsF)]) recTy = some concl) :
    concl.looseBVarsBounded 0 = true ∧
      ∀ l ∈ concl.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF := by
  have hrecNil : recTy.fvarLeaves = [] := ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hf₁
  have hcb : cbody.looseBVarsBounded 0 = true := (openPisAtFvars_bounded nF h₂ hb₂).1
  -- an opener's own leaves are openers
  have hlP := prefLeaves_of_open h₁ hf₁
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
  have hargs : ∀ a ∈ fvsPref ++ cbody.getAppArgs.drop nPc
      ++ [Expr.mkAppN (.const cname lvls) (ds ++ fvsF)],
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
      · exact hdsB x hx'
      · exact openPisAtFvars_fvars_closed h₂ x hx'
  -- the lift IS the plain instantiation at those arguments
  rw [ConLeche.instPisAtLift_eq_instPisAt hargs, Option.map_eq_some_iff] at hpr
  obtain ⟨pr, hinst, rfl⟩ := hpr
  obtain ⟨ds', res⟩ := pr
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
    · exact List.mem_append_left _ (hdsL x hx' l hlx)
    · exact hlF x hx' l hlx

/-! ### 40.7 The GENERATED `ih` tower's two syntactic facts

`blockIhPis` (`Kernel/Inductives/BlockRec.lean`) is the ONE piece of a
rule's frame the kernel never types: the check opens
`ihTele.instantiateList (fvsPref ++ fvsF).reverse` and types the
RESIDUE under it, so nothing in the run says that the tower itself is
a closed term of the rule's frame.  §40.1 takes both facts as premises
(`hihfv`, `hihlb`) — as does `blockRuleHopener_of` —
and this is their proof: an induction over the generator, whose
binders are the constructor's own telescope moved to the rule's frame
(`structTeleAt`) over the CALLEE's stored type instantiated at a spine
of `bvar`s (`instPisAtLift`).

The arithmetic is the whole content.  A field's telescope entry `k` is
spelled at the CONSTRUCTOR's frame (`nP + i + k`) and `structIdxAt`
moves it by `nF - i + l` and then by `o = rP - nP`, which lands it at
`rP + nF + l + k` — exactly where the rule's frame has it — and that
identity is where `nP ≤ rP` and `i < nF` (the key's own field index)
are used. -/


/-! ### 40.8 `hokA`'s FIELD segment, from the CONSTRUCTOR's tower

The field openers' domains are the CONSTRUCTOR's, read at the
constructor's own frame and lifted past the `o = rP - nP` binders the
recursor's prefix carries between the parameters and the fields
(`ctorResidual_read_lift`).  Their grading is therefore the
constructor stage's — `CtorDataI.okTy` through `piTeleAV_graded` — but
at a spine that fits the CONSTRUCTOR's parameter domains, while the
rule's frame supplies values fitting the RECURSOR's.  This section
owns everything on the constructor's side of that seam: the lift
transfer and the tower's grading at an arbitrary entry.  The PARAMETER
HOP — that the rule frame's first `nP` values fit the constructor's
parameter domains — is the check's own chain (the recursor's parameter
domains against the type former's, `checkBlockRecTys`; the
constructor's against the former's, `checkSumCtor`'s
`checkStructDomsAt`), and §40.9 runs it. -/

/-- **A `.pi` tower's entry `n` is graded at its own fitting spine** —
`prefixDoms_graded_of_tower` at the whole peel. -/
theorem towerDom_graded_of_tower {rds : List (Nat × Nat × AnnotTerm)} {cc : AnnotTerm}
    (hwd : ∀ ρ : Nat → V, WellDenotedV V ρ (mkPisAV rds cc))
    {n : Nat} (hn : n < rds.length) {ρ : Nat → V} {ys : List V}
    (hys : SpineFit ρ ((rds.take n).map (·.2.2)) ys) :
    WellDenotedV V (consList ys ρ) (rds.getD n default).2.2 := by
  have hys' : SpineFit ρ (((rds.take rds.length).map fun d : Nat × Nat × AnnotTerm => d.2.2).take n)
      ys := by
    rw [List.take_length, ← List.map_take]
    exact hys
  have h := prefixDoms_graded_of_tower (V := V) (rds := rds) (cc := cc) (Nat.le_refl _) hwd hn hys'
  rw [List.take_length, List.getD_eq_getElem?_getD, List.getElem?_map] at h
  obtain ⟨d, hd⟩ : ∃ d, rds[n]? = some d := ⟨rds[n]'hn, List.getElem?_eq_getElem hn⟩
  rw [hd, Option.map_some, Option.getD_some] at h
  rwa [List.getD_eq_getElem?_getD, hd, Option.getD_some]

/-- **`hokA`'s FIELD segment, from the CONSTRUCTOR's tower.** -/
theorem blockRuleFseg_of_ctorTower {ds : List (Nat × Nat × AnnotTerm)} {bodyC : AnnotTerm}
    {nP nF o q : Nat}
    (hwd : ∀ ρ : Nat → V, WellDenotedV V ρ (mkPisAV ds bodyC))
    (hlenD : ds.length = nP + nF) (hq : q < nF)
    {σ : Nat → V} {ps ms ys : List V} (hms : ms.length = o)
    (hps : SpineFit σ ((ds.take nP).map (·.2.2)) ps)
    (hys : SpineFit (consList ms (consList ps σ))
      (((liftDoms o 0 (ds.drop nP)).map (·.2.2)).take q) ys) :
    WellDenotedV V (consList ys (consList ms (consList ps σ)))
      (((liftDoms o 0 (ds.drop nP)).map (·.2.2)).getD q default) := by
  have hdrop : (ds.drop nP).length = nF := by rw [List.length_drop, hlenD]; omega
  -- the entry, unlifted
  have hent : ((liftDoms o 0 (ds.drop nP)).map (·.2.2)).getD q default
      = (((ds.drop nP).getD q default).2.2).liftN o q := by
    obtain ⟨d, hd⟩ : ∃ d, (ds.drop nP)[q]? = some d :=
      ⟨(ds.drop nP)[q]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, liftDoms_getElem?, hd,
      List.getD_eq_getElem?_getD, hd]
    simp only [Option.map_some, Option.getD_some, Nat.zero_add]
  -- the spine, at the unlifted domains and the shifted frame
  have hshift : shiftE o 0 (consList ms (consList ps σ)) = consList ps σ := by
    rw [← hms]; exact shiftE_consList ms (consList ps σ)
  have hys' : SpineFit (consList ps σ) (((ds.drop nP).take q).map (·.2.2)) ys := by
    rw [← hshift]
    refine (spineFit_liftDoms (V := V) o).mp ?_
    rw [← liftDoms_take, List.map_take]
    exact hys
  have hylen : ys.length = q := by
    rw [SpineFit.length_eq hys', List.length_map, List.length_take]; omega
  -- the grading, at the constructor's own tower
  rw [hent]
  refine (WellDenotedV_liftN V o _ q (consList ys (consList ms (consList ps σ)))).mpr ?_
  have hfr : shiftE o q (consList ys (consList ms (consList ps σ))) = consList ys (consList ps σ) := by
    rw [← hylen, shiftE_consList_len, hshift]
  rw [hfr]
  have hnq : nP + q < ds.length := by omega
  have hgd : (ds.getD (nP + q) default).2.2 = ((ds.drop nP).getD q default).2.2 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
  have hsplit : (ds.take (nP + q)).map (fun d : Nat × Nat × AnnotTerm => d.2.2)
      = (ds.take nP).map (·.2.2) ++ ((ds.drop nP).take q).map (·.2.2) := by
    rw [← List.map_append, List.take_add]
  rw [← hgd, ← consList_append]
  exact towerDom_graded_of_tower hwd hnq (by rw [hsplit]; exact SpineFit.append hps hys')

/-! ### 40.9 `hokA`'s FIELD segment — THE PARAMETER HOP

§40.8 left one premise: `blockRuleFseg_of_ctorTower`'s `hps`, the rule
frame's first `nP` values fitting the CONSTRUCTOR's parameter domains,
while the frame supplies them fitting the RECURSOR's.  The check
compares both against the same third thing — the MEMBER'S TYPE FORMER's
opened parameter telescope: the recursor's by `checkBlockRecTys`'
`checkBlockDefEqList` at depth `nP`, the constructor's by
`checkSumCtor`'s `checkStructDomsAt` at each binder's own depth.

The constructor half of the chain is already a semantic fact — it is
what `BlockCtorsStage.frames` carries, `paramFrames` at the pins
(`ctorFramesGen`'s first output).  The recursor half is
the type record's `hparams` (`RecTyEntry`,
`Verify/Inductives/BlockRecRun.lean`); this section is its run-level
consumer.

Which currency each half speaks is forced by the CHECK, not chosen
here: `checkBlockDefEqList` compares at ONE fixed depth (`nP`), which
is `prefixDoms_spineFit`'s shape — the certified hop was written for a
stage of exactly this form — while `checkStructDomsAt` compares at
each binder's own depth, which is `paramFrames`' shape and yields a
`Sat`-iff.  So the recursor hop is a `SpineFit` transfer and the
constructor hop a satisfaction transfer, and `spineFit_iff_sat` is the
one bridge between them. -/

section ParamHop

/-- A spine fits a domain list exactly when the frame it pushes onto
satisfies the reversed list.  This is the bridge between the two
currencies the CHECK forces on the parameter chain's two halves — a
`SpineFit` transfer on the recursor's side (`prefixDoms_spineFit`, at
`checkBlockDefEqList`'s fixed depth) and a satisfaction transfer on
the constructor's (`paramFrames`, at `checkStructDomsAt`'s per-binder
depths). -/
theorem spineFit_iff_sat {Ds : List AnnotTerm} {as : List V} {ρ : Nat → V}
    (hlen : as.length = Ds.length) :
    SpineFit ρ Ds as ↔ Sat V Ds.reverse (consList as ρ) :=
  ⟨fun hsp => by simpa using sat_of_spineFit (Δ₀ := ([] : List AnnotTerm)) (Sat_nil V ρ) hsp,
    spineFit_of_sat_consList hlen⟩

/-- **THE PARAMETER HOP, at the run**: a spine fitting recursor `c`'s
first `nP` prefix domains fits the TYPE FORMER's parameter telescope
of the member `c` eliminates.

`prefixDoms_spineFit` at the two `nP`-openings — the recursor's stored
type split at `nP` (`openPisAtFvars_split`) and the former's — with
the check's own comparison as the `hdeq` disjunction's second
orientation (the stage compares the FORMER's domains against the
recursor's, in that order). -/
theorem blockRecParamHop_run {envC : Env} {p : ConLeche.BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hm : memR c) (hr : rs[c]? = some r) (ψ : Name → Nat)
    {cvTa : ConstantVal} {caps : ConLeche.IndCaps}
    (hcvTa : cvTas[p.toBlockShape.recTgtAt c]? = some cvTa)
    (hfT : envC.find? cvTa.name = some (.indInfo cvTa caps))
    {nFull : Nat} {resSort : Level} {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData mpC.base2 cvTa nFull resSort pps) (hle : p.nP ≤ nFull)
    {σ : Nat → V} {ps : List V}
    (hps : SpineFit σ
      ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).take p.nP) ps) :
    SpineFit σ (((pps ψ).take p.nP).map (·.2.2)) ps := by
  have hcl : c < rs.length := (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.recStageG_tyAt h hm hr
  have hopT := TE.hopenT
  have hopR := TE.hopen
  have hpins := TE.hparams
  obtain rfl : TE.cvTa = cvTa := Option.some.inj (TE.hcvTa.symm.trans hcvTa)
  -- the recursor type's own `nP`-opening, off the stage's `mI + 1` one
  have hnP := TE.nP_le
  have hmI : p.toBlockShape.rulePrefixAt c ≤ p.toBlockShape.majorIdxAt c :=
    blockRecHrPle (p := p) h hcl
  obtain ⟨mm, hmm⟩ : ∃ mm, p.toBlockShape.majorIdxAt c + 1 = p.nP + mm :=
    ⟨p.toBlockShape.majorIdxAt c + 1 - p.nP, by omega⟩
  rw [hmm] at hopR
  obtain ⟨fvsA, fvsA', oA, hopA, -, hfvsEq⟩ := openPisAtFvars_split p.nP hopR
  have hlA : fvsA.length = p.nP := ConLeche.Verify.openPisAtFvars_length _ hopA
  have htakeA : TE.fvs.take p.nP = fvsA := by
    rw [hfvsEq, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  -- and the one at the RULE PREFIX, which is where the domains are read
  obtain ⟨mm2, hmm2⟩ : ∃ mm2, p.toBlockShape.majorIdxAt c + 1
      = p.toBlockShape.rulePrefixAt c + mm2 :=
    ⟨p.toBlockShape.majorIdxAt c + 1 - p.toBlockShape.rulePrefixAt c, by omega⟩
  have hopR2 : openPisAtFvars (p.toBlockShape.rulePrefixAt c + mm2) r.1.type 0
      = some (TE.fvs, TE.concl) := by rw [← hmm2, hmm]; exact hopR
  obtain ⟨fvsP, -, oP, hopP, -, -⟩ := openPisAtFvars_split _ hopR2
  -- the two domain lists
  have hlenPd := blockRulePdomsAV_length hμ mpC h hr ψ
  have hlenA : ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).take p.nP).length
      = p.nP := by rw [List.length_take, hlenPd]; omega
  have hlenB : (((pps ψ).take p.nP).map (·.2.2)).length = p.nP := by
    rw [List.length_map, List.length_take, hFD.len ψ]; omega
  -- the FORMER's opening, read and graded
  obtain ⟨hTf, -, -, hTb, -⟩ := mpC.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfT)
  simp only [ConLeche.ConstantInfo.toConstantVal] at hTf hTb
  obtain ⟨Γt, Rt, hteleT, hOT⟩ := opened_of hopT hTf hTb (hFD.read ψ) (hFD.okTy ψ)
  obtain ⟨pps', hst', hΓt⟩ := stripPisAV_of_piTeleAV hteleT
  have hst'' := stripPisAV_mkPisAV_take p.nP (pps ψ) (AnnotTerm.sort (resSort.eval ψ))
    (by rw [hFD.len ψ]; exact hle)
  obtain ⟨rfl, -⟩ := Prod.mk.injEq _ _ _ _ ▸ Option.some.inj (hst'.symm.trans hst'')
  subst hΓt
  -- the certified hop
  refine prefixDoms_spineFit (V := V) (ψ := ψ) (fuel := F) hμ mpC hopA hopT
    (recStage_tyClosed h hr).1
    (Expr.WScoped.of_not_hasFvar hTf) (recStage_tyClosed h hr).2 hTb
    hlenA hlenB ?_ ?_ ?_ ?_ ?_ hps
  · -- the recursor's readings, at the `nP`-opening
    intro l x hx
    have hlt : l < p.nP := by
      have := (List.getElem?_eq_some_iff.mp hx).1; omega
    have hxP : fvsP[l]? = some x := by
      rw [openPisAtFvars_prefix_getElem (by omega) hopP hopA l hlt]; exact hx
    rw [blockRulePdomsAV_reads hμ mpC h hr ψ hopP l x hxP, getD_take_of_lt hlt]
  · -- the former's readings, off its opening
    intro l x hx
    have hlt : l < p.nP := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      rw [ConLeche.Verify.openPisAtFvars_length _ hopT] at this; exact this
    rw [hOT.doms l x hx, List.getD_eq_getElem?_getD,
      getElem?_reverse_entry hlenB hlt, Option.getD_some]
  · -- the recursor's prefix domains are graded
    intro i hi ρ ys hys
    rw [getD_take_of_lt hi]
    refine blockRulePdomsAV_graded hμ mpC h hr ψ i (by omega) ρ ys ?_
    rwa [List.take_take, show min i p.nP = i from by omega] at hys
  · -- the former's parameter domains are graded
    intro i hi ρ ys hys
    have hlenPP : p.nP ≤ (pps ψ).length := by rw [hFD.len ψ]; exact hle
    exact prefixDoms_graded_of_tower (V := V) (cc := AnnotTerm.sort (resSort.eval ψ))
      hlenPP (hFD.okTy ψ) hi hys
  · -- the check's own comparison, in its own orientation
    intro i hi
    exact Or.inr (by rw [htakeA] at hpins; exact hpins i hi)

/-- **THE PARAMETER HOP**: the rule frame's first `nP` values fit the
CONSTRUCTOR's parameter domains.

The two halves of the check's chain, composed through the type former:
the recursor's comparison (`blockRecParamHop_run`, a `SpineFit`
transfer) and the constructor's (`hframes`, a satisfaction transfer —
`BlockCtorsStage.frames` at this member and constructor, which is
`paramFrames` at `checkStructDomsAt`'s pins).  `hframes` is bounded by
that clause and by nothing wider: it is about THIS constructor's
domains and THIS member's former, at this `ψ`. -/
theorem blockRuleParamFit_run {envC : Env} {p : ConLeche.BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hm : memR c) (hr : rs[c]? = some r) (ψ : Name → Nat)
    {cvTa : ConstantVal} {caps : ConLeche.IndCaps}
    (hcvTa : cvTas[p.toBlockShape.recTgtAt c]? = some cvTa)
    (hfT : envC.find? cvTa.name = some (.indInfo cvTa caps))
    {nFull : Nat} {resSort : Level} {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData mpC.base2 cvTa nFull resSort pps) (hle : p.nP ≤ nFull)
    {ds : List (Nat × Nat × AnnotTerm)} {nF : Nat} (hlenD : ds.length = p.nP + nF)
    (hframes : ∀ ρ : Nat → V, Sat V (((pps ψ).take p.nP).map (·.2.2)).reverse ρ ↔
      Sat V ((ds.take p.nP).map (·.2.2)).reverse ρ)
    {σ : Nat → V} {ps : List V}
    (hps : SpineFit σ
      ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).take p.nP) ps) :
    SpineFit σ ((ds.take p.nP).map (·.2.2)) ps := by
  have hT := blockRecParamHop_run (hm := hm) hμ mpC h hr ψ hcvTa hfT hFD hle hps
  have hlenT : (((pps ψ).take p.nP).map (·.2.2)).length = p.nP := by
    rw [List.length_map, List.length_take, hFD.len ψ]; omega
  have hlenC : ((ds.take p.nP).map (·.2.2)).length = p.nP := by
    rw [List.length_map, List.length_take, hlenD]; omega
  have hlenps : ps.length = p.nP := by rw [SpineFit.length_eq hT, hlenT]
  exact (spineFit_iff_sat (by rw [hlenps, hlenC])).mpr
    ((hframes _).mp ((spineFit_iff_sat (by rw [hlenps, hlenT])).mp hT))

/-- **`hokA`'s FIELD segment, AT THE RUN.**  §40.8's model reasoning
with its last premise discharged: the frame's prefix values split at
`nP`, the first `nP` of them fit the constructor's parameter domains
by the hop, and the rest are the `o = rP - nP` binders the recursor's
prefix carries between the parameters and the fields. -/
theorem blockRuleFseg_of_run {envC : Env} {p : ConLeche.BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hm : memR c) (hr : rs[c]? = some r) (ψ : Name → Nat)
    {cvTa : ConstantVal} {caps : ConLeche.IndCaps}
    (hcvTa : cvTas[p.toBlockShape.recTgtAt c]? = some cvTa)
    (hfT : envC.find? cvTa.name = some (.indInfo cvTa caps))
    {nFull : Nat} {resSort : Level} {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData mpC.base2 cvTa nFull resSort pps) (hle : p.nP ≤ nFull)
    {ds : List (Nat × Nat × AnnotTerm)} {bodyC : AnnotTerm} {nF o : Nat}
    (hwd : ∀ ρ : Nat → V, WellDenotedV V ρ (mkPisAV ds bodyC))
    (hlenD : ds.length = p.nP + nF)
    (hframes : ∀ ρ : Nat → V, Sat V (((pps ψ).take p.nP).map (·.2.2)).reverse ρ ↔
      Sat V ((ds.take p.nP).map (·.2.2)).reverse ρ)
    (ho : p.toBlockShape.rulePrefixAt c = p.nP + o) :
    ∀ q, q < nF → ∀ (σ : Nat → V) (xs ys : List V),
      SpineFit σ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) xs →
      SpineFit (consList xs σ) (((liftDoms o 0 (ds.drop p.nP)).map (·.2.2)).take q) ys →
      WellDenotedV V (consList ys (consList xs σ))
        (((liftDoms o 0 (ds.drop p.nP)).map (·.2.2)).getD q default) := by
  intro q hq σ xs ys hxs hys
  have hxlen : xs.length = p.toBlockShape.rulePrefixAt c := by
    rw [SpineFit.length_eq hxs, blockRulePdomsAV_length hμ mpC h hr ψ]
  have hms : (xs.drop p.nP).length = o := by rw [List.length_drop, hxlen, ho]; omega
  have hps := blockRuleParamFit_run (hm := hm) hμ mpC h hr ψ hcvTa hfT hFD hle hlenD hframes
    (spineFit_take_any hxs p.nP)
  have hsplit : xs.take p.nP ++ xs.drop p.nP = xs := List.take_append_drop _ _
  rw [← hsplit, consList_append] at hys ⊢
  exact blockRuleFseg_of_ctorTower hwd hlenD hq hms hps hys

end ParamHop

/-! ### 40.10 `hokA`'s `ih` SEGMENT, from the FIELD's telescope

The `ih` opener at position `q` reads to `mkPisAV (ihTeleAtR nF o i q
(rebit (pwBit ψ pw) tl)) conclA` (`denoteMeta_blockIhOpenerTy`,
`BlockRecOpenerRead.lean`): the field's OWN telescope `tl`, read at
the constructor's frame, moved to the rule's — each entry `k` lifted
past the `nF - i` later fields at the telescope's cutoff `k` and past
the prefix's `o = rP - nP` extras at the fields' cutoff
(`ihIdxAtM`) — over whatever the guarded call reads to.

Two observations cut the algebra in half.

*The `ih` level is not a third lift.*  `ihIdxAtM nF o i l m` is
`ihIdxAtM (nF + l) o i 0 m` whenever `i ≤ nF` (`ihIdxAtM_merge`): the
`l` ih values already bound sit exactly where fields sit, so the whole
segment is the `l = 0` statement at the longer field list `fs ++ ys`.
That is why this section reuses `interp_ihIdxAtM_rule` and
`spineFit_ihTeleAtGo_rule` (`BlockRecTyping.lean`) verbatim instead of
restating them at an ih frame.

*The BIT clause is guarded.*  `WellDenotedV` is `WellDenoted ∧
AnnotValid` and `AnnotValid`'s `.pi` clause carries a third conjunct
`v = 0 → ∀ x ∈ˢ interp ρ A, interp (cons x ρ) B ∈ˢ univZero`
(`Model/Annot/Valid.lean`).  `rebit` stamps EVERY binder of the moved
telescope with `pwBit ψ pw`, which is zero exactly at a
`Prop`-eliminating recursor (`pwBit_zeronessOf`) — so at a non-`Prop`
elimination the clause is VACUOUS, and where it bites it reduces to
ONE fact about the tower's body, the guarded call's reading being a
truth value.  It is therefore a premise of this section
(`h0`), guarded by `b = 0` and by nothing wider, and its producer is
the conclusion-sort fact (`blockRuleIseg_h0_of_conclAt`).

What the segment consumes about the telescope is its hereditary
grading AT THE FIELD's frame — `FieldsOkB 0` and `FieldsValid` of
`tl.map (·.2.2)` under the parameters and the `i` earlier fields —
which is what peeling the constructor's own tower at the field's entry
gives (`recEntry`/`reflEntry`, `BlockData.lean`). -/

section IhSeg

open ConLeche.Semantics

variable {ρ : Nat → V}

/-- **The `ih` level is not a third lift**: the `l` ih values already
bound stand exactly where fields stand, so the move to ih level `l` is
the move at level `0` over `nF + l` "fields". -/
theorem ihIdxAtM_merge {nF o i l m : Nat} (hi : i ≤ nF) (E : AnnotTerm) :
    ihIdxAtM nF o i l m E = ihIdxAtM (nF + l) o i 0 m E := by
  unfold ihIdxAtM
  rw [show nF - i + l = nF + l - i + 0 from by omega,
    show nF + l + m = nF + l + 0 + m from by omega]

/-- `ihIdxAtM_merge`, carried down the telescope. -/
theorem ihTeleAtGo_merge {nF o i l : Nat} (hi : i ≤ nF) :
    ∀ (k : Nat) (tl : List (Nat × Nat × AnnotTerm)),
      ihTeleAtGo nF o i l k tl = ihTeleAtGo (nF + l) o i 0 k tl
  | _, [] => rfl
  | k, d :: tl => by
    show (d.1, d.2.1, ihIdxAtM nF o i l k d.2.2) :: ihTeleAtGo nF o i l (k + 1) tl
      = (d.1, d.2.1, ihIdxAtM (nF + l) o i 0 k d.2.2) :: ihTeleAtGo (nF + l) o i 0 (k + 1) tl
    rw [ihIdxAtM_merge hi, ihTeleAtGo_merge hi (k + 1) tl]

/-- The whole moved telescope, at the longer field list. -/
theorem ihTeleAtR_merge {nF o i l : Nat} (hi : i ≤ nF) (tl : List (Nat × Nat × AnnotTerm)) :
    ihTeleAtR nF o i l tl = ihTeleAtR (nF + l) o i 0 tl :=
  ihTeleAtGo_merge hi 0 tl

/-- **One entry's GRADING across the two frames** —
`interp_ihIdxAtM_rule`'s cancellation in the `WellDenotedV` currency:
the outer lift `o` cancels the prefix's extra binders `x⃗.drop nP`, the
inner `nF - i` the later fields `f⃗.drop i`. -/
theorem wellDenotedV_ihIdxAtM_rule {nF o i m : Nat} {xs fs bs as : List V}
    (hxl : xs.length = as.length + o) (htake : xs.take as.length = as)
    (hfl : fs.length = nF) (hbl : bs.length = m) (E : AnnotTerm) :
    WellDenotedV V (consList bs (consList (xs ++ fs) ρ)) (ihIdxAtM nF o i 0 m E)
      ↔ WellDenotedV V (consList bs (consList (fs.take i) (consList as ρ))) E := by
  have hdrop : (xs.drop as.length).length = o := by rw [List.length_drop, hxl]; omega
  have hfd : (fs.drop i).length = nF - i := by rw [List.length_drop, hfl]
  have e1 : shiftE o (nF + m) (consList bs (consList (xs ++ fs) ρ))
      = consList (fs ++ bs) (consList as ρ) := by
    rw [consList_ruleFrame,
      show nF + m = (fs ++ bs).length from by rw [List.length_append, hfl, hbl],
      shiftE_consList_len, shiftE_drop_consList xs as.length hdrop ρ, htake]
  have e2 : shiftE (nF - i) m (consList (fs ++ bs) (consList as ρ))
      = consList bs (consList (fs.take i) (consList as ρ)) := by
    rw [consList_append, ← hbl, shiftE_consList_len,
      shiftE_drop_consList fs i hfd (consList as ρ)]
  unfold ihIdxAtM
  simp only [Nat.add_zero]
  rw [WellDenotedV_liftN, e1, WellDenotedV_liftN, e2]

/-- **The field telescope's HEREDITARY grading across the two
frames** — `spineFit_ihTeleAtGo_rule`'s induction in the grading
currency, `FieldsOkB 0` and `FieldsValid` together because each step
needs both halves of `WellDenotedV` to cross. -/
theorem fieldsWD_ihTeleAtGo_rule {nF o i : Nat} {xs fs as : List V}
    (hxl : xs.length = as.length + o) (htake : xs.take as.length = as)
    (hfl : fs.length = nF) :
    ∀ (tl : List (Nat × Nat × AnnotTerm)) (ws : List V),
      FieldsOkB 0 (consList ws (consList (fs.take i) (consList as ρ))) (tl.map (·.2.2)) →
      FieldsValid (consList ws (consList (fs.take i) (consList as ρ))) (tl.map (·.2.2)) →
      FieldsOkB 0 (consList ws (consList (xs ++ fs) ρ))
          ((ihTeleAtGo nF o i 0 ws.length tl).map (·.2.2)) ∧
        FieldsValid (consList ws (consList (xs ++ fs) ρ))
          ((ihTeleAtGo nF o i 0 ws.length tl).map (·.2.2))
  | [], _, _, _ => ⟨trivial, trivial⟩
  | d :: tl, ws, hF, hV => by
    rw [List.map_cons] at hF hV
    obtain ⟨hok, -, hrest⟩ := hF
    obtain ⟨hval, hvrest⟩ := hV
    have hmv := wellDenotedV_ihIdxAtM_rule (ρ := ρ) (i := i) hxl htake hfl (rfl : ws.length = _)
      d.2.2
    have hint := interp_ihIdxAtM_rule (ρ := ρ) (i := i) hxl htake hfl (rfl : ws.length = _) d.2.2
    have htop : WellDenotedV V (consList ws (consList (xs ++ fs) ρ))
        (ihIdxAtM nF o i 0 ws.length d.2.2) := hmv.mpr ⟨hok, hval⟩
    refine ⟨⟨htop.1, fun h0 => absurd rfl h0, fun a ha => ?_⟩, ⟨htop.2, fun a ha => ?_⟩⟩
    · rw [hint] at ha
      have h := fieldsWD_ihTeleAtGo_rule hxl htake hfl tl (ws ++ [a])
        (by rw [← consList_snoc']; exact hrest a ha) (by rw [← consList_snoc']; exact hvrest a ha)
      rw [List.length_append, List.length_singleton, ← consList_snoc' a ws] at h
      exact h.1
    · rw [hint] at ha
      have h := fieldsWD_ihTeleAtGo_rule hxl htake hfl tl (ws ++ [a])
        (by rw [← consList_snoc']; exact hrest a ha) (by rw [← consList_snoc']; exact hvrest a ha)
      rw [List.length_append, List.length_singleton, ← consList_snoc' a ws] at h
      exact h.2

/-- **`hokA`'s `ih` ENTRY, from the FIELD's telescope.**  The opener's
reading is the field's telescope moved to the rule's frame over the
guarded call's reading; its grading is the telescope's hereditary
grading at the CONSTRUCTOR's frame, transported entry by entry, over
the body's — with the bit clause guarded by `b = 0` and reduced, there,
to the body's reading being a truth value. -/
theorem blockRuleIhEntry_of_fieldTele {nF o i l b : Nat} {xs fs ys as : List V}
    {tl : List (Nat × Nat × AnnotTerm)} {conclA : AnnotTerm}
    (hi : i ≤ nF)
    (hxl : xs.length = as.length + o) (htake : xs.take as.length = as)
    (hfl : fs.length = nF) (hyl : ys.length = l)
    (hF : FieldsOkB 0 (consList (fs.take i) (consList as ρ)) (tl.map (·.2.2)))
    (hV : FieldsValid (consList (fs.take i) (consList as ρ)) (tl.map (·.2.2)))
    (hR : ∀ bs, SpineFit (consList ys (consList fs (consList xs ρ)))
        ((ihTeleAtR nF o i l (rebit b tl)).map (·.2.2)) bs →
      WellDenotedV V (consList bs (consList ys (consList fs (consList xs ρ)))) conclA)
    (h0 : b = 0 → ∀ bs, SpineFit (consList ys (consList fs (consList xs ρ)))
        ((ihTeleAtR nF o i l (rebit b tl)).map (·.2.2)) bs →
      interp V (consList bs (consList ys (consList fs (consList xs ρ)))) conclA
        ∈ˢ (univZero : V)) :
    WellDenotedV V (consList ys (consList fs (consList xs ρ)))
      (mkPisAV (ihTeleAtR nF o i l (rebit b tl)) conclA) := by
  have hfl' : (fs ++ ys).length = nF + l := by rw [List.length_append, hfl, hyl]
  have htk : (fs ++ ys).take i = fs.take i :=
    List.take_append_of_le_length (by rw [hfl]; omega)
  have hframe : consList (xs ++ (fs ++ ys)) ρ = consList ys (consList fs (consList xs ρ)) := by
    rw [consList_append, consList_append]
  -- the telescope's grading, transported to the rule's frame
  have hmv := fieldsWD_ihTeleAtGo_rule (ρ := ρ) (i := i) (fs := fs ++ ys) hxl htake hfl'
    (rebit b tl) [] (by rw [rebit_map_dom, consList_nil, htk]; exact hF)
    (by rw [rebit_map_dom, consList_nil, htk]; exact hV)
  rw [List.length_nil, consList_nil, hframe, ← ihTeleAtR] at hmv
  rw [ihTeleAtR_merge hi] at hR h0 ⊢
  refine ⟨WellDenoted_mkPisAV_of (w := 0) hmv.1 fun bs hsp => (hR bs hsp).1,
    AnnotValid_mkPisAV_of (w := b) (fun d hd => ?_) hmv.2
      (fun bs hsp => (hR bs hsp).2) (fun hb bs hsp => h0 hb bs hsp)⟩
  obtain ⟨d', hd', he⟩ := mem_ihTeleAtGo hd
  rw [he, mem_rebit hd']

/-- **The FIELD telescope's hereditary grading, at the field's own
frame** — the constructor's tower peeled at entry `nP + i`.  The
premise `hentry` is the reading record's own equation
(`BlockCtorDataI.recEntry` at a recursive field, an EMPTY telescope;
`.reflEntry` at a reflexive one), and the two fits are the FIELD
segment's: the parameters by the hop, the fields by the frame. -/
theorem blockRuleIhTele_graded_of_ctorTower {ds tl : List (Nat × Nat × AnnotTerm)}
    {bodyC bodyF : AnnotTerm} {nP nF i : Nat}
    (hwd : ∀ ρ : Nat → V, WellDenotedV V ρ (mkPisAV ds bodyC))
    (hlenD : ds.length = nP + nF) (hi : i < nF)
    (hentry : (ds.getD (nP + i) default).2.2 = mkPisAV tl bodyF)
    {σ : Nat → V} {ps fs : List V}
    (hps : SpineFit σ ((ds.take nP).map (·.2.2)) ps)
    (hfs : SpineFit (consList ps σ) ((ds.drop nP).map (·.2.2)) fs) :
    FieldsOkB 0 (consList (fs.take i) (consList ps σ)) (tl.map (·.2.2)) ∧
      FieldsValid (consList (fs.take i) (consList ps σ)) (tl.map (·.2.2)) := by
  have hnq : nP + i < ds.length := by omega
  have hsplit : (ds.take (nP + i)).map (fun d : Nat × Nat × AnnotTerm => d.2.2)
      = (ds.take nP).map (·.2.2) ++ ((ds.drop nP).take i).map (·.2.2) := by
    rw [← List.map_append, List.take_add]
  have hfit : SpineFit σ ((ds.take (nP + i)).map (·.2.2)) (ps ++ fs.take i) := by
    rw [hsplit]
    exact SpineFit.append hps (by rw [List.map_take]; exact spineFit_take_any hfs i)
  have h := towerDom_graded_of_tower hwd hnq hfit
  rw [hentry, consList_append] at h
  exact ⟨(WellDenoted_mkPisAV_inv h.1).1, (AnnotValid_mkPisAV_inv h.2).1⟩

/-- **`hokA`'s `ih` SEGMENT, AT THE RUN** — §40.10 composed with the
PARAMETER HOP (§40.9).  The frame is the rule's own: the prefix `x⃗`
fitting the recursor's domains, the fields `f⃗` fitting the
constructor's telescope moved past the `o = rP - nP` extras, and the
`q` `ih` values already bound.  The two premises left are the ones the
frame cannot supply: the OPENER's own field index and telescope
(`hentry`, the reading record's equation) and the guarded call's
reading `conclA` (`hR` and, at a `Prop` elimination only, `h0`) —
both stated AT THIS FRAME, so neither is quantified past the fact that
produces it. -/
theorem blockRuleIseg_of_run {envC : Env} {p : ConLeche.BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hm : memR c) (hr : rs[c]? = some r) (ψ : Name → Nat)
    {cvTa : ConstantVal} {caps : ConLeche.IndCaps}
    (hcvTa : cvTas[p.toBlockShape.recTgtAt c]? = some cvTa)
    (hfT : envC.find? cvTa.name = some (.indInfo cvTa caps))
    {nFull : Nat} {resSort : Level} {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData mpC.base2 cvTa nFull resSort pps) (hle : p.nP ≤ nFull)
    {ds tl : List (Nat × Nat × AnnotTerm)} {bodyC bodyF conclA : AnnotTerm}
    {nF o i q b : Nat}
    (hwd : ∀ ρ : Nat → V, WellDenotedV V ρ (mkPisAV ds bodyC))
    (hlenD : ds.length = p.nP + nF)
    (hframes : ∀ ρ : Nat → V, Sat V (((pps ψ).take p.nP).map (·.2.2)).reverse ρ ↔
      Sat V ((ds.take p.nP).map (·.2.2)).reverse ρ)
    (ho : p.toBlockShape.rulePrefixAt c = p.nP + o) (hi : i < nF)
    (hentry : (ds.getD (p.nP + i) default).2.2 = mkPisAV tl bodyF)
    {σ : Nat → V} {xs fs ys : List V}
    (hxs : SpineFit σ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) xs)
    (hfs : SpineFit (consList xs σ) ((liftDoms o 0 (ds.drop p.nP)).map (·.2.2)) fs)
    (hyl : ys.length = q)
    (hR : ∀ bs, SpineFit (consList ys (consList fs (consList xs σ)))
        ((ihTeleAtR nF o i q (rebit b tl)).map (·.2.2)) bs →
      WellDenotedV V (consList bs (consList ys (consList fs (consList xs σ)))) conclA)
    (h0 : b = 0 → ∀ bs, SpineFit (consList ys (consList fs (consList xs σ)))
        ((ihTeleAtR nF o i q (rebit b tl)).map (·.2.2)) bs →
      interp V (consList bs (consList ys (consList fs (consList xs σ)))) conclA
        ∈ˢ (univZero : V)) :
    WellDenotedV V (consList ys (consList fs (consList xs σ)))
      (mkPisAV (ihTeleAtR nF o i q (rebit b tl)) conclA) := by
  have hxlen : xs.length = p.toBlockShape.rulePrefixAt c := by
    rw [SpineFit.length_eq hxs, blockRulePdomsAV_length hμ mpC h hr ψ]
  have hlenps : (xs.take p.nP).length = p.nP := by
    rw [List.length_take, hxlen, ho]; omega
  have hms : (xs.drop p.nP).length = o := by rw [List.length_drop, hxlen, ho]; omega
  have hps := blockRuleParamFit_run (hm := hm) hμ mpC h hr ψ hcvTa hfT hFD hle hlenD hframes
    (spineFit_take_any hxs p.nP)
  have hsplit : xs.take p.nP ++ xs.drop p.nP = xs := List.take_append_drop _ _
  have hregroup : consList xs σ = consList (xs.drop p.nP) (consList (xs.take p.nP) σ) := by
    rw [← consList_append, hsplit]
  have hshift : shiftE o 0 (consList xs σ) = consList (xs.take p.nP) σ := by
    rw [hregroup, ← hms]
    exact shiftE_consList _ _
  have hfs' : SpineFit (consList (xs.take p.nP) σ) ((ds.drop p.nP).map (·.2.2)) fs := by
    rw [← hshift]
    exact (spineFit_liftDoms (V := V) o).mp hfs
  have hfl : fs.length = nF := by
    rw [SpineFit.length_eq hfs', List.length_map, List.length_drop, hlenD]; omega
  obtain ⟨hFok, hVal⟩ := blockRuleIhTele_graded_of_ctorTower hwd hlenD hi hentry hps hfs'
  exact blockRuleIhEntry_of_fieldTele (Nat.le_of_lt hi)
    (by rw [hlenps, hxlen, ho]) (by rw [hlenps]) hfl hyl hFok hVal hR h0

end IhSeg

/-! ### 40.11 `hokC` — the CONCLUSION at the satisfied frame

The rule's conclusion `concl` is the RECURSOR's stored type with its
whole telescope instantiated (`instPisAtLift` at the rule's prefix
openers, the constructor's result index arguments and the fired
major, §40.6), so its reading `Ca` is the recursor type's reading
PEELED along the readings of those arguments
(`denoteMeta_instPisAtLift_peel`, `BlockRecRead.lean`).

The recursor type's reading is well-denoted at EVERY frame — it is a
closed reading, and `recStage_tyPis`' last component is exactly
that — so `hokC` is the tower's grading carried down the peel.  Each
peel step is `WellDenotedV_inst0` at the argument's own grading, which
is why this is a battery and not a projection: the peel consumes the
ARGUMENTS' grading too, and that is the one thing the tower does not
supply. -/

section HokC

/-- **A fit's RESIDUAL is graded**: the tower's grading carried down
the peel, one `WellDenotedV_inst0` per step. -/
theorem teleFitPA_wellDenotedV {ρ : Nat → V} :
    ∀ {T rest : AnnotTerm} {as : List AnnotTerm}, TeleFitPA V ρ T as rest →
      WellDenotedV V ρ T → (∀ a ∈ as, WellDenotedV V ρ a) → WellDenotedV V ρ rest
  | _, _, _, .nil, hT, _ => hT
  | _, _, _, .cons hmem hrest, hT, ha =>
    teleFitPA_wellDenotedV hrest
      ((WellDenotedV_inst0 (ha _ List.mem_cons_self)).mpr (WellDenotedV_pi_body hT hmem))
      (fun a' ha' => ha a' (List.mem_cons_of_mem _ ha'))

/-- **`hokC`, from the PEEL.**  `Ta` is the recursor type's reading —
a CLOSED reading, graded at every frame — and `vs` the readings of the
instantiating arguments; `hpeel` is `denoteMeta_instPisAtLift_peel`'s
output at the run.  The two premises the frame must supply are the
FIT (the arguments' memberships along the tower, the rule data's
tower fit) and the arguments' own grading, both bounded by
`Sat V Δ ρ` — the very frame the obligation is stated at. -/
theorem blockRuleHokC_of_peel {Ta Ca : AnnotTerm} {vs Δ : List AnnotTerm}
    (hpeel : ConLeche.Model.AnnotTerm.peelPis Ta vs = some Ca)
    (hTa : ∀ ρ : Nat → V, WellDenotedV V ρ Ta)
    (hfit : ∀ ρ : Nat → V, Sat V Δ ρ → ∃ rest, TeleFitPA V ρ Ta vs rest)
    (hargs : ∀ ρ : Nat → V, Sat V Δ ρ → ∀ a ∈ vs, WellDenotedV V ρ a) :
    ∀ ρ : Nat → V, Sat V Δ ρ → WellDenotedV V ρ Ca := by
  intro ρ hρ
  obtain ⟨rest, hf⟩ := hfit ρ hρ
  obtain rfl : rest = Ca := Option.some.inj (hf.peelPis.symm.trans hpeel)
  exact teleFitPA_wellDenotedV hf (hTa ρ) (hargs ρ hρ)

/-- **`hokC` AT THE RUN**: the peel's tower is the RECURSOR TYPE's
reading, whose grading at every frame is `recStage_tyPis`' last
component.  What is left is the frame's two, and neither is a new
object:

* the **fit** is the RULE CONTRACT's own `hfitR` — `TeleFitPA V ρ
  (blockRecTyAV … c) (xs ++ [maj]) restR` at exactly this tower, the
  premise `blockRecSplit_at_rule` and `blockRecSpF_of_rule`
  (`BlockRuleFit.lean`) already consume — with `xs` the prefix bvars
  followed by the index readings and `maj` the fired spine, which is
  `BlockRuleConclAt`'s `paramBvarsAt rP (rP + nF + nR) ++ esA ++ [mkA]`
  re-associated.  No producer is owed: a regime supplies it when it
  instantiates the rule, exactly as it supplies `residueOk`'s spine;
* the **arguments' grading** reduces by `blockRuleHokC_args` to the
  constructor's half, the prefix being bvars. -/
theorem blockRuleHokC_of_run {envC : Env} (hμ : μ.verifiedChecks = true)
    (mpC : EnvModelM V μ envC) {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) (ψ : Name → Nat) {Ca : AnnotTerm} {vs Δ : List AnnotTerm}
    (hpeel : ConLeche.Model.AnnotTerm.peelPis
      (blockRecTyAV mpC.base2.acval envC rs ψ c) vs = some Ca)
    (hfit : ∀ ρ : Nat → V, Sat V Δ ρ →
      ∃ rest, TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c) vs rest)
    (hargs : ∀ ρ : Nat → V, Sat V Δ ρ → ∀ a ∈ vs, WellDenotedV V ρ a) :
    ∀ ρ : Nat → V, Sat V Δ ρ → WellDenotedV V ρ Ca := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hwdTy⟩ := recStage_tyPis hμ mpC h hr ψ
  exact blockRuleHokC_of_peel hpeel hwdTy hfit hargs

end HokC

/-! ### 40.12 `hokA` ASSEMBLED, at the run

The three segments (§35 + §40.4 for the prefix, §40.8–§40.9 for the
fields, §40.10 for the `ih` openers) go into `blockRuleHokA_of_segments`
at the run's own spellings.  The two spelling equations are premises
here rather than rewrites inside, because the bundle's three lists are
`readOpenedDoms` of the openers and each segment is stated at the list
its OWNER produces: `blockRulePdomsAV_eq_readOpenedDoms` (§40.5) and
`blockRuleFdomsAV_liftDoms` (§27) are the two producers, and the `ih`
list's entries come one at a time — which is why `hIent` is an
existential PER KEY and not a function: the telescope and the
conclusion are the key's, and no run object is a function of the key.

`hIent`'s frame-dependent half is stated under the segment's own
`σ`/`xs`/`fs`/`ys`, so nothing in it is quantified past the fit that
produces it; its frame-INDEPENDENT half (the field index, the
telescope, the conclusion and the two equations) is hoisted, because
those are determined by the key alone. -/

section HokAssembly

/-- **`hokA` at the run**, from the three segments. -/
theorem blockRuleHokA_of_run {envC : Env} {p : ConLeche.BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hm : memR c) (hr : rs[c]? = some r) (ψ : Name → Nat)
    {cvTa : ConstantVal} {caps : ConLeche.IndCaps}
    (hcvTa : cvTas[p.toBlockShape.recTgtAt c]? = some cvTa)
    (hfT : envC.find? cvTa.name = some (.indInfo cvTa caps))
    {nFull : Nat} {resSort : Level} {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData mpC.base2 cvTa nFull resSort pps) (hle : p.nP ≤ nFull)
    {ds : List (Nat × Nat × AnnotTerm)} {bodyC : AnnotTerm} {nF o nR : Nat}
    (hwd : ∀ ρ : Nat → V, WellDenotedV V ρ (mkPisAV ds bodyC))
    (hlenD : ds.length = p.nP + nF)
    (hframes : ∀ ρ : Nat → V, Sat V (((pps ψ).take p.nP).map (·.2.2)).reverse ρ ↔
      Sat V ((ds.take p.nP).map (·.2.2)).reverse ρ)
    (ho : p.toBlockShape.rulePrefixAt c = p.nP + o)
    {P F' I : List AnnotTerm}
    (hPE : P = blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c)
    (hFE : F' = (liftDoms o 0 (ds.drop p.nP)).map (·.2.2))
    (hIlen : I.length = nR)
    (hIent : ∀ q, q < nR →
      ∃ (i b : Nat) (tl : List (Nat × Nat × AnnotTerm)) (bodyF conclA : AnnotTerm),
        i < nF ∧
        (ds.getD (p.nP + i) default).2.2 = mkPisAV tl bodyF ∧
        I.getD q default = mkPisAV (ihTeleAtR nF o i q (rebit b tl)) conclA ∧
        ∀ (σ : Nat → V) (xs fs ys : List V),
          SpineFit σ P xs → SpineFit (consList xs σ) F' fs →
          SpineFit (consList fs (consList xs σ)) (I.take q) ys →
          (∀ bs, SpineFit (consList ys (consList fs (consList xs σ)))
              ((ihTeleAtR nF o i q (rebit b tl)).map (·.2.2)) bs →
            WellDenotedV V (consList bs (consList ys (consList fs (consList xs σ)))) conclA) ∧
          (b = 0 → ∀ bs, SpineFit (consList ys (consList fs (consList xs σ)))
              ((ihTeleAtR nF o i q (rebit b tl)).map (·.2.2)) bs →
            interp V (consList bs (consList ys (consList fs (consList xs σ)))) conclA
              ∈ˢ (univZero : V))) :
    ∀ l, l < p.toBlockShape.rulePrefixAt c + nF + nR →
      ∀ (σ : Nat → V) (ys : List V),
        SpineFit σ ((P ++ F' ++ I).take l) ys →
        WellDenotedV V (consList ys σ) ((P ++ F' ++ I).getD l default) := by
  have hp : P.length = p.toBlockShape.rulePrefixAt c := by
    rw [hPE, blockRulePdomsAV_length hμ mpC h hr ψ]
  have hf : F'.length = nF := by
    rw [hFE, List.length_map, liftDoms_length, List.length_drop, hlenD]; omega
  refine blockRuleHokA_of_segments hp hf hIlen ?_ ?_ ?_
  · -- the PREFIX segment (§35 + §40.4)
    intro l hl σ ys hys
    rw [hPE] at hys ⊢
    exact blockRulePdomsAV_graded hμ mpC h hr ψ l hl σ ys hys
  · -- the FIELD segment (§40.8, §40.9)
    intro q hq σ xs ys hxs hys
    rw [hFE] at hys ⊢
    rw [hPE] at hxs
    exact blockRuleFseg_of_run (hm := hm) hμ mpC h hr ψ hcvTa hfT hFD hle hwd hlenD hframes ho
      q hq σ xs ys hxs hys
  · -- the `ih` segment (§40.10)
    intro q hq σ xs fs ys hxs hfs hys
    obtain ⟨i, b, tl, bodyF, conclA, hiF, hentry, hIq, hfr⟩ := hIent q hq
    obtain ⟨hR, h0⟩ := hfr σ xs fs ys hxs hfs hys
    have hyl : ys.length = q := by
      rw [SpineFit.length_eq hys, List.length_take, hIlen]; omega
    rw [hIq]
    rw [hPE] at hxs
    rw [hFE] at hfs
    exact blockRuleIseg_of_run (hm := hm) hμ mpC h hr ψ hcvTa hfT hFD hle hwd hlenD hframes ho hiF
      hentry hxs hfs hyl hR h0

end HokAssembly

/-! ### 40.13 THE PRODUCER — `BlockRuleCerts` AT THE RUN

§40.3 states the bundle at the frame's three opener LISTS; this is
that theorem at the run, with every argument the check or the model
already owns discharged, so a consumer takes the BUNDLE and not its
nineteen parts.

The prefix and field openers are not premises and not existentials:
`blockRuleData_run` (`BlockRecData.lean`) identifies the run's
witnesses with `blockRulePrefFvs`/`blockRuleFieldFvs`, the RECOMPUTED
spellings, and `blockRuleFdomsAV` is by definition `readOpenedDoms` at
the latter — so the bundle's field segment is the one §27 and §40.8
are already stated at, with no bridge.

What stays a premise is three groups, each bounded by the fact that
produces it:

* **stage (c)'s peel** — the `ih` opening `h₃` with the generated
  tower's three scoping facts (§40.7's, wired), the two typing runs
  `hinf`/`hdeq`, the conclusion's `instPisAtLift` equation `hpr`, and
  the two readings `hRb`/`hCa`.  The rule record (`RuleRun`)
  carries every one of them from the rule's own run; what it does NOT
  carry is the recursor-type list's closedness, which §40.7's wiring
  needs at EVERY callee index;
* the **record** group the FIELD and `ih` segments consume
  (§40.8–§40.10) together with §27's `fdoms` spelling, and the
  per-key `ih` data `hIent`;
* **`hokC`'s three** (§40.11) — the peel equation, the tower fit and
  the instantiating readings' grading.

`hexF` and `hexI` are the two segments' reading-EXISTENCE premises in
§40.2's shape; they are stated as existences, not as list equations,
because `readOpenedDoms` is a reading by construction and that is all
the bundle asks.

**Both are produced elsewhere, and the composition is one line each**
— checked against the producers' own statements, which match these
antecedents and depths character for character:

* `hexF` is `blockRuleFdomsAV_eq`'s SECOND conjunct
  (`BlockRecData.lean`), the per-opener reading at
  `rulePrefixAt c + l`: `fun l x hx => ⟨_, (…).2 l x hx⟩`;
* `hexI` is `blockIhOpenerDom_run`'s last component
  (`BlockRecTyShapeRun.lean`) at `rP + nF + r`, through the key
  (`fr.ihKeys[r]? = some (i, c')`, which every `r < nR` has since
  `nR = ihKeys.length`).

They stay PREMISES rather than being discharged inside: the two
producers together take some eighteen arguments — the constructor
data record, the opener frame and the callee's type facts — and
trading two bounded existences for eighteen record premises would
widen every consumer.  The caller holds those records; the one-liners
belong at the call site. -/


/-! ### 40.15 THE `univZero` PRODUCER — the recursor's CONCLUSION
lands in the universe the CHECK named

The `ih` segment's `h0` (`blockRuleIseg_h0_of_conclAt`) rests on ONE
fact: a peel of a recursor
type at a fitting spine lands in `univZero` when the elimination level
is zero.  Its source is a step the check already takes:

```lean
    let sty ← ops.inferType env (mI + 1) concl        -- BlockInstall.lean
    let u   ← ops.ensureSort env (mI + 1) sty
```

— stage (b) infers the recursor conclusion's type and `ensureSort`s
it, and STORES that `u` as `cvRus`' third component, which is exactly
`blockRecElimLevel_run`'s `uOf c`.  So the family's elimination level
IS the level of the sort the check inferred for the conclusion, and
the `blockLargeElimAllowed` guard plays no part: `ensureSort` alone
plus D-d's agreement gives it.

The model step is `SortSemAt` (`Model/Tiers.lean`), the same claim
`checkConstantVal_reads` uses one level up — at the recursor's OWN
opened frame instead of the empty one, so the context is the type's
own binder data reversed (`ctxOk_blockFrame` at a degenerate second
and third opening, since the recursor's type is opened ONCE). -/

section ConclUniv

omit [SetTheory V] in
/-- A term scoped at depth `0` has no free-variable leaf. -/
theorem fvarLeaves_nil_of_wscoped_zero {e : Expr} (hw : Expr.WScoped 0 e) :
    e.fvarLeaves = [] := by
  rcases he : e.fvarLeaves with _ | ⟨l, ls⟩
  · rfl
  · exact absurd (Expr.fvarLeaves_lt_of_wscoped hw l (by rw [he]; exact List.mem_cons_self))
      (Nat.not_lt_zero _)

/-- **THE `univZero` PRODUCER**, in its general form: the recursor's
conclusion reads into `univ (u.eval ψ)` at every frame satisfying the
type's own binder data. -/
theorem blockRecConcl_univ {envC : Env} (hμ : μ.verifiedChecks = true)
    (mpC : EnvModelM V μ envC) {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) (ψ : Name → Nat)
    {fvs : List Expr} {conclE sty : Expr} {u : Level}
    (hop : ConLeche.openPisAtFvars (p.toBlockShape.majorIdxAt c + 1) r.1.type 0
      = some (fvs, conclE))
    (hinf : ConLeche.inferTypeCore μ envC F (p.toBlockShape.majorIdxAt c + 1) conclE
      = .ok sty)
    (hens : ConLeche.ensureSortCore μ envC F (p.toBlockShape.majorIdxAt c + 1) sty = .ok u) :
    ∀ ρ : Nat → V,
      Sat V ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
          (·.2.2)).reverse ρ →
      interp V ρ (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ c)
        ∈ˢ (univ (u.eval ψ) : V) := by
  obtain ⟨hw₁, hb₁⟩ := recStage_tyClosed h hr
  obtain ⟨fvs', concl', hop', -, hTyE, hlenRds, -, hdomsR, hconclRead, hwdTy⟩ :=
    recStage_tyPis hμ mpC h hr ψ
  have heqP := Option.some.inj (hop'.symm.trans hop)
  have hfe : fvs' = fvs := congrArg Prod.fst heqP
  have hce : concl' = conclE := congrArg Prod.snd heqP
  rw [hfe] at hdomsR
  rw [hce] at hconclRead
  -- the frame's syntax
  have hlenFvs : fvs.length = p.toBlockShape.majorIdxAt c + 1 :=
    ConLeche.Verify.openPisAtFvars_length _ hop
  obtain ⟨hbC, hlbF⟩ := openPisAtFvars_bounded _ hop hb₁
  have hwsC : Expr.WScoped (p.toBlockShape.majorIdxAt c + 1) conclE := by
    have hq := (openPisAtFvars_WScoped _ r.1.type 0 hop hw₁).2
    rwa [Nat.zero_add] at hq
  have hnilTy : r.1.type.fvarLeaves = [] := fvarLeaves_nil_of_wscoped_zero hw₁
  have hleaf : ∀ l ∈ conclE.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs := by
    intro l hl
    rcases openPisAtFvars_leaves _ hop l (Or.inl hl) with h' | h'
    · rw [hnilTy] at h'; exact nomatch h'
    · exact h'
  have hLC : Expr.LeavesBounded conclE := leavesBounded_of_openers hlbF hleaf
  -- the frame's semantics: the binder data reads, and is graded
  have hdoms : ∀ (j : Nat) (x : Expr), fvs[j]? = some x →
      denoteMeta mpC.base2.acval envC ψ j (Expr.fvarTypeD x)
        = some (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
            (·.2.2)).getD j default) := by
    intro j x hx
    obtain ⟨pd, hpd, -, hrd⟩ := hdomsR j x hx
    rw [hrd, List.getD_eq_getElem?_getD, List.getElem?_map, hpd]
    rfl
  have hokTower : ∀ l, l < p.toBlockShape.majorIdxAt c + 1 →
      ∀ (σ : Nat → V) (ys : List V),
      SpineFit σ (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
          (·.2.2)).take l) ys →
      WellDenotedV V (consList ys σ)
        (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
          (·.2.2)).getD l default) := by
    intro l hl σ ys hys
    have hfull : (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).take
        (p.toBlockShape.majorIdxAt c + 1)
        = blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c :=
      List.take_of_length_le (by omega)
    rw [← hfull] at hys ⊢
    exact prefixDoms_graded_of_tower (cc := blockRecConclAV mpC.base2.acval envC
        p.toBlockShape rs ψ c) (by omega) (fun ρ' => by rw [← hTyE]; exact hwdTy ρ')
      hl hys
  -- the context IS the type's own binder data, reversed
  have hlenDoms : ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
      (·.2.2)).length = p.toBlockShape.majorIdxAt c + 1 := by
    rw [List.length_map, hlenRds]
  have hent : ∀ i, i < p.toBlockShape.majorIdxAt c + 1 →
      (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
          (·.2.2)).reverse)[p.toBlockShape.majorIdxAt c + 1 - 1 - i]?
        = some (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
          (·.2.2)).getD i default) := by
    intro i hi
    rw [List.getElem?_reverse (by omega), hlenDoms,
      show p.toBlockShape.majorIdxAt c + 1 - 1 - (p.toBlockShape.majorIdxAt c + 1 - 1 - i) = i
        from by omega,
      List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [hlenDoms]; omega)]
    rfl
  have hokΔ : ∀ i, i < p.toBlockShape.majorIdxAt c + 1 → ∀ ρ : Nat → V,
      Sat V ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
        (·.2.2)).reverse ρ →
      WellDenotedV V (fun j => ρ (j + (p.toBlockShape.majorIdxAt c + 1 - 1 - i) + 1))
        (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
          (·.2.2)).getD i default) := by
    have hq := blockRuleHokΔ_of (V := V)
      (pdoms := (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2))
      (fdoms := []) (ihdoms := []) (nF := 0) (nR := 0) hlenDoms rfl rfl
      (by simpa using hokTower)
    simp only [List.reverse_nil, List.append_nil, List.nil_append] at hq
    have hgd : ∀ i, i < p.toBlockShape.majorIdxAt c + 1 →
        (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
            (·.2.2)).reverse).getD (p.toBlockShape.majorIdxAt c + 1 - 1 - i) default
          = ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
            (·.2.2)).getD i default := by
      intro i hi
      rw [List.getD_eq_getElem?_getD, hent i hi]
      rfl
    intro i hi ρ hρ
    have hq' := hq i hi ρ hρ
    rwa [hgd i hi] at hq'
  have hctx : CtxOk mpC.base2 ψ (p.toBlockShape.majorIdxAt c + 1)
      ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2)).reverse
      conclE :=
    ctxOk_of_openers mpC.base2.acval_closed
      (Aa := fun i => ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
        (·.2.2)).getD i default)
      (by rw [List.length_reverse, hlenDoms])
      (by simpa using ConLeche.openPisAtFvars_index _ r.1.type 0 hop)
      (by simpa using (openPisAtFvars_WScoped _ r.1.type 0 hop hw₁).1)
      hdoms hleaf (fun l hl => Expr.fvarLeaves_lt_of_wscoped hwsC l hl) hent hokΔ
  obtain ⟨-, ihw, -, ihi⟩ := checkSoundAt (V := V) hμ (Rules.RulesInputs.ofSem mpC ψ) F
  exact fun ρ hρ => (sortSemAt_of_claims ihw ihi
    (inferReads_of hμ (Rules.RulesInputs.ofSem mpC ψ))
    hctx hwsC hbC hLC hinf (ConLeche.ensureSortCore_inv hens) hconclRead ρ hρ).2

end ConclUniv

/-! ### 40.16 `hwd` — the ι equation list's grading

`hwd` (`hEq_iotaEqsAV_of`'s premise) has three parts per rule:

* `FieldsOkB 0` of the rule's concatenated domain list.  `FieldsOkB`
  has **no producer anywhere and no near-miss** (the only theorem
  concluding it, `fieldsOkB_of_frame` in `StructTele.lean`, is stated
  over `fieldsFrom`'s reversed-context slicing, a different currency);
  `fieldsOkB_zero_of_spineGrading` below pays it.  At `w = 0` the
  predicate's middle conjunct is vacuous, so
  what is left is exactly the hereditary reading of §40.12's
  ASCENDING per-binder grading — one induction, no new content;
* the equation's RIGHT-hand side, `instsAV 0 (ihs c j) (Rb c j)`.
  That is the RESIDUE's grading, which is `BlockRuleCerts`' own first
  component (`ResidueOk.1`), and `wd_instsAV`
  (`Semantics/Tower/BlockRecI.lean`) crosses the substitution;
* the equation's LEFT-hand side, the recursor VARIABLE applied to the
  rule's spine.  Its head's membership is `hwd`'s own hypothesis (the
  chain slot inhabits the recursor type's reading), so it is
  `Rules.wellDenotedV_mkAppN_of_fit` at the RECURSOR's fit — the same
  shape §40.11's arguments took at the CONSTRUCTOR's. -/

section Hwd

/-- **`FieldsOkB 0` from the ASCENDING per-binder grading** (the
`hokA` currency).  At `w = 0` the universe clause is vacuous, so the
predicate is just "every entry is graded under the values of the
entries before it", which is what a spine-indexed grading says one
index at a time. -/
theorem fieldsOkB_zero_of_spineGrading :
    ∀ (L : List AnnotTerm) {σ : Nat → V},
      (∀ l, l < L.length → ∀ ys : List V,
        SpineFit σ (L.take l) ys → WellDenoted V (consList ys σ) (L.getD l default)) →
      FieldsOkB 0 σ L
  | [], _, _ => trivial
  | F :: Fs, σ, hok => by
    refine ⟨?_, (fun hz => absurd rfl hz), fun a ha => ?_⟩
    · simpa using hok 0 (by simp) [] trivial
    · refine fieldsOkB_zero_of_spineGrading Fs (fun l hl ys hys => ?_)
      have hstep : SpineFit σ ((F :: Fs).take (l + 1)) (a :: ys) := ⟨ha, hys⟩
      have hq := hok (l + 1) (by simp only [List.length_cons]; omega) (a :: ys) hstep
      simpa using hq

end Hwd

end CertsArgs

end ConLeche.Model

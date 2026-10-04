module

import ConLeche.Verify.Inductives.RecStage
import ConLeche.Model.Inductives.BlockRecTyping
public import ConLeche.Semantics.Tower.BlockRecTower
import ConLeche.Model.Annot.BitInst
import ConLeche.Verify.Subst
import ConLeche.Model.Inductives.BlockRecRead
public import ConLeche.Model.Inductives.BlockRecData

public section

/-!
# The recursor model's run-level library

`graphRecPre_core` (`Model/Inductives/BlockRecGraph.lean`) produces the
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
  `blockRec_hsplit_at`): the class's index set is the member's index-tuple
  set and its carrier the least pre-fixed tuple's component, i.e. the
  member's former at the prefix frame (`BlockModelAt.leaf`);
* **§4 `OneElimLevel` from the check** (`blockRecOneElimLevel`);
* **§9 the bound** (`blockRecMot`, `blockRec_hconcl_at`);
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

/-! ## 2. The carrier's case analysis

An element of a component's carrier is the injection of the
constructor that built it.  `BlockModelAt.fibre` says that at the
OPERATOR: component `c`'s fibre of `Φ X` at `t` consists exactly of
the injections of the spines fitting one of `c`'s constructors.  The
carrier is the least pre-fixed TUPLE, and the fixed-point equation
(`app_lfpTuple_eq`, off the representation's `maps`, `acc` and `mono`) moves the
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
  rw [← app_lfpTuple_eq (hM.closed hsat) (hM.mono hsat) (hM.maps ψ ρp hsat) hc ht] at hx
  obtain ⟨j, fs, hf, rfl⟩ := (hM.fibre ψ ρp hsat _ (lfpTuple_mem _ _ _ _) c hc t ht x).mp hx
  exact ⟨j, fs, (hM.carrier ψ ρp hsat c hc t ht j fs).mp hf, rfl⟩

/-! ## 3. The recursor classes at the block's own carriers

`GraphFamData` (`Semantics/Tower/BlockRecTower.lean`) asks, per PREFIX
SPINE, for the classes' index sets and ORDINARY carriers, the index
tuple, a graph kit, and the two readings the recursors' TYPES fix.
For a block the first three are not a choice:

* the prefix spine's first `nP` values ARE the block's parameters (the
  recursor's rule prefix begins with them, `targetRecTy`), so the
  parameter frame is `consList (xs.take nP) ρ`;
* class `c` eliminates the member `mem c`, so its index set is that
  component's index-tuple set and its carrier the least pre-fixed
  tuple's component — which is the member's FORMER at the parameter
  frame, by `BlockModelAt.leaf`.

That last identification is the whole content of `blockRec_hsplit_at`: the
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
  rw [blockRecIs, ite_eq_left ⟨h, hp⟩]

theorem blockRecIs_neg {d : BlockData V} {ψ : Name → Nat} {ρ : Nat → V}
    {pdoms : Nat → List AnnotTerm} {mem : Nat → Nat} {xs : List V} {c : Nat}
    (h : ¬ (SpineFit ρ (d.params ψ) (xs.take d.nP) ∧ SpineFit ρ (pdoms c) xs)) :
    blockRecIs d ψ ρ pdoms mem xs c = (empty : V) := by
  classical
  rw [blockRecIs, ite_eq_right h]

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

/-! ## 9. The kit's MOTIVE

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
  rw [tagDec, dite_eq_left hex]
  obtain ⟨-, heq⟩ := hex.choose_spec
  obtain ⟨h1, h2, h3⟩ := tagged_inj heq
  exact Prod.ext h1.symm (Prod.ext h2.symm h3.symm)

/-- **The kit's motive**: the recursor's CONCLUSION, read at the
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

These definitions are that instantiation; `hpl` — the rule's prefix domains are as
long as the rule prefix — is then a theorem, off
`blockRulePdomsAV_length` and `liftDomsK_length`. -/

section RunComponents

/-- The rule's PREFIX domains at the chain frame. -/
@[expose] def blockRecPdomsK (K : Nat) (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env)
    (p : ConLeche.BlockShape)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (ψ : Name → Nat) (c : Nat) : List AnnotTerm :=
  liftDomsK K 0 (blockRulePdomsAV acval envC p rs ψ c)

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

/-! ## 22. The fired spine's VALUE at the rule's frame

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
  (`acval_interp_closed`), so `BlockModelAt.ctor` applies — at ANY
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

end Insertion

/-! ## 28. The `K` lifts of §20 are the IDENTITY

The guard the kit reads back (`blockRecIs_fits`, §3) is
`SpineFit ρ (pdoms c) xs` at the BASE frame, while the bridges that
discharge it (`blockRecSpF`) hold at the
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

/-! ## 30. The `ih` openers' VALUES — `ihv` defined

The ih values `ihv` the graph kit consumes are DEFINED here, and they may not mention the recursor: the kit's
step is what the recursion theorem is being handed, so the only thing
an ih value may be built from is the GRAPH `g` the step receives.

A rule's `ih` opener for a guarded call `rec_{c'} x⃗ e⃗_i(a⃗) (f_i a⃗)`
is valued at the CURRIED λ-tower over the field's telescope (the ih's
domain is the telescope, not the predecessor set) whose body is the
graph at that call's PREDECESSOR — `blockRecIhvAt`. -/

section IhValues

/-! ### The tower congruence -/

end IhValues

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
index tuple.  Membership in
the callee's class is guarded by `SpineFit ρ (pdoms c') xs` — at the
CALLEE's class `c'` — while the rule supplies the fit at its own class
`c`.  `hpref'` bridges the two: a spine fitting recursor `c`'s
rule-prefix domains fits recursor `c'`'s.

Stage (b) alone never gives it: `targetRecTy` compares only the
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

/-- **A fit transfers at the walk's own frames**: the domains
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
  rw [List.getElem?_take, ite_eq_left h]

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
  exact ⟨Expr.WScoped.of_not_hasFvar TE.hcv.noFvar, TE.hcv.bounded⟩

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
    List.getElem?_take, ite_eq_left hl, hpd]
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
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take, ite_eq_left hl, hpd]
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
      List.getElem?_take, ite_eq_left (by omega), hpd]
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
(`targetRecTy`) — and fuel monotonicity (`inferTypeCore_mono`,
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
      simp only [hμ, ite_true, bind, Except.bind] at h
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
  SUBSINGLETON clause on (`CtorDataI.srcProp`);
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
    -- the type's own inference (the check's inference of the stored type)
    obtain ⟨stype, -, hinfTy, -⟩ := E.hcv.sorted
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
    have hinfTy' : ConLeche.inferTypeCore μ envC F 0 r.1.type = .ok stype := hinfTy
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
every `ψ` — the elimination-level pin (`RecFamFacts.pin`) read at the
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
* the `ih` segment is the opener type's reading at the opener's own
  `ih` level — its depth `nP + o + nF + r` IS `rP + nF + r`.

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
runs come from stage (c)'s record (`TargetRuleRun`), the frame's
readings and grading come SEGMENT by segment (§39), and the residue's
and conclusion's own readings are the rule stage's.  Nothing here is
quantified past the rule it is about, and every semantic premise names
`envT` — the CONSTRUCTORS' environment, where the check ran — and no
other. -/

end FrameSeam

/-! ## 40. `BlockRuleCerts`' PRODUCER — its arguments, at the run

§39.1 reduced the bundle to a list of named arguments; this section
owns that list.  The arguments split in three:

* the **scoping** half (`hw₂`, `hw₃`, `hlbF`, `hbR`, `hbC`, `hleafR`,
  `hleafC`, the three lengths) — plumbing over the frame's three
  openings, closed here against premises the run supplies;
* the **reading** half (`hP`, `hF`, `hI`) — the openers' stored types
  read to the frame's entries.  `hP` is §35's; the SPELLING
  `readOpenedDoms` is a reading-by-construction, so a segment's own
  entries need only the readings to EXIST;
* the **grading** half (`hokA`, `hokC`), segment by segment from
  §40.4 on.

The generated `ih` opener tower's two syntactic facts
(`hasFvar = false`, and `looseBVarsBounded (rP + nF)`) are premises of
§40.1. -/

section CertsArgs

open ConLeche (openPisAtFvars)

/-! ### 40.1 The scoping arguments -/

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
    -- the constructor's telescope draws its leaves from the prefix (at an outside
    -- major it is instantiated at the major's parameters, not the prefix openers)
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


/-! ### 40.4 `hokA`, segment by segment

`hokA` is stated at the ASCENDING frame, so its three segments are a
`take` split and nothing else — but the split must be taken on the
ascending side (a `take`-shaped reading of the REVERSED context
lands on the wrong valuation).  Each segment is
stated at its own frame: the prefix at the bare `σ`, the fields under
the prefix's values, the `ih` openers under both — which is the shape
each owner proves its grading in, and the only shape in which the
premise is bounded by the fact that produces it. -/

/-! ### 40.6 The CONCLUSION's two scoping arguments

`hbC` and `hleafC` are about the term the rule's residue is compared
against — the recursor's stored type instantiated at the rule's
prefix openers, the constructor's result index arguments and the
fired major.  Every one of those arguments is built from the frame's
openers over two STORED (fvar-free) types, so both arguments come off
`instPisAt`'s two batteries once the spine's entries are known to be
bvar-closed. -/

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
domains against the type former's, `targetRecTy`; the
constructor's against the former's, `checkSumCtor`'s
`checkStructDomsAt`), and §40.9 runs it. -/

/-! ### 40.9 `hokA`'s FIELD segment — THE PARAMETER HOP

§40.8 left one premise: `blockRuleFseg_of_ctorTower`'s `hps`, the rule
frame's first `nP` values fitting the CONSTRUCTOR's parameter domains,
while the frame supplies them fitting the RECURSOR's.  The check
compares both against the same third thing — the MEMBER'S TYPE FORMER's
opened parameter telescope: the recursor's by `targetRecTy`'s
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

/- The member-frame premises the parameter-hop, segment and `hokA`
lemmas below share: the recursor stage's run at a member recursor `c`
(data `r`) and its target member's former (`cvTa`, read as
`FormerData` with at least `nP` binders). -/
variable {envC : Env} {p : ConLeche.BlockParts}
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

/-! ### 40.15 THE `univZero` PRODUCER — the recursor's CONCLUSION
lands in the universe the CHECK named

The `ih` segment's `h0` rests on ONE
fact: a peel of a recursor
type at a fitting spine lands in `univZero` when the elimination level
is zero.  Its source is a step the check already takes:

```lean
    let sty ← ops.inferType env (mI + 1) concl        -- targetRecTy
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

/-- **A checked Π-type's conclusion reads into the universe of its
inferred sort**, at every frame satisfying the type's own binder data:
the claims' `SortSemAt` at the type's opened frame (its context is the
binder data reversed). -/
theorem piConcl_univ {envC : Env} (hμ : μ.verifiedChecks = true)
    (mpC : EnvModelM V μ envC) {F : Nat} (ψ : Name → Nat) {n : Nat} {T : Expr}
    {ea : AnnotTerm} {rds : List (Nat × Nat × AnnotTerm)} {cc : AnnotTerm}
    {fvs : List Expr} {conclE sty : Expr} {u : Level}
    (hw₁ : Expr.WScoped 0 T) (hb₁ : T.looseBVarsBounded 0 = true)
    (hTyE : ea = mkPisAV rds cc) (hlenRds : rds.length = n)
    (hdomsR : ∀ (j : Nat) (x : Expr), fvs[j]? = some x →
      ∃ pd, rds[j]? = some pd ∧ pd.1 = 0 ∧
        denoteMeta mpC.base2.acval envC ψ j x.fvarTypeD = some pd.2.2)
    (hconclRead : denoteMeta mpC.base2.acval envC ψ n conclE = some cc)
    (hwdTy : ∀ ρ : Nat → V, WellDenotedV V ρ ea)
    (hop : ConLeche.openPisAtFvars n T 0 = some (fvs, conclE))
    (hinf : ConLeche.inferTypeCore μ envC F n conclE = .ok sty)
    (hens : ConLeche.ensureSortCore μ envC F n sty = .ok u) :
    ∀ ρ : Nat → V, Sat V (rds.map (·.2.2)).reverse ρ →
      interp V ρ cc ∈ˢ (univ (u.eval ψ) : V) := by
  -- the frame's syntax
  have hlenFvs : fvs.length = n :=
    ConLeche.Verify.openPisAtFvars_length _ hop
  obtain ⟨hbC, hlbF⟩ := openPisAtFvars_bounded _ hop hb₁
  have hwsC : Expr.WScoped n conclE := by
    have hq := (openPisAtFvars_WScoped _ T 0 hop hw₁).2
    rwa [Nat.zero_add] at hq
  have hnilTy : T.fvarLeaves = [] := fvarLeaves_nil_of_wscoped_zero hw₁
  have hleaf : ∀ l ∈ conclE.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs := by
    intro l hl
    rcases openPisAtFvars_leaves _ hop l (Or.inl hl) with h' | h'
    · rw [hnilTy] at h'; exact nomatch h'
    · exact h'
  have hLC : Expr.LeavesBounded conclE := leavesBounded_of_openers hlbF hleaf
  -- the frame's semantics: the binder data reads, and is graded
  have hdoms : ∀ (j : Nat) (x : Expr), fvs[j]? = some x →
      denoteMeta mpC.base2.acval envC ψ j (Expr.fvarTypeD x)
        = some ((rds.map
            (·.2.2)).getD j default) := by
    intro j x hx
    obtain ⟨pd, hpd, -, hrd⟩ := hdomsR j x hx
    rw [hrd, List.getD_eq_getElem?_getD, List.getElem?_map, hpd]
    rfl
  have hokTower : ∀ l, l < n →
      ∀ (σ : Nat → V) (ys : List V),
      SpineFit σ ((rds.map
          (·.2.2)).take l) ys →
      WellDenotedV V (consList ys σ)
        ((rds.map
          (·.2.2)).getD l default) := by
    intro l hl σ ys hys
    have hfull : rds.take
        (n)
        = rds :=
      List.take_of_length_le (by omega)
    rw [← hfull] at hys ⊢
    exact prefixDoms_graded_of_tower (cc := cc) (by omega) (fun ρ' => by rw [← hTyE]; exact hwdTy ρ')
      hl hys
  -- the context IS the type's own binder data, reversed
  have hlenDoms : (rds.map
      (·.2.2)).length = n := by
    rw [List.length_map, hlenRds]
  have hent : ∀ i, i < n →
      ((rds.map
          (·.2.2)).reverse)[n - 1 - i]?
        = some ((rds.map
          (·.2.2)).getD i default) := by
    intro i hi
    rw [List.getElem?_reverse (by omega), hlenDoms,
      show n - 1 - (n - 1 - i) = i
        from by omega,
      List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [hlenDoms]; omega)]
    rfl
  have hokΔ : ∀ i, i < n → ∀ ρ : Nat → V,
      Sat V (rds.map
        (·.2.2)).reverse ρ →
      WellDenotedV V (fun j => ρ (j + (n - 1 - i) + 1))
        ((rds.map
          (·.2.2)).getD i default) := by
    have hq := blockRuleHokΔ_of (V := V)
      (pdoms := rds.map (·.2.2))
      (fdoms := []) (ihdoms := []) (nF := 0) (nR := 0) hlenDoms rfl rfl
      (by simpa using hokTower)
    simp only [List.reverse_nil, List.append_nil, List.nil_append, Nat.add_zero] at hq
    have hgd : ∀ i, i < n →
        ((rds.map
            (·.2.2)).reverse).getD (n - 1 - i) default
          = (rds.map
            (·.2.2)).getD i default := by
      intro i hi
      rw [List.getD_eq_getElem?_getD, hent i hi]
      rfl
    intro i hi ρ hρ
    have hq' := hq i hi ρ hρ
    rwa [hgd i hi] at hq'
  have hctx : CtxOk mpC.base2 ψ (n)
      (rds.map (·.2.2)).reverse
      conclE :=
    ctxOk_of_openers mpC.base2.acval_closed
      (Aa := fun i => (rds.map
        (·.2.2)).getD i default)
      (by rw [List.length_reverse, hlenDoms])
      (by simpa using ConLeche.openPisAtFvars_index _ T 0 hop)
      (by simpa using (openPisAtFvars_WScoped _ T 0 hop hw₁).1)
      hdoms hleaf (fun l hl => Expr.fvarLeaves_lt_of_wscoped hwsC l hl) hent hokΔ
  obtain ⟨-, ihw, -, ihi⟩ := checkSoundAt (V := V) hμ (Rules.RulesInputs.ofSem mpC ψ) F
  exact fun ρ hρ => (sortSemAt_of_claims ihw ihi
    (inferReads_of hμ (Rules.RulesInputs.ofSem mpC ψ))
    hctx hwsC hbC hLC hinf (ConLeche.ensureSortCore_inv hens) hconclRead ρ hρ).2


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
  exact piConcl_univ hμ mpC ψ hw₁ hb₁ hTyE hlenRds hdomsR hconclRead hwdTy hop hinf hens

end ConclUniv

/-! ### 40.16 `hwd` — the ι equation list's grading

`hwd` (`hEq_iotaEqsAV_of`'s premise) has three parts per rule:

* `FieldsOkB 0` of the rule's concatenated domain list.  `FieldsOkB`
  has **no producer anywhere and no near-miss** (the only theorem
  concluding it, `fieldsOkB_of_frame` in `FixKit.lean`, is stated
  over `fieldsFrom`'s reversed-context slicing, a different currency);
  `fieldsOkB_zero_of_spineGrading` below pays it.  At `w = 0` the
  predicate's middle conjunct is vacuous, so
  what is left is exactly the hereditary reading of §40.12's
  ASCENDING per-binder grading — one induction, no new content;
* the equation's RIGHT-hand side, `instsAV 0 (ihs c j) (Rb c j)`.
  That is the RESIDUE's grading, which is `BlockRuleCerts`' own first
  component (`ResidueOk.1`), and `wd_instsAV`
  (`Semantics/Tower/BlockRecTower.lean`) crosses the substitution;
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

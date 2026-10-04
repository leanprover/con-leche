module

import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.BlockRecMem
public import ConLeche.Model.Inductives.DeclBlock
import ConLeche.Model.Inductives.BlockRecLaw
import ConLeche.Verify.ProjSlots
import ConLeche.Verify.Inductives.BlockRecRun

public section

/-!
# The recursor stage, assembled at the run

`blockRecStaged_of` (`Model/Inductives/BlockStageRec.lean`) is the
recursor stage's cons, stated at eighteen premises.  This module
discharges from the CHECK'S OWN RUN every premise that is a syntactic
fact about the stored recursors, so that what is left of the Model half
is the two SEMANTIC seams — the family premise (`BlockRecPre`, the
recursor model `graphRecPre_core`) and the rule data
(`BlockRuleDataAt`, `hnew`).

What the run supplies, and where it comes from:

| premise | source |
|---|---|
| `hty`, `hrhs` | `recStage_facts` |
| `hresRec` | `recStage_reserved` |
| `hfr`, `hnres`, `hpsh` | the per-recursor type record's check (`RecStage.tyGenAt`, `ConstChecked`) |
| `hnoTy` | the same check's `ConstChecked.noProj` |
| `hrd` | `hrd_of_pre`, at the family premise |
| `hrecP` | `hrecP_ofR`, at the rule data |
-/

namespace ConLeche.Model

open ConLeche.Semantics (AnnotTerm)
open ConLeche.Semantics SetTheory
open ConLeche.Term
open ConLeche (Env Expr Name Level ConstantVal ConstantInfo RecRule BlockShape BlockParts
  consBlockRecs)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## 4. The stored RULES mention no empty slot

`hnoRhs` is `hnoTy`'s twin one stage down: a stored right-hand side has
no `.proj` node at an empty slot of the BARE-`k` environment
(`RuleOutOk.hnoProj`), whose `findProj?` is the constructors'
(`findProj?_consBlockRecsBare`).  Both facts
below are fields of the stage's rule record (`RecStage.ruleOutOf`,
`Verify/Inductives/RecStage.lean`). -/

section Annot

/-- **`blockRecStaged_of`'s `hnoRhs`**: a stored rule's right-hand side
mentions no EMPTY projection slot of the constructors' environment.
It is the rule record's `hnoProj` at the environment the stage stores
it in — the BARE-`k` one, whose `findProj?` is `envC`'s, because no
recursor's name is projection-shaped. -/
theorem recStage_rhsNoProj {envC : Env} {p : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR) :
    ∀ r ∈ rs, ∀ rhsA ∈ r.2.1, ∀ (T : Name) (i : Nat),
      envC.findProj? T i = none → Expr.NoProjAt T i rhsA := by
  obtain ⟨R⟩ := id h
  -- no rule-less recursor's name is projection-shaped, so the bare
  -- environment's slots are the constructors' environment's
  have hpsh : ∀ x ∈ rs.map (fun r => (r.1, r.2.2.1)), x.1.name.isProjFnShape = false := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hy
    obtain ⟨rc, u, -, -, ⟨E⟩⟩ := R.tyGenAt hi
    rw [E.name_eq, ← E.hcv0.1]
    exact E.hcv.notProjShape
  intro r hr rhsA hrhsA T i hslot
  obtain ⟨c, hc⟩ := List.getElem?_of_mem hr
  obtain ⟨j, rc, -, -, Q⟩ := R.ruleOutOf hc hrhsA
  refine Q.hnoProj T i ?_
  rw [findProj?_consBlockRecsBare hpsh]
  exact hslot

/-- **The rule's own typing run, at the stage's own bare-`k`
environment**, stated at the list the model's bare cons is built over
(`bareOf rs`, spelled out — `BlockStageRec`'s abbreviation is not in
this file's public view): the rule record's `htyR`. -/
theorem recStage_rhsInfer {envC : Env} {p : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR) :
    ∀ r ∈ rs, ∀ rhsA ∈ r.2.1, ∃ tyR : Expr,
      ConLeche.inferTypeCore μ
          (consBlockRecsBare p.toBlockShape 0 (rs.map fun r => (r.1, r.2.2.1)) envC) F 0 rhsA
        = .ok tyR := by
  obtain ⟨R⟩ := id h
  intro r hr rhsA hrhsA
  obtain ⟨c, hc⟩ := List.getElem?_of_mem hr
  obtain ⟨i, rc, -, -, Q⟩ := R.ruleOutOf hc hrhsA
  exact Q.htyR

end Annot

/-! ## 5. The stage's VALUATION

`blockRecStaged_of` takes the post-cons carrier's valuation `acv` as a
parameter with six facts about it.  The recursor stage CHOOSES it —
the `i`-th stored recursor's leaf is the `i`-th projection of the
family's chosen tuple and every other name reads as before — so it is
defined here and three of the six facts (`hag`, the valuation
spelling, and the arity) come with the definition.  The other three
are about the LEAF and belong beside `blockRecAV_facts`. -/

/-- **The recursors' cons's valuation**: the block's recursors read as
the family's leaves, everything else as the constructors' environment
reads it. -/
@[expose] noncomputable def blockRecAcvOf (base : Name → (Name → Nat) → AnnotTerm)
    (names : List Name) (leaf : (Name → Nat) → Nat → AnnotTerm) :
    Name → (Name → Nat) → AnnotTerm :=
  fun n ψ =>
    match names.findIdx? (· == n) with
    | some i => leaf ψ i
    | none => base n ψ

/-- Off the block's recursors the valuation is the constructors'. -/
theorem blockRecAcvOf_of_ne {base : Name → (Name → Nat) → AnnotTerm} {names : List Name}
    {leaf : (Name → Nat) → Nat → AnnotTerm} {n : Name} (hne : ∀ m ∈ names, n ≠ m) :
    blockRecAcvOf base names leaf n = base n := by
  have h : names.findIdx? (· == n) = none :=
    List.findIdx?_eq_none_iff.mpr (fun x hx => by
      simpa using fun hh => hne x hx hh.symm)
  funext ψ
  simp only [blockRecAcvOf, h]

/-- At the `i`-th stored recursor the valuation IS the `i`-th leaf —
the names being pairwise distinct is what makes the lookup land on
`i`. -/
theorem blockRecAcvOf_at {base : Name → (Name → Nat) → AnnotTerm} {names : List Name}
    {leaf : (Name → Nat) → Nat → AnnotTerm} (hnd : names.Nodup) {i : Nat} {n : Name}
    (hi : names[i]? = some n) :
    blockRecAcvOf base names leaf n = fun ψ => leaf ψ i := by
  have hlt : i < names.length := (List.getElem?_eq_some_iff.mp hi).1
  have hn : names[i] = n := by
    rw [List.getElem?_eq_getElem hlt] at hi
    exact Option.some.inj hi
  have h : names.findIdx? (· == n) = some i := by
    rw [← hn]
    refine List.findIdx?_eq_some_iff_getElem.mpr ⟨hlt, by simp, fun j hji hp => ?_⟩
    have hjl : j < names.length := by omega
    have : names[j] = names[i] := by simpa using hp
    exact absurd ((List.Nodup.getElem_inj hnd).mp this) (by omega)
  funext ψ
  simp [blockRecAcvOf, h]

/-! ## 6. The stage, assembled

`blockRecStaged_runR` is `blockRecStaged_of` with every SYNTACTIC
premise read off the run and the VALUATION defined rather than
assumed.  The
recursor types' readings are the run's too (`recStage_tyPis`),
so `RecTy` is not a parameter but the named spelling `blockRecTyAV`.

What is left is: the LEAF's four structural facts and its
ψ-dependence (beside `blockRecAV_facts`, the semantics tier's), and
the two SEMANTIC seams — the family premise `BlockRecPre` (the
regimes) and the rule data `hnew` (`hrecP_ofR`). -/

/-- The `i`-th recursor's LEAF at `ψ`: the `i`-th projection of the
family's chosen tuple, at the recursor types the run reads.

**The family's level `s` is a FUNCTION of `ψ`**: a large eliminator carries
its own level parameter, so a block's recursor types are sets of a
level that MOVES with the valuation, and `BlockRecPre.hTy` is stated
at `univ (s ψ)`. -/
@[expose] noncomputable def blockRecLeafAV (acval : Name → (Name → Nat) → AnnotTerm)
    (envC : Env) (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (s : (Name → Nat) → Nat) (eqs : (Name → Nat) → List AnnotTerm) (ψ : Name → Nat)
    (i : Nat) : AnnotTerm :=
  ConLeche.Semantics.blockRecAV (s ψ) rs.length (blockRecTyAV acval envC rs ψ) (eqs ψ) i

/-- The recursors' cons's valuation, at the block's own leaves. -/
@[expose] noncomputable def blockRecAcv (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (s : (Name → Nat) → Nat) (eqs : (Name → Nat) → List AnnotTerm) :
    Name → (Name → Nat) → AnnotTerm :=
  blockRecAcvOf acval (rs.map (·.1.name)) (blockRecLeafAV acval envC rs s eqs)

/-- **The recursor family's leaf facts** at the equation list `eqs`:
the leaf is closed, invariant under lifting, level-parametric in each
recursor's own parameters, graded and bit-valid, and the family premise
`hpre` that grades it. -/
structure BlockRecLeafOk {envC : Env} (mpC : EnvModelM V μ envC)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (s : (Name → Nat) → Nat) (eqs : (Name → Nat) → List AnnotTerm) : Prop where
  closed : ∀ (ψ : Name → Nat) (i : Nat),
    Term.Closed ((blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i).erase)
  liftN : ∀ (ψ : Name → Nat) (i k : Nat),
    (blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i).liftN 1 k
      = blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i
  par : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
    rs[i]? = some r → ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) →
      blockRecLeafAV mpC.base2.acval envC rs s eqs ψ₁ i
        = blockRecLeafAV mpC.base2.acval envC rs s eqs ψ₂ i
  wd : ∀ (ψ : Name → Nat) (i : Nat), i < rs.length → ∀ ρ : Nat → V,
    WellDenoted V ρ (blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i)
  valid : ∀ (ψ : Name → Nat) (i : Nat) (ρ : Nat → V),
    AnnotValid V ρ (blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i)
  pre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
    ConLeche.Semantics.BlockRecPre V (s ψ) rs.length
      (blockRecTyAV mpC.base2.acval envC rs ψ) (eqs ψ) ρ

/-- Off the stored recursors' names the valuation is the base one. -/
theorem blockRecAcv_of_notin {acval : Name → (Name → Nat) → AnnotTerm} {envC : Env}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {s : (Name → Nat) → Nat} {eqs : (Name → Nat) → List AnnotTerm} {n : Name}
    (hne : ∀ r ∈ rs, n ≠ r.1.name) : blockRecAcv acval envC rs s eqs n = acval n := by
  refine blockRecAcvOf_of_ne (fun m hm => ?_)
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
  exact hne r hr

/-- At the `i`-th stored recursor's name the valuation is the family's
`i`-th leaf. -/
theorem blockRecAcv_at {acval : Name → (Name → Nat) → AnnotTerm} {envC : Env}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {s : (Name → Nat) → Nat} {eqs : (Name → Nat) → List AnnotTerm}
    (hnd : (rs.map (·.1.name)).Nodup) {i : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)} (hr : rs[i]? = some r)
    (ψ : Name → Nat) :
    blockRecAcv acval envC rs s eqs r.1.name ψ
      = ConLeche.Semantics.blockRecAV (s ψ) rs.length (blockRecTyAV acval envC rs ψ) (eqs ψ) i := by
  have hi : (rs.map (·.1.name))[i]? = some r.1.name := by
    rw [List.getElem?_map, hr]; rfl
  rw [blockRecAcv, blockRecAcvOf_at hnd hi]
  rfl

/-- The leaf facts, at a stored recursor's name of the valuation. -/
theorem BlockRecLeafOk.stored {envC : Env} {mpC : EnvModelM V μ envC}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {s : (Name → Nat) → Nat} {eqs : (Name → Nat) → List AnnotTerm}
    (hleaf : BlockRecLeafOk mpC rs s eqs) (hnd : (rs.map (·.1.name)).Nodup)
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)} (hr : r ∈ rs) :
    (∀ ψ, Term.Closed ((blockRecAcv mpC.base2.acval envC rs s eqs r.1.name ψ).erase)) ∧
    (∀ ψ k, (blockRecAcv mpC.base2.acval envC rs s eqs r.1.name ψ).liftN 1 k
      = blockRecAcv mpC.base2.acval envC rs s eqs r.1.name ψ) ∧
    (∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) →
      blockRecAcv mpC.base2.acval envC rs s eqs r.1.name ψ₁
        = blockRecAcv mpC.base2.acval envC rs s eqs r.1.name ψ₂) ∧
    (∀ ψ (ρ : Nat → V), WellDenoted V ρ (blockRecAcv mpC.base2.acval envC rs s eqs r.1.name ψ)) ∧
    (∀ ψ (ρ : Nat → V), AnnotValid V ρ (blockRecAcv mpC.base2.acval envC rs s eqs r.1.name ψ)) := by
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hr
  simp only [blockRecAcv_at hnd hi]
  exact ⟨fun ψ => hleaf.closed ψ i, fun ψ k => hleaf.liftN ψ i k,
    fun ψ₁ ψ₂ hq => hleaf.par i r hi ψ₁ ψ₂ hq,
    fun ψ ρ => hleaf.wd ψ i (List.getElem?_eq_some_iff.mp hi).1 ρ, fun ψ ρ => hleaf.valid ψ i ρ⟩

/-- The `.nested` firings' pins facts: at every stored recursor `j`
whose rules fire `.nested lvls pins`, the rule prefix sits below the
major, the levels and pins are well scoped at the recursor, and the
major's domain is the pinned container applied to the pins and the
index variables. -/
abbrev NestedFiresOk (envC : Env) (p : BlockParts)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (fireOf : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) →
      ConLeche.RecRuleFire) : Prop :=
  ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
    rs[j]? = some r → ∀ lvls pins, fireOf j r = .nested lvls pins →
      p.toBlockShape.rulePrefixAt j ≤ p.toBlockShape.majorIdxAt j ∧
      (∀ l ∈ lvls, l.allParamsDefined r.1.levelParams = true) ∧
      (∀ pin ∈ pins, pin.hasFvar = false ∧
        pin.allLevelParamsDefined r.1.levelParams = true ∧
        pin.constsResolve envC = true ∧
        pin.looseBVarsBounded (p.toBlockShape.rulePrefixAt j) = true ∧
        ∀ (T : Name) (i : Nat), envC.findProj? T i = none → Expr.NoProjAt T i pin) ∧
      ∃ pre dom body bm D,
        r.1.type.stripPis (p.toBlockShape.majorIdxAt j) = some (pre, .forallE dom body bm) ∧
        dom.getAppFn = .const D lvls ∧
        dom.getAppArgs =
          pins.map (Expr.liftLooseBVars
            (p.toBlockShape.majorIdxAt j - p.toBlockShape.rulePrefixAt j) 0) ++
            (List.range (p.toBlockShape.majorIdxAt j - p.toBlockShape.rulePrefixAt j)).map
              (fun i => Expr.bvar
                (p.toBlockShape.majorIdxAt j - p.toBlockShape.rulePrefixAt j - 1 - i))

/-- **At every stored rule**: `P` holds at every model `m₃` of the
recursors' cons whose valuation is `blockRecAcv … s eqs`, every level
valuation `φ`, and every stored pair (recursor `j` with data `r`,
constructor `i` = `cA` with right-hand side `rhs`), and the pair's stored
rule bits. -/
abbrev AtStoredRules {envC : Env} (mpC : EnvModelM V μ envC)
    (R : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) → List ConLeche.RecRule)
    (p : BlockParts) (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (s : (Name → Nat) → Nat) (eqs : (Name → Nat) → List AnnotTerm) (nPc : Nat → Nat)
    (fireOf : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) →
      ConLeche.RecRuleFire)
    (P : EnvModel V (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) → (Name → Nat) →
      Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) → Nat →
      ConstantVal × Nat → Expr → ConLeche.RecRule → Prop) : Prop :=
  ∀ m₃ : EnvModel V (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC),
    m₃.acval = blockRecAcv mpC.base2.acval envC rs s eqs →
    ∀ (φ : Name → Nat) (j : Nat) (r : ConstantVal × List Expr × Nat ×
      List (ConstantVal × Nat)), rs[j]? = some r →
    ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
      P m₃ φ j r i cA rhs (ConLeche.recRuleBits envC.find? r.1.name
        { ctor := cA.1.name, nfields := cA.2, ctorParams := nPc j,
          fire := fireOf j r, rhs := rhs, paramsBlind := true })

/-- **The recursor stage, at the run, at any rules of the shape**: the
cons at a rules function `R` whose stored
rules have the SHAPE (`RecRulesShape`), the `.nested` firings' pins
facts (`hnest`), the stage's record at any majors (`RecStageG`), the
stored names distinct (`hnd`), the LEAF's facts with the family premise
(`BlockRecLeafOk`) and the rule seam (`hnew`, at every non-`.inert`
firing). -/
theorem blockRecStaged_runR {envC : Env} (hμ : μ.verifiedChecks = true)
    (mpC : EnvModelM V μ envC) {p : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {s : (Name → Nat) → Nat} {eqs : (Name → Nat) → List AnnotTerm}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    (hnd : (rs.map (·.1.name)).Nodup)
    {R : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) → List ConLeche.RecRule}
    {nPc : Nat → Nat}
    {fireOf : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) →
      ConLeche.RecRuleFire}
    (hshape : ConLeche.RecRulesShape envC.find? R rs nPc fireOf)
    (hnest : NestedFiresOk envC p rs fireOf)
    (hctorsIn : ∀ r ∈ rs, ∀ cA ∈ r.2.2.2,
      ∃ cvj cnP cnF, envC.find? cA.1.name = some (.ctorInfo cvj cnP cnF))
    (hleaf : BlockRecLeafOk mpC rs s eqs)
    (hnew : AtStoredRules mpC R p rs s eqs nPc fireOf fun m₃ φ j r _ _ _ rl =>
      fireOf j r ≠ .inert →
        RecRuleLaw m₃ φ r.1.name r.1 (p.toBlockShape.majorIdxAt j)
          (p.toBlockShape.rulePrefixAt j) rl) :
    BlockRecStagedAt (V := V) μ envC (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC)
      mpC := by
  have hfacts := ConLeche.recStage_facts h
  have hcv := recStage_cvFacts h
  have hag : ∀ n : Name, (∀ r ∈ rs, n ≠ r.1.name) →
      blockRecAcv mpC.base2.acval envC rs s eqs n = mpC.base2.acval n :=
    fun _ => blockRecAcv_of_notin
  have hL := fun r (hr : r ∈ rs) => hleaf.stored hnd hr
  exact blockRecStaged_of mpC hnd
    (fun r hr => (hcv r hr).1) (fun r hr => (hcv r hr).2.1) (fun r hr => (hcv r hr).2.2.1)
    (fun r hr => ⟨(hfacts r hr).1, (hfacts r hr).2.1, (hfacts r hr).2.2.1,
      (hfacts r hr).2.2.2.1⟩)
    hag (fun r hr => (hL r hr).1) (fun r hr => (hL r hr).2.1) (fun r hr => (hL r hr).2.2.1)
    (fun r hr => (hL r hr).2.2.2.1) (fun r hr => (hL r hr).2.2.2.2)
    (hrd_of_pre hμ mpC h rfl
      (fun i r hr ψ => by obtain ⟨-, -, -, hread, -⟩ := recStage_tyPis hμ mpC h hr ψ; exact hread)
      (fun i r hr ψ => blockRecAcv_at hnd hr ψ) hleaf.pre)
    (fun r hr rhs hrhs => (hfacts r hr).2.2.2.2 rhs hrhs)
    hctorsIn hshape hnest
    (hrecP_ofR mpC hshape (fun r hr => (hcv r hr).1) (fun r hr => (hcv r hr).2.2.1) hag hnew)
    (ConLeche.recStage_reserved h)
    (fun r hr T i hslot => (hcv r hr).2.2.2 T i hslot)
    (fun r hr rhs hrhs T i hslot => recStage_rhsNoProj h r hr rhs hrhs T i hslot)


end ConLeche.Model

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
recursor stage's cons, stated at eighteen premises; `declBlock`
(`Model/Inductives/DeclBlock.lean`) consumes it through the named
`BlockRecStaged`.  This module is the seam between them: it discharges
from the CHECK'S OWN RUN every premise that is a syntactic fact about
the stored recursors, so that what is left of the Model half is the
two SEMANTIC seams — the family premise (`BlockRecPre`, the recursor
model `blockRecPre_graph`)
and the rule data (`BlockRuleDataAt`, `hnew`).

What the run supplies, and where it comes from:

| premise | source |
|---|---|
| `hty`, `hrhs` | `recStage_facts` |
| `hresRec` | `recStage_reserved` |
| `hfr`, `hnres`, `hpsh` | `checkConstantVal_inv` at the per-recursor type record (`recStage_tyAt`) |
| `hnoTy` | `annotateCore_noProjAt` at the SAME run |
| `hrd` | `hrd_of_pre`, at the family premise |
| `hrecP` | `hrecP_ofR`, at the rule data |

and the generated guarded call's freedom from free variables
(`hnofv`) is here too, beside the other facts about the generated
forms.
-/

namespace ConLeche.Model

open ConLeche.Semantics (AnnotTerm)
open ConLeche.Semantics SetTheory
open ConLeche.Term
open ConLeche (Env Expr Name Level ConstantVal ConstantInfo RecRule BlockShape BlockParts
  consBlockRecs)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## 1. The generated guarded call carries no free variable

`hnofv`: the Π-tower `blockIhSpinePis` builds has `hasFvar = false`.
It is a one-level computation — the tower's binder
domains are `structIdxAt`-lifts of the constructor's own field
telescope, the spine is the rule's prefix `bvar`s, the field's index
expressions (again `structIdxAt`-lifted) and one applied `bvar`, and
the head is a `.const` — so it needs nothing of the constructor beyond
its type's own freedom from free variables. -/

/-! ## 2. The stored recursors' NAMES

The `k` recursors are checked at ONE environment — the constructors' —
so `checkConstantVal`'s freshness says each is fresh THERE and says
nothing about the `k` names being pairwise distinct.  That is the
NAME-SET check's (`blockRecNameSetOk`): the stored names are,
as a set, exactly `{T.rec : T a member}`, and there are as many of them
as there are members.  With the members' own names distinct, a
pigeonhole closes it. -/

/-- **The pigeonhole**: a list as long as a `Nodup` list it covers is
itself `Nodup`. -/
theorem nodup_of_subset_length {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {L M : List α}, M.Nodup → M ⊆ L → L.length ≤ M.length → L.Nodup
  | [], _, _, _, _ => List.nodup_nil
  | a :: L', M, hM, hML, hlen => by
    have hdup : a ∉ L' := by
      intro ha
      have hsub : M ⊆ L' := by
        intro x hx
        rcases List.mem_cons.mp (hML hx) with rfl | h
        · exact ha
        · exact h
      have := List.Nodup.length_le_of_subset hM hsub
      simp only [List.length_cons] at hlen
      omega
    refine List.nodup_cons.mpr ⟨hdup, ?_⟩
    by_cases hmem : a ∈ M
    · refine nodup_of_subset_length (M := M.erase a) (List.Nodup.erase a hM) ?_ ?_
      · intro x hx
        rcases List.mem_cons.mp (hML (List.mem_of_mem_erase hx)) with rfl | h
        · exact absurd hx (List.Nodup.not_mem_erase hM)
        · exact h
      · rw [List.length_erase_of_mem hmem]
        simp only [List.length_cons] at hlen
        omega
    · exfalso
      have hsub : M ⊆ L' := by
        intro x hx
        rcases List.mem_cons.mp (hML hx) with rfl | h
        · exact absurd hx hmem
        · exact h
      have := List.Nodup.length_le_of_subset hM hsub
      simp only [List.length_cons] at hlen
      omega


/-! ## 3. The stage, inverted at the NAMES and the per-recursor run

The per-index facts and the stored recursors' name facts
(`recStage_recNames`, `recStage_cvFacts`) are kernel
inversions and live in `Verify/Inductives/BlockRecNames.lean`, shared
with the η-closure's recursor freshness (`checkBlockRec_fresh`). -/


/-! ## 4. The stored RULES are annotated, and therefore mention no
empty slot

`hnoRhs` is `hnoTy`'s twin one stage down: a stored right-hand side is
`annotateCore`'s output at the BARE-`k` environment, whose `findProj?`
is the constructors' (`findProj?_consBlockRecsBare`).  Both facts
below are fields of the stage's rule record (`RecKRun.ruleOf`,
`Verify/Inductives/BlockRecRun.lean`). -/

section Annot

/-- **`blockRecStaged_of`'s `hnoRhs`**: a stored rule's right-hand side
mentions no EMPTY projection slot of the constructors' environment.
It is `annotateCore_noProjAt` at the environment the stage annotates
in — the BARE-`k` one, whose `findProj?` is `envC`'s, because no
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
    obtain ⟨-, -, hps, -⟩ := ConLeche.checkConstantVal_inv E.hcv
    rw [E.name_eq]
    exact hps
  intro r hr rhsA hrhsA T i hslot
  obtain ⟨c, hc⟩ := List.getElem?_of_mem hr
  obtain ⟨j, rc, rhs0, -, -, Q⟩ := R.ruleOutOf hc hrhsA
  refine ConLeche.annotateCore_noProjAt μ Q.hann Q.hfv ?_
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
  obtain ⟨i, rc, rhs0, -, -, Q⟩ := R.ruleOutOf hc hrhsA
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
    exact absurd ((List.getElem_inj hnd).mp this) (by omega)
  funext ψ
  simp [blockRecAcvOf, h]

/-! ## 6. The stage, assembled

`blockRecStaged_run` is `blockRecStaged_of` with every SYNTACTIC
premise read off the run and the VALUATION defined rather than
assumed, in the shape `declBlock` consumes (`BlockRecStaged`).  The
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

/-- **The recursor stage, at the run, at any rules of the shape** (lane
NESTIND, session 14): the cons at a rules function `R` whose stored
rules have the SHAPE (`RecRulesShape`), the `.nested` firings' pins
facts (`hnest`), the stage's record at any majors (`RecStageG`), the
stored names distinct (`hnd`), the LEAF's five facts and the two SEMANTIC
seams (`hpre`, and `hnew` at every non-`.inert` firing). -/
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
    (hnest : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
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
                  (p.toBlockShape.majorIdxAt j - p.toBlockShape.rulePrefixAt j - 1 - i)))
    (hctorsIn : ∀ r ∈ rs, ∀ cA ∈ r.2.2.2,
      ∃ cvj cnP cnF, envC.find? cA.1.name = some (.ctorInfo cvj cnP cnF))
    (hleafCl : ∀ (ψ : Name → Nat) (i : Nat),
      Term.Closed ((blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i).erase))
    (hleafLift : ∀ (ψ : Name → Nat) (i k : Nat),
      (blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i).liftN 1 k
        = blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i)
    (hleafPar : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[i]? = some r → ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) →
        blockRecLeafAV mpC.base2.acval envC rs s eqs ψ₁ i
          = blockRecLeafAV mpC.base2.acval envC rs s eqs ψ₂ i)
    (hleafOk : ∀ (ψ : Name → Nat) (i : Nat), i < rs.length → ∀ ρ : Nat → V,
      WellDenoted V ρ (blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i))
    (hleafVal : ∀ (ψ : Name → Nat) (i : Nat) (ρ : Nat → V),
      AnnotValid V ρ (blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i))
    (hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) rs.length
        (blockRecTyAV mpC.base2.acval envC rs ψ) (eqs ψ) ρ)
    (hnew : ∀ m₃ : EnvModel V (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC),
      m₃.acval = blockRecAcv mpC.base2.acval envC rs s eqs →
      ∀ (φ : Name → Nat) (j : Nat) (r : ConstantVal × List Expr × Nat ×
        List (ConstantVal × Nat)), rs[j]? = some r →
      ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
        r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
        fireOf j r ≠ .inert →
        RecRuleLaw m₃ φ r.1.name r.1 (p.toBlockShape.majorIdxAt j)
          (p.toBlockShape.rulePrefixAt j)
          (ConLeche.recRuleBits envC.find? r.1.name
            { ctor := cA.1.name, nfields := cA.2, ctorParams := nPc j,
              fire := fireOf j r, rhs := rhs, paramsBlind := true })) :
    BlockRecStagedAt (V := V) μ envC (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC)
      mpC := by
  have hfacts := ConLeche.recStage_facts h
  have hcv := recStage_cvFacts h
  -- the valuation's two defining facts
  have hag : ∀ n : Name, (∀ r ∈ rs, n ≠ r.1.name) →
      blockRecAcv mpC.base2.acval envC rs s eqs n = mpC.base2.acval n := by
    intro n hne
    refine blockRecAcvOf_of_ne (fun m hm => ?_)
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
    exact hne r hr
  have hacv : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[i]? = some r → ∀ ψ : Name → Nat,
        blockRecAcv mpC.base2.acval envC rs s eqs r.1.name ψ
          = ConLeche.Semantics.blockRecAV (s ψ) rs.length
              (blockRecTyAV mpC.base2.acval envC rs ψ) (eqs ψ) i := by
    intro i r hr ψ
    have hi : (rs.map (·.1.name))[i]? = some r.1.name := by
      rw [List.getElem?_map, hr]; rfl
    rw [blockRecAcv, blockRecAcvOf_at hnd hi]
    rfl
  have hty : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[i]? = some r → ∀ ψ : Name → Nat,
        denoteMeta mpC.base2.acval envC ψ 0 r.1.type
          = some (blockRecTyAV mpC.base2.acval envC rs ψ i) := by
    intro i r hr ψ
    obtain ⟨-, -, -, hread, -⟩ := recStage_tyPis hμ mpC h hr ψ
    exact hread
  -- the leaf's facts, transported to the valuation
  have hidx : ∀ r ∈ rs, ∃ i : Nat, rs[i]? = some r := fun r hr => List.getElem?_of_mem hr
  exact blockRecStaged_of mpC hnd
    (fun r hr => (hcv r hr).1) (fun r hr => (hcv r hr).2.1) (fun r hr => (hcv r hr).2.2.1)
    (fun r hr => ⟨(hfacts r hr).1, (hfacts r hr).2.1, (hfacts r hr).2.2.1,
      (hfacts r hr).2.2.2.1⟩)
    hag
    (fun r hr ψ => by
      obtain ⟨i, hi⟩ := hidx r hr
      rw [hacv i r hi ψ]; exact hleafCl ψ i)
    (fun r hr ψ k => by
      obtain ⟨i, hi⟩ := hidx r hr
      rw [hacv i r hi ψ]; exact hleafLift ψ i k)
    (fun r hr ψ₁ ψ₂ hq => by
      obtain ⟨i, hi⟩ := hidx r hr
      rw [hacv i r hi ψ₁, hacv i r hi ψ₂]
      exact hleafPar i r hi ψ₁ ψ₂ hq)
    (fun r hr ψ ρ => by
      obtain ⟨i, hi⟩ := hidx r hr
      rw [hacv i r hi ψ]
      exact hleafOk ψ i (List.getElem?_eq_some_iff.mp hi).1 ρ)
    (fun r hr ψ ρ => by
      obtain ⟨i, hi⟩ := hidx r hr
      rw [hacv i r hi ψ]; exact hleafVal ψ i ρ)
    (hrd_of_pre hμ mpC h rfl hty hacv hpre)
    (fun r hr rhs hrhs => (hfacts r hr).2.2.2.2 rhs hrhs)
    hctorsIn hshape hnest
    (hrecP_ofR mpC hshape (fun r hr => (hcv r hr).1) (fun r hr => (hcv r hr).2.2.1) hag hnew)
    (ConLeche.recStage_reserved h)
    (fun r hr T i hslot => (hcv r hr).2.2.2 T i hslot)
    (fun r hr rhs hrhs T i hslot => recStage_rhsNoProj h r hr rhs hrhs T i hslot)


end ConLeche.Model

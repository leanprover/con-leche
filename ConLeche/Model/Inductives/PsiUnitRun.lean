module

public import ConLeche.Model.Inductives.PsiRun
public import ConLeche.Verify.Inductives.NestedUnits

public section

/-!
# ψ at every UNIT, from the run — the consumer stated first (task #279 M-C″, DESIGN §M.58 (d)/(e))

Task #312 refuted `BridgeSyntax` at the run (DESIGN §M.55): the pins
minted from a container that is ITSELF nested form a transport cycle,
and ψ as a fold along `nestedTopoOrder` cannot exist there.  DESIGN
§M.58 replaces the fold's UNIT: not the pin but the ROOT container's
RECURSOR FAMILY at the pin's parameters (`NestedUnit`,
`Verify/Inductives/NestedUnits.lean`) — the unit's terms are ONE
application of that family (`J.rec`, `J.rec_1`, …) at motives the
block's copies of the unit's pins, minors that rebuild with the
copies' constructors, an inductive hypothesis at every position the
RECURSOR VIEW of the root's datum calls recursive (`ksR` — the nested
positions of a real constructor and every recursive position of a
family constructor), and the earlier units' terms at the transports
that leave the unit.  At a singleton unit (a non-nested container's
mint group) the term is today's `psiTerm` syntactically
(`psiUnitTerm_singleton`).

This module states the run-level CONSUMER first (the naming rule): the
unit fold along a topological order of `UnitRef` is `PsiTypedPi` at
every pin, at the pin's root datum and member position, from

* `UnitTable` — K.25 U1 read at the run (the fold's indexing);
* `TopoOrder (UnitRef …)` — K.25's unit order read at the run
  (`unitFold_spec`);
* `UnitStepTyped` — the unit step's typing at the datum: from
  `PsiTypedPi` at the entries of the units a unit refers to, the step's
  term is `PsiTypedPi` at each of the unit's pins.  Its discharge is
  §M.58 (d)'s datum-level work (`psiSetup_of_unit`: `PsiSetup` in the
  recursor view, the copy members' facts through the family pins'
  records and the two reading links, U2–U4 consumed there) and takes
  `CopyCtorsOfRun` and the surviving mention conjunct (`UnitBridge`)
  as its inputs — which is why neither is named HERE.

`psiUnitFold_typed_of_run` is `psiFold_typed_of_run`'s twin; the two
coexist until the unit step is discharged and the consumers
(`NestedRunCore`, `psiFinal`, R1/R2) move over.
-/

namespace ConLeche.Model
open ConLeche.Semantics

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps RecRule MutualBlock ElimState
  NestedPin AuxType NestedUnit)

universe w

variable {V : Type w} [SetTheory V]

namespace IndRepData

variable (d : IndRepData V)

/-! ## The unit's choice: leaves at the family's pins, hypotheses in the recursor view -/

/-- The fold's leaves for a unit: member `t` of the root's recursor
family is the block's copy at pin `ms t` (auxiliary member `k₀ + ms t`).
At a singleton unit `ms t = base + t` and this is `psiL`. -/
@[expose] def psiLU (m : EnvModel V env) (ψ : Name → Nat) (k₀ : Nat) (ms : Nat → Nat) :
    Nat → AnnotTerm :=
  fun t => m.acval (d.memberName (k₀ + ms t)) ψ

/-- Which fields use the hypothesis at a unit: the RECURSOR view's
recursive ones — a real constructor's nested positions (`P4C.append`'s
`Array (P4C α)`) and every recursive position of a family
constructor.  At a non-nested container `ksR = ksF` and this is
`psiUseIh`. -/
@[expose] def psiUseIhU (dJ : IndRepData V) : Nat → Nat → Bool :=
  fun Jc i => decide (i ∈ ConLeche.recIdxOf (dJ.ksR Jc))

/-- The transports at a unit: a field recursive in the copy's
constructor but NOT in the root's recursor view — its target is
outside the unit — carried by the table's term for the target copy
(`psiVia` with `ksF ↦ ksR`). -/
@[expose] def psiViaU (dJ : IndRepData V) (ψ : Name → Nat) (k₀ nPJ : Nat) (auxOf : Nat → Nat)
    (b : Nat) (tbl : Nat → AnnotTerm) : Nat → Nat → Option ViaSpec :=
  fun Jc i =>
    if i ∈ ConLeche.recIdxOf (d.ksR (auxOf Jc)) ∧ i ∉ ConLeche.recIdxOf (dJ.ksR Jc) ∧
        k₀ ≤ d.tgtsR (auxOf Jc) i then
      some ((tbl (d.tgtsR (auxOf Jc) i - k₀)).liftN nPJ 0,
        ((d.eissR (auxOf Jc) ψ).getD i []).map
          (·.liftN nPJ (i + ((d.tssR (auxOf Jc) ψ).getD i []).length)),
        rebit b (liftDoms nPJ i ((d.tssR (auxOf Jc) ψ).getD i [])))
    else none

/-- **The unit's term at member `t` of the root's recursor family**: the
root container's recursor `recNames t` (`J.rec` at a real member,
`J.rec_i` at a mimic motive) at the root pin's readings, the motives
the block's copies of the unit's pins (`psiLU`), the minors the
rebuilding bodies over ALL constructors of the recursor's block
(`nAll`) with hypotheses in the recursor view and transports out of
the unit through the table. -/
@[expose] def psiUnitTerm (m : EnvModel V env) (ψ : Name → Nat) (k₀ : Nat) (c : CopyData V)
    (ms : Nat → Nat) (auxOf : Nat → Nat) (tbl : Nat → AnnotTerm) (t : Nat) : AnnotTerm :=
  AnnotTerm.mkAppN (m.acval (c.dJ.recNames t) c.ψ')
    (c.DsA ++ c.dJ.motChoiceAVs m c.ψ' c.DsA
        (c.dJ.invTgAV c.ψ' c.DsA (d.psiLU m ψ k₀ ms) (d.psiPinsT c.dJ.nP)) ++
      c.dJ.minChoiceAVs c.ψ' c.DsA
        (c.dJ.motChoiceAVs m c.ψ' c.DsA
          (c.dJ.invTgAV c.ψ' c.DsA (d.psiLU m ψ k₀ ms) (d.psiPinsT c.dJ.nP)))
        (c.dJ.psiBodyAV (d.psiHead m ψ c.dJ.nP auxOf) (psiUseIhU c.dJ)
          (d.psiViaU c.dJ ψ k₀ c.dJ.nP auxOf (c.dJ.bb c.ψ') tbl)) c.dJ.nAll)

/-- **A singleton unit is today's case**: at a container whose recursor
view is its functor view (`ksR = ksF`) and whose family is its mint
group (`ms t = base + t`), the unit's term at the copy's own member is
`psiTerm`. -/
theorem psiUnitTerm_singleton (m : EnvModel V env) (ψ : Name → Nat) (k₀ : Nat) (c : CopyData V)
    (auxOf : Nat → Nat) (tbl : Nat → AnnotTerm)
    (hview : ∀ J, c.dJ.ksR J = c.dJ.ksF J) :
    d.psiUnitTerm m ψ k₀ c (fun t => c.base + t) auxOf tbl c.mm = d.psiTerm m ψ k₀ c auxOf tbl := by
  have hL : d.psiLU m ψ k₀ (fun t => c.base + t) = d.psiL m ψ k₀ c.base := by
    funext t
    simp only [psiLU, psiL, Nat.add_assoc]
  have hU : psiUseIhU c.dJ = psiUseIh c.dJ := by
    funext Jc i
    simp only [psiUseIhU, psiUseIh, hview]
  have hV : d.psiViaU c.dJ ψ k₀ c.dJ.nP auxOf (c.dJ.bb c.ψ') tbl
      = d.psiVia c.dJ ψ k₀ c.dJ.nP auxOf (c.dJ.bb c.ψ') tbl := by
    funext Jc i
    simp only [psiViaU, psiVia, hview]
  unfold psiUnitTerm psiTerm
  rw [hL, hU, hV]

/-! ## The step over a unit, and the property at a pin -/

/-- The fold's step at unit `u`: the whole table, with the unit's
entries set to the unit's terms at their member positions (the pin's
index in the unit's member list) and every other entry untouched. -/
@[expose] def psiUnitStep (m : EnvModel V env) (ψ : Name → Nat) (k₀ : Nat) (cd : Nat → CopyData V)
    (auxOfs : Nat → Nat → Nat) (units : List NestedUnit) (tbl : Nat → AnnotTerm) (u : Nat) :
    Nat → AnnotTerm :=
  fun j =>
    match units[u]? with
    | some U =>
      if j ∈ U.members then
        d.psiUnitTerm m ψ k₀ (cd U.root) (fun t => U.members.getD t 0) (auxOfs U.root) tbl
          (U.members.idxOf j)
      else tbl j
    | none => tbl j

/-- The step's frame condition: an entry the unit does not own is
untouched. -/
theorem psiUnitStep_frame (m : EnvModel V env) (ψ : Name → Nat) (k₀ : Nat) (cd : Nat → CopyData V)
    (auxOfs : Nat → Nat → Nat) (units : List NestedUnit) (tbl : Nat → AnnotTerm) (u j : Nat)
    (h : ¬ ConLeche.unitOwns units u j) :
    d.psiUnitStep m ψ k₀ cd auxOfs units tbl u j = tbl j := by
  unfold psiUnitStep
  cases hU : units[u]? with
  | none => rfl
  | some U =>
    simp only
    rw [if_neg (fun hm => h ⟨U, hU, hm⟩)]

/-- **The fold's property at pin `j`**: for every unit owning `j`, the
term is `PsiTypedPi` at the unit's ROOT datum, the root pin's
assignment and readings, the unit's leaves, and `j`'s member position
in the root's recursor family.  At a singleton unit this is `PsiP` at
the pin's own data. -/
@[expose] def PsiPU (m : EnvModel V env) (ψ : Name → Nat) (k₀ : Nat) (σ : Nat → V)
    (cd : Nat → CopyData V) (units : List NestedUnit) (j : Nat) (Ψ : AnnotTerm) : Prop :=
  ∀ U ∈ units, j ∈ U.members →
    (cd U.root).dJ.PsiTypedPi m (cd U.root).ψ' σ (cd U.root).DsA
      (d.psiLU m ψ k₀ (fun t => U.members.getD t 0)) (d.psiPinsT (cd U.root).dJ.nP)
      (U.members.idxOf j) Ψ

end IndRepData

/-- **The unit step is typed** — NAMED (DESIGN §M.58 (d), its discharge
the datum-level work of `psiSetup_of_unit`): at any table whose entries
at the units `u` refers to are `PsiPU`, the step's term at each of
`u`'s pins is `PsiPU`.  Consumed at the run by `psiUnitFold_typed_of_run`
through `psiUnitFold_typed`. -/
@[expose] def UnitStepTyped {μ : CheckMode} (mp : EnvModelM V μ env) (d : IndRepData V)
    (ψ : Name → Nat) (k₀ : Nat) (σ : Nat → V) (cd : Nat → CopyData V) (auxOfs : Nat → Nat → Nat)
    (units : List NestedUnit) (R : Nat → Nat → Prop) : Prop :=
  ∀ (tbl : Nat → AnnotTerm) (u : Nat) (U : NestedUnit), units[u]? = some U →
    (∀ u', R u u' → ∀ j, ConLeche.unitOwns units u' j → d.PsiPU mp.base2 ψ k₀ σ cd units j (tbl j)) →
    ∀ j ∈ U.members,
      d.PsiPU mp.base2 ψ k₀ σ cd units j (d.psiUnitStep mp.base2 ψ k₀ cd auxOfs units tbl u j)

namespace IndRepData

variable (d : IndRepData V)

/-- **ψ at every pin, over units** (the datum level): the unit fold along
a topological order of `R` from any initial table is `PsiPU` at every
pin, from the unit table (the fold's indexing) and the step's typing
(`UnitStepTyped`). -/
theorem psiUnitFold_typed {μ : CheckMode} (mp : EnvModelM V μ env) {ψ : Name → Nat} {k₀ : Nat}
    {σ : Nat → V} {cd : Nat → CopyData V} {auxOfs : Nat → Nat → Nat} {n : Nat}
    {units : List NestedUnit} (hunits : ConLeche.UnitTable n units)
    {R : Nat → Nat → Prop} {order : List Nat} (hord : TopoOrder R units.length order)
    (hstep : UnitStepTyped mp d ψ k₀ σ cd auxOfs units R) (tbl₀ : Nat → AnnotTerm) :
    ∀ j, j < n →
      d.PsiPU mp.base2 ψ k₀ σ cd units j
        (ConLeche.unitFold (d.psiUnitStep mp.base2 ψ k₀ cd auxOfs units) order tbl₀ j) := by
  intro j hj
  obtain ⟨u, hu⟩ := hunits.complete j hj
  have hun : u < units.length := by
    obtain ⟨U, hU, -⟩ := hu
    exact (List.getElem?_eq_some_iff.mp hU).1
  refine hord.unitFold_all (d.psiUnitStep mp.base2 ψ k₀ cd auxOfs units)
    (fun j Ψ => d.PsiPU mp.base2 ψ k₀ σ cd units j Ψ) (ConLeche.unitOwns units) hunits.disj
    (fun tbl u j h => d.psiUnitStep_frame mp.base2 ψ k₀ cd auxOfs units tbl u j h) ?_ tbl₀ u hun j hu
  intro tbl u ih j hj
  obtain ⟨U, hU, hm⟩ := hj
  exact hstep tbl u U hU ih j hm

end IndRepData

/-! ## ψ at every unit, from the run -/

set_option maxHeartbeats 800000 in
/-- **ψ AT EVERY PIN OVER UNITS, FROM THE RUN** (DESIGN §M.58 (e), the
consumer stated first): under the containers' representation, for
every level assignment and parameter frame of the scratch block, the
unit fold along a topological order of `UnitRef` — K.25's unit order —
is `PsiPU` at every pin, given the unit table (K.25 U1) and the unit
step's typing (`UnitStepTyped`) at the pins' data `cd` this run reads
(`pinFacts_of_run`).  The three are NAMED here, each consumed at the
run's own `st`/`d`/`cd`: the table by the fold's indexing, the order
by `unitFold_spec`, the step's typing by the step. -/
theorem psiUnitFold_typed_of_run {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {env envOut : Env} {p : ConLeche.NestedParts} (mp : EnvModelM V μ env)
    (hE : ConLeche.EtaFamiliesClosed env) (h : DeclNestedRun μ F env p envOut) :
    ∃ (st : ElimState) (b : MutualBlock) (envAux : Env),
      ConLeche.auxBlock p st = some b ∧
      st.types.length = p.k + st.pins.length ∧
      ∃ (mpAux : EnvModelM V μ envAux) (d : IndRepData V), MutualBlockReps mpAux.base2 b d ∧
        CtorsChecked μ F env b true d ∧
        ∃ (params : List Expr) (pbs : List (Expr × ConLeche.BinderMeta)),
        (ContainersRep env envAux mpAux.base2 → ∀ ψ : Name → Nat,
          ∃ cd : Nat → CopyData V,
            (∀ j, j < st.pins.length → PinRunFacts F env p st b params pbs mpAux d ψ cd j) ∧
            ∀ (units : List NestedUnit) (order : List Nat),
              -- NAMED (K.25 U1, read at the run): the unit table
              ConLeche.UnitTable st.pins.length units →
              -- NAMED (K.25's unit order, read at the run)
              TopoOrder (ConLeche.UnitRef p.k st units) units.length order →
              ∀ (ρ₀ : Nat → V) (psA : List AnnotTerm), psA.length = d.nP →
                SpineFit ρ₀ (d.params ψ) (psA.map (interp V ρ₀)) →
                ∀ auxOfs : Nat → Nat → Nat,
                  -- NAMED (§M.58 (d)): the unit step's typing at the datum
                  UnitStepTyped mpAux d ψ p.k (consList (psA.map (interp V ρ₀)) ρ₀) cd auxOfs units
                    (ConLeche.UnitRef p.k st units) →
                  ∀ (tbl₀ : Nat → AnnotTerm) (j' : Nat), j' < st.pins.length →
                    d.PsiPU mpAux.base2 ψ p.k (consList (psA.map (interp V ρ₀)) ρ₀) cd units j'
                      (ConLeche.unitFold (d.psiUnitStep mpAux.base2 ψ p.k cd auxOfs units) order
                        tbl₀ j')) := by
  obtain ⟨st, b, envAux, params, pbs, fmsA, ctorsA, stored, order, hb, -, -, hlenSt, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, mpAux, d, hreps, hchk, -, hpins⟩ := pinFacts_of_run hμ mp hE h
  refine ⟨st, b, envAux, hb, hlenSt, mpAux, d, hreps, hchk, params, pbs, ?_⟩
  intro hcr ψ
  obtain ⟨cd, hcd⟩ := hpins hcr ψ
  refine ⟨cd, hcd, ?_⟩
  intro units order hunits hord ρ₀ psA _hpsA _hparamsA auxOfs hstep tbl₀ j' hj'
  exact d.psiUnitFold_typed mpAux hunits hord hstep tbl₀ j' hj'

end ConLeche.Model

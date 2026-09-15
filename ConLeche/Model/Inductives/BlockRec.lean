module

public import ConLeche.Model.Inductives.BlockRecCand
public import ConLeche.Semantics.Tower.SigChainI
public section

/-!
# The block's recursors: the consumer (task #315, M3)

**The uniform route's recursors are ONE chosen tuple, pinned by its ι
equations** (DESIGN §U.4): the Σ'-chain of the `k` recursor types
followed by the conjunction of the rules' equations, chosen by
`choice`, member `mm`'s leaf its `mm`-th projection
(`Semantics/Tower/SigChainI.lean`, `blockRecAVI`).  This file spells
the rules' equations at official's `k`-motive shape and states the
run-level consumer `blockRecs`: the leaves are typed at the recursor
types' readings, graded, and their tuple satisfies every rule's
equation — from the readings' formation, the equations' grading at
every fitting tuple, and the CANDIDATE tuple's typing and equations
(`BlockRepData.blockCand`, the union recursor at the frame's motives
and minors, `BlockRecCand.lean`).  The four named facts are M3's
remaining sessions (DESIGN §U.4 (f)); `blockRecs` is their consumer.

**The equation of rule `J`** (member `mJ`'s constructor, `nF` fields,
under the `k` tuple binders `r₀ … r_{k-1}`):

    Π p⃗ M⃗ m⃗ f⃗,  r_{mJ} p⃗ M⃗ m⃗ e⃗_J(f⃗) (C_J p⃗ f⃗)  =  m_J f⃗ ih⃗

`specEqAV`: the `Prop`-valued Π-tower over the rule's binder data (the
`k`-motive `mutualRuleDataAV`, bits `0`) of `specLhsAV = specRuleCoreAV`;
the right-hand side is `mutualRuleCoreAV` with the recursor of the
member a field targets the TUPLE's variable at the ih's depth
(`tupleVarAV`), so the equation mentions no leaf — the leaves are what
the chosen tuple's projections turn out to be.  `blockRecs_iota` reads
an equation's membership as the ι rule at every fitting spine
(`pt_mem_mkPisAV_eqE_iff`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The ι-specification's terms -/

/-- Member `t`'s recursor variable of the Σ'-specification, seen `dp`
binders above the `k` tuple binders (`r_{k-1}` is the innermost). -/
@[expose] def tupleVarAV (k dp t : Nat) : AnnotTerm := .bvar (dp + (k - 1 - t))

/-- **Rule `J`'s right-hand side** in the specification:
`mutualRuleCoreAV` with the recursor of the member field `i` targets
the tuple's variable at the ih's depth (the rule's leaf plus the
field's telescope). -/
@[expose] def specRuleCoreAV (b k : Nat) (tgtsJ : Nat → Nat) (nP n nF J : Nat) (recIdx : List Nat)
    (tls : List (List (Nat × Nat × AnnotTerm))) (Eiss : List (List AnnotTerm)) : AnnotTerm :=
  AnnotTerm.mkAppN (.bvar (nF + n - 1 - J))
    (fieldBvars nF ++ recIdx.map fun i =>
      ihAppAVK (tupleVarAV k (nP + k + n + nF + (tls.getD i []).length) (tgtsJ i)) nP k n nF i
        (rebit b (tls.getD i [])) (Eiss.getD i []))

/-- **Rule `J`'s left-hand side**: member `mJ`'s recursor variable at
the block's variables `p⃗ M⃗ m⃗`, the constructor's index readings (moved
under the `k + n` extras) and the constructor's leaf at the parameters
and fields. -/
@[expose] def specLhsAV (k nP n nF mJ : Nat) (Es : List AnnotTerm) (C : AnnotTerm) : AnnotTerm :=
  AnnotTerm.mkAppN (tupleVarAV k (nP + k + n + nF) mJ)
    (recPrefixBvarsMK nP k n nF 0 ++ Es.map (fun E => E.liftN (k + n) nF) ++
      [AnnotTerm.mkAppN C (paramBvarsAt nP (nP + k + n + nF) ++ fieldBvars nF)])

/-- **Rule `J`'s equation**: the `Prop`-valued Π-tower over the rule's
binder data of `lhs = rhs`. -/
@[expose] def specEqAV (ruleData : List (Nat × AnnotTerm)) (lhs rhs : AnnotTerm) : AnnotTerm :=
  mkPisAV (ruleData.map fun d => (0, 0, d.2)) (.eqE lhs rhs)

omit [SetTheory V] in
theorem specEqAV_bits (ruleData : List (Nat × AnnotTerm)) :
    ∀ d ∈ ruleData.map (fun d : Nat × AnnotTerm => ((0 : Nat), (0 : Nat), d.2)), d.2.1 = 0 := by
  intro d hd
  obtain ⟨d', -, rfl⟩ := List.mem_map.mp hd
  rfl

/-- An equation is a truth value at every frame. -/
theorem specEqAV_univZero (ruleData : List (Nat × AnnotTerm)) (lhs rhs : AnnotTerm) (ρ : Nat → V) :
    interp V ρ (specEqAV ruleData lhs rhs) ∈ˢ (univZero : V) := by
  unfold specEqAV
  cases ruleData with
  | nil => exact eqv_mem_univZero _ _
  | cons d ds =>
    show piR 0 _ _ ∈ˢ _
    exact piR_zero_mem_univZero

/-- An equation holds at a frame iff the ι rule holds at every fitting
spine there. -/
theorem pt_mem_specEqAV_iff (ruleData : List (Nat × AnnotTerm)) (lhs rhs : AnnotTerm) (ρ : Nat → V) :
    (pt : V) ∈ˢ interp V ρ (specEqAV ruleData lhs rhs) ↔
      ∀ xs : List V, SpineFit ρ (ruleData.map (·.2)) xs →
        interp V (consList xs ρ) lhs = interp V (consList xs ρ) rhs := by
  unfold specEqAV
  rw [pt_mem_mkPisAV_eqE_iff (specEqAV_bits ruleData)]
  simp only [List.map_map, Function.comp_def]

/-! ## The consumer -/

/-- **The block's recursor leaves**: member `mm`'s leaf at the level
assignment `ψ`, from the recursor types' readings `rdsM`/`concM`, the
types' sort `s` and the equations `eqs`. -/
@[expose] def blockLeafAV (s : Nat) (k : Nat) (rdsM : Nat → List (Nat × Nat × AnnotTerm))
    (concM : Nat → AnnotTerm) (eqs : List AnnotTerm) (mm : Nat) : AnnotTerm :=
  blockRecAVI s k (fun t => mkPisAV (rdsM t) (concM t)) eqs mm

/-- **THE CONSUMER — the block's recursors** (DESIGN §U.4 (e)).  At a
block datum `d` whose `k` recursor types read to `mkPisAV (rdsM mm ψ)
(concM mm)` and whose rules' equations are `eqs ψ`: if the readings
are formed at a sort `s ψ` and graded (`hT`), the equations are truth
values and graded at every fitting tuple (`heq`), and the CANDIDATE
tuple — the union recursor at the frame's motives and minors,
`d.blockCand` — is typed at the readings (`hcand`) and satisfies every
equation (`hceq`), then at every frame the leaves `blockLeafAV` are
typed at the readings, graded, and their tuple satisfies every
equation.  The four premises are named facts with this consumer
(DESIGN §U.4 (f)). -/
theorem blockRecs (d : BlockRepData V) (s ℓ : (Name → Nat) → Nat)
    (rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (concM : Nat → AnnotTerm)
    (eqs : (Name → Nat) → List AnnotTerm)
    (hT : ∀ (ψ : Name → Nat) (ρ : Nat → V) (mm : Nat), mm < d.k →
      interp V ρ (mkPisAV (rdsM mm ψ) (concM mm)) ∈ˢ (univ (s ψ) : V) ∧
      WellDenoted V ρ (mkPisAV (rdsM mm ψ) (concM mm)))
    (heq : ∀ (ψ : Name → Nat) (ρ : Nat → V) (rs : List V), rs.length = d.k →
      (∀ mm, mm < d.k → rs.getD mm pt ∈ˢ interp V ρ (mkPisAV (rdsM mm ψ) (concM mm))) →
      ∀ e ∈ eqs ψ, interp V (consList rs ρ) e ∈ˢ (univZero : V) ∧ WellDenoted V (consList rs ρ) e)
    (hcand : ∀ (ψ : Name → Nat) (ρ : Nat → V) (mm : Nat), mm < d.k →
      d.blockCand ψ (ℓ ψ) (rdsM mm ψ) mm ρ ∈ˢ interp V ρ (mkPisAV (rdsM mm ψ) (concM mm)))
    (hceq : ∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ e ∈ eqs ψ,
      (pt : V) ∈ˢ interp V
        (consList ((List.range d.k).map fun mm => d.blockCand ψ (ℓ ψ) (rdsM mm ψ) mm ρ) ρ) e) :
    ∀ (ψ : Name → Nat) (ρ : Nat → V), ∃ a : Nat → V,
      (∀ mm, mm < d.k →
        a mm ∈ˢ interp V ρ (mkPisAV (rdsM mm ψ) (concM mm)) ∧
        interp V ρ (blockLeafAV (s ψ) d.k (fun t => rdsM t ψ) concM (eqs ψ) mm) = a mm ∧
        WellDenoted V ρ (blockLeafAV (s ψ) d.k (fun t => rdsM t ψ) concM (eqs ψ) mm)) ∧
      ∀ e ∈ eqs ψ, (pt : V) ∈ˢ interp V (consList ((List.range d.k).map a) ρ) e := by
  intro ψ ρ
  exact blockRecAVI_facts (s ψ) d.k (fun t => mkPisAV (rdsM t ψ) (concM t)) (eqs ψ) ρ
    (hT ψ ρ) (heq ψ ρ) (fun mm => d.blockCand ψ (ℓ ψ) (rdsM mm ψ) mm ρ) (hcand ψ ρ) (hceq ψ ρ)

/-- **The ι rule of rule `J`, read off the tuple**: with the tuple's
components `a`, an equation's membership is the rule at every spine
fitting the rule's binder data at the tuple frame. -/
theorem blockRecs_iota {ρ : Nat → V} {k : Nat} {a : Nat → V}
    {ruleData : List (Nat × AnnotTerm)} {lhs rhs : AnnotTerm}
    (h : (pt : V) ∈ˢ interp V (consList ((List.range k).map a) ρ) (specEqAV ruleData lhs rhs)) :
    ∀ xs : List V, SpineFit (consList ((List.range k).map a) ρ) (ruleData.map (·.2)) xs →
      interp V (consList xs (consList ((List.range k).map a) ρ)) lhs
        = interp V (consList xs (consList ((List.range k).map a) ρ)) rhs :=
  (pt_mem_specEqAV_iff ruleData lhs rhs _).mp h

end ConLeche.Model

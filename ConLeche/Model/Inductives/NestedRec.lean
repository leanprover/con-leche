module

public import ConLeche.Model.Inductives.NestedRecCand
public import ConLeche.Model.Inductives.BlockRec
public section

/-!
# The nested block's recursors: the consumer (task #315, M7 — lane L-D)

`BlockRec.lean`'s `blockRecs` at `k + nPins` CLASSES: the restored
recursors of a nested block — the members' `T_m.rec` and the
auxiliary `T.rec_q` (one per pin, official's `mk_aux_rec_name_map`) —
are ONE chosen tuple pinned by its ι equations (DESIGN §U.4 (a)), the
Σ'-chain of the `k + nPins` restored recursor types followed by the
conjunction of every rule's equation — the members' rules AND the
auxiliary rules (the simultaneous fold: a member's rule whose field
targets a pin fires the pin's recursor, a pin's rule whose field
targets a member fires the member's) — chosen by `choice`, class `c`'s
leaf its `c`-th projection (`blockLeafAV` at `k + nPins`).  The
CANDIDATE tuple is `BlockModel.blockCandT`: the class recursor over the
extended union (`NestedRecCand.lean`) at the frame's `k + nPins`
motives and `nCtorsT` minors.

**The statement** `nestedRecs` is `blockRecs`'s verbatim with `d.k`
replaced by `d.kT` and the candidate by `blockCandT`; its proof is the
same one line (`blockRecAVI_facts` is generic in the class count).
Its four premises are the named facts of this lane, with `nestedRecs`
as their consumer (DESIGN §U.25 (c)):

* `hT` — the `k + nPins` restored recursor types' readings formed at a
  sort and graded (the readings at `k + nPins`: the pins' motives read
  the container at the pin's components, the pins' minors the
  container's constructors at them — the stage's, from
  `restoreRecTys`);
* `heq` — the rules' equations graded at every fitting tuple (the
  member rules' AND the auxiliary rules');
* `hcand` — the candidate typed at the readings (the kit's bound and
  step obligations at the extended classes: `kitBT_mem` is proved at
  a semantic motive typing; `kitStT_mem` needs the pins' minors'
  readings);
* `hceq` — every equation at the candidate (`blockRecAtT_eq` per rule,
  member rules and auxiliary rules alike, the step decoded by the
  class's injection).

`nestedRecs_iota` is `blockRecs_iota` (generic in `k`): an equation's
membership at the tuple is the ι rule at every fitting spine.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule)

universe w

variable {V : Type w} [SetTheory V]

/-- **THE CONSUMER — the nested block's recursors** (DESIGN §U.25).
At a block model `d` with the pins' constructors `pc`, whose `k +
nPins` restored recursor types read to `mkPisAV (rdsM c ψ) (concM c)`
and whose rules' equations (members' and auxiliary) are `eqs ψ`: if
the readings are formed at a sort `s ψ` and graded (`hT`), the
equations are truth values and graded at every fitting tuple (`heq`),
and the CANDIDATE tuple — the class recursor over the extended union
at the frame's motives and minors, `d.blockCandT pc` — is typed at the
readings (`hcand`) and satisfies every equation (`hceq`), then at every
frame the leaves `blockLeafAV` at `k + nPins` are typed at the
readings, graded, and their tuple satisfies every equation.  The four
premises are named facts with this consumer. -/
theorem nestedRecs (d : BlockModel V) (pc : Nat → PinCtors V) (s ℓ : (Name → Nat) → Nat)
    (rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (concM : Nat → AnnotTerm)
    (eqs : (Name → Nat) → List AnnotTerm)
    (hT : ∀ (ψ : Name → Nat) (ρ : Nat → V) (c : Nat), c < d.kT →
      interp V ρ (mkPisAV (rdsM c ψ) (concM c)) ∈ˢ (univ (s ψ) : V) ∧
      WellDenoted V ρ (mkPisAV (rdsM c ψ) (concM c)))
    (heq : ∀ (ψ : Name → Nat) (ρ : Nat → V) (rs : List V), rs.length = d.kT →
      (∀ c, c < d.kT → rs.getD c pt ∈ˢ interp V ρ (mkPisAV (rdsM c ψ) (concM c))) →
      ∀ e ∈ eqs ψ, interp V (consList rs ρ) e ∈ˢ (univZero : V) ∧ WellDenoted V (consList rs ρ) e)
    (hcand : ∀ (ψ : Name → Nat) (ρ : Nat → V) (c : Nat), c < d.kT →
      d.blockCandT pc ψ (ℓ ψ) (rdsM c ψ) c ρ ∈ˢ interp V ρ (mkPisAV (rdsM c ψ) (concM c)))
    (hceq : ∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ e ∈ eqs ψ,
      (pt : V) ∈ˢ interp V
        (consList ((List.range d.kT).map fun c => d.blockCandT pc ψ (ℓ ψ) (rdsM c ψ) c ρ) ρ) e) :
    ∀ (ψ : Name → Nat) (ρ : Nat → V), ∃ a : Nat → V,
      (∀ c, c < d.kT →
        a c ∈ˢ interp V ρ (mkPisAV (rdsM c ψ) (concM c)) ∧
        interp V ρ (blockLeafAV (s ψ) d.kT (fun t => rdsM t ψ) concM (eqs ψ) c) = a c ∧
        WellDenoted V ρ (blockLeafAV (s ψ) d.kT (fun t => rdsM t ψ) concM (eqs ψ) c)) ∧
      ∀ e ∈ eqs ψ, (pt : V) ∈ˢ interp V (consList ((List.range d.kT).map a) ρ) e := by
  intro ψ ρ
  exact blockRecAVI_facts (s ψ) d.kT (fun t => mkPisAV (rdsM t ψ) (concM t)) (eqs ψ) ρ
    (hT ψ ρ) (heq ψ ρ) (fun c => d.blockCandT pc ψ (ℓ ψ) (rdsM c ψ) c ρ) (hcand ψ ρ) (hceq ψ ρ)

/-- **The ι rule of a rule, read off the tuple** — a member's or an
auxiliary one: `blockRecs_iota` at `k + nPins` classes. -/
theorem nestedRecs_iota {ρ : Nat → V} {kT : Nat} {a : Nat → V}
    {ruleData : List (Nat × AnnotTerm)} {lhs rhs : AnnotTerm}
    (h : (pt : V) ∈ˢ interp V (consList ((List.range kT).map a) ρ) (specEqAV ruleData lhs rhs)) :
    ∀ xs : List V, SpineFit (consList ((List.range kT).map a) ρ) (ruleData.map (·.2)) xs →
      interp V (consList xs (consList ((List.range kT).map a) ρ)) lhs
        = interp V (consList xs (consList ((List.range kT).map a) ρ)) rhs :=
  blockRecs_iota h

omit [SetTheory V] in
/-- At a block without pins the classes are the members: the `k + 0`
classes, the extended union the carrier's. -/
theorem BlockModel.kT_of_noPins (d : BlockModel V) (hnp : d.pins = []) : d.kT = d.k := by
  simp only [BlockModel.kT, BlockModel.nPins, hnp, List.length_nil, Nat.add_zero]

end ConLeche.Model

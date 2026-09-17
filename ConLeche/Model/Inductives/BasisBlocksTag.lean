module

public import ConLeche.Model.Inductives.NestedPremise
import ConLeche.Model.Inductives.BasisBlocksNat
public section

/-!
# The tag shape against the pinned carriers: `Nat` and `PUnit` have NO block model (task #315, M7-4)

`ContainerModeled.inj` (`NestedPremise.lean`) demands that a stored
container's injections BE the tagged towers, `d.inj ψ mm j fs = injW
(d.w ψ) j (mkTower (fs ++ [pt]))` — the shape the nested route's pin
identification reads (`pinLeaf`, DESIGN §U.15 (a)).  At a `Type`-valued
block the tower is `inj j … = spair (vnat j) … = kpair …`, so every
element of the carrier is a Kuratowski pair.

**The pinned basis carriers are not built that way.**  `Nat` is `ω`,
whose element `natzero = ∅` is no pair (`kpair_ne_empty`), and `PUnit`
is `{pt}`, whose element is the proof point, chosen precisely so that
it is no pair (`pt_ne_kpair`).  So `ContainerModeled` is UNSATISFIABLE
at either block, and with it `EnvBlockModels` at any environment that
stores them — which every accepted environment does.

The obstruction is `ContainerModeled.inj` alone: `IsBlockModel` itself
keeps the injections abstract, and the pinned carriers satisfy its
clauses (`Nat`'s `Φ` is the successor operator, whose least pre-fixed
family is `ω`).  `Empty`, `False` and `Eq` are unaffected — the first
two have no constructor to inject, and `Eq` is `Prop`-valued, where
`injW 0 j _ = pt` IS the pinned value.

The two theorems below are the counter-instance, with the READ-BACK
computed for `Nat` so that the obligation they refute is the one the
field actually raises.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecRule ContainerInfo ContainerMember)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The obstruction -/

/-- **Every element of a modelled container's carrier is a Kuratowski
pair**, at a member whose stored type is a bare sort (no parameters,
no indices) and at a level assignment where that sort is nonzero: the
leaf reads the carrier, the fibre decomposes it by the constructors,
and `ContainerModeled.inj` makes every injection a tagged tower. -/
theorem ContainerModeled.mem_carrier_kpair {env : Env} {m : EnvModel V env} {ci : ContainerInfo}
    {d : BlockModel V} (C : ContainerModeled m ci d)
    (Cinj : ∀ (ψ : Name → Nat) (mm' j : Nat) (fs : List V),
      d.inj ψ mm' j fs = injW (d.w ψ) j (mkTower (fs ++ [pt])))
    (hnP : ci.nP = 0)
    {i : Nat} {M : ContainerMember} (hM : ci.members[i]? = some M) {s : Level}
    (hty : M.type = .sort s) {ψ : Name → Nat} (hw : s.eval ψ ≠ 0) {ρ : Nat → V} {x : V}
    (hx : x ∈ˢ interp V ρ (m.acval M.name ψ)) :
    ∃ a b : V, x = kpair a b := by
  obtain ⟨-, -, cvR, mI, rP, rules, hI⟩ := C.member i M hM
  have hnP0 : d.nP = 0 := by rw [C.nP, hnP]
  -- the member has no indices: its stored type is a bare sort
  obtain ⟨bs, s', hstrip, hs'⟩ := hI.strip
  have hst2 : (Expr.sort s).stripPis (d.nP + d.nIdxAt i) = some (bs, .sort s') := by
    rw [← hty]; exact hstrip
  rw [hnP0, Nat.zero_add] at hst2
  have hidx : d.nIdxAt i = 0 := by
    cases hn : d.nIdxAt i with
    | zero => rfl
    | succ n => rw [hn] at hst2; exact nomatch hst2
  have hsEq : ∀ ψ' : Name → Nat, s.eval ψ' = d.resSort.eval ψ' := by
    rw [hidx] at hst2
    have : s' = s := (Expr.sort.inj (Prod.mk.inj (Option.some.inj hst2)).2).symm
    rw [← this]; exact hs'
  -- the parameter and index telescopes are empty
  have hlen : (d.ppsM i ψ).length = 0 := by rw [hI.former.len ψ, hnP0, hidx]
  have hIds : d.IdsM i ψ = ([] : List AnnotTerm) := by
    show ((d.ppsM i ψ).drop d.nP).map (·.2.2) = []
    rw [hnP0, List.eq_nil_of_length_eq_zero hlen]; rfl
  have hpar : d.params ψ = ([] : List AnnotTerm) := by
    show ((d.ppsM 0 ψ).take d.nP).map (·.2.2) = []
    rw [hnP0]; rfl
  have hρp : Sat V (d.params ψ).reverse ρ := by rw [hpar]; exact Sat_nil V ρ
  -- the leaf, at the empty parameter and index spines
  have hleaf := hI.leaf ψ ρ [] [] (by rw [hpar]; exact trivial) (by rw [hIds]; exact trivial)
  rw [List.append_nil, List.foldl_nil] at hleaf
  have ht : d.tup ψ i [] ∈ˢ d.idx ψ (consList [] ρ) i :=
    d.tupMem (ψ := ψ) (ρp := consList [] ρ) (mm' := i) (is := []) (by rw [hIds]; exact trivial)
  have hρp' : Sat V (d.params ψ).reverse (consList [] ρ) := hρp
  rw [hleaf, ← hI.carrier_app_eq hρp' hI.memberLt ht] at hx
  obtain ⟨j, fs, -, -, rfl⟩ :=
    (hI.fibre ψ (consList [] ρ) hρp' _ (lfpTuple_mem _ _ _ _) i hI.memberLt _ ht _).mp hx
  refine ⟨vnat j, mkTower (fs ++ [pt]), ?_⟩
  rw [Cinj ψ i j fs, injW_pos (by rw [show d.w ψ = s.eval ψ from (hsEq ψ).symm]; exact hw)]
  unfold SetTheory.Tower.inj SetTheory.spair
  rfl

/-! ## The counter-instances: the UNGUARDED clause, refuted -/

/-- **`Nat` admits no block model with the TAGGED injections**: its
carrier `ω` holds `natzero = ∅`, which is no Kuratowski pair, while the
unguarded tag shape makes every element of a `Type`-valued block's
carrier one.  The historical form of task #315 M7-4's refutation (DESIGN
§U.42 (c)): before the guard, this hypothesis WAS
`ContainerModeled.inj`, so `EnvBlockModels` was unsatisfiable at every
environment storing the pinned block.  Kept as the reason the guard
`0 < d.nP` is there. -/
theorem no_containerModeled_nat_unguarded {env : Env} {m : EnvModel V env} {d : BlockModel V}
    (hT : env.find? ConLeche.natName = some ConLeche.natA)
    (C : ContainerModeled m ⟨0, [⟨ConLeche.natName, [], ConLeche.natA.toConstantVal.type,
        [⟨ConLeche.natZeroName, ConLeche.natZeroA.toConstantVal.type, 0⟩,
         ⟨ConLeche.natSuccName, ConLeche.natSuccA.toConstantVal.type, 1⟩]⟩]⟩ d) :
    ¬ ∀ (ψ : Name → Nat) (mm' j : Nat) (fs : List V),
        d.inj ψ mm' j fs = injW (d.w ψ) j (mkTower (fs ++ [pt])) := by
  intro Cinj
  have hval : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (m.acval ConLeche.natName ψ) = (omega : V) := by
    intro ψ ρ
    have hpd : ConLeche.Verify.pinnedStructT ConLeche.natName ψ
        = some (Term.const .nat []) := by
      simp +decide [ConLeche.Verify.pinnedStructT]
    rw [acval_basis_pinned hT (by decide) hpd]
    rfl
  have hmem : (empty : V) ∈ˢ interp V (fun _ => pt) (m.acval ConLeche.natName (fun _ => 0)) := by
    rw [hval]; exact empty_mem_omega
  obtain ⟨a, b, hab⟩ := C.mem_carrier_kpair Cinj (i := 0) rfl rfl (s := .succ .zero) rfl
    (ψ := fun _ => 0) (by decide) (ρ := fun _ => pt) hmem
  exact kpair_ne_empty hab.symm

/-- **`PUnit` admits no block model with the TAGGED injections**: its
carrier `{pt}` holds the proof point, chosen so that it is no
Kuratowski pair (`Derive/Pt.lean`), at every level assignment where
`PUnit` is not `Prop`-valued.  The second half of the refutation the
guard answers. -/
theorem no_containerModeled_punit_unguarded {env : Env} {m : EnvModel V env} {d : BlockModel V}
    (hT : env.find? ConLeche.punitName = some ConLeche.punitA)
    (C : ContainerModeled m ⟨0, [⟨ConLeche.punitName, [ConLeche.uN],
        ConLeche.punitA.toConstantVal.type,
        [⟨ConLeche.punitUnitName, ConLeche.punitUnitA.toConstantVal.type, 0⟩]⟩]⟩ d) :
    ¬ ∀ (ψ : Name → Nat) (mm' j : Nat) (fs : List V),
        d.inj ψ mm' j fs = injW (d.w ψ) j (mkTower (fs ++ [pt])) := by
  intro Cinj
  have hval : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (m.acval ConLeche.punitName ψ) = (unitSet : V) := by
    intro ψ ρ
    have hpd : ConLeche.Verify.pinnedStructT ConLeche.punitName ψ
        = some (Term.const .punit [ψ ConLeche.uN]) := by
      simp +decide [ConLeche.Verify.pinnedStructT]
    rw [acval_basis_pinned hT (by decide) hpd]
    rfl
  have hmem : (pt : V) ∈ˢ interp V (fun _ => pt) (m.acval ConLeche.punitName (fun _ => 1)) := by
    rw [hval]; exact pt_mem_unitSet
  obtain ⟨a, b, hab⟩ := C.mem_carrier_kpair Cinj (i := 0) rfl rfl
    (s := .param ConLeche.uN) rfl (ψ := fun _ => 1) (by decide) (ρ := fun _ => pt) hmem
  exact pt_ne_kpair a b hab

/-- **Neither block is a pin's container**, which is why the guard
costs nothing: `containerInfo?` reads `nP = 0` at both (the parameter
count comes off `Nat.zero`'s and `PUnit.unit`'s records), and
`nestedOccOk` mints a pin only where a member is mentioned among
`args.take ci.nP` — empty at `ci.nP = 0`. -/
theorem containerInfo?_natA_nP {env : Env}
    (hT : env.find? ConLeche.natName = some ConLeche.natA)
    (hR : env.find? (ConLeche.natName.str "rec") = some ConLeche.natRecA)
    (hZ : env.find? ConLeche.natZeroName = some ConLeche.natZeroA)
    (hS : env.find? ConLeche.natSuccName = some ConLeche.natSuccA)
    {ci : ContainerInfo} (hci : ConLeche.containerInfo? env ConLeche.natName = some ci) :
    ci.nP = 0 := by
  rw [containerInfo?_natA hT hR hZ hS] at hci
  rw [← Option.some.inj hci]

end ConLeche.Model


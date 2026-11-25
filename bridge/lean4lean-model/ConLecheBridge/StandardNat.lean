import ConLecheBridge.Carneiro
import ConLecheBridge.IsModelNat

/-!
# In Carneiro's set theory, `Nat` denotes the standard naturals

ConLeche's `SetTheory` is first-order, so if it has a model it has one whose `ω` is not
standard (by compactness; not proved here); in such a model what `Nat` denotes has non-standard
members too (`nat_eq_omega`, `ConLecheBridge/IsModelNat.lean`).  The set theory this package
builds from Carneiro's hypothesis is not one of them:

* `omegaStandard_chain`: the `ω` of `setTheoryOfChain κ` is standard.  `ZFSet` separates by
  an arbitrary Lean predicate, so "is a meta-level numeral `vnat k`" cuts an inductive subset
  out of `ω`, and `ω` is the least inductive set.  This is the one second-order step.
* `nat_standard_chain`, `carneiro_nat_standard`: so in every model of a stream declaring the
  prelude's `Nat` and `Eq`, the literals' values `natLitVal model : ℕ → ZFSet` are exactly the
  members of what `Nat` denotes, each once.  `natLitVal model` takes `0` to `⟦Nat.zero⟧` and
  `k + 1` to `⟦Nat.succ⟧` at `k`'s value by definition, so it is an isomorphism of Lean's `ℕ`
  with what `Nat` denotes.

The comparison is with the `ℕ` of the Lean these theorems are stated in, as it has to be:
"standard" is relative to a meta-theory.
-/

universe u

open ConLeche ConLeche.SetTheory

namespace ConLecheBridge

/-- **The `ω` of `setTheoryOfChain κ` is standard**: every member is a meta-level numeral
`vnat k`.  `ZFSet.sep` separates `ω` by that (Lean-level) property; the subset is inductive,
and `ω` is the least inductive set. -/
theorem omegaStandard_chain (κ : ℕ → Cardinal.{u}) (hmono : StrictMono κ)
    (hinacc : ∀ n, (κ n).IsInaccessible) :
    @OmegaStandard ZFSet.{u} (setTheoryOfChain κ hmono hinacc) := by
  let inst : SetTheory ZFSet.{u} := setTheoryOfChain κ hmono hinacc
  intro i hi
  have hI : Inductive (ZFSet.sep (fun n : ZFSet.{u} => ∃ k : ℕ, n = vnat k) omega) := by
    refine ⟨?_, fun n hn => ?_⟩
    · show (empty : ZFSet.{u}) ∈ ZFSet.sep _ _
      exact ZFSet.mem_sep.mpr ⟨(empty_mem_omega : (empty : ZFSet.{u}) ∈ˢ omega), 0, rfl⟩
    · have hn' : n ∈ ZFSet.sep (fun n : ZFSet.{u} => ∃ k : ℕ, n = vnat k) omega := hn
      obtain ⟨hno, k, rfl⟩ := ZFSet.mem_sep.mp hn'
      show vsucc (vnat k : ZFSet.{u}) ∈ ZFSet.sep _ _
      exact ZFSet.mem_sep.mpr
        ⟨(vsucc_mem_omega hno : vsucc (vnat k : ZFSet.{u}) ∈ˢ omega), k + 1, rfl⟩
  have hi' : i ∈ ZFSet.sep (fun n : ZFSet.{u} => ∃ k : ℕ, n = vnat k) omega :=
    omega_subset_inductive hI i hi
  exact (ZFSet.mem_sep.mp hi').2

/-- **Over a chain of inaccessibles, `Nat` denotes the standard naturals**: in every model, in
`setTheoryOfChain κ`, of a stream declaring the prelude's `Nat` and `Eq`, the literals' values
are exactly the members of what `Nat` denotes, each once. -/
theorem nat_standard_chain (κ : ℕ → Cardinal.{u}) (hmono : StrictMono κ)
    (hinacc : ∀ n, (κ n).IsInaccessible) {model : Name → List ℕ → ZFSet.{u}}
    {R : ConstantInfo → Prop}
    (h : @IsModel ZFSet.{u} (setTheoryOfChain κ hmono hinacc) model R)
    (hN : DeclaresNat R) (hE : DeclaresEq R) :
    (∀ x : ZFSet.{u}, x ∈ model natName [] ↔
      ∃ k : ℕ, x = @natLitVal ZFSet.{u} (setTheoryOfChain κ hmono hinacc) model k) ∧
    Function.Injective (@natLitVal ZFSet.{u} (setTheoryOfChain κ hmono hinacc) model) := by
  obtain ⟨hmem, hinj⟩ := @nat_standard ZFSet.{u} (setTheoryOfChain κ hmono hinacc) model R
    (omegaStandard_chain κ hmono hinacc) h hN hE
  exact ⟨hmem, fun k l e => hinj k l e⟩

/-- **Under Carneiro's hypothesis, `Nat` denotes the standard naturals**: in every model, in
the set theory `setTheoryOfCarneiro` builds, of a stream declaring the prelude's `Nat` and
`Eq`, the literals' values `natLitVal model : ℕ → ZFSet` are exactly the members of what `Nat`
denotes, each once. -/
theorem carneiro_nat_standard (hO : OmegaInaccessibles.{u}) {model : Name → List ℕ → ZFSet.{u}}
    {R : ConstantInfo → Prop} (h : @IsModel ZFSet.{u} (setTheoryOfCarneiro hO) model R)
    (hN : DeclaresNat R) (hE : DeclaresEq R) :
    (∀ x : ZFSet.{u}, x ∈ model natName [] ↔
      ∃ k : ℕ, x = @natLitVal ZFSet.{u} (setTheoryOfCarneiro hO) model k) ∧
    Function.Injective (@natLitVal ZFSet.{u} (setTheoryOfCarneiro hO) model) :=
  nat_standard_chain _ _ _ h hN hE

/--
info: 'ConLecheBridge.carneiro_nat_standard' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms carneiro_nat_standard

/--
info: 'ConLecheBridge.nat_eq_omega' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nat_eq_omega

end ConLecheBridge

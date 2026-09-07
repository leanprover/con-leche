import Lech.SetP.DirectFix.FixRuleDataP
import Lech.SetP.DirectFix.FixRuleOkP
import Lech.SetP.DirectFix.FixRecLeafP
import Lech.Semantics.Tower.FixWire

/-!
# The recursive recursor's stage, part 1: the rule law (task #188)

The semantic data of a recursive block at an assignment (`fssOfR`,
`essOfR`, `eissOfR`, `rssOfK`), the recursor leaf (`fixLeafAV`), the
rule's binder data as domains (`fixRuleDataAV_map_dom`), and **the
rule law** at the recursor's cons (`fixRecRuleLaw`): the sum route's
`sumRecRuleLaw` with the rule read at the cons (`fixRuleData_of`),
its gradedness from the model (`fixRuleOkP`, supplied), and the
recursor's iota (`fixRecLawCore`).
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory Lech.SetTheory.Tower
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta
  DirectFixParts RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The semantic data of a block -/

/-- The constructors' field lists. -/
def fssOfR (nP : Nat) (cds : List CtorDatumR) : List (List AVExpr) :=
  cds.map fun cd => (cd.2.2.1.drop nP).map (·.2.2)

/-- The constructors' index readings. -/
def essOfR (cds : List CtorDatumR) : List (List AVExpr) := cds.map fun cd => cd.2.2.2.1

/-- The constructors' per-field index expressions. -/
def eissOfR (cds : List CtorDatumR) : List (List (List AVExpr)) := cds.map fun cd => cd.2.2.2.2.2

/-- The recursive flags of the first `n` constructors. -/
def rssOfK (ksF : Nat → List RecFieldKind) (n : Nat) : List (List Bool) :=
  (List.range n).map fun j => rsOf (ksF j)

omit [SetTheory V] in
theorem fssOfR_getElem? (nP : Nat) (cds : List CtorDatumR) (j : Nat) :
    (fssOfR nP cds)[j]? = (cds[j]?).map fun cd => (cd.2.2.1.drop nP).map (·.2.2) := by
  simp [fssOfR]

omit [SetTheory V] in
theorem essOfR_getElem? (cds : List CtorDatumR) (j : Nat) :
    (essOfR cds)[j]? = (cds[j]?).map fun cd => cd.2.2.2.1 := by simp [essOfR]

omit [SetTheory V] in
theorem eissOfR_getElem? (cds : List CtorDatumR) (j : Nat) :
    (eissOfR cds)[j]? = (cds[j]?).map fun cd => cd.2.2.2.2.2 := by simp [eissOfR]

omit [SetTheory V] in
theorem fssOfR_length (nP : Nat) (cds : List CtorDatumR) : (fssOfR nP cds).length = cds.length := by
  simp [fssOfR]

omit [SetTheory V] in
theorem essOfR_length (cds : List CtorDatumR) : (essOfR cds).length = cds.length := by simp [essOfR]

omit [SetTheory V] in
theorem eissOfR_length (cds : List CtorDatumR) : (eissOfR cds).length = cds.length := by
  simp [eissOfR]

omit [SetTheory V] in
theorem rssOfK_getD {ksF : Nat → List RecFieldKind} {n j : Nat} (hj : j < n) :
    (rssOfK ksF n).getD j [] = rsOf (ksF j) := by
  simp [rssOfK, List.getD_eq_getElem?_getD, List.getElem?_range hj]

/-! ## The rule's binder data as domains -/

theorem fixRuleDataAV_map_dom {m : EnvS2Core V env} {T : Name} {ψ : Name → Nat} {nP nIdx : Nat}
    {ℓ : Level} {pps ips : List (Nat × Nat × AVExpr)} {cds : List CtorDatumR}
    {ds : List (Nat × Nat × AVExpr)} (hlenP : pps.length = nP) (hlenI : ips.length = nIdx) :
    (fixRuleDataAV m T ψ nP nIdx ℓ pps ips cds ds).map (·.2)
      = ((fixRecDataAV m T ψ nP nIdx ℓ pps ips cds).take (nP + 1 + cds.length)).map (·.2.2) ++
        (liftDoms (cds.length + 1) 0 (ds.drop nP)).map (·.2.2) := by
  have hlenX : (rebit (pwBit ψ (Level.zeronessOf ℓ)) pps ++
      [(0, pwBit ψ (Level.zeronessOf ℓ), motiveAVI m T ψ nP nIdx ℓ ips)] ++
      fixMinorsData m ψ nP (pwBit ψ (Level.zeronessOf ℓ)) cds 1).length = nP + 1 + cds.length := by
    simp only [List.length_append, rebit_length, hlenP, List.length_singleton, fixMinorsData_length]
  generalize hX : rebit (pwBit ψ (Level.zeronessOf ℓ)) pps ++
      [(0, pwBit ψ (Level.zeronessOf ℓ), motiveAVI m T ψ nP nIdx ℓ ips)] ++
      fixMinorsData m ψ nP (pwBit ψ (Level.zeronessOf ℓ)) cds 1 = X at hlenX
  have hlenXD : (X ++ rebit (pwBit ψ (Level.zeronessOf ℓ)) (liftDoms (cds.length + 1) 0 ips)).length
      = nP + 1 + cds.length + nIdx := by
    rw [List.length_append, hlenX, rebit_length, liftDoms_length, hlenI]
  unfold fixRuleDataAV fixRecDataAV
  rw [hX, List.take_append_of_le_length (by omega :
      nP + 1 + cds.length ≤ (X ++ rebit (pwBit ψ (Level.zeronessOf ℓ)) (liftDoms (cds.length + 1) 0 ips)).length),
    List.take_append_of_le_length (by omega : nP + 1 + cds.length ≤ X.length),
    List.take_of_length_le (by omega : X.length ≤ nP + 1 + cds.length)]
  simp only [List.map_append, List.map_map, rebit]
  rfl

/-! ## The recursor leaf -/

/-- The restriction of an assignment to a level-parameter list. -/
def restrictΨ (lps : List Name) (ψ : Name → Nat) : Name → Nat :=
  fun q => if q ∈ lps then ψ q else 0

omit [SetTheory V] in
theorem restrictΨ_agree (lps : List Name) (ψ : Name → Nat) :
    ∀ q ∈ lps, restrictΨ lps ψ q = ψ q := by
  intro q hq
  simp [restrictΨ, hq]

omit [SetTheory V] in
theorem restrictΨ_congr {lps : List Name} {ψ₁ ψ₂ : Name → Nat}
    (h : ∀ q ∈ lps, ψ₁ q = ψ₂ q) : restrictΨ lps ψ₁ = restrictΨ lps ψ₂ := by
  funext q
  unfold restrictΨ
  split
  · next hq => exact h q hq
  · rfl

/-- The recursor leaf's sort: the kernel's inferred sort at the
restricted assignment, floored at one at a nonzero elimination level,
zero at a zero one. -/
def fixSortAV (elimL : Level) (u : Level) (lps : List Name) (ψ : Name → Nat) : Nat :=
  if elimL.eval ψ = 0 then 0 else max 1 (u.eval (restrictΨ lps ψ))

omit [SetTheory V] in
theorem fixSortAV_zero_iff (elimL u : Level) (lps : List Name) (ψ : Name → Nat) :
    fixSortAV elimL u lps ψ = 0 ↔ elimL.eval ψ = 0 := by
  unfold fixSortAV
  split
  · next h => exact ⟨fun _ => h, fun _ => rfl⟩
  · next h =>
    exact ⟨fun h' => absurd h' (by have := Nat.le_max_left 1 (u.eval (restrictΨ lps ψ)); omega),
      fun h' => absurd h' h⟩

end Lech.SetP

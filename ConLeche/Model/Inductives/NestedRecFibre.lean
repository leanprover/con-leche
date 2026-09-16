module

public import ConLeche.Model.Inductives.NestedRecScratch
public section

/-!
# The fibre kit of the recursors' stage (task #315, M7-2)

PLAN-M7 §1e step 4 and §1c's bridge: the pieces that identify the
SCRATCH (auxiliary) block's semantics with the COMPOSED nested block's
at one and the same stored leaf.

* `IsBlockModels.ctorsTyped` — the constructors of ANY block model of
  an `EnvModelM` are typed at their types' readings (the run's
  `mem_type` at each stored constructor);
* `slotSet_congr_app` (with `piTele_congr`) — a recursive slot only
  sees its family through the applications at FITTING spines;
* `NestedTailIn.fibreAt` — **the fibre identity**: the scratch block's
  least tuple and the composed block's agree pointwise at fitting index
  spines (two folds of the ONE stored member leaf);
* `NestedTailIn.pinCarAt` — the same at a pin: the container's own
  least tuple against the composed one;
* `NestedTailIn.slotAt_aux` — the scratch block's recursive slots at
  its least tuple ARE the composed slots of `CopyCtorInst.fit_iff_at`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  NestedParts MutualBlock MutualFormer MutualCtor4 AuxStored ElimState NestedPin IndCaps
  fueledOps BinderMeta PropWhen RestoreTbl)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

/-! ## F1 — the constructors typed at any block model -/

/-- **The constructors are typed** at every block model of an
`EnvModelM`: the stored constructor inhabits its type's reading, which
the block model says is the Π-tower over the constructor's field
telescope ending in the member's leaf at the index readings.  The run's
`mem_type` at `BlockCtorData`'s `read`. -/
theorem IsBlockModels.ctorsTyped {env : Env} (mp : EnvModelM V μ env) {d : BlockModel V}
    (hreps : IsBlockModels mp.base2 d) (ψ : Name → Nat) : CtorsTyped mp.base2 d ψ := by
  intro c hc j cA hj ρ
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := hreps c hc
  obtain ⟨hfind, -, hCD⟩ := hI.ctors c j cA hc hj
  exact mp.mem_type _ (ConLeche.Semantics.Env.find?_mem hfind) ψ _ (hCD.read ψ) ρ

/-! ## F2 — the slot's congruence at fitting spines -/

/-- The nested product over a telescope only sees its body at FITTING
spines. -/
theorem piTele_congr {v : Nat} {B B' : List V → V} :
    ∀ {n : Nat} (T : TeleS V n) (acc : List V),
      (∀ bs, FitsS T bs → B (acc ++ bs) = B' (acc ++ bs)) →
      piTele v T B acc = piTele v T B' acc
  | _, .nil, acc, h => by
    have := h [] (by trivial)
    rw [List.append_nil] at this
    exact this
  | _, .cons A T, acc, h => by
    refine piR_congr fun x hx => piTele_congr (T x) (acc ++ [x]) fun bs hfit => ?_
    rw [List.append_assoc, List.singleton_append]
    exact h (x :: bs) ⟨hx, hfit⟩

/-- **The recursive slot's congruence**: two families whose
applications agree at every spine FITTING the field's telescope give
the same slot. -/
theorem slotSet_congr_app {w u u' : Nat} {ρ : Nat → V} {tl : List (Nat × Nat × AnnotTerm)}
    {Eis : List AnnotTerm} {X X' : V}
    (h : ∀ bs : List V, SpineFit ρ (tl.map (·.2.2)) bs →
      SetTheory.app X (tupW u (Eis.map (interp V (consList bs ρ))))
        = SetTheory.app X' (tupW u' (Eis.map (interp V (consList bs ρ))))) :
    slotSet w u ρ tl Eis X = slotSet w u' ρ tl Eis X' := by
  unfold slotSet
  refine piTele_congr _ [] fun bs hfit => ?_
  rw [List.nil_append]
  exact h bs (fitsS_teleOfFields.mp hfit)

end ConLeche.Model

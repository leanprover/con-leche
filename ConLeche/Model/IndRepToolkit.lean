module

public import ConLeche.Model.IndRep
import ConLeche.SetTheory.Derive.Bekic
import ConLeche.Model.Inductives.StructTele
public section

/-!
# The toolkit over a representation (task #280)

Theorems derived from `IndRep` (`ConLeche/Model/IndRep.lean`), never
stored: a represented family is **monotone in its parameters wherever
its functor is** — the map action on parameter positions in the form
the set model has it, an inclusion (`IndRep.leaf_mono`; least fixed
points are monotone in the functor, `lfpFamSet_mono_functor`), and
**Bekić's lemma** for the simultaneous fixed point of a family functor
over a disjoint union of index sets (`bekic_restr`, `bekic_nested`,
`ConLeche/SetTheory/Derive/Bekic.lean`), by which a nested block's
auxiliary copy of a container is identified with the container's own
least fixed point at the copy's pins (the nested design, §5.3).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-- A fitting parameter spine satisfies the parameter telescope. -/
theorem IndRepData.satOfSpine (d : IndRepData V) {ψ : Name → Nat} {ρ : Nat → V}
    {as : List V} (hsp : SpineFit ρ (d.params ψ) as) :
    Sat V (d.params ψ).reverse (consList as ρ) := by
  have := ConLeche.Model.sat_of_spineFit (Sat_nil V ρ) hsp
  simpa using this

/-- **The map action on the parameters, as an inclusion**: when the
representing functor at one parameter spine lies below the functor at
another (over the same index set), so does the represented family —
at every index.  A parameter occurring only in the chains' ordinary
domains and only positively there yields the premise; a parameter
occurring negatively (`α → Nat`) does not, and no map exists for it. -/
theorem IndRep.leaf_mono {m : EnvModel V env} {T : Name} {cvT cvR : ConstantVal} {mI rP : Nat}
    {rules : List RecRule} {d : IndRepData V} {mm : Nat} (h : IndRep m T cvT cvR mI rP rules d mm)
    {ψ : Name → Nat} {ρ : Nat → V} {as as' : List V}
    (hsp : SpineFit ρ (d.params ψ) as) (hsp' : SpineFit ρ (d.params ψ) as')
    (hidx : d.idx ψ (consList as ρ) = d.idx ψ (consList as' ρ))
    (hle : ∀ X, X ∈ˢ famSpace (d.w ψ) (d.idx ψ (consList as ρ)) →
      FamLe (d.idx ψ (consList as ρ)) (app (d.Φ ψ (consList as ρ)) X)
        (app (d.Φ ψ (consList as' ρ)) X))
    {is : List V} (hi : SpineFit (consList as ρ) (d.IdsM mm ψ) is)
    (hi' : SpineFit (consList as' ρ) (d.IdsM mm ψ) is) :
    (as ++ is).foldl app (interp V ρ (m.acval T ψ))
      ⊆ˢ (as' ++ is).foldl app (interp V ρ (m.acval T ψ)) := by
  rw [h.leaf ψ ρ as is hsp hi, h.leaf ψ ρ as' is hsp' hi']
  obtain ⟨-, hmono', -, hcl'⟩ := h.functor ψ (consList as' ρ) (d.satOfSpine hsp')
  have ht : d.tup ψ mm is ∈ˢ d.idx ψ (consList as ρ) :=
    h.tupMem ψ (consList as ρ) (d.satOfSpine hsp) is hi
  have key := lfpFamSet_mono_functor (I := d.idx ψ (consList as ρ)) hle (by rw [hidx]; exact hmono')
    (by rw [hidx]; exact hcl') _ ht
  rw [hidx] at key ⊢
  exact key

end ConLeche.Model

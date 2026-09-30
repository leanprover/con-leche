module

public import ConLeche.Model.Inductives.ClassRecKit

public section

/-!
# The step's typing at the generated family (`hstep`, G1-syn)

The graph route's producer at the generated family (`graphRecPre_gen`,
`ClassRecKit.lean`) asks for the STEP's typing, `hstep`: the rule's
residue, read at the fields and at the `ih` values the graph gives,
lands in the motive at the constructor.  At the generated rule the
residue is the MINOR PREMISE applied to the fields and the `ih`s
(`genRb0`), so its typing is the minor premise's own type: a minor of
type `Π f⃗ (ih⃗ : Π a⃗, motive_t e⃗ (f a⃗)), motive_c es mk` applied to
fitting fields and to `ih` values of their binders' types lands in
`motive_c es mk`.  What is left is that the graph's `ih` values ARE of
their binders' types: a generated `ih` is `λ a⃗, rec_t x⃗ e⃗ (f a⃗)`
(`genIhAV`), read at the chain valuation of the graph (`genF`) it is
`λ a⃗, g (tagged t e⃗ (f a⃗))` (the tower's fold), and the graph lands
in the motive at every predecessor — which the call is.

This file proves `hstep` over the minor premise's typing stated
semantically (`hminor`), the class side's call typing (`hihTy`, as in
`genIhs_hcallTy`), the conclusion's reading (`hconcl`: the motive's
variable applied to the index and major variables), and the class
side's `hmk` and index fit.  The `ih` binders' types are
`genIhDomAV` — the generated `ih`'s own telescope over the motive's
variable applied to its arguments, BY CONSTRUCTION the `ih` term's
type.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The residue and the `ih` binders -/

/-- **The generated residue**: at the rule's frame extended by the `ih`
values (depth `nPre + nF + nIh`), the minor premise of prefix position
`minPos` applied to the fields and the `ih` values. -/
@[expose] def genRb0 (nPre minPos nF nIh : Nat) : AnnotTerm :=
  AnnotTerm.mkAppN (.bvar (nIh + nF + (nPre - 1 - minPos)))
    (prefVarsAV nF nIh ++ prefVarsAV nIh 0)

/-- **A generated `ih` binder's type**, at the rule's depth `D`: the
`ih`'s telescope over the callee's motive (prefix position `mt`) applied
to the `ih`'s index and major arguments. -/
@[expose] def genIhDomAV (D mt : Nat) (q : IhDatum) : AnnotTerm :=
  mkPisAV (q.2.1.map fun p => (0, p.1, p.2))
    (AnnotTerm.mkAppN (.bvar (D + q.2.1.length - 1 - mt)) (q.2.2.1 ++ [q.2.2.2]))

/-- A prefix variable at a frame extended by `n` values. -/
theorem consList_prefix_getD {xs bs : List V} {ρ : Nat → V} {k : Nat} (hk : k < xs.length) :
    consList (xs ++ bs) ρ (bs.length + xs.length - 1 - k) = xs.getD k pt := by
  have hlen : (xs ++ bs).length = bs.length + xs.length := by simp; omega
  rw [consList_getD_of_lt _ _ _ (by omega), hlen,
    show bs.length + xs.length - 1 - (bs.length + xs.length - 1 - k) = k by omega,
    List.getD_eq_getElem?_getD, List.getElem?_append_left hk, ← List.getD_eq_getElem?_getD]

theorem interp_genRb0 {ρ : Nat → V} {xs fs hs : List V} {minPos : Nat}
    (hmin : minPos < xs.length) :
    interp V (consList hs (consList (xs ++ fs) ρ))
        (genRb0 xs.length minPos fs.length hs.length)
      = (fs ++ hs).foldl SetTheory.app (xs.getD minPos pt) := by
  rw [genRb0, interp_mkAppN, ← List.foldl_map]
  have h1 : (prefVarsAV fs.length hs.length).map (interp V (consList hs (consList (xs ++ fs) ρ)))
      = fs := by
    have := interp_prefVarsAV (V := V) (xs := fs) (bs := hs) (ρ := consList xs ρ) rfl
    rw [consList_append] at this
    rw [consList_append]
    exact this
  have h2 : (prefVarsAV hs.length 0).map (interp V (consList hs (consList (xs ++ fs) ρ))) = hs := by
    have := interp_prefVarsAV (V := V) (xs := hs) (bs := []) (ρ := consList (xs ++ fs) ρ) rfl
    simpa using this
  rw [List.map_append, h1, h2]
  congr 1
  show consList hs (consList (xs ++ fs) ρ) (hs.length + fs.length + (xs.length - 1 - minPos)) = _
  rw [← consList_append, List.append_assoc,
    show hs.length + fs.length + (xs.length - 1 - minPos)
      = (fs ++ hs).length + xs.length - 1 - minPos by simp; omega]
  exact consList_prefix_getD hmin

/-- **A λ-tower inhabits the Π-tower of the same binder data**, as soon
as its body inhabits the codomain at every fitting spine — at two frames
that agree below the telescope's bound. -/
theorem lamTower_mem_piTower :
    ∀ (tl : List (Nat × AnnotTerm)) {D : Nat} {σ σ' : Nat → V} {b C : AnnotTerm},
      FieldsBelow D (tl.map (·.2)) → (∀ i, i < D → σ i = σ' i) →
      (∀ bs, SpineFit σ' (tl.map (·.2)) bs →
        interp V (consList bs σ) b ∈ˢ interp V (consList bs σ') C) →
      interp V σ (mkLamsAV tl b) ∈ˢ interp V σ' (mkPisAV (tl.map fun p => (0, p.1, p.2)) C)
  | [], D, σ, σ', b, C, _, _, h => by simpa [mkLamsAV, mkPisAV] using h [] trivial
  | (v, A) :: tl, D, σ, σ', b, C, hb, hag, h => by
    show lamR v (interp V σ A) (fun x => interp V (cons x σ) (mkLamsAV tl b))
      ∈ˢ piR v (interp V σ' A) (fun x => interp V (cons x σ') (mkPisAV _ C))
    have hA : interp V σ A = interp V σ' A := interp_congr_below V A D σ σ' hb.1 hag
    rw [hA]
    refine lamR_mem fun x hx => ?_
    refine lamTower_mem_piTower tl (D := D + 1) hb.2 (fun i hi => ?_) (fun bs hbs => ?_)
    · cases i with
      | zero => rfl
      | succ i => exact hag i (by omega)
    · have := h (x :: bs) ⟨hx, hbs⟩
      simpa [consList_cons] using this

/-! ## `hstep` -/

section Step

variable {K : Nat} {ρ : Nat → V} {rP nCt : Nat → Nat}
  {pre idxB : Nat → List (Nat × Nat × AnnotTerm)} {majB : Nat → Nat × Nat × AnnotTerm}
  {uX : Nat → Nat} {concl : Nat → AnnotTerm}
  {fdoms es : Nat → Nat → List AnnotTerm} {mk : Nat → Nat → AnnotTerm}
  {injX : Nat → Nat → List V → V} {ihd : Nat → Nat → List IhDatum}

omit [SetTheory V] in
/-- Frames agreeing below `D` still agree below `D + |bs|` once extended
by the same spine. -/
theorem consList_congr_below : ∀ (bs : List V) {σ σ' : Nat → V} {D : Nat},
    (∀ i, i < D → σ i = σ' i) → ∀ i, i < D + bs.length → consList bs σ i = consList bs σ' i
  | [], _, _, _, h, i, hi => h i (by simpa using hi)
  | b :: bs, σ, σ', D, h, i, hi => by
    rw [consList_cons, consList_cons]
    refine consList_congr_below bs (D := D + 1) (fun k hk => ?_) i (by simp at hi; omega)
    cases k with
    | zero => rfl
    | succ k => exact h k (by omega)

end Step

end ConLeche.Model

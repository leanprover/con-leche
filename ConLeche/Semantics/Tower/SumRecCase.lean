module

public import ConLeche.Semantics.Tower.SumMk
import ConLeche.Semantics.Tower.TowerRec
import ConLeche.Semantics.Univ
@[expose] public section

/-!
# The sum recursor's case split, spelled (task #175 sum-types, stage S4a; indexed)

The body of a direct sum's recursor cases on the major's tag with a
nested `Nat.rec` tower (`caseRecAV`): stage `j` is a `Nat.rec` whose
motive is `λ k, Π (y : case (drop j) k), M ı⃗ (mk (succ^j k) y)`, whose
base is constructor `j`'s branch `λ (y : T_j), m_j (y.0) … (y.(nF_j - 1))`
(the minor applied along the uniform projections of the payload —
`towerRec`'s witness, as in the structure route; the payload's last
component, the index-equation proof, is not passed), and whose step
descends to stage `j + 1` on the predecessor tag; past the last
constructor the branch is the vacuous `λ (y : Empty), prf`.

**The frame** (task #175 indexed).  Every piece is spelled at an
explicit depth `D` below the recursor's **K-frame** — the frame
`(p⃗, motive, minors, ı⃗)` holding the parameters, the motive, the `n`
minors and the `nIdx` index variables — so the motive is `bvar (D +
nIdx + n)`, minor `j` is `bvar (D + nIdx + n - 1 - j)` and index `l` is
`bvar (D + nIdx - 1 - l)` (`RecFrameS`, with the values `frM`/`frMs`/
`frameIdx` read off the K-frame valuation `ρ₀`); the constructor
chains are the restricted chains `rChains (nIdx + n + 1) nIdx Fss Ess`
scoped at the K-frame (the field chains lifted from the parameter
frame `frP = shiftE (nIdx + n + 1) 0 ρ₀`, followed by the index
equation), and the motive is applied to the index variables before
the injection.  A plain sum is the `nIdx = 0` instance.  The nesting
(two binders per stage) is plain arithmetic and no substitution is
ever performed.

Semantically the stage-`j` motive at the numeral `i` is the product
`piR ℓ (f (j + i)) (λ y, Mi (inj (j + i) y))` (`motSem`, `Mi` the
motive at the frame's index tuple), the branch is `baseSem`, and the
three facts — membership in the motive, iota (the selected branch),
and grading — are one induction on the remaining constructor count
(`caseRec_facts`).  The minor space `minorSpI` is the structure
route's `minorSp` with an explicit conclusion function (`concI`: the
motive at the constructor's index tuple, at the injection of the
point-terminated tupler); the motive's own typing is the nested
product over the index telescope (`piTele`), from which its
applications at ANY tuple are truth values at a zero elimination
level (`piTele_app_univZero`: a fitting tuple lands in the motive's
space, an unfitting one in junk).  **The index equation is
discharged at the branch**: a payload of the restricted tower has its
index tuple equal to the frame's (`restricted_member_elim`), so the
minor's conclusion at the payload's projections IS the motive at the
frame's indices.  The case split serves the graph regime only (`w ≠
0`): at a squash instantiation the recursor body is spelled without
it (`ConLeche/Semantics/Tower/SumRec.lean`).
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## The nested product over a telescope -/


/-- The application chain `M i₀ … i_{k-1}` is graded: each prefix is a
member of a product the next index inhabits. -/
def AppChainOk (M : V) (is : List V) : Prop :=
  ∀ l, l < is.length → ∃ (v : Nat) (A : V) (B : V → V),
    (is.take l).foldl SetTheory.app M ∈ˢ piR v A B ∧ is.getD l pt ∈ˢ A ∧
    (v = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V))


/-! ## The K-frame -/


/-! ## The spelled pieces -/

/-- An application spine graded by the chain: its grading and its
value as the fold. -/
theorem mkAppN_wellDenoted_of_chain :
    ∀ {args : List AnnotTerm} {f : AnnotTerm} {σ : Nat → V},
      WellDenoted V σ f → (∀ a ∈ args, WellDenoted V σ a) →
      AppChainOk (interp V σ f) (args.map (interp V σ)) →
      WellDenoted V σ (AnnotTerm.mkAppN f args) ∧
        interp V σ (AnnotTerm.mkAppN f args)
          = (args.map (interp V σ)).foldl SetTheory.app (interp V σ f)
  | [], _, _, hf, _, _ => ⟨hf, rfl⟩
  | a :: args, f, σ, hf, hargs, hchain => by
    obtain ⟨v, A, B, hm, ha, hz⟩ := hchain 0 (by simp)
    simp only [List.take_zero, List.foldl_nil, List.map_cons, List.getD_cons_zero] at hm ha
    have hoka : WellDenoted V σ (.app f a) := by
      rw [WellDenoted_app]
      exact ⟨hf, hargs a List.mem_cons_self, v, A, B, hm, ha, hz⟩
    have hchain' : AppChainOk (interp V σ (.app f a)) (args.map (interp V σ)) := by
      intro l hl
      obtain ⟨v', A', B', hm', ha', hz'⟩ := hchain (l + 1) (by simpa using hl)
      simp only [List.map_cons, List.take_succ_cons, List.foldl_cons, List.getD_cons_succ] at hm' ha'
      exact ⟨v', A', B', hm', ha', hz'⟩
    have ih := mkAppN_wellDenoted_of_chain (args := args) (f := .app f a) hoka
      (fun a' ha' => hargs a' (List.mem_cons_of_mem _ ha')) hchain'
    rw [AnnotTerm.mkAppN_cons]
    exact ⟨ih.1, by rw [ih.2, List.map_cons, List.foldl_cons]; rfl⟩

/-! ## The hypotheses of the stage facts -/


namespace RecHypCore

variable {ℓ w : Nat} {ρ₀ : Nat → V} {Fss Ess : List (List AnnotTerm)} {Ids : List AnnotTerm}
  {famAt : List V → V}


end RecHypCore

end ConLeche.Semantics

module

import ConLeche.Semantics.Tower.SumRecCase
import ConLeche.Semantics.Tower.FixFamI
import ConLeche.Semantics.Tower.SumRec
import ConLeche.Semantics.Tower.SumWire
public import ConLeche.Semantics.Tower.IhSpell

@[expose] public section

/-!
# The recursive family's recursor, core: the step and the premise (task #188, indexed)

The recursor of a directly installed recursive family is spelled as a
**closed** term — a fixed point of its one-step unfolding over the
recursor's whole type `RecTy = Π p⃗ M m⃗ ı⃗ t, M ı⃗ t`, selected by
`Classical.choice`:

    Step := λ (r : RecTy). λ p⃗ M m⃗ ı⃗ t. case_r t     (`fixStepAVI`)
    Σ    := Σ' (r : RecTy), Step r = r                 (`fixSigAVI`)
    Sel  := (choice Σ prf).1                           (`fixSelAVI`; the leaf)

The function being unfolded thus sits at the BOTTOM of every frame of
the case split — below the parameters — so the sum route's K-frame
arithmetic (`(p⃗, M, m⃗, ı⃗)` above the frame's tail) applies unchanged,
and the recursor type's binder data, being closed, needs no lifting
under `λ r`.  The inductive hypothesis for a recursive field `f_i`
(with index expressions `e⃗_i` at the earlier fields) is
`r p⃗ M m⃗ e⃗_i f_i`, the index expressions read at the payload's
projections by SUBSTITUTION (`substProj`: `interp_inst0` at each field
binder — no λ-tower).  The case split's abstract ih obligation
(`IhArgsOk`, `FixCaseI.lean`) is discharged here.

The certificate `prf : ¬¬Σ` is the existence of a fixed point,
exhibited by rank recursion over the ω-iterate family (`fixSem`, as in
the non-indexed checkpoint): the candidate is the semantic λ-tower over
the recursor's binder data (`lamTower`) whose body at a leaf frame is the
major's own stage's value.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Term (Term)

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## The K-frame package and the ih obligation -/

namespace FixKI

variable {ℓ w u nP : Nat} {ρ₀ : Nat → V} {Fss Ess Fss₀ : List (List AnnotTerm)} {Ids : List AnnotTerm}
  {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))} {rds : List (Nat × Nat × AnnotTerm)}

/-- The `l`-th value of a fitting spine is in the `l`-th domain at the
prefix. -/
theorem spineFit_getD_mem' {ρ : Nat → V} :
    ∀ {Fs : List AnnotTerm} {as : List V} {l : Nat}, SpineFit ρ Fs as → l < Fs.length →
      as.getD l pt ∈ˢ interp V (consList (as.take l) ρ) (Fs.getD l default)
  | [], _, _, _, hl => absurd hl (Nat.not_lt_zero _)
  | _ :: _, [], _, h, _ => h.elim
  | F :: Fs, a :: as, 0, h, _ => by simpa using h.1
  | F :: Fs, a :: as, l + 1, h, hl => by
    simp only [List.getD_cons_succ, List.take_succ_cons, consList_cons]
    exact spineFit_getD_mem' (Fs := Fs) (as := as) (l := l) h.2 (by simpa using hl)

end FixKI

/-! ## K-frames of the walk -/

section WalkFrames

variable {u w : Nat} {Fss Ess Fss₀ : List (List AnnotTerm)} {Ids : List AnnotTerm} {rss : List (List Bool)}
  {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}

omit [SetTheory V] in
/-- The index tuple of a K-frame over a bottom. -/
theorem frameIdx_of (nIdx : Nat) {as is : List V} (hilen : is.length = nIdx) (ρb : Nat → V) :
    frameIdx nIdx (consList (as ++ is) ρb) = is := by
  rw [consList_append, ← hilen]
  exact frameIdx_consList' is _

end WalkFrames

/-! ## The squash regime's stages -/

section KRecZero

variable {ℓ w u : Nat} {K : Nat → V} {Fss Ess Fss₀ : List (List AnnotTerm)} {Ids : List AnnotTerm}
  {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}


end KRecZero

/-! ## The recursor's semantics -/

section Rec

variable {ℓ w u nP s : Nat} {Fss Ess Fss₀ : List (List AnnotTerm)} {Ids : List AnnotTerm}
  {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))} {rds : List (Nat × Nat × AnnotTerm)}

/-- A spine fitting a chain fits a prefix of it. -/
theorem spineFit_prefix {ρ : Nat → V} {Ds : List AnnotTerm} {as bs : List V}
    (h : SpineFit ρ Ds (as ++ bs)) : SpineFit ρ (Ds.take as.length) as := by
  have hlen : (as ++ bs).length = Ds.length := h.length_eq
  have hsplit : Ds = Ds.take as.length ++ Ds.drop as.length := (List.take_append_drop _ _).symm
  rw [hsplit] at h
  obtain ⟨as₁, as₂, heq, h1, -⟩ := spineFit_append_split h
  have hl₁ : as₁.length = as.length := by
    rw [h1.length_eq, List.length_take]
    rw [List.length_append] at hlen
    omega
  obtain ⟨rfl, -⟩ := List.append_inj heq hl₁.symm
  exact h1

end Rec

end ConLeche.Semantics

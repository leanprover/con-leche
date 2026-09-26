module

public import ConLeche.Semantics.NoBVar
public import ConLeche.Semantics.Tower.TowerKit

@[expose] public section

/-!
# Monotonicity in the holes, case by case (lane POSPROOF)

Charter item 3: "the theorem is 'returns true ⇒ the operator is
monotone', proved by inversion of [`nestPos`'s] run".  This module is
the SEMANTIC half of that inversion, over readings (`AnnotTerm`) and
`interp`, one lemma per case of `nestPos`
(`Kernel/Inductives/Positivity.lean`):

| `nestPos` case | lemma |
|---|---|
| the `whnf` step before every case | `MonoOn.of_eqOn` (the reading of the reduct is the reading of the term — `WhnfClaim`'s conclusion shape) |
| `const`: the reduct mentions no hole | `ConstOn.of_noBVar`, `ConstOn.monoOn` |
| `pi`: hole-free domain, positive codomain | `MonoOn.pi` |
| `holeApp`: a hole applied to hole-free arguments | `MonoOn.holeApp` |
| a frame's hole (in progress) at its own parameters | `MonoOn.holeAppArgs` |
| `contApp`: a container instance | `Model/Annot/BlockLfpMono.lean` (`LfpClause.leaf_le_of_holes`), through the container's lfp clause |

**The relation.**  A `FrameRel` relates a SMALLER frame to a LARGER
one: the frames agree off the hole positions (`FrameRel.AgreesOff`) and
the hole values grow (`HoleOn`: spine-wise inclusion at the hole's
arity).  A term is `MonoOn` a relation when its reading grows along it,
`ConstOn` when its reading is the same at related frames.  Under a
binder the relation is `FrameRel.under` — the SAME bound value at both
frames, taken from the smaller frame's domain (a product only reads its
codomain on its domain, `piR_subset_mono`) — and along a constructor's
field telescope it is `FrameRel.underTele`.

**The telescope** (`TeleMonoOn`, `teleOfFields_sub`, `spineFit_mono`):
a field telescope whose every field is positive under its predecessors
has a pointwise larger telescope at the larger frame — the operator's
fibre (`towerSet w (teleOfFields …)`) grows (`towerSet_mono`).  This is
the consumer's core: the block operator built from the constructor
types with holes is monotone as soon as every field reading is
`MonoOn` the tuple order (`Model/Annot/BlockLfpMono.lean`).

Nothing here is about `Expr` or the kernel: the run inversion supplies
each case's premises (`NoBVar` from "the reduct mentions no hole", the
reduct equation from `WhnfClaim`), and the relation is chosen by the
caller — holes growing (the block's own members, the consumer) or the
outer holes growing with a container's own holes FIXED (the container
case; `SetModel/HoleClose.lean`).
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## The relation and the two predicates -/

/-- A relation from a smaller frame to a larger one. -/
abbrev FrameRel (V : Type uv) := (Nat → V) → (Nat → V) → Prop

/-- **Positive**: the reading grows along the relation. -/
def MonoOn (R : FrameRel V) (a : AnnotTerm) : Prop :=
  ∀ ρ ρ', R ρ ρ' → interp V ρ a ⊆ˢ interp V ρ' a

/-- **Hole-free**: the reading is the same at related frames. -/
def ConstOn (R : FrameRel V) (a : AnnotTerm) : Prop :=
  ∀ ρ ρ', R ρ ρ' → interp V ρ a = interp V ρ' a

namespace FrameRel

/-- **Under a binder** of domain `A`: the same bound value at both
frames, a member of the SMALLER frame's domain. -/
def under (R : FrameRel V) (A : AnnotTerm) : FrameRel V :=
  fun σ σ' => ∃ x ρ ρ', σ = cons x ρ ∧ σ' = cons x ρ' ∧ R ρ ρ' ∧ x ∈ˢ interp V ρ A

/-- **Along a field telescope**: under each field in turn. -/
def underTele : FrameRel V → List AnnotTerm → FrameRel V
  | R, [] => R
  | R, F :: Fs => underTele (R.under F) Fs


/-- Related frames agree off the positions `P` (the holes). -/
def AgreesOff (R : FrameRel V) (P : Nat → Prop) : Prop :=
  ∀ ρ ρ', R ρ ρ' → AgreeOff P ρ ρ'

theorem AgreesOff.under {R : FrameRel V} {P : Nat → Prop} (h : R.AgreesOff P) (A : AnnotTerm) :
    (R.under A).AgreesOff (shiftP P) := by
  rintro _ _ ⟨x, ρ, ρ', rfl, rfl, hR, -⟩
  exact agreeOff_cons (h ρ ρ' hR) x


/-- The frames a fitting spine reaches are related along the
telescope. -/
theorem underTele_consList :
    ∀ {R : FrameRel V} {ρ ρ' : Nat → V} (Fs : List AnnotTerm) (as : List V),
      R ρ ρ' → SpineFit ρ Fs as → R.underTele Fs (consList as ρ) (consList as ρ')
  | _, _, _, [], [], hR, _ => hR
  | _, _, _, [], _ :: _, _, h => h.elim
  | _, _, _, _ :: _, [], _, h => h.elim
  | _, ρ, ρ', _ :: Fs, a :: as, hR, h =>
    underTele_consList (R := _) Fs as ⟨a, ρ, ρ', rfl, rfl, hR, h.1⟩ h.2

end FrameRel

/-! ## The cases -/

/-- A hole-free reading is (trivially) positive. -/
theorem ConstOn.monoOn {R : FrameRel V} {a : AnnotTerm} (h : ConstOn R a) : MonoOn R a :=
  fun ρ ρ' hR => by rw [h ρ ρ' hR]; exact Subset.refl _

/-- **`const`**: a reading that mentions no hole is hole-free. -/
theorem ConstOn.of_noBVar {R : FrameRel V} {P : Nat → Prop} (hR : R.AgreesOff P)
    {a : AnnotTerm} (h : NoBVar P a) : ConstOn R a :=
  fun ρ ρ' hr => interp_congr_noBVar a h (hR ρ ρ' hr)

/-- **The `whnf` step**: a term whose reading is the reading of a
positive reduct, at every frame of the domain `Q` the relation lives
in, is positive. -/
theorem MonoOn.of_eqOn {R : FrameRel V} {Q : (Nat → V) → Prop}
    (hdom : ∀ ρ ρ', R ρ ρ' → Q ρ ∧ Q ρ') {a b : AnnotTerm}
    (heq : ∀ ρ, Q ρ → interp V ρ a = interp V ρ b) (hb : MonoOn R b) : MonoOn R a := by
  intro ρ ρ' hR
  rw [heq ρ (hdom ρ ρ' hR).1, heq ρ' (hdom ρ ρ' hR).2]
  exact hb ρ ρ' hR

/-- The same for `ConstOn`. -/
theorem ConstOn.of_eqOn {R : FrameRel V} {Q : (Nat → V) → Prop}
    (hdom : ∀ ρ ρ', R ρ ρ' → Q ρ ∧ Q ρ') {a b : AnnotTerm}
    (heq : ∀ ρ, Q ρ → interp V ρ a = interp V ρ b) (hb : ConstOn R b) : ConstOn R a := by
  intro ρ ρ' hR
  rw [heq ρ (hdom ρ ρ' hR).1, heq ρ' (hdom ρ ρ' hR).2]
  exact hb ρ ρ' hR

/-- **`pi`**: a product with a hole-free domain and a positive codomain
is positive. -/
theorem MonoOn.pi {R : FrameRel V} {A B : AnnotTerm} (u v : Nat) (hA : ConstOn R A)
    (hB : MonoOn (R.under A) B) : MonoOn R (.pi u v A B) := by
  intro ρ ρ' hR
  rw [interp_pi, interp_pi, ← hA ρ ρ' hR]
  exact piR_subset_mono fun x hx => hB _ _ ⟨x, ρ, ρ', rfl, rfl, hR, hx⟩

/-- **The hole order at position `h`**: at related frames the hole's
values, applied to any `n` arguments, grow (a curried family over its
parameters and indices, compared at its full arity). -/
def HoleOn (R : FrameRel V) (h n : Nat) : Prop :=
  ∀ ρ ρ', R ρ ρ' → ∀ as : List V, as.length = n → as.foldl app (ρ h) ⊆ˢ as.foldl app (ρ' h)

/-- The hole order survives a binder (the hole one position further). -/
theorem HoleOn.under {R : FrameRel V} {h n : Nat} (hh : HoleOn R h n) (A : AnnotTerm) :
    HoleOn (R.under A) (h + 1) n := by
  rintro _ _ ⟨x, ρ, ρ', rfl, rfl, hR, -⟩ as has
  exact hh ρ ρ' hR as has

/-- **`holeApp`**: a hole applied to hole-free arguments, at its full
arity, is positive. -/
theorem MonoOn.holeApp {R : FrameRel V} {h : Nat} {es : List AnnotTerm}
    (hh : HoleOn R h es.length) (hes : ∀ e ∈ es, ConstOn R e) :
    MonoOn R (AnnotTerm.mkAppN (.bvar h) es) := by
  intro ρ ρ' hR
  rw [interp_mkAppN_foldl, interp_mkAppN_foldl, interp_bvar, interp_bvar]
  have hmap : es.map (interp V ρ) = es.map (interp V ρ') :=
    List.map_congr_left fun e he => hes e he ρ ρ' hR
  rw [hmap]
  exact hh ρ ρ' hR _ (by simp)


/-- **A hole at its instantiation's own arguments** (lane CONTSEM): at
related frames the hole's values, applied to the readings of the SAME
argument terms `ds` (a container frame's instantiation parameters) and
any `ni` further arguments (its indices), grow.  A frame's hole is its
container's family curried over the parameters; comparing it at
ARBITRARY parameter spines would compare a graph on its domain with one
off it (`app_lamR_of_not_mem`), so the order is stated where the walk
uses it: at the key's parameters, which the kernel checks syntactically
(`nestPos`'s frame-hole case). -/
def HoleOnArgs (R : FrameRel V) (h : Nat) (ds : List AnnotTerm) (ni : Nat) : Prop :=
  ∀ ρ ρ', R ρ ρ' → ∀ is : List V, is.length = ni →
    (ds.map (interp V ρ) ++ is).foldl app (ρ h) ⊆ˢ (ds.map (interp V ρ') ++ is).foldl app (ρ' h)

theorem HoleOnArgs.under {R : FrameRel V} {h : Nat} {ds : List AnnotTerm} {ni : Nat}
    (hh : HoleOnArgs R h ds ni) (A : AnnotTerm) :
    HoleOnArgs (R.under A) (h + 1) (ds.map (AnnotTerm.liftN 1 · 0)) ni := by
  rintro _ _ ⟨x, ρ, ρ', rfl, rfl, hR, -⟩ is his
  have hl : ∀ (σ : Nat → V), (ds.map (AnnotTerm.liftN 1 · 0)).map (interp V (cons x σ))
      = ds.map (interp V σ) := by
    intro σ
    rw [List.map_map]
    refine List.map_congr_left fun a _ => ?_
    show interp V (cons x σ) (a.liftN 1 0) = interp V σ a
    rw [interp_liftN]
    congr 1
  rw [hl, hl]
  exact hh ρ ρ' hR is his

/-- **An in-progress hole**: a frame's hole applied to its
instantiation's parameters and hole-free indices is positive. -/
theorem MonoOn.holeAppArgs {R : FrameRel V} {h : Nat} {ds is : List AnnotTerm}
    (hh : HoleOnArgs R h ds is.length) (his : ∀ e ∈ is, ConstOn R e) :
    MonoOn R (AnnotTerm.mkAppN (.bvar h) (ds ++ is)) := by
  intro ρ ρ' hR
  rw [interp_mkAppN_foldl, interp_mkAppN_foldl, interp_bvar, interp_bvar, List.map_append,
    List.map_append]
  have hmap : is.map (interp V ρ) = is.map (interp V ρ') :=
    List.map_congr_left fun e he => his e he ρ ρ' hR
  rw [hmap]
  exact hh ρ ρ' hR _ (by simp)

/-! ## The field telescope -/

/-- **Every field positive under its predecessors.** -/
def TeleMonoOn : FrameRel V → List AnnotTerm → Prop
  | _, [] => True
  | R, F :: Fs => MonoOn R F ∧ TeleMonoOn (R.under F) Fs


/-- **A fitting spine fits the larger telescope.** -/
theorem spineFit_mono :
    ∀ {R : FrameRel V} (Fs : List AnnotTerm), TeleMonoOn R Fs →
      ∀ {ρ ρ' : Nat → V}, R ρ ρ' → ∀ {as : List V}, SpineFit ρ Fs as → SpineFit ρ' Fs as
  | _, [], _, _, _, _, [], _ => trivial
  | _, [], _, _, _, _, _ :: _, h => h.elim
  | _, _ :: _, _, _, _, _, [], h => h.elim
  | _, _ :: Fs, ⟨hF, hFs⟩, ρ, ρ', hR, a :: _, h =>
    ⟨hF ρ ρ' hR a h.1, spineFit_mono Fs hFs ⟨a, ρ, ρ', rfl, rfl, hR, h.1⟩ h.2⟩

/-! ## Hole-free telescopes (D2: an unreached member's hole) -/

/-- No field of the telescope mentions the positions `P` (shifted under
its predecessors). -/
def NoBVarTele : (Nat → Prop) → List AnnotTerm → Prop
  | _, [] => True
  | P, F :: Fs => NoBVar P F ∧ NoBVarTele (shiftP P) Fs


end ConLeche.Semantics
